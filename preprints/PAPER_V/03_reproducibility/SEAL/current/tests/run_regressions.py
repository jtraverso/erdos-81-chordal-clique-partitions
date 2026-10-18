"""Deterministic transaction regressions; independent physical checks of all ports.
Authors: Juan Pablo Traverso Gianini.
"""
from pathlib import Path
from collections import Counter
from fractions import Fraction
import json, sys, subprocess, os, hashlib, time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'tests/results'
OUT.mkdir(exist_ok=True)
sys.path.insert(0, str(ROOT / 'python'))
import seal

cases = [
    dict(name='cap1_improves', hosts=[[0,1,2],[0,1]], caps=[1,1], initial=[[0,[0,1]]], e=[0,2], f=[0,1], gain=1, expect=True),
    dict(name='weighted_positive', hosts=[[0,1,2],[0,1]], caps=[1,1], initial=[[0,[0,1]]], e=[0,2], f=[0,1], gain=0.5, expect=True),
    dict(name='zero_gain_rejected', hosts=[[0,1,2],[0,1]], caps=[1,1], initial=[[0,[0,1]]], e=[0,2], f=[0,1], gain=0, expect=False),
    dict(name='negative_gain_rejected', hosts=[[0,1,2],[0,1]], caps=[1,1], initial=[[0,[0,1]]], e=[0,2], f=[0,1], gain=-1, expect=False),
    dict(name='destination_full_rollback', hosts=[[0,1,2],[0,1,3]], caps=[1,1], initial=[[0,[0,1]],[1,[0,3]]], e=[0,2], f=[0,1], gain=1, expect=False),
    dict(name='target_blocked_rollback', hosts=[[0,1,2,3],[0,1]], caps=[1,1], initial=[[0,[0,1]],[0,[2,3]]], e=[0,2], f=[0,1], gain=1, expect=False),
    dict(name='cap2_improves', hosts=[[0,1,2,3,4],[0,1]], caps=[2,2], initial=[[0,[0,1]],[0,[0,3]],[0,[2,4]]], e=[0,2], f=[0,1], gain=1, expect=True),
    dict(name='cap2_target_full_rollback', hosts=[[0,1,2,3,4],[0,1]], caps=[2,2], initial=[[0,[0,1]],[0,[2,3]],[0,[2,4]]], e=[0,2], f=[0,1], gain=1, expect=False),
    dict(name='nonhost_destination_rejected', hosts=[[0,1,2],[0,3]], caps=[1,1], initial=[[0,[0,1]]], e=[0,2], f=[0,1], gain=1, expect=False),
]
(ROOT / 'tests/transaction_cases.json').write_text(json.dumps(cases, indent=2)+'\n', encoding='utf-8')

def canonical(p):
    return [sorted(map(list, r)) for r in p.R]

def verify(hosts, caps, R):
    seen=set()
    for h, cap, row in zip(hosts,caps,R):
        degree=Counter()
        for pair in row:
            assert len(pair)==2 and pair[0]<pair[1] and set(pair)<=set(h)
            assert tuple(pair) not in seen
            seen.add(tuple(pair)); degree.update(pair)
        assert all(d<=cap for d in degree.values())
    return len(seen)

python=[]
for c in cases:
    p=seal.Packing(seal.normalize(c['hosts']),c['caps'])
    for j,e in c['initial']:p.place(j,tuple(e))
    before=canonical(p)
    ok=p.relocate_insert(0,1,tuple(c['f']),tuple(c['e']),c['gain'])
    assert ok==c['expect']
    after=canonical(p); verify(c['hosts'],c['caps'],after)
    if not ok:assert after==before
    else:assert sum(map(len,after))==sum(map(len,before))+1
    python.append(dict(name=c['name'],accepted=ok,R=after))
(OUT/'python_transactions.json').write_text(json.dumps(python,indent=2)+'\n')

js=r'''const fs=require('fs'),{Packing,normalize,seal}=require('../../js/seal.js');
const cases=JSON.parse(fs.readFileSync(process.argv[2]));
const out=cases.map(c=>{const p=new Packing(normalize(c.hosts),c.caps);
for(const [j,e] of c.initial)p.place(j,e.join(','));
const accepted=p.relocateInsert(0,1,c.f.join(','),c.e.join(','),c.gain);
return {name:c.name,accepted,R:p.R.map(r=>[...r].map(e=>e.split(',').map(Number)).sort((a,b)=>a[0]-b[0]||a[1]-b[1]))};});
console.log(JSON.stringify(out));'''
(OUT/'transactions.js').write_text(js)

cpp=['#define main seal_cli_main', '#include "../../cpp/seal.cpp"','#undef main','int main(){cout<<"[";']
for idx,c in enumerate(cases):
    lit=lambda x:json.dumps(x,separators=(',',':')).replace('[','{').replace(']','}')
    cpp+=['{vector<vector<int>> hosts='+lit(c['hosts'])+';vector<int> caps='+lit(c['caps'])+';Packing p(hosts,caps);']
    for j,e in c['initial']:cpp+=[f'p.place({j},"{e[0]},{e[1]}");']
    cpp += [f'bool ok=p.relocateInsert(0,1,"{c["f"][0]},{c["f"][1]}","{c["e"][0]},{c["e"][1]}",{c["gain"]});',
            'Result result{0,p.size(),0,{}};for(auto&r:p.R){vector<pair<int,int>> pairs;for(auto&e:r)pairs.push_back(parsePair(e));sort(pairs.begin(),pairs.end());result.R.push_back(pairs);}',
            f'cout<<"{"," if idx else ""}{{\\\"name\\\":\\\"{c["name"]}\\\",\\\"accepted\\\":"<<(ok?"true":"false")<<",\\\"output\\\":";printResult(result,true);cout<<"}}";}}']
cpp+=['cout<<"]";return 0;}']
# The JSON framing uses a C++ escaped quote, not a literal backslash in output.
cppsrc='\n'.join(cpp).replace('\\\\\\"','\\"')
(OUT/'transactions.cpp').write_text(cppsrc)

compiler='C:/msys64/ucrt64/bin/g++.exe'
env=os.environ.copy();env['PATH']=str(Path(compiler).parent)+os.pathsep+env['PATH']
runs=[]
def run(name, cmd):
    t=time.monotonic();p=subprocess.run(cmd,cwd=ROOT,env=env,capture_output=True,timeout=120)
    (OUT/(name+'.stdout')).write_bytes(p.stdout);(OUT/(name+'.stderr')).write_bytes(p.stderr)
    runs.append(dict(name=name,command=cmd,exit_code=p.returncode,seconds=time.monotonic()-t))
    assert p.returncode==0,(name,p.stderr.decode(errors='replace'))
    return p.stdout

jout=json.loads(run('js_transactions',['node',str(OUT/'transactions.js'),str(ROOT/'tests/transaction_cases.json')]))
run('cpp_transactions_compile',[compiler,'-std=c++17','-O2',str(OUT/'transactions.cpp'),'-o',str(OUT/'transactions.exe')])
cout=json.loads(run('cpp_transactions',[str(OUT/'transactions.exe')]))
for c,p,j,k in zip(cases,python,jout,cout):
    assert j==p
    assert k['name']==p['name'] and k['accepted']==p['accepted'] and k['output']['R']==p['R']
    verify(c['hosts'],c['caps'],j['R']);verify(c['hosts'],c['caps'],k['output']['R'])

# A real solver call must perform N1, not merely a manually seeded transaction.
real=seal.seal([[0,1,2],[0,1]],construct='hostmatch',track_potential=True)
assert real['n1_moves']==1 and real['size']==2
assert all(x[0]<y[0] for x,y in zip(real['potential_trace'],real['potential_trace'][1:]))
verify([[0,1,2],[0,1]],[1,1],real['R'])
jreal=json.loads(run('js_real_N1',['node','-e',"const {seal}=require('./js/seal.js');console.log(JSON.stringify(seal([[0,1,2],[0,1]],{construct:'hostmatch'})))"]))
assert jreal['n1_moves']==1 and jreal['size']==2
verify([[0,1,2],[0,1]],[1,1],jreal['R'])
cppreal='#define main seal_cli_main\n#include "../../cpp/seal.cpp"\n#undef main\nint main(){vector<vector<int>>h{{0,1,2},{0,1}};vector<int>c{1,1};printResult(sealRun(h,c,nullptr,0,1),true);}'
(OUT/'real_n1.cpp').write_text(cppreal)
run('cpp_real_compile',[compiler,'-std=c++17','-O2',str(OUT/'real_n1.cpp'),'-o',str(OUT/'real_n1.exe')])
creal=json.loads(run('cpp_real_N1',[str(OUT/'real_n1.exe')]))
assert creal['n1_moves']==1 and creal['size']==2
verify([[0,1,2],[0,1]],[1,1],creal['R'])

# Zero weights must remain zero in the JS objective and ordering.
zero_hosts=[[0,1,2],[0,1]];zero_w={(0,1):0,(0,2):2,(1,2):1}
zero=seal.seal_best(zero_hosts,weights=zero_w,mode='weighted')
jzero=json.loads(run('js_zero_weight',['node','-e',"const {sealBest}=require('./js/seal.js');console.log(JSON.stringify(sealBest([[0,1,2],[0,1]],{mode:'weighted',weights:new Map([['0,1',0],['0,2',2],['1,2',1]])})))"]))
assert zero['value']==jzero['value'] and zero['R']==[list(map(tuple,r)) for r in jzero['R']]
zero_dir=ROOT/'tests/zero_instances';zero_dir.mkdir(exist_ok=True)
(zero_dir/'manifest.json').write_text('["zero", "all_zero"]')
for name, weights in [('zero',{'0,1':0,'0,2':2,'1,2':1}),('all_zero',{'0,1':0,'0,2':0,'1,2':0})]:
    (zero_dir/(name+'.json')).write_text(json.dumps(dict(hosts=zero_hosts,caps=[2,2],weights=weights),indent=2))
run('cpp_cli_compile',[compiler,'-std=c++17','-O2',str(ROOT/'cpp/seal.cpp'),'-o',str(OUT/'seal_cli.exe')])
czero=json.loads(run('cpp_zero_cli',[str(OUT/'seal_cli.exe'),str(zero_dir),'--packings']))
jzero_cli=json.loads(run('js_zero_cli',['node',str(ROOT/'js/seal.js'),str(zero_dir),'--packings']))
for name in ['zero','all_zero']:
    inp=json.loads((zero_dir/(name+'.json')).read_text())
    pyzero=seal.seal_best(inp['hosts'],weights={tuple(map(int,k.split(','))):v for k,v in inp['weights'].items()},mode='weighted')
    for port in [czero,jzero_cli]:
        assert port[name]['weighted']['value']==pyzero['value']
        verify(inp['hosts'],[1,1],port[name]['weighted']['R'])
        expected=sum(Fraction(inp['weights'][','.join(map(str,e))]) for row in port[name]['weighted']['R'] for e in row)
        assert expected==Fraction(str(port[name]['weighted']['value']))
import seal_v3
rejections=[]
for opts in [dict(caps=[2,2]),dict(weights={(0,1):0,(0,2):1,(1,2):1})]:
    try:seal_v3.seal_v3(zero_hosts,**opts)
    except ValueError:rejections.append(True)
    else:raise AssertionError('unsupported v3 model was accepted')
result=dict(status='PASS',transaction_cases=len(cases),languages=['Python','JavaScript','C++'],transaction_results=python,
            real_N1=real,real_N1_js=jreal,real_N1_cpp=creal,zero_weight_python=zero,zero_weight_js=jzero,
            zero_weight_cli_python_js_cpp=True,v3_unsupported_models_rejected=len(rejections),runs=runs,
            negative_gain_scope='Only N1 requires positive gain; construction behavior is unchanged.')
(OUT/'REGRESSION_RESULTS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','transaction_cases','languages','v3_unsupported_models_rejected']}))
