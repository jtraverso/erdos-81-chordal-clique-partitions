"""Independent checker for saved physical outputs and rational duals. Standard library only."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter,defaultdict
from itertools import combinations
import argparse,json,copy,csv,hashlib
R=Path(__file__).resolve().parents[1]
ap=argparse.ArgumentParser();ap.add_argument('--source-root',type=Path,default=R.parent/'current');a=ap.parse_args()
load=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
for rec in load(R/'INPUT_MANIFEST.json'):
 assert hashlib.sha256((R/rec['path']).read_bytes()).hexdigest()==rec['sha256'],'input manifest'
for rec in load(R/'SOURCE_SNAPSHOT.json')['files']:
 assert hashlib.sha256((a.source_root/rec['path']).read_bytes()).hexdigest()==rec['sha256'],'source snapshot'
for name in load(R/'inputs/release_manifest.json'):
 saved=load(R/'inputs'/(name+'.json'));saved.pop('group')
 assert saved==load(a.source_root/'instances'/(name+'.json')),'release input identity'

def packing(inp,out,mode='standard'):
 hosts=[set(h) for h in inp['hosts']];caps=inp['caps'] if mode=='bmatching' else [1]*len(hosts);weights=inp['weights'] if mode=='weighted' else None
 assert len(out['R'])==len(hosts),'host count';used=set();value=F(0)
 for j,entries in enumerate(out['R']):
  deg=Counter()
  for raw in entries:
   assert len(raw)==2 and raw[0]<raw[1],'pair schema';e=tuple(raw)
   assert set(e)<=hosts[j],'host containment';assert e not in used,'repeated pair';used.add(e);deg.update(e)
   value+=F(str(weights.get(','.join(map(str,e)),1))) if weights is not None else 1
  assert all(v<=caps[j] for v in deg.values()),'host capacity'
 assert len(used)==out['size'],'size'
 if 'value' in out:assert abs(value-F(str(out['value'])))<=F(1,1000000),'value'
 return value

def dual(inp,c):
 hosts=[set(h) for h in inp['hosts']];d=c['full_exact_dual'];price_pair=defaultdict(F);price_deg=defaultdict(F);price_odd=defaultdict(list);upper=F(0)
 for row in d['rows']:
  kind,key,rhs,y=row['kind'],row['key'],F(row['rhs']),F(row['y']);assert y>=0,'negative price'
  if kind=='pair':
   e=tuple(key);assert len(e)==2 and e[0]<e[1] and any(set(e)<=h for h in hosts) and rhs==1,'pair row';price_pair[e]+=y
  elif kind=='deg':
   j,v=key;assert 0<=j<len(hosts) and v in hosts[j] and rhs==1,'degree row';price_deg[j,v]+=y
  elif kind=='odd':
   j,vs=key;assert 0<=j<len(hosts) and len(vs)==len(set(vs)) and set(vs)<=hosts[j] and len(vs)>=3 and len(vs)%2==1,'odd schema';assert rhs==F(len(vs)-1,2),'odd rhs'
   if y:price_odd[j].append((set(vs),y))
  else:raise AssertionError('unknown row')
  upper+=rhs*y
 objects=0
 for j,h in enumerate(hosts):
  for e in combinations(sorted(h),2):
   total=price_pair[e]+price_deg[j,e[0]]+price_deg[j,e[1]]+sum((y for vs,y in price_odd[j] if e[0] in vs and e[1] in vs),F(0))
   assert total>=1,'dual undercoverage';objects+=1
 out=c['output'];assert upper==F(d['U'])==F(out['audit_U'])==F(d['summary']['U']),'dual objective';floor=upper.numerator//upper.denominator
 assert floor==out['audit_floor_U']==d['summary']['floor_U'],'floor';assert floor-out['size']==out['audit_gap'],'gap';assert out['certified_optimal']==(floor==out['size'] or out['u']==0),'optimal flag'
 return objects,len(d['rows']),upper

base=load(R/'outputs/base_packings.json');manifest=load(R/'inputs/release_manifest.json');assert len(base)==72
counts=Counter();n1=Counter();tables=[]
for c in base:
 inp=load(R/'inputs'/(c['name']+'.json'));packing(inp,c['output'],c['variant']);counts[c['variant']]+=1;n1[c['variant']]+=c['output']['n1_moves']
 if c['variant']=='psi':
  tr=c['output']['potential_trace'];assert all(x[0]<y[0] and x[1]>y[1] for x,y in zip(tr,tr[1:])),'potential';assert tr[-1][0]==c['output']['size']
 tables.append(dict(suite='base',name=c['name'],variant=c['variant'],size=c['output']['size'],value=c['output']['value'],n1_moves=c['output']['n1_moves'],lower='',upper='',gap='',certified_optimal=''))
assert dict(counts)=={k:18 for k in ['standard','weighted','bmatching','psi']}
objects=rows=0;v3=[];bygroup=Counter();zero=Counter()
for name in load(R/'inputs/v3_manifest.json'):
 inp=load(R/'inputs'/(name+'.json'));c=load(R/'outputs'/(name+'.json'));assert c['hosts']==inp['hosts'],'input binding';packing(inp,c['output']);o,n,U=dual(inp,c);objects+=o;rows+=n;v3.append(c);bygroup[c['group']]+=1
 pairs=set().union(*(set(combinations(sorted(set(h)),2)) for h in inp['hosts']));out=c['output'];assert out['cov']==len(pairs) and out['u']==len(pairs)-out['size'],'residual';zero[c['group']]+=int(out['audit_gap']==0)
 tables.append(dict(suite=c['group'],name=name,variant='v3_cardinality',size=out['size'],value=out['size'],n1_moves=out.get('n1_moves',''),lower=out['size'],upper=str(U),gap=out['audit_gap'],certified_optimal=out['audit_gap']==0))
assert dict(bygroup)==dict(release=18,witness=2,table2=18)
ports={};agreements={};physical={}
for lang in ['js','cpp']:
 data=load(R/'outputs'/(lang+'_packings.json'));checked=0;equal=0
 assert set(data)==set(manifest)
 for name,variants in data.items():
  inp=load(R/'inputs'/(name+'.json'));assert set(variants)=={'standard','weighted','bmatching'}
  for mode,out in variants.items():
   val=packing(inp,out,mode);checked+=1;py=next(c for c in base if c['name']==name and c['variant']==mode)['output'];assert val==F(str(py['value'])),'port objective mismatch';equal+=1
 physical[lang]=checked;agreements[lang]=equal;ports[lang]=data
w=load(R/'outputs/n1_witness.json');assert w['before']['size']==1 and w['after']['size']==2 and w['after']['n1_moves']==1
packing(w['input'],w['before']);packing(w['input'],w['after'])
neg=[]
def rejects(name,fn):
 try:fn()
 except AssertionError as ex:neg.append(dict(name=name,rejected=True,reason=str(ex)))
 else:raise AssertionError('negative control accepted: '+name)
c=base[0];inp=load(R/'inputs'/(c['name']+'.json'));bad=copy.deepcopy(c['output']);j=next(j for j,es in enumerate(bad['R']) if es);bad['R'][j].append(bad['R'][j][0]);rejects('repeated pair',lambda:packing(inp,bad))
bad=copy.deepcopy(c['output']);bad['R'][j][0]=[-100,100];rejects('non-host pair',lambda:packing(inp,bad))
bad=copy.deepcopy(c['output']);bad['size']+=1;rejects('false size',lambda:packing(inp,bad))
bad=copy.deepcopy(c['output']);bad['value']+=1;rejects('false objective',lambda:packing(inp,bad))
c=v3[0];inp=load(R/'inputs'/(c['name']+'.json'));bad=copy.deepcopy(c)
for row in bad['full_exact_dual']['rows']:row['y']='0'
rejects('zero dual undercoverage',lambda:dual(inp,bad));bad=copy.deepcopy(c);bad['full_exact_dual']['U']='0';rejects('false dual objective',lambda:dual(inp,bad))
bad=copy.deepcopy(w['after']);bad['R']=[[[0,1],[0,2]],[]];rejects('host degree overcapacity',lambda:packing(w['input'],bad))
for row in tables:
 inp_path=R/'inputs'/(row['name']+'.json');inp=load(inp_path)
 row.update(family=inp.get('family',''),n=inp.get('n',''),parameter=inp.get('parameter',''),seed=inp.get('seed',''),input_path=inp_path.relative_to(R).as_posix(),input_sha256=hashlib.sha256(inp_path.read_bytes()).hexdigest())
with (R/'CURRENT_RESULTS.csv').open('w',newline='',encoding='utf8') as f:
 writer=csv.DictWriter(f,fieldnames=list(tables[0]));writer.writeheader();writer.writerows(tables)
result=dict(status='PASS',checker_imports_implementation_or_solver=False,base_outputs=dict(counts),base_n1_moves=dict(n1),v3_outputs=dict(bygroup),certified_cardinality_optima=dict(zero),dual_objects=objects,dual_rows=rows,exact_rational_duals=len(v3),python_physical_packings=len(base)+len(v3),port_physical_packings=physical,port_equal_objectives=agreements,explicit_n1_witness=True,negative_controls=neg,scope='Saved finite physical outputs; duals certify cardinality upper bounds. A positive gap is an interval, not a known optimum. No polynomial-time or general software-correctness assertion.')
(R/'CHECK_RESULTS.json').write_text(json.dumps(result,indent=2),encoding='utf8');print(json.dumps(result,indent=2))
