"""Certo generation/replay and distinct schema/provenance controls."""
from pathlib import Path
from collections import Counter
import gzip,json,subprocess,os,copy,time,hashlib
from verify_v06 import verify,partition,pairs
R=Path(__file__).resolve().parent;T=R/'certo';T.mkdir(exist_ok=True)
env=os.environ|{'PYTHONUTF8':'1','PYTHONIOENCODING':'utf-8'}
records=[]
def run(label,cmd):
    t=time.monotonic();p=subprocess.run(cmd,env=env,capture_output=True,timeout=120)
    (T/(label+'.stdout')).write_bytes(p.stdout);(T/(label+'.stderr')).write_bytes(p.stderr)
    out=json.loads(p.stdout);row={'label':label,'command':cmd,'exit_code':p.returncode,'seconds':time.monotonic()-t,'output':out};records.append(row);return row
selected=['19_37_three_edit_classes_all_k4','37_73_concentrated_stars_triangles','63_125_mixed_alternating_types','63_127_mixed_all_k5','exceptional_p2_q5_a2_b1','exceptional_p2_q5_a0_b4']
for name in selected:
    d=json.loads(gzip.decompress((R/'certificates'/(name+'.json.gz')).read_bytes()))
    sp=T/(name+'.py');cert=T/(name+'.certificate.json')
    sp.write_text('from certo import CoverSpec\ndef spec():\n return CoverSpec(universe='+repr(d['graph_edges'])+', parts='+repr(d['blocks'])+', cliques=True, exact=True, title='+repr(name)+')\n',encoding='utf-8')
    gen=run(name+'_generate',['certo','cover',str(sp),'--json','--cert',str(cert),'--deadline','90','--max-memory-mb','2048'])
    assert gen['exit_code']==0 and cert.exists(),gen
    checked=run(name+'_verify',['certo','verify',str(cert),'--spec',str(sp),'--json'])
    assert checked['exit_code']==0 and checked['output'].get('ok') is True,checked

# Provenance refusal is deliberately distinguished from a mathematical counterexample.
source=T/(selected[0]+'.py');wrong=T/'wrong_spec.py';wrong.write_text(source.read_text(encoding='utf-8')+'\n# Changed physical-specification identity for negative replay.\n',encoding='utf-8')
negative=run('wrong_spec_identity',['certo','verify',str(T/(selected[0]+'.certificate.json')),'--spec',str(wrong),'--json'])
assert negative['exit_code']!=0 and negative['output'].get('error')=='refused'
negative['classification']='PROVENANCE_REFUSAL; not a solver or mathematical-invalidity result'

# Independently reject physical corruption, without relying on certificate metadata.
base=json.loads(gzip.decompress((R/'certificates'/(selected[0]+'.json.gz')).read_bytes()));controls=[]
for label,mut in [('missing_coverage',lambda d:d['blocks'].pop()),('double_coverage',lambda d:d['blocks'].append(d['blocks'][0])),('wrong_prescription',lambda d:d['outside_type_assignment'].__setitem__(next(iter(d['outside_type_assignment'])),5))]:
    d=copy.deepcopy(base);mut(d)
    try:verify(d)
    except AssertionError as e:controls.append({'case':label,'rejected':True,'reason':str(e),'classification':'INDEPENDENT_PHYSICAL_OR_TYPE_REJECTION'})
    else:raise AssertionError('Negative control accepted: '+label)
payload={'status':'PASS_CERTO_REPLAY_AND_NEGATIVES','certo_certificates':len(selected),'runs':records,'independent_negative_controls':controls,'universal_claim':False,'scope':'Certo exact-cover certificates verify supplied partitions, not global optimality. Independent integer dual witnesses certify optimality for these finite cases.'}
(R/'CERTO_RESULTS.json').write_text(json.dumps(payload,indent=2)+'\n',encoding='utf-8')
print('Certo certificates verified:',len(selected),'negative controls:',len(controls)+1)
