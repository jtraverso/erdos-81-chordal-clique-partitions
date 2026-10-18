"""Certo independently replays each supplied physical recourse state."""
from pathlib import Path
import gzip,json,subprocess,os,time
R=Path(__file__).resolve().parent;T=R/'certo';d=json.loads(gzip.decompress((R/'RECOURSE_TWO_EDGES.json.gz').read_bytes()));rows=[]
env=os.environ|{'PYTHONUTF8':'1','PYTHONIOENCODING':'utf-8'}
for i,blocks in enumerate(d['states']):
 name=f'recourse_state_{i}';sp=T/(name+'.py');cert=T/(name+'.certificate.json')
 sp.write_text('from certo import CoverSpec\ndef spec():\n return CoverSpec(universe='+repr(d['graph_edges'])+', parts='+repr(blocks)+', cliques=True, exact=True, title='+repr(name)+')\n',encoding='utf-8')
 for kind,cmd in [('generate',['certo','cover',str(sp),'--json','--cert',str(cert),'--deadline','90','--max-memory-mb','2048']),('verify',['certo','verify',str(cert),'--spec',str(sp),'--json'])]:
  t=time.monotonic();p=subprocess.run(cmd,env=env,capture_output=True,timeout=120);(T/(name+'_'+kind+'.stdout')).write_bytes(p.stdout);(T/(name+'_'+kind+'.stderr')).write_bytes(p.stderr);o=json.loads(p.stdout)
  assert p.returncode==0 and (kind!='verify' or o.get('ok') is True)
  rows.append({'state':i,'operation':kind,'command':cmd,'exit_code':p.returncode,'seconds':time.monotonic()-t,'output':o})
(R/'CERTO_RECOURSE_RESULTS.json').write_text(json.dumps({'status':'PASS','state_certificates':3,'runs':rows,'scope':'Physical exact edge coverage for each supplied state. Path distances, preservation, lifting class and finite optimality are checked independently; this is not a universal connectivity proof.'},indent=2)+'\n',encoding='utf-8')
print('Three Certo recourse-state certificates: PASS')
