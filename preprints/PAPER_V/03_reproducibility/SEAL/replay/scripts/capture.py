"""Capture corrected implementation outputs; no ILP benchmark or theorem claim."""
from pathlib import Path
import argparse,json,sys,time
R=Path(__file__).resolve().parents[1]
ap=argparse.ArgumentParser();ap.add_argument('--source-root',type=Path,required=True);ap.add_argument('--group',choices=['base','v3'],required=True);ap.add_argument('--case');a=ap.parse_args()
sys.path.insert(0,str(a.source_root/'python'));import seal
load=lambda p:json.loads(p.read_text(encoding='utf8'))
if a.group=='base':
 results=[]
 for name in load(R/'inputs/release_manifest.json'):
  inp=load(R/'inputs'/(name+'.json'))
  for mode in ['standard','weighted','bmatching','psi']:
   kw={}
   if mode=='weighted':kw['weights']={tuple(map(int,k.split(','))):v for k,v in inp['weights'].items()}
   if mode=='bmatching':kw['caps']=inp['caps']
   t=time.perf_counter()
   out=seal.seal(inp['hosts'],mode='psi',track_potential=True) if mode=='psi' else seal.seal_best(inp['hosts'],mode=mode,**kw)
   results.append(dict(name=name,variant=mode,output=out,elapsed_seconds=time.perf_counter()-t))
   print(name,mode,out['size'],out.get('n1_moves','not_exposed'),flush=True)
  (R/'outputs/base_packings.json').write_text(json.dumps(results,indent=2,default=str),encoding='utf8')
else:
 import seal_v3
 inp=load(R/'inputs'/(a.case+'.json'))
 t=time.perf_counter();out=seal_v3.seal_v3(inp['hosts']);elapsed=time.perf_counter()-t
 certificate=out['certificate'];assert 'rows' in certificate
 captured=[dict(rows=certificate['rows'],U=out['audit_U'],summary={k:v for k,v in certificate.items() if k!='rows'})]
 result=dict(name=a.case,group=inp['group'],hosts=inp['hosts'],output=out,full_exact_dual=captured[0],elapsed_seconds=elapsed)
 (R/'outputs'/(a.case+'.json')).write_text(json.dumps(result,indent=2,default=str),encoding='utf8')
 print(a.case,out['size'],out['audit_U'],out['audit_gap'],elapsed,flush=True)
