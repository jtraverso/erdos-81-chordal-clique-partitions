"""Save full inputs and run corrected suites with a finite per-process limit."""
from pathlib import Path
import argparse,json,hashlib,subprocess,sys,time,random
R=Path(__file__).resolve().parents[1]
ap=argparse.ArgumentParser();ap.add_argument('--source-root',type=Path,default=R.parent/'current');a=ap.parse_args();S=a.source_root.resolve()
for sub in ['inputs','outputs','logs']:(R/sub).mkdir(exist_ok=True)
load=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
manifest=load(S/'instances/manifest.json');(R/'inputs/release_manifest.json').write_text(json.dumps(manifest),encoding='utf8')
(R/'inputs/manifest.json').write_text(json.dumps(manifest),encoding='utf8')
cases=[]
for name in manifest:
 d=load(S/'instances'/(name+'.json'));d['group']='release';(R/'inputs'/(name+'.json')).write_text(json.dumps(d,indent=2),encoding='utf8');cases.append(name)
witnesses={'witness_galvin_K33':[[u,v] for u in (0,1,2) for v in (3,4,5) for _ in range(3)],'witness_bkw_local_star':[[0,1]]*3+[[0,2]]*3+[[0,3]]*3+[[1,4]]*2}
for name,hosts in witnesses.items():(R/'inputs'/(name+'.json')).write_text(json.dumps(dict(group='witness',hosts=hosts),indent=2),encoding='utf8');cases.append(name)
for family,n,param in [('rand',24,60),('rand',32,100),('rand',40,140),('bigrand',24,40),('bigrand',32,60),('bigrand',40,80),('rr',24,6),('rr',32,8),('rr',40,10)]:
 for seed in [1,2]:
  rng=random.Random(seed)
  if family=='rand':hosts=[sorted(rng.sample(range(n),rng.randint(3,min(7,n)))) for _ in range(param)]
  elif family=='bigrand':hosts=[sorted(rng.sample(range(n),rng.randint(n//2,3*n//4))) for _ in range(param)]
  else:hosts=[sorted(set(range(n))-set(rng.sample(range(n),param))) for _ in range(n-1 if n%2==0 else n)]
  name=f'table2_{family}_{n}_{param}_{seed}';(R/'inputs'/(name+'.json')).write_text(json.dumps(dict(group='table2',family=family,n=n,parameter=param,seed=seed,hosts=hosts),indent=2),encoding='utf8');cases.append(name)
(R/'inputs/v3_manifest.json').write_text(json.dumps(cases,indent=2),encoding='utf8')
source_paths=[S/'python/seal.py',S/'python/seal_v3.py',S/'js/seal.js',S/'cpp/seal.cpp',*sorted((S/'instances').glob('*.json'))]
source=[dict(path=p.relative_to(S).as_posix(),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in source_paths]
inputs=[dict(path=p.relative_to(R).as_posix(),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in sorted((R/'inputs').glob('*.json'))]
(R/'INPUT_MANIFEST.json').write_text(json.dumps(inputs,indent=2),encoding='utf8')
(R/'SOURCE_SNAPSHOT.json').write_text(json.dumps(dict(source_root=str(S),files=source),indent=2),encoding='utf8')
runs=[]
def run(label,args,output):
 cmd=[sys.executable,str(R/'scripts/capture.py'),'--source-root',str(S),*args];t=time.perf_counter();timed=False
 with (R/'logs'/(label+'.stdout')).open('wb') as out,(R/'logs'/(label+'.stderr')).open('wb') as err:
  try:q=subprocess.run(cmd,stdout=out,stderr=err,timeout=180);code=q.returncode
  except subprocess.TimeoutExpired:code=None;timed=True
 rec=dict(label=label,command=cmd,exit_code=code,timed_out=timed,seconds=time.perf_counter()-t,timeout_seconds=180);runs.append(rec);(R/'RUNS.json').write_text(json.dumps(runs,indent=2),encoding='utf8');print(label,code,rec['seconds'],flush=True)
 if code!=0:raise SystemExit('Case failed; inspect saved logs: '+label)
run('base',['--group','base'],R/'outputs/base_packings.json')
for name in cases:run(name,['--group','v3','--case',name],R/'outputs'/(name+'.json'))
print('ALL_CAPTURED',len(cases),'v3;72BASE',flush=True)
