from pathlib import Path
import subprocess,json,time,sys,os,shutil,argparse
R=Path(__file__).resolve().parents[1]
ap=argparse.ArgumentParser();ap.add_argument('--source-root',type=Path,default=R.parent/'current');ap.add_argument('--cxx');a=ap.parse_args();S=a.source_root.resolve();runs=[]
compiler=a.cxx or os.environ.get('CXX') or shutil.which('g++') or ('C:/msys64/ucrt64/bin/g++.exe' if Path('C:/msys64/ucrt64/bin/g++.exe').exists() else None)
if not compiler: raise SystemExit('A C++17 compiler is required; use --cxx.')
def run(label,cmd,output,timeout=120):
 t=time.perf_counter()
 env=dict(os.environ);env['PATH']=str(Path(compiler).resolve().parent)+os.pathsep+env['PATH']
 with output.open('wb') as out,(R/'logs'/(label+'.stderr')).open('wb') as err:q=subprocess.run(cmd,stdout=out,stderr=err,timeout=timeout,env=env)
 runs.append(dict(label=label,command=cmd,exit_code=q.returncode,seconds=time.perf_counter()-t));(R/'PORT_RUNS.json').write_text(json.dumps(runs,indent=2),encoding='utf8');assert q.returncode==0,label
run('js',['node',str(S/'js/seal.js'),str(R/'inputs'),'--packings'],R/'outputs/js_packings.json')
binary=R/('seal_current.exe' if os.name=='nt' else 'seal_current');run('cpp_compile',[compiler,'-std=c++17','-O2',str(S/'cpp/seal.cpp'),'-o',str(binary)],R/'logs/cpp_compile.stdout')
run('cpp',[str(binary),str(R/'inputs'),'--packings'],R/'outputs/cpp_packings.json')
sys.path.insert(0,str(S/'python'));import seal
inp={'hosts':[[0,1,2],[0,1]]};before=seal.seal(inp['hosts'],construct='hostmatch',use_repair=False);after=seal.seal(inp['hosts'],construct='hostmatch',use_repair=True)
(R/'outputs/n1_witness.json').write_text(json.dumps(dict(input=inp,before=before,after=after),indent=2),encoding='utf8');print('PORTS_AND_N1_CAPTURED')
