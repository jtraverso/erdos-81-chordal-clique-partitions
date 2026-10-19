"""Compile documentary PDFs only. Author: Juan Pablo Traverso Gianini."""
from pathlib import Path
import os,sys,subprocess
r=Path(sys.argv[1]).resolve()
for folder,stem in [('01_manuscript','PAPER_II_preprint_v1.3'),('05_formalization','FORMALIZATION_COMPANION_v1.3')]:
 for lang in ['en','es']:
  p=r/folder/(stem+'_'+lang+'.tex')
  subprocess.run([os.environ.get('TECTONIC','tectonic'),'--keep-logs',p.name],cwd=p.parent,check=True)
