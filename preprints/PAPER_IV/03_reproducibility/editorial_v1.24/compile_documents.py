"""Compile documentary PDFs only; never executes Lean/Lake."""
from pathlib import Path
import os, subprocess, sys
root=Path(sys.argv[1]).resolve()
for folder,stem in [('01_manuscript','PAPER_IV_preprint_v1.24'),('05_formalization','FORMALIZATION_COMPANION_v1.24')]:
    for lang in ['en','es']:
        p=root/folder/f'{stem}_{lang}.tex'
        subprocess.run([os.environ.get('TECTONIC','tectonic'),'--keep-logs',p.name],cwd=p.parent,check=True)
