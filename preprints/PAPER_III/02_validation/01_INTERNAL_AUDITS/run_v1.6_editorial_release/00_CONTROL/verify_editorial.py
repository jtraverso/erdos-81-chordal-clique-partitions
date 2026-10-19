"""Verify current document hashes and unchanged frozen Git tree; no builds."""
from pathlib import Path
import hashlib,json,subprocess,sys
r=Path(sys.argv[1]).absolute();p=r/'preprints/PAPER_III'
for row in (p/'04_integrity/EDITORIAL_v1.6/SHA256SUMS.txt').read_text(encoding='utf-8').splitlines():
 h,name=row.split('  ',1);assert hashlib.sha256((p/name).read_bytes()).hexdigest()==h,name
before=subprocess.check_output(['git','ls-tree','-r','eb335845bfa23375d5040ea31fc4f4b366346287','preprints/PAPER_III/05_formalization/lean_v1.4_freeze'],cwd=r)
after=subprocess.check_output(['git','ls-tree','-r','HEAD','preprints/PAPER_III/05_formalization/lean_v1.4_freeze'],cwd=r)
assert before==after
print('PASS: editorial manifest and unchanged frozen source tree; no Lean build')
