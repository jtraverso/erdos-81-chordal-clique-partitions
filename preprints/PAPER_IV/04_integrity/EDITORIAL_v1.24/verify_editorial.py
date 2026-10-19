"""Verify documentary hashes; never starts Lean/Lake."""
from pathlib import Path
import json,hashlib,sys,os
root=Path(sys.argv[1]).resolve()
if os.name=='nt':root=Path('\\\\?\\'+str(root))
m=json.loads((Path(__file__).parent/'MANIFEST.json').read_text(encoding='utf-8'))
bad=[e['path'] for e in m['files'] if not (root/e['path']).is_file() or hashlib.sha256((root/e['path']).read_bytes()).hexdigest()!=e['sha256']]
print(json.dumps({'status':'FAIL' if bad else 'PASS','files':len(m['files']),'mismatches':bad}))
sys.exit(bool(bad))
