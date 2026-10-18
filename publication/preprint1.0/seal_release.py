"""Create byte manifests for the current public release.

Copyright 2026 Juan Pablo Traverso Gianini
SPDX-License-Identifier: Apache-2.0
"""
from pathlib import Path
import hashlib
import json
import os
import subprocess

root = Path(__file__).resolve().parents[2]

def digest(path):
    # All callers provide absolute paths already anchored to the repository.
    readable = Path('\\\\?\\' + str(path)) if os.name == 'nt' else path
    return hashlib.sha256(readable.read_bytes()).hexdigest()

for work in json.loads((root / 'PUBLICATION_INDEX.json').read_text())['works']:
    folder = root / work['path']
    integrity = folder / '04_integrity'
    integrity.mkdir(exist_ok=True)
    (integrity / 'README.md').write_text(
        '# Release integrity — Preprint 1.0\n\n'
        'The SHA-256 manifest identifies every file in this work, except the '
        'manifest itself. Source archives also carry their own formal-source '
        'manifests. Validation records describe the scope of each check.\n\n'
        'From the repository root, run `python publication/preprint1.0/verify_release.py` '
        'to verify the complete public series manifest. This checks bytes; Lean '
        'builds and independent computational checks have separate instructions '
        'in the formalization companion.\n', encoding='utf-8')
    target = integrity / 'manifest_sha256.txt'
    files = sorted(f for f in folder.rglob('*') if f.is_file() and f != target)
    target.write_text(''.join(digest(f) + '  ' + f.relative_to(folder).as_posix() + '\n'
                              for f in files), encoding='utf-8')

names = subprocess.check_output(
    ['git', 'ls-files', '-z', '--cached', '--others', '--exclude-standard'], cwd=root
).decode('utf-8').split('\0')
names = sorted(set(n for n in names if n and n != 'manifest_sha256.txt'))
(root / 'manifest_sha256.txt').write_text(
    ''.join(digest(root / name) + '  ' + name + '\n' for name in names), encoding='utf-8')
print(json.dumps({'manifest_files': len(names), 'works': 4}))
