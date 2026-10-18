"""Verify exact bytes in the public series manifest (standard library only).

Copyright 2026 Juan Pablo Traverso Gianini
SPDX-License-Identifier: Apache-2.0
"""
from pathlib import Path
import hashlib
import json
import sys
import os

root = Path(__file__).resolve().parents[2]
manifest = root / 'manifest_sha256.txt'
failures = []
seen = set()
for line in manifest.read_text(encoding='utf-8').splitlines():
    if not line:
        continue
    expected, name = line.split('  ', 1)
    target = (root / name).resolve()
    if not target.is_relative_to(root) or name in seen:
        failures.append({'path': name, 'error': 'invalid or duplicate path'})
        continue
    seen.add(name)
    # Historical source packages can exceed Windows' legacy MAX_PATH.
    readable = Path('\\\\?\\' + str(target)) if os.name == 'nt' else target
    if not readable.is_file():
        failures.append({'path': name, 'error': 'missing'})
    elif hashlib.sha256(readable.read_bytes()).hexdigest() != expected:
        failures.append({'path': name, 'error': 'hash mismatch'})
print(json.dumps({'status': 'PASS' if not failures else 'FAIL',
                  'checked_files': len(seen), 'failures': failures}, indent=2))
sys.exit(bool(failures))
