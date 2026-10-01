# Historical inputs — not public manuscript editions

This directory preserves the exact intermediate inputs needed to understand
and reproduce the audit chain. They are **not alternative releases**.
Read the current manuscript at ../../../01_manuscript/ (relative to the
Paper IV package root, the current location is 01_manuscript/).

Original manuscript filenames and sealed ZIPs are retained. Original audit
targets are not rewritten: their paths describe the workspace used at the
time. The [relocation map](../../../04_integrity/RELOCATION_MAP_v1.22.json)
identifies original and current relative paths and hashes for every copied
artifact. The selected public manuscripts have a second identical copy at
the current manuscript location.

For portable replay, the release verification tool can restore mapped
artifacts to their original relative paths in a new, separate directory.
This does not execute Lean or restore dependencies. The actual prior build
cache is not a publication artifact.
