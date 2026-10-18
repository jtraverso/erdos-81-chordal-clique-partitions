# Copyright (c) 2026 Juan Pablo Traverso Gianini.
# SPDX-License-Identifier: Apache-2.0
from pathlib import Path
from fractions import Fraction
import json, hashlib

def baseline_checks():
    residues = pairs = 0
    for n in range(10001):
        M=n*(n+1)//6; Q=Fraction((2*n+1)**2,24)
        assert Q-M == (Fraction(9,24) if n%3==1 else Fraction(1,24))
        residues+=1
        sizes=range(n+1) if n<200 else sorted({0,n,(n+1)//3,n//2,min(n,(n+1)//3+1)})
        for p in sizes:
            B=p*(n-p)-p*(p-1)//2
            assert B<=M
            assert Q-B==Fraction((6*p-2*n-1)**2,24)
            pairs+=1
    return {"orders":residues,"core_sizes":pairs,"domain":"n=0..10000; all p for n<200, otherwise five documented sizes"}

result={"status":"PASS","scope":"Finite exact-arithmetic transcription checks of the split baseline; no new theorem or stronger constant is asserted.","baseline":baseline_checks()}
# Negative controls reject a wrong residue at n=1 and a corrupted maximizing baseline.
def check_residue(n, candidate):
    return candidate == Fraction((2*n+1)**2,24)-n*(n+1)//6
def check_baseline(n,p,candidate):
    return candidate==p*(n-p)-p*(p-1)//2 and candidate<=n*(n+1)//6
assert not check_residue(1,Fraction(1,24))
assert not check_baseline(3,1,3)
result["negative_controls_rejected"]=2

result["script_sha256"]=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
Path(__file__).with_name("EXACT_ARITHMETIC_RESULTS.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
print(json.dumps(result,indent=2))
