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

from itertools import product

def transfer_checks():
    count=0
    for q in range(1,4):
        for gains in product(range(5),repeat=q):
            for losses in product(range(3),repeat=q):
                for deleted in range(3):
                    D=sum(gains)+sum(losses)+deleted; C=sum(losses)+deleted
                    assert q*max(gains)>=D-C
                    for e in range(max(gains),max(gains)+4):
                        for T in range(e+1):
                            if q*e+C<=q*T+D:
                                assert e-max(gains)<=T
                            count+=1
    return count
result={"status":"PASS","scope":"Finite exact-arithmetic transcription checks only; not a proof of graph construction or a replacement for Lean.","baseline":baseline_checks(),"transfer_budget_cases":transfer_checks()}
# Negative control: a realization loss cannot be dropped from the budget.
e,g,D,C,T=5,1,5,4,0
assert e-D<=T and not e-g<=T
result["negative_controls_rejected"]=1

result["script_sha256"]=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
Path(__file__).with_name("EXACT_ARITHMETIC_RESULTS.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
print(json.dumps(result,indent=2))
