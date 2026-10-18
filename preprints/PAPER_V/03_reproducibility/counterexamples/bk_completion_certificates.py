# Copyright (c) 2026 Juan Pablo Traverso Gianini.
# Released under Apache 2.0; see the series software LICENSE.
# The exact dual value 19/2 bounds every integral packing by 9.
# Enumerating all feasible nine-element families therefore enumerates every optimum.
"""Recover exact ancillary BK certificates; numerical LP output is rationally rechecked."""
from fractions import Fraction
from pathlib import Path
import json
import sys

assert sys.argv[1:] in ([], ['--verify-only'])
verify_only = sys.argv[1:] == ['--verify-only']
destination = Path(__file__).resolve().parent/'BK_ANCILLARY_CERTIFICATES.json'
saved = json.loads(destination.read_text(encoding='utf-8')) if verify_only else None

objects = [(0,0,1),(1,0,3),(1,0,5),(1,3,5),(2,0,5),(3,0,2),(3,0,3),
           (3,0,4),(3,2,3),(3,2,4),(3,3,4),(4,0,1),(4,0,2),(4,0,4),
           (4,1,2),(4,1,4),(4,2,4),(5,0,3),(5,0,4),(5,0,5),(5,3,4),
           (5,3,5),(5,4,5),(6,0,1),(7,0,4),(7,0,5),(7,4,5)]
pairs = sorted({(a,b) for _,a,b in objects})
labels = [('pair',a,b) for a,b in pairs] + [('host',j,a) for j in range(8) for a in range(6)]
matrix = [[int((a,b) == (r,s)) if kind == 'pair' else int(j == r and s in (a,b))
           for j,a,b in objects] for kind,r,s in labels]
if verify_only:
    listed = {tuple(r['resource']): Fraction(r['price']) for r in saved['exact_dual']}
    assert set(listed) <= set(labels)
    prices = [listed.get(label, Fraction(0)) for label in labels]
else:
    from scipy.optimize import linprog
    result = linprog([-1]*27, A_ub=matrix, b_ub=[1]*len(labels), bounds=(0,None), method='highs')
    assert result.success
    prices = [Fraction(-x).limit_denominator(10000) for x in result.ineqlin.marginals]
assert all(x >= 0 for x in prices)
assert all(sum(prices[i]*matrix[i][j] for i in range(len(labels))) >= 1 for j in range(27))
assert sum(prices) == Fraction(19,2)
conflict = [sum(1 << j for j,(k,c,d) in enumerate(objects)
                if i != j and ((a,b) == (c,d) or (h == k and set((a,b)) & set((c,d)))))
            for i,(h,a,b) in enumerate(objects)]
maximum = []
def visit(mask, selected):
    need = 9-len(selected)
    if need == 0:
        maximum.append(tuple(selected))
        return
    if mask.bit_count() < need:
        return
    v = (mask & -mask).bit_length()-1
    rest = mask & ~(1 << v)
    visit(rest & ~conflict[v], selected+[v])
    visit(rest, selected)
visit((1 << 27)-1, [])
assert len(maximum) == 70
beta = 0
beta_witness = None
for packing in maximum:
    used = {(objects[i][1],objects[i][2]) for i in packing}
    residual = [p for p in pairs if p not in used]
    for a in residual:
        for b in residual:
            if not set(a) & set(b):
                beta = max(beta,2)
                beta_witness = {'packing': packing, 'uncovered_pairs': [a,b]}
            for c in residual:
                assert set(a)&set(b) or set(a)&set(c) or set(b)&set(c)
record = {'objects':objects, 'exact_dual': [dict(resource=label,price=str(y))
          for label,y in zip(labels,prices) if y], 'dual_value':str(sum(prices)),
          'number_of_maximum_packings':len(maximum), 'all_maximum_packings':maximum,
          'beta':beta, 'beta_witness':beta_witness,
          'scope':'Exact finite recomputation and rational certificate check, not a universal Lean proof.'}
if verify_only:
    assert json.loads(json.dumps(record)) == saved
else:
    destination.write_text(json.dumps(record,indent=2),encoding='utf-8')
print(json.dumps({k:record[k] for k in ['exact_dual','dual_value','number_of_maximum_packings','beta','beta_witness']},indent=2))
