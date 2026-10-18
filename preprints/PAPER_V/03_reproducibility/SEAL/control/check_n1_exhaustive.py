"""Finite exhaustive N1 regression against an independent physical-set predicate.

No solver is used. Run with the corrected release directory as first argument.
The check covers two fixed host systems, both capacities one and two, and gains
zero and one. It is a software regression, not a proof for arbitrary inputs.
"""
from itertools import combinations, product
from pathlib import Path
import hashlib, importlib.util, json, sys

root = Path(sys.argv[1]).resolve()
spec = importlib.util.spec_from_file_location('tested_seal', root/'python/seal.py')
seal = importlib.util.module_from_spec(spec)
spec.loader.exec_module(seal)

def feasible(assignment, hosts, caps):
    used=set()
    degrees=[{} for _ in hosts]
    for j, pairs in enumerate(assignment):
        for e in pairs:
            if e in used or not set(e) <= set(hosts[j]): return False
            used.add(e)
            for v in e: degrees[j][v]=degrees[j].get(v,0)+1
    return all(d <= caps[j] for j,row in enumerate(degrees) for d in row.values())

def inspect(p, expected):
    actual=[set(row) for row in p.R]
    assert actual==expected
    assert p.used==set().union(*expected)
    for j, row in enumerate(expected):
        verts=set(p.hosts[j]) | set(p.deg[j])
        assert all(p.deg[j].get(v,0)==sum(v in e for e in row) for v in verts)

states=trials=accepted=rejected=0
systems=[[[0,1,2],[0,1,3]], [[0,1,2,3],[0,1,2,3]]]
for hosts in systems:
    pairs=sorted(set().union(*(set(combinations(h,2)) for h in hosts)))
    options=[[-1]+[j for j,h in enumerate(hosts) if set(e)<=set(h)] for e in pairs]
    for cap in (1,2):
        caps=[cap]*len(hosts)
        for choices in product(*options):
            initial=[set() for _ in hosts]
            for e,j in zip(pairs,choices):
                if j>=0: initial[j].add(e)
            if not feasible(initial,hosts,caps): continue
            states+=1
            for j in range(len(hosts)):
                for f in initial[j]:
                    for e in pairs:
                        for gain in (0,1):
                            jp=1-j
                            # A candidate is an actual relocation followed by an
                            # uncovered insertion, not merely a move to free space.
                            expected=[set(row) for row in initial]
                            expected[j].remove(f)
                            expected[jp].add(f)
                            expected[j].add(e)
                            admissible=(gain>0 and e not in set().union(*initial)
                                        and feasible(expected,hosts,caps))
                            p=seal.Packing(hosts,caps)
                            for h,row in enumerate(initial):
                                for edge in row: p.place(h,edge)
                            result=p.relocate_insert(j,jp,f,e,gain)
                            assert result==admissible
                            inspect(p,expected if admissible else initial)
                            assert feasible([set(row) for row in p.R],hosts,caps)
                            trials+=1
                            if result: accepted+=1
                            else: rejected+=1

report={'status':'PASS','feasible_initial_states':states,'operation_trials':trials,
        'accepted_positive_insertions':accepted,'rejected_trials_restored':rejected,
        'capacities':[1,2],'gains':[0,1],'host_systems':systems,
        'source_sha256':hashlib.sha256((root/'python/seal.py').read_bytes()).hexdigest(),
        'scope':'Finite exhaustive regression against independent physical-set feasibility; no universal theorem claim.'}
print(json.dumps(report,indent=2))
