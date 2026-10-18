"""Generate new finite certificates, not a replay of the historical SEAL implementation.
Author: Juan Pablo Traverso Gianini.
"""
import copy
import hashlib
import json
import time
from pathlib import Path
from itertools import combinations
from seal_reference import construct, dual, family, objects, repair_at
from check_certificate import check

ROOT = Path(__file__).resolve().parent


def exhaustive_optimum(hosts):
    pairs = sorted(objects(hosts))
    index = {e: i for i, e in enumerate(pairs)}
    choices = []
    for h in hosts:
        edges = list(combinations(h, 2))
        masks = [0]
        def visit(start, used, mask):
            for i in range(start, len(edges)):
                e = edges[i]
                if not set(e) & used:
                    nxt = mask | (1 << index[e])
                    masks.append(nxt)
                    visit(i+1, used | set(e), nxt)
        visit(0, set(), 0)
        choices.append(masks)
    reachable = {0}
    for masks in choices:
        reachable = {old | new for old in reachable for new in masks if not old & new}
    return max(x.bit_count() for x in reachable)


def main():
    out = ROOT/'certificates'
    out.mkdir(exist_ok=True)
    cases = [('empty', [], True, True), ('triangle_one_host', [[0,1,2]], True, True),
             ('triangle_three_hosts', [[0,1,2]]*3, True, True),
             ('k4_two_hosts', [list(range(4))]*2, True, True),
             ('overlap', [[0,1,2],[1,2,3],[0,2,3]], True, True),
             ('five_one_host', [list(range(5))], True, True)]
    for seed in range(1,7):
        cases.append((f'compact_{seed}', family(8, 9, seed, 'rand'), True, False))
    # Same host-generation parameters as historical Table 2; deliberately no N1/N2
    # on these larger inputs. These are selector/dual tests, not benchmark replication.
    for kind, configs in [('rand', [(24,60),(32,100),(40,140)]),
                          ('bigrand', [(24,40),(32,60),(40,80)]),
                          ('rr', [(24,6),(32,8),(40,10)])]:
        for n, m in configs:
            for seed in (1,2):
                cases.append((f'{kind}_{n}_{m}_{seed}', family(n,m,seed,kind), False, False))
    results, negative = [], []
    for name, hosts, repairs, exact in cases:
        start = time.monotonic()
        R, moves = construct(hosts, repairs=repairs)
        cert, upper = dual(hosts)
        data = {'name': name, 'implementation': 'SEAL_REFERENCE_v1', 'hosts': hosts,
                'mode': 'selector_N1_N2_dual' if repairs else 'selector_dual_no_repairs',
                'packing': [[j,*e] for e,j in sorted(R.items())], 'dual': cert,
                'lower': len(R), 'upper': str(upper),
                'certified_optimal': len(R) == upper.numerator//upper.denominator,
                'accepted_repairs': moves}
        result = check(data)
        if exact:
            opt = exhaustive_optimum(hosts)
            assert len(R) <= opt <= upper
            result['independent_enumeration_optimum'] = opt
        path = out/f'{name}.json'
        path.write_text(json.dumps(data, indent=2)+'\n', encoding='utf-8')
        result.update(mode=data['mode'], accepted_repairs=moves,
                      elapsed_seconds=round(time.monotonic()-start, 3),
                      certificate_sha256=hashlib.sha256(path.read_bytes()).hexdigest())
        results.append(result)
        print(json.dumps(result), flush=True)
    sample = json.loads((out/'triangle_one_host.json').read_text())
    for label in ('duplicate_pair', 'uncovered_dual', 'inflated_lower', 'wrong_upper'):
        bad = copy.deepcopy(sample)
        if label == 'duplicate_pair': bad['packing'].append(bad['packing'][0])
        if label == 'uncovered_dual': bad['dual'] = []
        if label == 'inflated_lower': bad['lower'] += 1
        if label == 'wrong_upper': bad['upper'] = '0'
        try:
            check(bad)
        except AssertionError as e:
            negative.append({'mutation': label, 'rejected': True, 'reason': str(e)})
        else:
            raise AssertionError(f'accepted corruption: {label}')
    # Directly exercise both repair definitions, rather than infer coverage from runs.
    move_cases = [([[0,1,2],[0,2]], {(0,2):0}, 1),
                  ([[0,1,2],[0,2,3],[2,3]], {(0,2):0,(2,3):1}, 2)]
    move_checks = []
    for hosts, R, depth in move_cases:
        nxt = repair_at(R, objects(hosts), (0,1), 0, depth)
        assert nxt is not None and len(nxt) == len(R)+1
        assert all(sum(j == k and bool(set(e)&set(f)) for f,k in nxt.items()) == 1 for e,j in nxt.items())
        move_checks.append({'move': f'N{depth}', 'before': [[j,*e] for e,j in R.items()],
                            'after': [[j,*e] for e,j in nxt.items()], 'hosts': hosts, 'verified': True})
    report = {'status': 'PASS', 'count': len(results), 'results': results,
              'negative_controls': negative, 'direct_move_checks': move_checks,
              'scope': 'Finite witnesses and rational upper bounds; no universal theorem or historical runtime claim.'}
    (ROOT/'RESULTS.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')


if __name__ == '__main__':
    main()
