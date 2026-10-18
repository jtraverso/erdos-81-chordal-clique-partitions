"""Independent exact checker. Standard library only; no producer import or LP solver.
Author: Juan Pablo Traverso Gianini.
"""
import json
import sys
from pathlib import Path
from fractions import Fraction
from itertools import combinations


def check(data):
    hosts = [set(h) for h in data['hosts']]
    pairs = {e for h in hosts for e in combinations(sorted(h), 2)}
    seen, used = set(), [set() for _ in hosts]
    for item in data['packing']:
        j, a, b = item
        assert isinstance(j, int) and 0 <= j < len(hosts), 'host index'
        assert a < b and {a, b} <= hosts[j], 'packing object'
        assert (a, b) not in seen, 'duplicate pair'
        assert not {a, b} & used[j], 'host matching conflict'
        seen.add((a, b))
        used[j].update((a, b))
    constraints, upper = [], Fraction(0)
    for r in data['dual']:
        v, j, vs, kind = Fraction(r['value']), r['host'], set(r['vertices']), r['kind']
        assert v >= 0, 'negative dual'
        assert len(vs) == len(r['vertices']), 'duplicate vertices'
        if kind == 'pair':
            assert j == -1 and len(vs) == 2 and tuple(sorted(vs)) in pairs, 'pair constraint'
            rhs = 1
        else:
            assert isinstance(j, int) and 0 <= j < len(hosts) and vs <= hosts[j], 'host constraint'
            if kind == 'vertex':
                assert len(vs) == 1, 'vertex constraint'
                rhs = 1
            else:
                assert kind == 'odd' and len(vs) >= 3 and len(vs) % 2 == 1, 'odd constraint'
                rhs = (len(vs)-1)//2
        constraints.append((kind, j, vs, v))
        upper += rhs*v
    for j, h in enumerate(hosts):
        for e in combinations(sorted(h), 2):
            weight = sum(v for kind, host, vs, v in constraints
                         if (kind == 'pair' and vs == set(e))
                         or (host == j and kind == 'vertex' and bool(vs & set(e)))
                         or (host == j and kind == 'odd' and set(e) <= vs))
            assert weight >= 1, f'uncovered dual object {j,e}'
    assert upper == Fraction(data['upper']), 'reported upper'
    lower, bound = len(seen), upper.numerator//upper.denominator
    assert lower == data['lower'] <= bound, 'reported lower'
    assert data['certified_optimal'] == (lower == bound), 'optimality label'
    return {'name': data['name'], 'lower': lower, 'upper': str(upper), 'floor_upper': bound,
            'certified_optimal': lower == bound, 'objects': sum(len(h)*(len(h)-1)//2 for h in hosts)}


if __name__ == '__main__':
    directory = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).parent/'certificates'
    results = [check(json.loads(p.read_text(encoding='utf-8'))) for p in sorted(directory.glob('*.json'))]
    assert results, 'no certificates'
    print(json.dumps({'status': 'PASS', 'count': len(results), 'results': results}, indent=2))
