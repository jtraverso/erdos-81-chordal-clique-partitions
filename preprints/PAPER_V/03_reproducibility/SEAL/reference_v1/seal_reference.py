"""New reference implementation, not the missing historical seal.py.

Author: Juan Pablo Traverso Gianini. Scope: unweighted host matchings, capacity 1.
The optional dual solver is a witness generator; check_certificate.py is independent.
"""
from fractions import Fraction
from itertools import combinations
import random


def objects(hosts):
    return {e: [j for j, h in enumerate(hosts) if set(e) <= set(h)]
            for e in sorted({e for h in hosts for e in combinations(sorted(set(h)), 2)})}


def available(R, j, e):
    return e not in R and all(j != k or not set(e) & set(f) for f, k in R.items())


def blockers(R, j, e):
    return [f for f, k in R.items() if k == j and set(e) & set(f)]


def repair_at(R, lists, e, j, depth):
    """Exhaust the N1 (depth=1) or N2 (depth=2) move at this target."""
    bs = blockers(R, j, e)
    if len(bs) != 1:
        return None
    f = bs[0]
    base = dict(R)
    del base[f]
    for jp in lists[f]:
        if jp == j:
            continue
        trial = dict(base)
        if not available(trial, jp, f):
            if depth != 2:
                continue
            gs = blockers(trial, jp, f)
            if len(gs) != 1:
                continue
            g = gs[0]
            del trial[g]
            for jpp in lists[g]:
                if jpp == jp or not available(trial, jpp, g):
                    continue
                nxt = dict(trial)
                nxt[g] = jpp
                if available(nxt, jp, f):
                    nxt[f] = jp
                    if available(nxt, j, e):
                        nxt[e] = j
                        return nxt
            continue
        trial[f] = jp
        if available(trial, j, e):
            trial[e] = j
            return trial
    return None


def construct(hosts, repairs=True):
    lists = objects(hosts)
    R = {}
    while True:
        occupied = [set() for _ in hosts]
        counts = [0 for _ in hosts]
        for f, j in R.items():
            occupied[j].update(f)
            counts[j] += 1
        choices = [(len(js), e, js) for e in lists if e not in R
                   if (js := [j for j in lists[e] if e[0] not in occupied[j] and e[1] not in occupied[j]])]
        if not choices:
            break
        _, e, js = min(choices)
        j = min(js, key=lambda j: (len(hosts[j])-2*counts[j], j))
        R[e] = j
    accepted = {'N1': 0, 'N2': 0}
    if repairs:
        while True:
            improved = False
            for depth in (1, 2):
                for e in lists:
                    if e in R:
                        continue
                    for j in lists[e]:
                        nxt = repair_at(R, lists, e, j, depth)
                        if nxt is not None:
                            assert len(nxt) == len(R)+1
                            R = nxt
                            accepted[f'N{depth}'] += 1
                            improved = True
                            break
                    if improved:
                        break
                if improved:
                    break
            if not improved:
                break
    return R, accepted


def dual(hosts):
    """Pair, host-vertex and small odd-set inequalities; rational repair."""
    from scipy.optimize import linprog
    from scipy.sparse import lil_matrix
    lists = objects(hosts)
    obs = [(j, e) for e, js in lists.items() for j in js]
    rows = [('pair', -1, e, 1) for e in lists]
    for j, h in enumerate(hosts):
        rows += [('vertex', j, (v,), 1) for v in h]
        if len(h) <= 9:
            rows += [('odd', j, s, (len(s)-1)//2) for k in range(3, len(h)+1, 2)
                     for s in combinations(h, k)]
    matrix = lil_matrix((len(obs), len(rows)), dtype=float)
    covers = []
    for col, (j, e) in enumerate(obs):
        ids = [i for i, (kind, host, vs, _) in enumerate(rows)
               if (kind == 'pair' and tuple(vs) == e)
               or (host == j and kind == 'vertex' and vs[0] in e)
               or (host == j and kind == 'odd' and set(e) <= set(vs))]
        covers.append(ids)
        for i in ids:
            matrix[col, i] = -1
    if not obs:
        return [], Fraction(0)
    ans = linprog([r[3] for r in rows], A_ub=matrix.tocsr(), b_ub=[-1]*len(obs),
                  bounds=(0, None), method='highs', options={'time_limit': 30})
    if not ans.success:
        # The trivial pair certificate remains valid even when optimization fails.
        vals = [Fraction(1 if row[0] == 'pair' else 0) for row in rows]
    else:
        vals = [max(Fraction(0), Fraction(float(x)).limit_denominator(10**6)) for x in ans.x]
    pair_row = {tuple(row[2]): i for i, row in enumerate(rows) if row[0] == 'pair'}
    for (_, e), ids in zip(obs, covers):
        deficit = 1-sum(vals[i] for i in ids)
        if deficit > 0:
            vals[pair_row[e]] += deficit
    certificate = [{'kind': kind, 'host': j, 'vertices': list(vs), 'value': str(value)}
                   for (kind, j, vs, rhs), value in zip(rows, vals) if value]
    upper = sum(Fraction(row[3])*v for row, v in zip(rows, vals))
    return certificate, upper


def family(n, m, seed, kind):
    rng = random.Random(seed)
    if kind == 'rand':
        return [sorted(rng.sample(range(n), rng.randint(3, min(7, n)))) for _ in range(m)]
    if kind == 'bigrand':
        return [sorted(rng.sample(range(n), rng.randint(n//2, 3*n//4))) for _ in range(m)]
    return [sorted(set(range(n))-set(rng.sample(range(n), m))) for _ in range(n-1 if n % 2 == 0 else n)]
