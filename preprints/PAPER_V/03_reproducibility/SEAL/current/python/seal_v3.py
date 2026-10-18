"""
SEAL v3 -- computational companion to Paper V.
Authors: Juan Pablo Traverso Gianini. Corrected prepublication release, 18 October 2026.

The public driver supports unit weights and capacity one only. Bipartite
components satisfying the global Galvin or local BKW list conditions are
offered to a constructive routine. Its assignment is checked before use;
this implementation does not assert that the routine succeeds throughout
the full range of either existence theorem. Unsolved components use the
corrected construction plus transactional N1 heuristic in seal.py.

The Konig bound is diagnostic. The rational audit uses CBC to generate
candidate prices, rationalises and repairs them, and exports every dual
row. Exact independent checking of those rows and the physical packing
certifies the recorded upper bound. A zero cardinality gap certifies that
particular packing's optimum. It does not establish a universal algorithm
guarantee or an end-to-end Lean verification of this source code.
"""

from fractions import Fraction
from itertools import combinations
from collections import defaultdict, deque
import json, math, time

from seal import normalize, build_cov, Packing, seal_best, ilp_optimum


# ----------------------------------------------------------------------
# (1) coverable-pair graph, components, bipartiteness
# ----------------------------------------------------------------------

def components(cov):
    """Connected components of the coverable-pair graph. Returns list of (vertices, pairs)."""
    adj = defaultdict(set)
    for (a, b) in cov:
        adj[a].add(b); adj[b].add(a)
    seen = set(); comps = []
    for v in sorted(adj):
        if v in seen:
            continue
        q = deque([v]); seen.add(v); verts = {v}
        while q:
            x = q.popleft()
            for y in adj[x]:
                if y not in seen:
                    seen.add(y); verts.add(y); q.append(y)
        pairs = [e for e in cov if e[0] in verts]
        comps.append((verts, pairs))
    return comps


def two_colour(verts, pairs):
    """BFS 2-colouring; returns dict v->0/1 or None if not bipartite."""
    adj = defaultdict(set)
    for (a, b) in pairs:
        adj[a].add(b); adj[b].add(a)
    col = {}
    for s in sorted(verts):
        if s in col:
            continue
        col[s] = 0; q = deque([s])
        while q:
            x = q.popleft()
            for y in adj[x]:
                if y not in col:
                    col[y] = 1 - col[x]; q.append(y)
                elif col[y] == col[x]:
                    return None
    return col


# ----------------------------------------------------------------------
# (1) Konig Delta-edge-colouring of a bipartite (multi)graph by alternating paths
# ----------------------------------------------------------------------

def konig_edge_colouring(edges, left_of, right_of, Delta):
    """edges: list of hashable edge ids; left_of/right_of: id -> vertex. Returns dict id -> colour in range(Delta)."""
    colour = {}
    at = defaultdict(dict)          # at[vertex][colour] = edge id
    for e in edges:
        u, v = left_of[e], right_of[e]
        free_u = next(c for c in range(Delta) if c not in at[u])
        free_v = next(c for c in range(Delta) if c not in at[v])
        if free_u == free_v:
            c = free_u
        else:
            # alpha free at u, beta free at v; swap alpha/beta along the path starting at v with alpha
            alpha, beta = free_u, free_v
            path = []; x = v; c_cur = alpha; side_left = False
            while c_cur in at[x]:
                f = at[x][c_cur]
                path.append(f)
                x = left_of[f] if not side_left else right_of[f]
                side_left = not side_left
                c_cur = beta if c_cur == alpha else alpha
            # the path cannot reach u (bipartite parity); swap colours on the path
            for f in path:
                old = colour[f]; new = beta if old == alpha else alpha
                del at[left_of[f]][old]; del at[right_of[f]][old]
                colour[f] = new
            for f in path:
                at[left_of[f]][colour[f]] = f; at[right_of[f]][colour[f]] = f
            c = alpha
        colour[e] = c
        at[u][c] = e; at[v][c] = e
    return colour


# ----------------------------------------------------------------------
# (1) Galvin list edge colouring via kernels (stable matchings)
# ----------------------------------------------------------------------

def stable_matching_kernel(S, left_of, right_of, rank):
    """Kernel of the Galvin orientation on edge set S: left vertices prefer LARGER rank, right vertices prefer
    SMALLER rank. Deferred acceptance with left vertices proposing. Returns the matching (set of edge ids)."""
    S = list(S)
    by_left = defaultdict(list)
    for e in S:
        by_left[left_of[e]].append(e)
    for u in by_left:
        by_left[u].sort(key=lambda e: -rank[e])      # best first
    ptr = {u: 0 for u in by_left}
    held = {}                                        # right vertex -> edge held
    free = deque(by_left.keys())
    while free:
        u = free.popleft()
        if ptr[u] >= len(by_left[u]):
            continue
        e = by_left[u][ptr[u]]; ptr[u] += 1
        r = right_of[e]
        if r not in held:
            held[r] = e
        else:
            f = held[r]
            if rank[e] < rank[f]:                    # right prefers smaller rank
                held[r] = e
                free.append(left_of[f])
            else:
                free.append(u)
    return set(held.values())


def galvin_list_colouring(edges, left_of, right_of, lists, Delta):
    """Proper list edge colouring of a bipartite multigraph with |L(e)| >= Delta (Galvin). Returns id -> colour,
    or None if the construction failed (which the theorem excludes when the hypothesis holds)."""
    rank = konig_edge_colouring(edges, left_of, right_of, Delta)
    L = {e: set(lists[e]) for e in edges}
    uncoloured = set(edges)
    result = {}
    colours = sorted({c for e in edges for c in lists[e]})
    for c in colours:
        S = [e for e in uncoloured if c in L[e]]
        if not S:
            continue
        K = stable_matching_kernel(S, left_of, right_of, rank)
        for e in K:
            result[e] = c
        uncoloured -= K
        for e in S:
            L[e].discard(c)
    if uncoloured:
        return None
    return result


def proper_list_assignment_check(pairs, host_of, lists):
    """Exact re-check of the theorem hypothesis on the OUTPUT: host in list, and pairs sharing a vertex get
    distinct hosts (this is `Host.ProperOn`, decidable)."""
    for e in pairs:
        if host_of[e] not in lists[e]:
            return False
    by_vertex = defaultdict(list)
    for e in pairs:
        by_vertex[e[0]].append(e); by_vertex[e[1]].append(e)
    for v, es in by_vertex.items():
        hs = [host_of[e] for e in es]
        if len(set(hs)) != len(hs):
            return False
    return True


def galvin_regime(hosts, cov):
    """Detect and solve the exact regime component by component.
    Returns (assignment dict pair->host for solved pairs, report list)."""
    assignment = {}
    report = []
    for verts, pairs in components(cov):
        col = two_colour(verts, pairs)
        deg = defaultdict(int)
        for (a, b) in pairs:
            deg[a] += 1; deg[b] += 1
        Delta = max(deg[v] for v in verts) if verts else 0
        lists = {e: cov[e] for e in pairs}
        rec = {"vertices": len(verts), "pairs": len(pairs), "bipartite": col is not None, "Delta": Delta,
               "galvin_global": False, "bkw_local": False, "solved": False, "konig_bound": None}
        if col is not None and Delta >= 1:
            rec["konig_bound"] = math.ceil(len(pairs) / Delta)
            rec["galvin_global"] = all(len(lists[e]) >= Delta for e in pairs)
            rec["bkw_local"] = all(len(lists[e]) >= max(deg[e[0]], deg[e[1]]) for e in pairs)
            if rec["galvin_global"] or rec["bkw_local"]:
                left_of = {e: (e[0] if col[e[0]] == 0 else e[1]) for e in pairs}
                right_of = {e: (e[1] if col[e[0]] == 0 else e[0]) for e in pairs}
                # the constructive algorithm implemented here is Galvin's (global lists); on a component where
                # only the local BKW condition holds it is attempted and its output verified.
                res = galvin_list_colouring(pairs, left_of, right_of, lists, Delta)
                if res is not None and proper_list_assignment_check(pairs, res, lists):
                    assignment.update(res); rec["solved"] = True
        report.append(rec)
    return assignment, report


# ----------------------------------------------------------------------
# (3) exact rational dual certificate of the master LP (generated cuts)
# ----------------------------------------------------------------------

def exact_dual_bound(hosts, weights=None, caps=None, blossom_max_palette=9, time_limit=60):
    """Returns (U : Fraction, certificate dict). U is an EXACT upper bound on the (weighted) optimum nu,
    verified with Fraction arithmetic against every object of the instance (weak duality)."""
    import pulp
    hosts = normalize(hosts)
    cov = build_cov(hosts)
    if weights is None:
        weights = {e: 1 for e in cov}
    if caps is None:
        caps = [1] * len(hosts)
    objs = [(j, e) for e, js in cov.items() for j in js]
    prob = pulp.LpProblem("master", pulp.LpMaximize)
    x = {o: pulp.LpVariable(f"x_{i}", 0, 1) for i, o in enumerate(objs)}
    prob += pulp.lpSum(float(weights[e]) * x[(j, e)] for (j, e) in objs)
    cons = []   # (kind, key, rhs, member objects)
    for e, js in cov.items():
        mem = [(j, e) for j in js]
        cons.append(("pair", e, Fraction(1), mem))
    hv = defaultdict(list)
    for (j, e) in objs:
        for a in e:
            hv[(j, a)].append((j, e))
    for (j, a), mem in hv.items():
        cons.append(("deg", (j, a), Fraction(caps[j]), mem))
    for j, N in enumerate(hosts):
        if caps[j] != 1 or len(N) > blossom_max_palette:
            continue
        for r in range(3, len(N) + 1, 2):
            for S in combinations(N, r):
                Ss = set(S)
                mem = [(j, e) for e in combinations(N, 2) if set(e) <= Ss and (j, e) in x]
                if mem:
                    cons.append(("odd", (j, S), Fraction(r - 1, 2), mem))
    # solve the DUAL explicitly (min sum rhs*y  s.t.  every object covered by weight >= w(e), y >= 0);
    # reading dual variables is more robust than reading constraint multipliers from CBC.
    dual = pulp.LpProblem("master_dual", pulp.LpMinimize)
    yv = [pulp.LpVariable(f"y_{k}", 0) for k in range(len(cons))]
    dual += pulp.lpSum(float(cons[k][2]) * yv[k] for k in range(len(cons)))
    incident0 = defaultdict(list)
    for k, (kind, key, rhs, mem) in enumerate(cons):
        for o in mem:
            incident0[o].append(k)
    for (j, e) in objs:
        dual += pulp.lpSum(yv[k] for k in incident0[(j, e)]) >= float(weights[e])
    dual.solve(pulp.PULP_CBC_CMD(msg=0, timeLimit=time_limit))
    prob = dual
    y = []
    for v in yv:
        val = v.value() if v.value() is not None else 0.0
        y.append(max(Fraction(0), Fraction(val).limit_denominator(10 ** 6)))
    incident = defaultdict(list)
    for k, (kind, key, rhs, mem) in enumerate(cons):
        for o in mem:
            incident[o].append(k)
    pair_index = {key: k for k, (kind, key, rhs, mem) in enumerate(cons) if kind == "pair"}
    repaired = 0
    for (j, e) in objs:
        s = sum(y[k] for k in incident[(j, e)])
        w = Fraction(weights[e])
        if s < w:
            y[pair_index[e]] += (w - s); repaired += 1
    # exact verification (weak duality: y >= 0, every object covered)
    for (j, e) in objs:
        assert sum(y[k] for k in incident[(j, e)]) >= Fraction(weights[e])
    assert all(v >= 0 for v in y)
    U = sum(y[k] * cons[k][2] for k in range(len(cons)))
    cert = {"num_constraints": len(cons), "num_odd_sets": sum(1 for c in cons if c[0] == "odd"),
            "repaired_objects": repaired, "U": str(U), "floor_U": math.floor(U),
            "lp_status": pulp.LpStatus[prob.status]}
    cert['rows'] = [{'kind': c[0], 'key': c[1], 'rhs': str(c[2]), 'y': str(price)}
                    for c, price in zip(cons, y)]
    return U, cert


# ----------------------------------------------------------------------
# SEAL v3 driver
# ----------------------------------------------------------------------

def seal_v3(hosts, weights=None, caps=None, with_audit=True):
    """Standard unit-weight, capacity-one v3 only; other variants use seal_best."""
    hosts = normalize(hosts)
    if caps is not None and (len(caps) != len(hosts) or any(c != 1 for c in caps)):
        raise ValueError('seal_v3 supports capacity one only')
    if weights is not None and any(w != 1 for w in weights.values()):
        raise ValueError('seal_v3 supports unit weights only')
    cov = build_cov(hosts)
    t0 = time.time()
    # Phase 0/1: exact regime on bipartite components, then SEAL on the rest
    assignment, report = galvin_regime(hosts, cov)
    P = Packing(hosts, caps or [1] * len(hosts))
    for e, j in assignment.items():
        assert P.can_place(j, e); P.place(j, e)
    # remaining pairs: run SEAL (seal_best) on the instance restricted to unsolved components is equivalent
    # to running it with the solved pairs pre-placed; we do the latter by removing solved pairs' hosts' usage.
    base = seal_best(hosts, weights=weights, caps=caps)
    # merge: keep exact-regime assignments (they are optimal on their components) and SEAL's assignments on
    # the other components (components are vertex-disjoint, so per-host matchings do not interact).
    solved_vertices = set()
    for verts, pairs in components(cov):
        if pairs and all(e in assignment for e in pairs):
            solved_vertices |= verts
    for j, Rj in enumerate(base["R"]):
        for e in Rj:
            if e[0] in solved_vertices:
                continue
            if P.can_place(j, tuple(e)):
                P.place(j, tuple(e))
    t1 = time.time()
    out = {"size": P.size(), "R": [sorted(P.R[j]) for j in range(len(hosts))],
           "seal_time": round(t1 - t0, 4), "components": report,
           "exact_regime_pairs": len(assignment), "cov": len(cov),
           "u": len(cov) - P.size()}
    if with_audit:
        U, cert = exact_dual_bound(hosts, weights, caps)
        out["audit_U"] = str(U); out["audit_floor_U"] = math.floor(U)
        out["audit_gap"] = math.floor(U) - P.size(); out["certificate"] = cert
        out["certified_optimal"] = (out["audit_gap"] == 0) or (out["u"] == 0)
    return out


if __name__ == "__main__":
    # smoke: K_{3,3} coverable pairs with 3 hosts each containing all 6 vertices -> Galvin regime, u = 0
    hosts = [[0, 1, 2, 3, 4, 5]] * 3
    # restrict to bipartite pairs by using palettes {u, r} per host? build a bipartite instance explicitly:
    hosts = [[0, 3], [0, 4], [0, 5], [1, 3], [1, 4], [1, 5], [2, 3], [2, 4], [2, 5]]
    r = seal_v3(hosts)
    print(json.dumps({k: v for k, v in r.items() if k not in ("R", "components")}, indent=1))
