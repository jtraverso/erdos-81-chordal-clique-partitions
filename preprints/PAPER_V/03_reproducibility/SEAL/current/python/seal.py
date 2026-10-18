"""
Authors: Juan Pablo Traverso Gianini.
Corrected prepublication N1 implementation, 18 October 2026.
SEAL and extensions -- reference implementation (Python).

Host-clique packing model accompanying Paper V. This software is a
companion artifact and makes no universal algorithmic theorem claim.
See ../README.md for the scope of the corrected implementation.

Model
-----
An instance is a list of hosts; host j has a palette N_j (a set of vertices).
An object is a pair (j, e) with e = {a,b} subset of N_j. A packing R assigns
objects subject to:
  (P) global pair capacity: each pair e is used by at most one host;
  (H) per-host capacity: inside host j, each vertex lies in at most cap_j
      chosen pairs (cap_j = 1 recovers the per-host matching of the paper;
      cap_j > 1 is the b-matching extension).
Objective: maximise sum of weights w(e) over assigned objects
(w == 1 recovers the unweighted cardinality objective).

Variants
--------
  "standard"  : cap=1, w=1, construction plus transactional N1 repair.
  "psi"       : standard, instrumented with an explicit lexicographic
                potential Psi and per-move monotonicity checks (EMPIRICAL
                termination evidence -- NOT a termination proof; see README).
  "weighted"  : w(e) arbitrary >= 0 (max-weight packing).
  "bmatching" : cap_j >= 1 (host holds a b-matching).

Bounds
------
  ilp_optimum() and lp_bound() expose numerical CBC results and status.
  A floating solver result alone is not an independently checked exact
  certificate. Standard v3 exports rational dual rows for exact checking.
"""

from itertools import combinations
from collections import defaultdict
import json


# ----------------------------------------------------------------------
# instance helpers
# ----------------------------------------------------------------------

def normalize(hosts):
    """Each host -> sorted tuple of distinct vertices."""
    return [tuple(sorted(set(h))) for h in hosts]


def build_cov(hosts):
    """cov[pair] = list of host indices whose palette contains the pair."""
    cov = defaultdict(list)
    for j, N in enumerate(hosts):
        for e in combinations(N, 2):
            cov[tuple(sorted(e))].append(j)
    return dict(cov)


def default_weights(cov):
    return {e: 1.0 for e in cov}


def default_caps(hosts):
    return [1] * len(hosts)


# ----------------------------------------------------------------------
# feasibility bookkeeping
# ----------------------------------------------------------------------

class Packing:
    """A feasible host-clique packing with incremental bookkeeping."""

    def __init__(self, hosts, caps):
        self.hosts = hosts
        self.caps = caps
        self.R = [set() for _ in hosts]        # R[j] = set of pairs at host j
        self.deg = [defaultdict(int) for _ in hosts]  # deg[j][vertex]
        self.used = set()                       # globally used pairs

    def can_place(self, j, e):
        if e in self.used:
            return False
        a, b = e
        c = self.caps[j]
        return self.deg[j][a] < c and self.deg[j][b] < c

    def place(self, j, e):
        a, b = e
        self.R[j].add(e)
        self.deg[j][a] += 1
        self.deg[j][b] += 1
        self.used.add(e)

    def remove(self, j, e):
        a, b = e
        self.R[j].discard(e)
        self.deg[j][a] -= 1
        self.deg[j][b] -= 1
        self.used.discard(e)

    def value(self, weights):
        return sum(weights[e] for j in range(len(self.hosts)) for e in self.R[j])

    def size(self):
        return sum(len(rj) for rj in self.R)

    def relocate_insert(self, j, jp, f, e, gain):
        """Commit both operations, or restore the original packing completely."""
        if jp == j or f not in self.R[j] or e in self.used or gain <= 0:
            return False
        if not set(f) <= set(self.hosts[jp]) or not set(e) <= set(self.hosts[j]):
            return False
        self.remove(j, f)
        if self.can_place(jp, f):
            self.place(jp, f)
            if self.can_place(j, e):
                self.place(j, e)
                return True
            self.remove(jp, f)
        self.place(j, f)
        return False


# ----------------------------------------------------------------------
# SEAL solver (parametrised over the four variants)
# ----------------------------------------------------------------------

def seal(hosts, weights=None, caps=None, mode="standard",
         use_repair=True, track_potential=False, construct="scarcity"):
    """
    Returns dict with keys:
      R (list of lists of pairs), size, value, moves, potential_trace (if asked),
      monotone (bool, if track_potential).
    """
    hosts = normalize(hosts)
    cov = build_cov(hosts)
    if weights is None:
        weights = default_weights(cov)
    if caps is None:
        caps = default_caps(hosts)

    P = Packing(hosts, caps)
    moves = 0
    n1_moves = 0
    trace = []

    def scarcity_residual():
        # secondary potential component: total remaining "room", used only for
        # the lexicographic tie-break log; smaller is more constrained.
        return sum(1 for e in cov if e not in P.used)

    def log_potential():
        # With nonnegative weights value is nondecreasing; a zero-weight
        # insertion may leave it unchanged. Accepted N1 moves have gain > 0.
        trace.append((round(P.value(weights), 6), scarcity_residual()))

    if track_potential:
        log_potential()

    # ---- Phase 1: construction ------------------------------------------
    if construct == "hostmatch":
        # per-host greedy matching: hosts by decreasing palette size (ties by
        # index), within a host add sorted pairs keeping the b-matching.
        for j in sorted(range(len(hosts)), key=lambda j: (-len(hosts[j]), j)):
            for e in combinations(hosts[j], 2):
                e = tuple(sorted(e))
                if P.can_place(j, e):
                    P.place(j, e)
                    moves += 1
                    if track_potential:
                        log_potential()
    else:  # "scarcity"
        if mode == "weighted":
            order = sorted(cov, key=lambda e: (-weights[e], len(cov[e])))
        else:
            order = sorted(cov, key=lambda e: len(cov[e]))
        for e in order:
            if e in P.used:
                continue
            for j in cov[e]:
                if P.can_place(j, e):
                    P.place(j, e)
                    moves += 1
                    if track_potential:
                        log_potential()
                    break

    # ---- Phase 3: repair (insert + N1), monotone-accept only ------------
    if use_repair:
        improved = True
        while improved:
            improved = False

            # (a) plain insertion of any still-free pair with room
            for e in cov:
                if e in P.used:
                    continue
                for j in cov[e]:
                    if P.can_place(j, e):
                        P.place(j, e)
                        moves += 1
                        improved = True
                        if track_potential:
                            log_potential()
                        break

            # (b) N1 relocate-insert: free a blocking pair by moving it, then
            #     insert the target. Accepted only when it nets a value gain.
            for e in list(cov):
                if e in P.used:
                    continue
                a, b = e
                for j in cov[e]:
                    if e in P.used:
                        break
                    # blocking pairs at j touching a or b (sorted: cross-language determinism)
                    blockers = sorted(f for f in P.R[j] if (a in f or b in f))
                    for f in blockers:
                        # find alternative host j' != j hosting f with room
                        moved = False
                        for jp in cov.get(f, []):
                            if jp == j:
                                continue
                            if P.relocate_insert(j, jp, f, e, weights[e]):
                                moves += 2
                                n1_moves += 1
                                moved = True
                                break
                        if moved:
                            improved = True
                            if track_potential:
                                log_potential()
                            break
                    if e in P.used:
                        break

    result = {
        "R": [sorted(P.R[j]) for j in range(len(hosts))],
        "size": P.size(),
        "value": round(P.value(weights), 6),
        "moves": moves,
        "n1_moves": n1_moves,
    }
    if track_potential:
        # Nondecreasing primary component, including zero-weight insertions.
        vals = [t[0] for t in trace]
        monotone = all(vals[i] <= vals[i + 1] for i in range(len(vals) - 1))
        result["potential_trace"] = trace
        result["monotone_value"] = monotone
        result["num_accepted_moves"] = len(trace) - 1
    return result


def seal_best(hosts, weights=None, caps=None, mode="standard"):
    """Deterministic multi-start: run both construction strategies + repair,
    keep the better packing. Ports replicate the same two strategies."""
    best = None
    for c in ("scarcity", "hostmatch"):
        r = seal(hosts, weights=weights, caps=caps, mode=mode, construct=c)
        if best is None or r["value"] > best["value"]:
            best = r
            best["construct"] = c
    return best


# ----------------------------------------------------------------------
# exact / LP bounds via pulp (CBC)  -- the "used-today" baseline + certificate
# ----------------------------------------------------------------------

def _lp(hosts, weights, caps, integer, time_limit=20):
    import pulp
    hosts = normalize(hosts)
    cov = build_cov(hosts)
    if weights is None:
        weights = default_weights(cov)
    if caps is None:
        caps = default_caps(hosts)

    prob = pulp.LpProblem("hostclique", pulp.LpMaximize)
    x = {}
    for e, js in cov.items():
        for j in js:
            cat = "Binary" if integer else "Continuous"
            v = pulp.LpVariable(f"x_{j}_{e[0]}_{e[1]}", 0, 1, cat)
            x[(j, e)] = v

    prob += pulp.lpSum(weights[e] * x[(j, e)] for (j, e) in x)

    # (P) pair capacity
    for e, js in cov.items():
        prob += pulp.lpSum(x[(j, e)] for j in js) <= 1

    # (H) per-host vertex degree <= cap_j
    host_vertex_pairs = defaultdict(list)
    for (j, e) in x:
        for a in e:
            host_vertex_pairs[(j, a)].append(x[(j, e)])
    for (j, a), vs in host_vertex_pairs.items():
        prob += pulp.lpSum(vs) <= caps[j]

    prob.solve(pulp.PULP_CBC_CMD(msg=0, timeLimit=time_limit))
    return pulp.value(prob.objective), pulp.LpStatus[prob.status]


def ilp_optimum(hosts, weights=None, caps=None, time_limit=20):
    return _lp(hosts, weights, caps, integer=True, time_limit=time_limit)


def lp_bound(hosts, weights=None, caps=None, time_limit=20):
    return _lp(hosts, weights, caps, integer=False, time_limit=time_limit)


# ----------------------------------------------------------------------
# instance IO (shared with the C++ and JS ports)
# ----------------------------------------------------------------------

def load_instance(path):
    with open(path) as f:
        d = json.load(f)
    hosts = d["hosts"]
    weights = None
    if "weights" in d and d["weights"]:
        weights = {tuple(sorted(map(int, k.split(",")))): float(v)
                   for k, v in d["weights"].items()}
    caps = d.get("caps")
    return hosts, weights, caps


def dump_instance(path, hosts, weights=None, caps=None):
    d = {"hosts": hosts}
    if weights:
        d["weights"] = {f"{min(e)},{max(e)}": w for e, w in weights.items()}
    if caps:
        d["caps"] = caps
    with open(path, "w") as f:
        json.dump(d, f)


if __name__ == "__main__":
    # tiny smoke test: K4 palette on one host, cap 1 -> matching size 2
    r = seal([[0, 1, 2, 3]], mode="standard")
    print("smoke:", r["size"], r["value"])
