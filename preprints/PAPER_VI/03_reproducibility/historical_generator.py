#!/usr/bin/env python3
"""Finite certificates for exact clique partitions near a complete split graph.

Standard-library only. The universal proof is in the accompanying manuscript.
The completion search used here is a greedy heuristic, NOT an implementation
of the full Haggkvist--Janssen theorem. Every returned certificate is checked
independently for exact edge coverage, clique legality, counts, and prescribed
types. A failed heuristic would not refute the existence theorem.
"""

from __future__ import annotations
import argparse
import gzip
import hashlib
import itertools
import json
from pathlib import Path
import random
import time


def edge(a, b):
    return (a, b) if a < b else (b, a)


def complete_split(p, q):
    return set(itertools.combinations(range(p), 2)) | {
        (a, x) for a in range(p) for x in range(p, p + q)
    }


def matching_perturbation(p, q, budget, kind, seed):
    rng = random.Random(seed)
    edits = set()
    vertices = list(range(p + q)) if kind == "mixed" else list(range(p, p + q))
    for _ in range(budget):
        order = vertices[:]
        rng.shuffle(order)
        for a, b in zip(order[::2], order[1::2]):
            edits.add(edge(a, b))
    return complete_split(p, q) ^ edits


def exterior_cliques(p, q, degree):
    graph = complete_split(p, q)
    for start in range(p, p + q, degree + 1):
        group = range(start, min(start + degree + 1, p + q))
        graph.update(itertools.combinations(group, 2))
    return graph


def parameters(p, q, graph):
    base = complete_split(p, q)
    differences = graph ^ base
    deg = [0] * (p + q)
    for a, b in differences:
        deg[a] += 1
        deg[b] += 1
    core = {e for e in graph if e[1] < p}
    outer = {e for e in graph if e[0] >= p}
    cross = graph - core - outer
    return {
        "p": p, "q": q, "n": p + q,
        "h": max(deg, default=0), "C": p * (p - 1) // 2 - len(core),
        "A": p * q - len(cross), "m": len(outer), "u": len(core),
        "s": len(cross), "edges": len(graph),
        "M": (p + q) * (p + q + 1) // 6,
        "core": core, "outer": outer, "cross": cross,
    }


def find_core_clique(candidates, size, available):
    for ia, a in enumerate(candidates):
        later = [b for b in candidates[ia + 1:] if edge(a, b) in available]
        if size == 2 and later:
            return [a, later[0]]
        if size == 3:
            for ib, b in enumerate(later):
                for c in later[ib + 1:]:
                    if edge(b, c) in available:
                        return [a, b, c]
    raise RuntimeError("No available core clique in this search")


def construct(p, q, graph, mode, seed):
    rng = random.Random(seed)
    par = parameters(p, q, graph)
    h, m = par["h"], par["m"]
    core_available = set(par["core"])
    outside = list(range(p, p + q))
    at_outside = {x: set() for x in outside}
    forbidden = [{x for x in outside if (a, x) not in graph} for a in range(p)]
    loads = [0] * p
    blocks = []
    tags = {}
    if mode == "triangles":
        cap = max(1, 2 * h)
    elif mode == "all_k4":
        cap = max(1, 4 * h)
    elif mode == "elementary_k5":
        cap = m + 1
    else:
        cap = max(1, 7 * h)
    outer_edges = sorted(par["outer"])
    rng.shuffle(outer_edges)
    for number, (x, y) in enumerate(outer_edges):
        if mode == "triangles":
            size = 1
        elif mode == "all_k4":
            size = 2
        elif mode in {"all_k5", "elementary_k5"}:
            size = 3
        else:
            size = 2 + (rng.randrange(2) if mode == "random_types" else number % 2)
        forbidden_hosts = at_outside[x] | at_outside[y]
        candidates = [
            a for a in range(p)
            if loads[a] < cap and a not in forbidden_hosts
            and (a, x) in graph and (a, y) in graph
        ]
        rng.shuffle(candidates)
        candidates.sort(key=lambda a: loads[a])
        if size == 1:
            if not candidates:
                raise RuntimeError("No available triangle host")
            chosen = candidates[:1]
        else:
            chosen = find_core_clique(candidates, size, core_available)
        block = chosen + [x, y]
        blocks.append(block)
        tags[f"{x},{y}"] = size + 2
        for a in chosen:
            loads[a] += 1
            forbidden[a].update((x, y))
        at_outside[x].update(chosen)
        at_outside[y].update(chosen)
        for a, b in itertools.combinations(chosen, 2):
            core_available.remove(edge(a, b))

    # A search routine for finite examples. The proof uses HJ if this fails.
    completion = None
    for attempt in range(30):
        palette_rng = random.Random(seed * 1000 + attempt)
        used_colors = [set() for _ in range(p)]
        residual = sorted(core_available)
        if attempt:
            palette_rng.shuffle(residual)
        candidate_completion = []
        for a, b in residual:
            excluded = forbidden[a] | forbidden[b] | used_colors[a] | used_colors[b]
            allowed = [x for x in outside if x not in excluded]
            if not allowed:
                break
            x = palette_rng.choice(allowed)
            used_colors[a].add(x)
            used_colors[b].add(x)
            candidate_completion.append([a, b, x])
        else:
            completion = candidate_completion
            break
    if completion is None:
        raise RuntimeError("Completion heuristic failed; universal proof uses HJ")
    blocks.extend(completion)
    consumed = {edge(a, b) for block in blocks for a, b in itertools.combinations(block, 2)}
    blocks.extend([list(e) for e in sorted(graph - consumed)])
    return {
        "p": p, "q": q, "mode": mode, "seed": seed,
        "graph_edges": [list(e) for e in sorted(graph)],
        "blocks": blocks, "outside_type_assignment": tags,
        "search_completion_attempts": attempt + 1,
        "max_lift_load": max(loads, default=0), "load_cap": cap,
    }


def verify(certificate):
    """Check the certificate directly, without using construction state."""
    p, q = certificate["p"], certificate["q"]
    graph = {tuple(e) for e in certificate["graph_edges"]}
    assert len(graph) == len(certificate["graph_edges"]), "Repeated graph edge"
    assert all(0 <= a < b < p + q for a, b in graph), "Invalid graph edge"
    par = parameters(p, q, graph)
    covered = set()
    blocks_by_size = {}
    realized_tags = {}
    for block in certificate["blocks"]:
        assert len(block) >= 2 and len(set(block)) == len(block)
        assert all(0 <= v < p + q for v in block)
        a_count = sum(v < p for v in block)
        b_count = len(block) - a_count
        for a, b in itertools.combinations(block, 2):
            e = edge(a, b)
            assert e in graph, "A claimed clique contains a nonedge"
            assert e not in covered, "An edge is covered more than once"
            covered.add(e)
        blocks_by_size[len(block)] = blocks_by_size.get(len(block), 0) + 1
        if certificate["mode"] == "triangles":
            assert len(block) <= 3
        else:
            slack = 1 - a_count * b_count + a_count * (a_count - 1) // 2
            slack += b_count * (b_count - 1)
            assert slack == 0, "A part has nonzero dual slack"
        if b_count == 2:
            x, y = sorted(v for v in block if v >= p)
            realized_tags[f"{x},{y}"] = len(block)
    assert covered == graph, "The partition leaves uncovered edges"
    assert realized_tags == certificate["outside_type_assignment"]
    expected = par["s"] - par["u"] - (1 if certificate["mode"] == "triangles" else 2) * par["m"]
    assert len(certificate["blocks"]) == expected
    if certificate["mode"] not in {"triangles", "elementary_k5"}:
        count_k5 = blocks_by_size.get(5, 0)
        assert blocks_by_size.get(4, 0) == par["m"] - count_k5
        assert blocks_by_size.get(3, 0) == par["u"] - par["m"] - 2 * count_k5
        assert blocks_by_size.get(2, 0) == par["s"] - 2 * par["u"] - 2 * par["m"] + 2 * count_k5
    return {
        k: v for k, v in par.items() if k not in {"core", "outer", "cross"}
    } | {
        "mode": certificate["mode"],
        "parts": expected, "blocks_by_size": blocks_by_size,
        "completion_attempts": certificate["search_completion_attempts"],
        "verified": True,
    }


def run_suite(destination):
    destination.mkdir(parents=True, exist_ok=True)
    cases = []
    # The all-order boundary p=18h+1, and the exactly balanced p=18h case.
    for p, q, h in [(18, 36, 1), (19, 37, 1), (19, 38, 1), (19, 39, 1),
                    (37, 73, 2), (37, 74, 2), (72, 144, 4)]:
        for kind in ["outer", "mixed"]:
            cases.append((p, q, h, kind, "all_k4"))
            cases.append((p, q, h, kind, "triangles"))
    # Prescribed types at and close to p=63h, in all three residue classes.
    for p, q, h in [(63, 125, 1), (63, 126, 1), (63, 127, 1),
                    (64, 128, 1), (126, 251, 2), (126, 252, 2), (126, 253, 2)]:
        for mode in ["all_k4", "all_k5", "alternating_types", "random_types"]:
            cases.append((p, q, h, "mixed", mode))
    # Elementary K5 theorem at Delta(H)=p/24.
    for p, q, h in [(24, 47, 1), (24, 48, 1), (24, 49, 1), (48, 96, 2)]:
        cases.append((p, q, h, "outer", "elementary_k5"))
    # Chordal examples: clique joined to disjoint exterior cliques.
    for p, q, h in [(63, 126, 1), (126, 252, 2)]:
        for mode in ["all_k4", "all_k5", "random_types", "triangles"]:
            cases.append((p, q, h, "chordal", mode))
    # Base cases (no perturbation).
    for p, q in [(1, 1), (1, 2), (1, 3), (2, 3), (2, 4), (2, 5), (5, 10)]:
        cases.append((p, q, 0, "mixed", "all_k4"))
    results = []
    started = time.time()
    for index, (p, q, h, kind, mode) in enumerate(cases):
        seed = 20261018 + index * 997
        graph = exterior_cliques(p, q, h) if kind == "chordal" else matching_perturbation(p, q, h, kind, seed)
        certificate = construct(p, q, graph, mode, seed)
        result = verify(certificate)
        payload = json.dumps(certificate, separators=(",", ":"), sort_keys=True).encode()
        filename = f"case_{index:03d}_{kind}_{mode}.json.gz"
        with open(destination / filename, "wb") as raw:
            with gzip.GzipFile(fileobj=raw, mode="wb", mtime=0) as stream:
                stream.write(payload)
        result |= {"case": index, "kind": kind, "certificate": filename,
                   "certificate_json_sha256": hashlib.sha256(payload).hexdigest()}
        results.append(result)
    output = {
        "date_utc": "2026-10-18",
        "status": "FINITE_CERTIFICATES_VERIFIED_NOT_LEAN",
        "cases": len(results),
        "all_verified": all(r["verified"] for r in results),
        "runtime_seconds": round(time.time() - started, 3),
        "total_partition_parts_checked": sum(r["parts"] for r in results),
        "total_edges_checked": sum(r["edges"] for r in results),
        "max_completion_attempts": max(r["completion_attempts"] for r in results),
        "results": results,
    }
    (destination.parent / "verification_results.json").write_text(json.dumps(output, indent=2))
    print(json.dumps({k: v for k, v in output.items() if k != "results"}, indent=2), flush=True)
    return output


def verify_saved(directory):
    files = sorted(directory.glob("*.json.gz"))
    if not files:
        raise ValueError("No saved certificates found")
    recorded = json.loads((directory.parent / "verification_results.json").read_text())
    expected = {item["certificate"]: item for item in recorded["results"]}
    assert len(files) == recorded["cases"]
    assert {path.name for path in files} == set(expected)
    for path in files:
        payload = gzip.decompress(path.read_bytes())
        assert hashlib.sha256(payload).hexdigest() == expected[path.name]["certificate_json_sha256"]
        result = verify(json.loads(payload))
        for key in ("p", "q", "h", "C", "A", "m", "u", "s", "M", "edges", "parts", "mode"):
            assert result[key] == expected[path.name][key]
    print(json.dumps({"saved_certificates_checked": len(files), "hashes_match": True, "all_verified": True}))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1] / "certificates")
    parser.add_argument("--verify-only", action="store_true")
    args = parser.parse_args()
    if args.verify_only:
        verify_saved(args.output)
    else:
        run_suite(args.output)
