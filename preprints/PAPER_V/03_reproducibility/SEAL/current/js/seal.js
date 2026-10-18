// SEAL and extensions -- JavaScript (Node) port.
// Authors: Juan Pablo Traverso Gianini. Corrected prepublication N1, 18 October 2026.
// Companion repository artifact; not part of the manuscript, no theorem claims.
// Mirrors python/seal.py exactly (deterministic) for cross-language validation.
// Bounds (ILP/LP) live only in the Python reference; this port covers the
// four SEAL variants (construction + repair) and reports value/size.
"use strict";
const fs = require("fs");
const path = require("path");

const key = (a, b) => (a < b ? `${a},${b}` : `${b},${a}`);

function combinations2(arr) {           // ascending lexicographic, arr sorted
  const out = [];
  for (let i = 0; i < arr.length; i++)
    for (let j = i + 1; j < arr.length; j++) out.push([arr[i], arr[j]]);
  return out;
}

function normalize(hosts) {
  return hosts.map(h => [...new Set(h)].sort((a, b) => a - b));
}

function buildCov(hosts) {               // Map preserves insertion (discovery) order
  const cov = new Map();
  hosts.forEach((N, j) => {
    for (const [a, b] of combinations2(N)) {
      const k = key(a, b);
      if (!cov.has(k)) cov.set(k, []);
      cov.get(k).push(j);
    }
  });
  return cov;
}

class Packing {
  constructor(hosts, caps) {
    this.hosts = hosts; this.caps = caps;
    this.R = hosts.map(() => new Set());          // set of pair-keys per host
    this.deg = hosts.map(() => new Map());
    this.used = new Set();
  }
  d(j, v) { return this.deg[j].get(v) || 0; }
  canPlace(j, k) {
    if (this.used.has(k)) return false;
    const [a, b] = k.split(",").map(Number);
    return this.d(j, a) < this.caps[j] && this.d(j, b) < this.caps[j];
  }
  place(j, k) {
    const [a, b] = k.split(",").map(Number);
    this.R[j].add(k); this.used.add(k);
    this.deg[j].set(a, this.d(j, a) + 1); this.deg[j].set(b, this.d(j, b) + 1);
  }
  remove(j, k) {
    const [a, b] = k.split(",").map(Number);
    this.R[j].delete(k); this.used.delete(k);
    this.deg[j].set(a, this.d(j, a) - 1); this.deg[j].set(b, this.d(j, b) - 1);
  }
  value(W) {
    let s = 0;
    for (let j = 0; j < this.hosts.length; j++)
      for (const k of this.R[j]) s += (W ? (W.get(k) ?? 1) : 1);
    return s;
  }
  size() { return this.R.reduce((s, rj) => s + rj.size, 0); }
  relocateInsert(j, jp, f, e, gain) {
    if (jp === j || !this.R[j].has(f) || this.used.has(e) || gain <= 0) return false;
    if (!f.split(',').map(Number).every(v => this.hosts[jp].includes(v)) ||
        !e.split(',').map(Number).every(v => this.hosts[j].includes(v))) return false;
    this.remove(j, f);
    if (this.canPlace(jp, f)) {
      this.place(jp, f);
      if (this.canPlace(j, e)) { this.place(j, e); return true; }
      this.remove(jp, f);
    }
    this.place(j, f);
    return false;
  }
}

function seal(hosts, { weights = null, caps = null, mode = "standard",
                       construct = "scarcity" } = {}) {
  hosts = normalize(hosts);
  const cov = buildCov(hosts);
  if (!caps) caps = hosts.map(() => 1);
  const W = weights;                              // Map pair-key -> weight, or null
  const P = new Packing(hosts, caps);
  let n1Moves = 0;

  // ---- Phase 1: construction ----
  if (construct === "hostmatch") {
    const order = [...hosts.keys()].sort(
      (i, j) => (hosts[j].length - hosts[i].length) || (i - j));
    for (const j of order)
      for (const [a, b] of combinations2(hosts[j])) {
        const k = key(a, b);
        if (P.canPlace(j, k)) P.place(j, k);
      }
  } else {
    const keys = [...cov.keys()];
    if (mode === "weighted")
      keys.sort((x, y) => ((W.get(y) ?? 1) - (W.get(x) ?? 1)) ||
                          (cov.get(x).length - cov.get(y).length));
    else
      keys.sort((x, y) => cov.get(x).length - cov.get(y).length);
    for (const k of keys) {
      if (P.used.has(k)) continue;
      for (const j of cov.get(k)) if (P.canPlace(j, k)) { P.place(j, k); break; }
    }
  }

  // ---- Phase 3: repair (insert + N1), monotone-accept ----
  let improved = true;
  while (improved) {
    improved = false;
    // (a) plain insertion
    for (const k of cov.keys()) {
      if (P.used.has(k)) continue;
      for (const j of cov.get(k)) if (P.canPlace(j, k)) { P.place(j, k); improved = true; break; }
    }
    // (b) N1 relocate-insert
    for (const e of cov.keys()) {
      if (P.used.has(e)) continue;
      const [a, b] = e.split(",").map(Number);
      for (const j of cov.get(e)) {
        if (P.used.has(e)) break;
        const blockers = [...P.R[j]]
          .filter(f => { const [x, y] = f.split(",").map(Number); return x === a || x === b || y === a || y === b; })
          .sort((p, q) => { const [p0, p1] = p.split(",").map(Number), [q0, q1] = q.split(",").map(Number); return (p0 - q0) || (p1 - q1); });
        for (const f of blockers) {
          let moved = false;
          for (const jp of (cov.get(f) || [])) {
            if (jp === j) continue;
            if (P.relocateInsert(j, jp, f, e, W ? (W.get(e) ?? 1) : 1)) {
              n1Moves++; moved = true; break;
            }
          }
          if (moved) { improved = true; break; }
        }
        if (P.used.has(e)) break;
      }
    }
  }
  return { size: P.size(), value: Math.round(P.value(W) * 1e6) / 1e6,
    n1_moves: n1Moves, R: P.R.map(r => [...r].map(k => k.split(',').map(Number))
      .sort((p, q) => (p[0] - q[0]) || (p[1] - q[1]))) };
}

function sealBest(hosts, opts = {}) {
  let best = null;
  for (const construct of ["scarcity", "hostmatch"]) {
    const r = seal(hosts, { ...opts, construct });
    if (!best || r.value > best.value) best = r;
  }
  return best;
}

module.exports = { seal, sealBest, buildCov, normalize, Packing };

// ---- CLI: read shared instances, emit canonical values as JSON ----
if (require.main === module) {
  const INST = process.argv[2] || path.join(__dirname, "..", "instances");
  const physical = process.argv.includes('--packings');
  const manifest = JSON.parse(fs.readFileSync(path.join(INST, "manifest.json")));
  const out = {};
  for (const name of manifest) {
    const d = JSON.parse(fs.readFileSync(path.join(INST, name + ".json")));
    const W = new Map(Object.entries(d.weights).map(([k, v]) => [k, Number(v)]));
    out[name] = {
      standard: sealBest(d.hosts, { mode: "standard" }),
      weighted: sealBest(d.hosts, { weights: W, mode: "weighted" }),
      bmatching: sealBest(d.hosts, { caps: d.caps, mode: "bmatching" }),
    };
    if (!physical) for (const k of Object.keys(out[name])) out[name][k] = out[name][k].value;
  }
  process.stdout.write(JSON.stringify(out, null, 0));
}
