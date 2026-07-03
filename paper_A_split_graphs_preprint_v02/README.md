# Summary of changes for run 1420ef69-2382-426b-a4f2-9291ec3c58ab
I formalized the mathematical content of the paper *Clique Partitions of Split Graphs and the 1/6 Barrier* (which concerns Erdős Problem #81) in Lean 4 / Mathlib. The whole project builds with no `sorry`, no `axiom`, and no `@[implemented_by]`; the main theorems were checked to depend only on the standard axioms `propext`, `Classical.choice`, `Quot.sound`.
Files (all under `RequestProject/`):
- `Envelope.lean` — **Lemma 2 (Envelope Lemma), analytic core**, fully proved: the two governing polynomial inequalities `envelope_ineqI` and `envelope_ineqM` on the triangle `{a≥1, c≥0, a+c≤3}`, and the pointwise fractional inequality `envelope_pointwise` (`a/2 + u + max(c(a-1)/2, ac/2 − (a/c)u) ≥ (a+c)²/4 − (a+c)/2 + 3/4`). This is the fractional inequality on `K_k` from which the constant `1/6` arises.
- `LoadIdentity.lean` — **Lemma 1 (Load identity)**, fully proved: the co-neighborhood loads over the clique side sum to `b≥2 / 2`.
- `CliquePartition.lean` — definitions of an edge clique partition (`IsEdgeCliquePartition`) and the clique partition number (`cliquePartitionNumber`) for finite simple graphs (Mathlib has cliques but no clique-partition number), plus existence of a partition (`exists_edgeCliquePartition`) and a reduction lemma (`le_cliquePartitionNumber`).
- `Sharpness.lean` — **Section 7 (Sharpness), in full** for the complete split graph `K_p ∨ \bar{K_q}` (`compSplit`): `compSplit_partition_lower` (every edge clique partition has ≥ `q·p − C(p,2)` parts, via the covering-clique counting argument), `compSplit_cliquePartitionNumber_lower` (`cp ≥ q·p − C(p,2)`), and `compSplit_sharp_lower` (for `q = 2p`, so `n = 3p`, one has `n² ≤ 6·cp(G)`, i.e. `cp(G) ≥ n²/6`), exhibiting a split graph that witnesses sharpness of the constant `1/6`.
- `Main.lean` — imports everything and documents precisely what is and is not formalized.
Scope note (also recorded in `Main.lean`): I proved the analytic heart of the paper (the Envelope Lemma), Lemma 1, and the complete matching lower bound / sharpness result. I did not formalize the *upper bound* half of Theorem 1 (`cp(G) ≤ (1/6+o(1))n²` for all split graphs). Its proof (Sections 2–6) reduces, via fractional triangle packing, to the Envelope Lemma but crucially invokes the Haxell–Rödl / Yuster theorem on the asymptotic equivalence of fractional and integral packings, which is not available in Mathlib; I therefore did not reprove that external input or the associated `o(n²)` reduction (doing so honestly would have required either reproving Yuster's theorem or assuming it — I avoided introducing any axiom). Everything actually stated is proved in full.


This project was edited by [Aristotle](https://aristotle.harmonic.fun).
To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
