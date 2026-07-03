import Mathlib
import RequestProject.Envelope
import RequestProject.LoadIdentity
import RequestProject.CliquePartition
import RequestProject.Sharpness
/-!
# Clique Partitions of Split Graphs and the 1/6 Barrier — formalization
This project formalizes the mathematical content of the paper
*Clique Partitions of Split Graphs and the 1/6 Barrier* (Preprint v0.2), which studies the
edge clique partition number `cp(G)` of split graphs in relation to **Erdős Problem #81**.
## What is formalized (with complete, `sorry`-free proofs)
* **Lemma 1 (Load identity)** — `ErdosSplit.load_identity`
  (`RequestProject/LoadIdentity.lean`): the co-neighborhood loads over the clique side sum to
  `b≥2 / 2`.
* **Lemma 2 (Envelope Lemma), analytic core** — `ErdosSplit.envelope_pointwise`, together with
  the two polynomial inequalities `ErdosSplit.envelope_ineqI` and `ErdosSplit.envelope_ineqM`
  (`RequestProject/Envelope.lean`).  This is the fractional inequality on `K_k` from which the
  constant `1/6` (i.e. the extremum of `µn − (3/2)µ²`) arises.
* **Definitions** of the edge clique partition and the clique partition number
  `ErdosSplit.cliquePartitionNumber` for finite simple graphs, together with existence of a
  partition `ErdosSplit.exists_edgeCliquePartition` (`RequestProject/CliquePartition.lean`).
* **Section 7 (Sharpness), in full** — for the complete split graph `K_p ∨ \bar{K_q}`
  (`ErdosSplit.compSplit`):
  * `ErdosSplit.compSplit_partition_lower`: every edge clique partition has at least
    `q·p − C(p,2)` parts;
  * `ErdosSplit.compSplit_cliquePartitionNumber_lower`: hence `cp ≥ q·p − C(p,2)`;
  * `ErdosSplit.compSplit_sharp_lower`: for `q = 2p` (so `n = 3p`), `n² ≤ 6·cp(G)`, i.e.
    `cp(G) ≥ n²/6`.  This exhibits a split graph witnessing that the constant `1/6` is
    asymptotically sharp.
## What is *not* formalized
The **upper bound** half of Theorem 1 (`cp(G) ≤ (1/6 + o(1)) n²` for all split graphs `G`) is
not formalized.  Its proof (Sections 2–6) reduces the problem, via a fractional triangle
packing, to the Envelope Lemma, but this reduction crucially invokes the Haxell–Rödl / Yuster
theorem on the asymptotic equivalence of fractional and integral packings of a fixed graph
family.  That theorem is not available in Mathlib, and it is not reproved here; consequently the
`o(n²)` reduction and the final upper bound are left unformalized.  The analytic heart of that
argument (the Envelope Lemma) *is* proved, as is the matching lower bound (sharpness).
-/
