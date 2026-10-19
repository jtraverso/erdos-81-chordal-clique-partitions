# Paper I: formalization and reproducibility

**Juan Pablo Traverso Gianini**

Companion to editorial edition 1.4 · 19 October 2026

This document accompanies the mathematical article. It preserves the formal declarations, scope qualifications and computational evidence previously included in the article. The source freeze and its recorded verification are unchanged. No Lean/Lake build was run for this edition. Historical section and table numbers in the records below refer to the preceding article; they are retained as locators, not renumbered as new verification results. Original references [1], [2], etc. are listed at the end.

[Frozen sources and historical evidence / Fuentes congeladas y evidencias históricas](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/eb335845bfa23375d5040ea31fc4f4b366346287/preprints/PAPER_I/05_formalization) · [Previous article / Artículo anterior](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/eb335845bfa23375d5040ea31fc4f4b366346287/preprints/PAPER_I/01_manuscript)

### Theorem 1.1

**Formalization status.** The Paper I Lean v1.2 freeze uses Lean 4 / Mathlib v4.28.0 [6,7] and records Theorem 1.1 as `paperI_main_sharp`. The declaration `paperI_main` supplies a weaker companion form with additive term \(n\). In these recorded names, `sharp` refers to the quadratic coefficient \(1/6\), not to optimality of the additive term. The axiom gate covers the main theorem, `PaperI.assembly_sharp`, `PaperI.Split.residual_duality`, the finite packing–covering duality of Proposition B.1, and the interface declarations listed in Section 10. Their recorded footprint is `propext`, `Classical.choice`, and `Quot.sound`, with no project-level mathematical axiom. Section 10 gives the freeze and archive record.

## 10. Reproducibility and proof record

The proof is analytic. Computational experiments were used during development to search for counterexamples and detect transcription errors, but no computation is a logical premise of the theorem. For that reason, computational regression material is kept outside the paper rather than included as a second appendix.

The accompanying calculation ledger records:

- every exact identity;
- every inequality direction;
- the complete loss accounting;
- the branch \(q=0\);
- the orbit regimes;
- the final conversion to \(n\).

The author reports an internal AI-assisted adversarial audit of the theorem statement, quantitative bound, and proof assembly. This is a validation record, not a claim of external peer review.

### Formalization status in Lean

The snapshot at `PAPER_I/05_formalization/lean_v1.2_freeze` contains the Lean sources and a successful recorded 8,034-job build against Lean 4 / Mathlib v4.28.0 [6,7]. It contains `paperI_main_sharp`, whose statement is `Phi ≤ n^2/6 + n/2`, together with the weaker companion declaration `paperI_main` and the interface results listed below. Its axiom gate also queries `PaperI.assembly_sharp` and `PaperI.Split.residual_duality`. Appendix C records the main declaration. The exact archive was subsequently reproduced in an external clean room with the same 8,034-job result and the same theorem-level axiom footprint.

The frozen axiom report records only Lean's standard foundational axioms, `propext`, `Classical.choice`, and `Quot.sound`, for the main theorem and the listed declarations; it records no project-level mathematical axiom. These are logical foundations used throughout Mathlib, not additional mathematical assumptions of the paper.

The release artifact also records the finite-dimensional packing-covering duality used in Proposition B.1. In Lean it appears as `residual_duality`, an application of the general theorem `covering_packing_duality`. The artifact records that theorem as derived from a finite Farkas lemma and Mathlib's closed-cone infrastructure, rather than postulated as an external axiom. Schrijver [4, Chapter 7] remains the classical reference for the written proof.

The frozen source archive is `PAPER_I_lean_v1.2_freeze.zip`, with SHA-256 `0181506408644fc1f8872d711de5a98a500f4052aa295bcd6f8c82776694fd3a`. It is stored under `PAPER_I/05_formalization/lean_v1.2_freeze` and excludes project caches and compiled objects. The freeze build target includes several `Contrib` modules used for possible upstreaming; that contribution lane is a byproduct and is not part of the paper's trusted mathematical assumptions. The axiom report above controls the logical dependency statement. The external clean-room reproduction applies to these exact archive bytes; the manuscript revision does not alter the formal artifact.

---

## Appendix C. Formalized statement

The accompanying formal artifact records the following Lean 4 declaration for Theorem 1.1:

```lean
theorem paperI_main_sharp (G : Split) :
    G.Phi ≤ (G.n : ℝ) ^ 2 / 6 + (G.n : ℝ) / 2

-- weaker companion form (larger additive term):
theorem paperI_main (G : Split) :
    G.Phi ≤ (G.n : ℝ) ^ 2 / 6 + (G.n : ℝ)
```

Here `Split` packages the data of a split graph used in the proof: a clique of size `p`, an independent vertex type, and the neighborhoods of the independent vertices inside the clique. The field `n` is the total number of vertices. The quantity `Phi` is defined as `|E| − 2·nu3star`, where `nu3star` is the supremum of the feasible fractional triangle-packing values. Elsewhere in the series this fractional deficit is written \(\Phi^*\), while the unstarred \(\Phi\) is reserved for the integral deficit \(|E(G)|-2\nu_3(G)\); the Lean identifier is retained to match the recorded declaration. With these definitions, `paperI_main_sharp` is precisely

\[
|E(G)|-2\nu_3^*(G)\le \frac{n^2}{6}+\frac{n}{2},
\]

the inequality stated in Theorem 1.1 (declaration `paperI_main_sharp`). The companion declaration `paperI_main` records the weaker additive term \(n\).

The supplied build report records zero `sorry`. The supplied axiom report is:

```text
PaperI.Split.paperI_main_sharp depends on axioms: [propext, Classical.choice, Quot.sound]
PaperI.paperI_main         depends on axioms: [propext, Classical.choice, Quot.sound]
PaperI.assembly_sharp      depends on axioms: [propext, Classical.choice, Quot.sound]
PaperI.Split.residual_duality depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the three standard foundational axioms of Lean and Mathlib. No project-specific axiom is used.

**Table 2. Frozen formalization perimeter (Lean v1.2 freeze).** The frozen Lean 4 / Mathlib v4.28.0 snapshot records the proved core with only Lean's standard foundational axioms and no project-level mathematical axiom. An external clean-room build and theorem-level axiom check reproduced the exact archive.

| Node | Statement | Axiom footprint |
|---|---|---|
| `paperI_main_sharp` (Theorem 1.1) | \(\lvert E(G)\rvert-2\nu_3^*(G)\le n^2/6+n/2\) | `propext`, `Classical.choice`, `Quot.sound` |
| `paperI_main` (weaker companion bound) | \(\lvert E(G)\rvert-2\nu_3^*(G)\le n^2/6+n\) | `propext`, `Classical.choice`, `Quot.sound` |
| `lpVal_concave`, `lpVal_ge_min` (§5 interface) | abstract concavity / pure-profile lower bound | `propext`, `Classical.choice`, `Quot.sound` |
| `lpVal_lipschitz` (§5 interface) | parametric stability of the fractional value | `propext`, `Classical.choice`, `Quot.sound` |
| `residual_duality` (Prop. B.1) | finite packing–covering duality | `propext`, `Classical.choice`, `Quot.sound` |

### Proposition B.1

**Formalization note.** The v1.2 freeze records Proposition B.1 as the Lean declaration `PaperI.Split.residual_duality`, an instance of the general finite strong-duality theorem `covering_packing_duality`. The artifact records the latter as proved from a finite Farkas lemma, using the closedness of a finitely generated convex cone and the hyperplane-separation theorem for closed convex cones. Thus the duality used here is derived inside the formal development, not postulated as a project-specific axiom. Schrijver remains the classical reference for the written argument. The corresponding sources, build log, and axiom report are delivered in `PAPER_I/05_formalization/lean_v1.2_freeze`.

### 1. Introduction

**Series notation.** In cross-paper discussion, the fractional deficit of Paper I is written \(\Phi^*(G)=|E(G)|-2\nu_3^*(G)\). Paper II writes the same quantity as \(\Phi_\tau(G)=|E(G)|-2\tau_3^*(G)\), while Paper III reserves the unstarred \(\Phi(G)\) for the integral deficit \(|E(G)|-2\nu_3(G)\). The Lean identifier `Phi` in the Paper I artifact is retained for traceability.

### Remark (fixed-polytope concavity)

The reduction just used is an instance of a purely convex-analytic fact, stated here in abstract form. Fix a feasible polytope that does not depend on the profile and an objective that depends affinely on the profile mass \(\mu=(\mu_S)\). Because the optimal value of a linear program over a fixed polytope is concave in its objective vector, the value at a mixed profile dominates the corresponding convex combination of pure-profile values, and hence their minimum:
\[
M_b(\kappa_\mu)\ \ge\ \sum_S \tfrac{\mu_S}{q}\,M_b(\kappa^{S,q})\ \ge\ \min_S M_b(\kappa^{S,q}).
\]
This is recorded in the formal development as `lpVal_concave` and `lpVal_ge_min`. A companion estimate, `lpVal_lipschitz`, bounds the change in the fractional value when the baseline or the profile distribution is perturbed. It is intended for robust and near-split variants. Both are stated for a fixed feasible polytope with an affinely varying objective; neither requires symmetry, which enters only afterwards, on a single pure profile, in Section 6.


## References

[1] P. Erdős, E. T. Ordman, and Y. Zalcstein, “Clique partitions of chordal graphs,” *Combinatorics, Probability and Computing* **2** (1993), no. 4, 409–415.

[2] G.-T. Chen, P. Erdős, and E. T. Ordman, “Clique partitions of split graphs,” in *Combinatorics, Graph Theory, Algorithms and Applications* (Beijing, 1993), World Scientific, 1994, pp. 21–30, author-hosted scan: https://ordman.net/MathResearch/CEOClique_Parts.pdf, accessed August 21, 2026.

[3] T. F. Bloom, “Erdős Problem #81,” *Erdős Problems*, https://www.erdosproblems.com/81, accessed August 21, 2026.

[4] A. Schrijver, *Theory of Linear and Integer Programming*, Wiley-Interscience Series in Discrete Mathematics and Optimization, John Wiley & Sons, Chichester, 1986.

[5] M. S. Cavers, *Clique Partitions and Coverings of Graphs*, M.Math. essay, University of Waterloo, 2005.

[6] L. de Moura and S. Ullrich, “The Lean 4 Theorem Prover and Programming Language,” in *Automated Deduction – CADE 28*, Lecture Notes in Computer Science **12699**, Springer, 2021, pp. 625–635, https://doi.org/10.1007/978-3-030-79876-5_37.

[7] The mathlib Community, “The Lean Mathematical Library,” in *Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP 2020)*, ACM, 2020, pp. 367–381, https://doi.org/10.1145/3372885.3373824.
