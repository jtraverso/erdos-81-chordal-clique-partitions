# Paper III: formalization and reproducibility

**Juan Pablo Traverso Gianini**

Companion to editorial edition 1.6 · 19 October 2026

This document accompanies the mathematical article. It preserves the formal declarations, scope qualifications and computational evidence previously included in the article. The source freeze and its recorded verification are unchanged. No Lean/Lake build was run for this edition. Historical section and table numbers in the records below refer to the preceding article; they are retained as locators, not renumbered as new verification results. Original references [1], [2], etc. are listed at the end.

[Frozen sources and historical evidence / Fuentes congeladas y evidencias históricas](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/eb335845bfa23375d5040ea31fc4f4b366346287/preprints/PAPER_III/05_formalization) · [Previous article / Artículo anterior](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/eb335845bfa23375d5040ea31fc4f4b366346287/preprints/PAPER_III/01_manuscript)

## 11.6 Formal-verification perimeter and current status

The formalization discussion is confined to this section and the release record in Section 13. The current formal snapshot separates the unconditional final assembly from its downstream interfaces. The public aggregate root `PaperIII` imports both `PaperIII.Theorem_1_1_Final` and `PaperIII.PublicAPI`. The final module discharges the two interfaces used by the paper and exports Theorem 1.1 and Corollary 1.2. `PaperIII.CanonicalTrianglePacking` makes `PaperIII.nu3` and `PaperIII.nu3Star` the manuscript-facing quantities and proves their equality with the edge-hypergraph implementations used by AX1; it also proves `PaperIII.tau3Star = PaperIII.nu3Star` and identifies the cover-side AX1 interface with the packing-side statement in Section 2. `PaperIII.PaperImprovements` contains the paper-facing certificates; `PaperIII.PublicAPI`, `PaperIII.OfPartition`, and `PaperIII.Obstructions` expose downstream interfaces. The directed canonical gate reports the following axiom footprint for these theorem surfaces:

```text
[propext, Classical.choice, Quot.sound]
```

The final assembly uses explicit bridges to the Haxell--Rödl/Yuster and dense-decomposition formalizations. The cited asymptotic theorems remain in the manuscript for mathematical provenance. The recorded author-side public-root build completed 8,455 jobs with exit code 0; the subsequent query-root build completed 8,444 jobs with exit code 0. That author-side process was resumed after an application restart. Separately, the external audit performed an uninterrupted reproduction from an absent project build directory: the public root completed 8,455 jobs, the query roots completed 8,444 jobs, and all eight axiom-query files exited successfully. The immutable formal archive is sealed, and the internal and external Lean gates pass within the scope stated in Section 13.

Appendix E gives a curated selection of paper-level and reusable certificates. The complete implementation-level inventory remains in the formal source rather than being duplicated in the manuscript.

**Table 2. Formalization surfaces.** Statuses in this table are records of the sealed local freeze; they are not a substitute for independent reproduction.

| Surface | Purpose | Current local status |
|---|---|---|
| `PaperIII` | aggregate/compatibility root | public-root build completed 8,455 jobs; exit 0; imports the final theorem and public API |
| `PaperIII.MainNibble` | theorem and corollary assembly through explicit AX1/AX2 interfaces | compiled in the recorded closure |
| `PaperIII.Theorem_1_1_Final` | unconditional discharge of AX1/AX2 and final theorem surfaces | compiled; final theorem footprint is foundational-only |
| `PaperIII.CanonicalTrianglePacking` | canonical `nu3`, `nu3Star`, `tau3Star` and AX1 statement bridges | compiled; exact target-side bridges recorded |
| `PaperIII.CanonicalTrianglePackingGate` | statement and axiom gate for the canonical interfaces | exit 0; foundational-only footprints recorded |
| `PaperIII.PaperImprovements` and `PaperIII.PaperImprovementsGate` | paper-facing corollaries and selected auxiliary certificates | compiled in the consolidated gate run |
| `PaperIII.PublicAPI`, `PaperIII.OfPartition`, `PaperIII.Obstructions` | downstream API, split-partition transport, and obstruction certificates | compiled in the recorded closure |
| `FREEZE_REPORT.md` and `ESCAPE_HATCH_ASSESSMENT.md` | immutable build, axiom and raw-token assessment | generated and included in the sealed formal archive |

At the `SimpleGraph` level, `Theorem_1_1_of_splitPartition_uncond` accepts a finite graph equipped with a clique/independent partition. The construction `SplitGraph.ofPartition` is connected to the original graph by `ofPartitionIso`; the vertex count, edge count, \(\nu_3\), and \(\Phi\) are transported through graph-isomorphism invariance, including `nu3_congr_of_iso`. Other type-specialized theorem forms remain in `PaperIII.PublicAPI` for downstream use but are not mathematical results of the paper and are not catalogued here.

The directed canonical-module compilation, public- and query-root builds, eight compatible axiom-query files, escape-hatch assessment, immutable source manifests, and internal audit pass their author-side checks. The external audit independently reproduced the public and query roots and verified the designated axiom surfaces against the same frozen bytes.

No computation or regression script is a premise of the proof. The exact-arithmetic and integer-programming checks remain supplementary audits. The completed adversarial review and corpus-bounded prior-art assessment are not substitutes for human peer review or a specialist determination of priority; public tagging is a repository-level release operation.

## 11.7 Reusable formalization components

The formalization also produced a standalone `Contrib.*` library whose modules import only Mathlib. Four groups are especially relevant beyond this paper:

- finite packing/covering LP strong duality via a conic-Farkas argument (`Contrib.LPStrongDuality`);
- variance-sensitive concentration and martingale tails (`Contrib.BennettBernstein`, `Contrib.HoeffdingUpper`, `Contrib.ConditionalHoeffding`, and `Contrib.FreedmanBernstein`);
- Dirac-type Hamiltonicity and matching results (`Contrib.DiracHamiltonian` and `Contrib.SpreadMatchingDirac`);
- finite max-flow/min-cut and selected design-theoretic components (`Contrib.MaxFlowMinCut` and `Contrib.FanoSTS`).

These modules are reusable formalization byproducts, not premises of Theorem 1.1. They are held for separate review and possible upstream submission. The present manuscript makes no claim that their APIs or individual statements are novel relative to the current Mathlib library; that comparison requires a separate upstream-oriented literature and API review. Appendix E.6 records only the components closest to the mathematical proof.

---

## 13. Reproducibility

The mathematical source is this manuscript. The manuscript-facing formal surfaces are `PaperIII.Theorem_1_1_Final`, `PaperIII.CanonicalTrianglePacking`, `PaperIII.PublicAPI`, `PaperIII.OfPartition`, and `PaperIII.Obstructions`. `PaperIII.PaperImprovementsGate` is the byproduct gate, and `PaperIII.CanonicalTrianglePackingGate` checks the exact correspondence between the canonical packing parameters and the Nibble/Yuster model used to discharge AX1.

The formal development is sealed as `PAPER_III_lean_v1.4_freeze.zip`, with SHA-256 `79ee24c38fd776bc2585a0c3c996e30817f0829fc5064463bdbde0fa2d3d7104`. It contains 704 Lean source files and the three pinned Lake/toolchain files listed in the 707-entry source manifest. The recorded verification uses Lean 4.28.0 and Mathlib v4.28.0 at commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

The available local verification record is summarized below.

**Table 3. Sealed local verification record.**

| Check | Log or command | Current result |
|---|---|---|
| public aggregate-root build | `gate_logs/run_2026-08-22_CCS_NOTEBOOK456_resumed/logs/02_build_public_root_clean.log` | exit 0; 8,455 jobs completed; clean-origin process resumed after an application restart |
| query-root completion | `gate_logs/run_2026-08-22_CCS_NOTEBOOK456_resumed/logs/03_build_query_roots_incremental.log` | exit 0; 8,444 jobs completed |
| canonical statement-and-axiom gate | `PaperIII.CanonicalTrianglePackingGate` | exit 0; target-side integral and fractional bridges checked |
| complete theorem-level axiom record | eight `FreezeAxioms*.lean` files | exit 0; only `propext`, `Classical.choice`, and `Quot.sound` |
| quantitative Lean-closure regression | `FreezeAxiomsAuditClosure.lean` and `FreezeAxiomsAX1Closure.lean` | all named closure surfaces present with foundational-only footprints |
| escape-hatch assessment | raw-token and focused build/footprint checks | no active `sorry` warning, no active `native_decide`, and no project axiom in a canonical surface |
| immutable seal | source/package manifests, ZIP and SHA-256 sidecar | 707 source entries; archive hash verified |

The recorded verification used one unchanged source snapshot. Its build sequence was

```text
lake build PaperIII
lake build BKLO.MainDenseUnconditional Nibble.AX1Closed PaperIII.CanonicalTrianglePacking PaperIII.Obstructions PaperIII.PaperImprovementsGate PaperIII.PublicAPI PaperIII.Theorem_1_1_Final
#print axioms PaperIII.Theorem_1_1
#print axioms PaperIII.AX1_holds
#print axioms PaperIII.AX2_holds
```

The author-side project began with no `.lake` directory or compiled project object. The desktop application restarted during the first public-root process; the unchanged project was then resumed incrementally and completed successfully. The immutable freeze therefore records `PASS_CLEAN_ORIGIN_RESUMED`, not a single uninterrupted author invocation. It preserves that disclosure, verbatim output, component identifiers, source manifest, archive manifest, and SHA-256 inventories. The external audit subsequently supplied an uninterrupted reproduction from an absent project build directory, using the pinned dependency revisions: 8,455 public-root jobs and 8,444 query-root jobs completed with exit code 0, and all eight axiom-query files passed. Those declaration-level checks establish build conformance and axiom footprints; they do not replace independent mathematical rederivation.

Two archived legacy modules, `Ax2/PartB/Axioms.lean` and `Ax2/PartA/Wlog.lean`, contain project-local axiom declarations. No source file imports either module, and neither declaration occurs in the dependency footprint of a canonical release surface. Accordingly, the precise formal claim is declaration-level: the canonical theorem and release interfaces have no project-local mathematical axiom; the complete historical source tree is not claimed to contain no `axiom` token.

The proof itself remains in the manuscript. Regression scripts and computational audits are not hypotheses, reductions, or proof steps.

The canonical repository package contains the complete Lean source, toolchain, manifest, build and axiom logs, manuscript sources, and SHA-256 inventories. The public tag and commit bind those files at repository level; no commit identifier is asserted inside the manuscript itself.

Written materials are intended for distribution under CC BY-NC 4.0. Author-owned verification and regression code is intended for distribution under the PolyForm Noncommercial License 1.0.0; third-party dependencies retain their own licenses.

**Review boundary:** the independent reproduction and external adversarial audit are complete, and the novelty review is corpus-bounded. Human peer review and specialist priority determination have not been performed. The public tag and commit are repository metadata rather than premises of the theorem.

---

## Appendix C. Computational Audits

## C.1 Exact common-profile LP

`verify_common_profile_lp.py` enumerates the vertices of the symmetrized cover polyhedron using exact rational Gaussian elimination and compares the optimum with (3.5).

## C.2 Exact fractional margin

`verify_fractional_margin.py` checks Theorem 4.2 for

\[
3\le p\le80,
\qquad
1\le q\le2p,
\qquad
0\le d\le p
\]

using exact rational arithmetic.

## C.3 Small ILP audits

`verify_factor_rounding.py` and `verify_shifted_center.py` compute exact integral triangle packings on small instances using a binary edge-capacity ILP. They verify the stated upper bounds on \(\Phi(G)\).

## C.4 Polarization

`verify_polarization.py` performs exhaustive small-profile and randomized exact-integer checks of Lemma 6.1.

## C.5 Divisibility

`verify_divisibility_correction.py` exhaustively verifies the path parity construction through order eighteen, checks the fixed minimum-degree threshold exactly, and follows the full parity and modulo-three correction on randomized dense residuals.

---

### Remark 2.3\(^{\prime}\) — Necessity of a density hypothesis

**Lean certificates.** `PaperIII.ax2_divisibility_degree_insufficient`, `PaperIII.ax2_density_necessary_K7_minus_two_triangles`, re-exported through `PaperIII.Obstructions`.

### Corollary 10.2b — Sharp quadratic term and forced linear coefficient

**Lean certificate.** `PaperIII.Corollary_1_2_sharp`, assembled from `PaperIII.Corollary_1_2`, `PaperIII.Byproduct_leading_constant_forced`, and `PaperIII.Byproduct_completeSplit_cp_sharp`. The declaration `Byproduct_leading_constant_forced` certifies the assertion about the linear coefficient; sharpness of the quadratic coefficient follows from the exact complete-split value as \(p\to\infty\).

### Corollary E.1.1 — Single factor-assignment packing

**Lean certificate.** `Byproduct_factorization_assignment_packing`.

### Corollary E.1.2 — Double-factorization lower bound

**Lean certificate.** `Byproduct_double_factorization_packing`.

### Corollary E.1.3 — Reserved-gain packing bound

**Lean certificate.** `Byproduct_reserved_gain_packing_bound_subset`.

### Corollary E.2.1 — Short-corridor constant \(3/2\)

**Lean certificate.** `Byproduct_short_corridor_constant_three_halves`.

### Corollary E.2.2 — Packing-to-partition bridge

**Lean certificates.** `Byproduct_cp_le_Phi`, `Byproduct_low_corridor_cp_three_halves`, `Byproduct_effective_low_corridor_cp_bound`.

### Corollary E.3.1 — Exact fractional optimum

**Lean certificate.** `Byproduct_commonProfile_tau3Star_eq_F`.

### Corollary E.3.2 — Phase regions

**Lean certificates.** `Byproduct_commonProfile_tau3Star_eq_uniform_region`, `Byproduct_commonProfile_tau3Star_eq_separated_region`, `Byproduct_commonProfile_tau3Star_eq_hot_region`.

### Corollary E.4.1 — Fractional slack lower bound

**Lean certificate.** `Byproduct_unified_fractional_margin`.

### Corollary E.5.1 — Exact value and normal form

**Lean certificates.** `Byproduct_completeSplit_cp_exact_value`, `Byproduct_completeSplit_cp_sharp`.

### Corollary E.5.2 — Forced linear coefficient

**Lean certificates.** `Byproduct_leading_constant_forced`, packaged with the upper bound and exact family as `Corollary_1_2_sharp`.

### E.6.1 Finite packing/covering LP duality

**Lean certificates.** `Byproduct_triangle_LP_duality`; standalone form `Contrib.LPDuality.lp_strong_duality` in `Contrib.LPStrongDuality`.

### E.6.2 Dirac-type matching and dense correction

**Lean certificates.** `Byproduct_dirac_perfect_matching_even`, `Byproduct_dirac_near_perfect_matching`, `Byproduct_dense_divisible_correction_edges`; standalone matching form in `Contrib.SpreadMatchingDirac`.

### E.6.3 Uniform nibble interface

**Lean certificate.** `Byproduct_almostPerfectMatching_uniform`.

### Corollary E.7.1 — Attainment and fractional edge bound

**Lean certificates.** `Byproduct_nu3_achieved`, `Byproduct_nu3star_le_edges_div_three`.

### Corollary E.7.2 — Majority-nibble edge-gap form

**Lean certificate.** `Byproduct_nu3star_sub_nu3_le_edge_gap_most`.

### Appendix E. Selected Formalization-Derived Corollaries

The theorem names follow `PaperIII.PaperImprovements` and the standalone `Contrib.*` package. Their release status is governed by the consolidated build and axiom gate in Section 13.

### Corollary E.5.2 — Forced linear coefficient

The weaker certificate `Byproduct_leading_constant_sharp`, which follows immediately from the exact normal form, is not separately catalogued.

### E.6.3 Uniform nibble interface

The accompanying standalone library also contains concentration, Hamiltonicity, max-flow/min-cut, codegree-counting, hypergeometric-tail, and design-theoretic modules. Section 11.7 records their scope without presenting them as additional corollaries of this paper.

### Corollary 10.2a — Exact complete-split benchmark

The Lean development records the upper bound, lower bound, and equality as `Byproduct_completeSplit_cp_le_exact_value`, `Byproduct_completeSplit_cp_ge_exact_value`, and `Byproduct_completeSplit_cp_exact_value`. Appendix E.5 retains only the exact normal form and the logically distinct forced-linear-coefficient statement.

### Packing-form corollaries

The following corollaries restate results from Sections 5 and 7 directly in packing language. They are formalized as `factorization_assignment_packing`, `double_factorization_packing`, and `reserved_gain_packing_bound_subset`. All three are unconditional: none uses Theorem 2.1 or Theorem 2.3.


## References

[1] P. Allen, J. Böttcher, O. Cooley, and R. Mycroft, “Tight cycles and regular slices in dense hypergraphs,” *Journal of Combinatorial Theory, Series A* **149** (2017), 30–100.

[2] B. Barber, D. Kühn, A. Lo, and D. Osthus, “Edge-decompositions of graphs with high minimum degree,” *Advances in Mathematics* **288** (2016), 337–385.

[3] T. F. Bloom, “Erdős Problem #81,” *Erdős Problems*, https://www.erdosproblems.com/81, accessed July 6, 2026.

[4] O. V. Borodin, A. V. Kostochka, and D. R. Woodall, “List edge and list total colourings of multigraphs,” *Journal of Combinatorial Theory, Series B* **71** (1997), no. 2, 184–204.

[5] G.-T. Chen, P. Erdős, and E. T. Ordman, “Clique partitions of split graphs,” in *Combinatorics, Graph Theory, Algorithms and Applications* (Beijing, 1993), World Scientific, 1994, pp. 21–30.

[6] G. A. Dirac, “Some theorems on abstract graphs,” *Proceedings of the London Mathematical Society* (3) **2** (1952), 69–81.

[7] F. Dross, “Fractional triangle decompositions in graphs with large minimum degree,” *SIAM Journal on Discrete Mathematics* **30** (2016), no. 1, 36–42.

[8] P. Erdős, E. T. Ordman, and Y. Zalcstein, “Clique partitions of chordal graphs,” *Combinatorics, Probability and Computing* **2** (1993), no. 4, 409–415.

[9] D. Gale and L. S. Shapley, “College admissions and the stability of marriage,” *The American Mathematical Monthly* **69** (1962), no. 1, 9–15.

[10] F. Galvin, “The list chromatic index of a bipartite multigraph,” *Journal of Combinatorial Theory, Series B* **63** (1995), no. 1, 153–158.

[11] P. E. Haxell and V. Rödl, “Integer and fractional packings in dense graphs,” *Combinatorica* **21** (2001), 13–38.

[12] P. Keevash, “The existence of designs,” arXiv:1401.3665, revised 2018.

[13] D. König, “Über Graphen und ihre Anwendung auf Determinantentheorie und Mengenlehre,” *Mathematische Annalen* **77** (1916), 453–465.

[14] M. Krivelevich, “On a conjecture of Tuza about packing and covering of triangles,” *Discrete Mathematics* **142** (1995), 281–286.

[15] J. P. Traverso Gianini, “Affine profile reduction for fractional triangle packings in split graphs” (Paper I in the series), preprint, July 2026.

[16] J. P. Traverso Gianini, “Complete-split extremizers for a fractional triangle-cover functional on chordal graphs” (Paper II in the series), preprint, July 2026.

[17] R. Yuster, “Integer and fractional packing of families of graphs,” *Random Structures & Algorithms* **26** (2005), 110–118.
