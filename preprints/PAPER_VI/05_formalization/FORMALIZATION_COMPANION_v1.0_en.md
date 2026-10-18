# Paper VI — Formalization and reproducibility companion

**Juan Pablo Traverso Gianini**  
**Preprint 1.0**  
**Date:** 18 October 2026  
**Copyright:** © 2026 Juan Pablo Traverso Gianini. This document is licensed under CC BY-NC 4.0.

## 1. Source package and entry point

The [public source package](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/main/preprints/PAPER_VI/05_formalization) contains the formal statements and proofs for Paper VI. Its default target, `PaperVIRelease`, publicly imports `PaperVI`, the compatibility alias `PaperVIExtended`, and `PaperVIRecourse`. The complete local import closure contains 79 modules. It includes Theorems A–E, the general-size window, intrinsic and exceptional results, the appendices, and the complete-join all-K5 prefix, recourse and restricted-connectivity results of Section 10.

The toolchain is `leanprover/lean4:v4.35.0`; Mathlib is pinned to `56a005855ea17e0b0958f73ec801ae140b0a1679`. The author's Lean sources are licensed under Apache-2.0. Copyright and SPDX headers preserve existing author credits and third-party notices. The theorem types and proof bodies are unchanged by these licensing headers.

`PaperVIRelease.lean` SHA256: `05de8cc26e4077d04e74d9a15c1373e40f8c66ed32590df90c617509bf44acee`.

`SOURCE_CLOSURE.json` SHA256: `1c121b7b8bf561acde97166ee7fe7c16b68d7dba771d601a0705633b396227a3`.

`PAPER_VI_Preprint1.0_LEAN435_FORMAL_SOURCE_FREEZE.zip` SHA256: `c5c32a9d9315350d8e2683f0c58389824116bd1844f58f7b09ad78d7fe3b61bb`.

## 2. Theorem correspondence


The printed theorem letters follow the manuscript's reading order. The Lean
identifiers below are the stable names in the supplied source archive.

| Manuscript result | Lean declaration |
|---|---|
| A: exact local formula | `PaperVI.theoremA` |
| B: restriction to triangles | `PaperVI.theoremC` |
| C: exterior prescriptions | `PaperVI.theoremB` |
| Proposition 2.1: general-size window | `PaperVI.cp_window_K4_simple`, with the order-four construction in `PaperVI.cp_window_K4` |
| Second complete-split baseline | `PaperVI.Research.second_split_baseline` |
| Perturbations of the second core | `PaperVI.Research.second_core_formula` |
| Intrinsic maximum | `PaperVI.Research.cp_eq_max_PhiQ` |
| Degree recognition | `PaperVI.Research.core_eq_highDegree` |
| D: exceptional partition optimum | `PaperVI.Research.ExSetup.theoremE1` |
| D: fractional equality optimum | `PaperVI.Research.ExSetup.theoremE1_frac` |
| D: triangle optimum | `PaperVI.Research.ExSetup.theoremE2` |
| D: restriction gap | `PaperVI.Research.ExSetup.theoremE3` |
| Maximum over all cores in the exceptional family | `PaperVI.Research.ExSetup.theoremE4` |
| Concrete linear-gap examples | `PaperVI.Research.exModel_linear_gap` |
| Retaining a partial physical lifting | `PaperVI.Research.theoremB_extending` |
| Exterior recourse | `PaperVI.Research.theoremB_recourse` |
| E: count for one prescription | `PaperVI.Research.prescribed_count` |
| E: total lower and upper bounds | `PaperVI.Research.theoremN` |
| Lemma 10.1: exact compensation | `PaperVIRecourse.used_add_resid_eq` |
| Lemma 10.1: arbitrary legal prefix | `PaperVIRecourse.exists_optimal_partition_extending_prefix` |
| Physical compatible-triangle prefix | `PaperVIRecourse.exists_optimal_partition_of_compatible_triangles` |
| Proposition 10.2: full 34k/68k recourse | `PaperVIRecourse.exists_full_allK5_recourse` |
| Optimal terminal counts | `PaperVIRecourse.optimal_allK5_counts` |
| Protected lifting repair | `PaperVIRecourse.protected_allK5_step` |
| First connectivity phase | `PaperVIRecourse.lift_alignment` |
| Second phase: steps of distance 18 | `PaperVIRecourse.terminal_alignment_missing_bound`, `PaperVIRecourse.terminal_alignment` |
| Theorem 10.3: restricted connectivity | `PaperVIRecourse.restricted_allK5_connectivity` |
| Balanced reference identity and unperturbed split optimum | `PaperVI.Mval_eq`, `PaperVI.cp_refGraph_eq_Mval` |
| Universal bipartition certificate and lower bound | `PaperVI.slack_identity`, `PaperVI.slack_nonneg`, `PaperVI.cp_ge` |
| Triangle packing: integral and real fractional optima | `PaperVI.triangle_packing_eq` |
| Lemma 6.1: rigidity of the chordal core | `PaperVI.core_complete_of_chordal` |
| Chordal formula and two-sided edit stability | `PaperVI.cp_chordal`, `PaperVI.chordal_stability` |
| Real fractional partition optimum | `PaperVI.fractional_eq_cp`, `PaperVI.frac_slack_identity` |
| Integral and fractional gain optima | `PaperVI.gain_eq` |
| Types in every integral and fractional optimum | `PaperVI.optimal_types`, `PaperVI.frac_optimal_support` |
| Exceptional partial-star obstruction | `PaperVI.Research.ExSetup.partial_star_obstruction` |
| Appendix A: elementary complete-join formula at p≥24Δ(H) | `PaperVI.theoremA1` |
| Appendix B: localization of inefficient blocks on at most 21t edges | `PaperVI.inefficient_edges_le`, using `PaperVI.choose_two_le_21_slack` |
| Distinct optimal prescriptions | `PaperVI.two_pow_m_optimal` |

The companion map covers 39 manuscript result groups. `COMPLETE_THEOREM_MAP.json` identifies their source modules and declaration locations; `SOURCE_IMPORT_DECLARATION_MAP.json` covers every module in the imported closure. The local window in A and B is p≥18h+1 (p≥18h in the balanced case); C uses p≥63h. Proposition 2.1 has its separately stated general-size inequalities.

All partition conclusions concern actual clique partitions of G. The
exceptional setup specifies a clique P, an independent R, complete adjacency between
them, and one additional vertex z with the specified neighborhood. It is not merely
an integer model with an assumed partition number.


## 3. Exact scope of the encoded conclusions


Theorem D and the partial-star example in Section 8.3 require `|R| ≥ |P|+2`, equivalently `q ≥ p+3`; its unrestricted-size setup permits p=0 and empty
neighbor sets. The maximum-over-cores comparison requires `q=2p` and `p≥19`.
The concrete linear-gap family takes `p=3t`, `t≥7`.

Recognition by degrees under A assumes n≥3. It identifies the reference satisfying
the local theorem, but does not assert that the intrinsic maximum has a unique
maximizer. No uniqueness theorem for the intrinsic maximizer is asserted.

Proposition 9.1 is conditional on the actual lifting invariant: legal edges,
disjoint used core pairs, disjoint core sets for incident exterior edges, prescribed
cardinalities and bounded load. In its general mixed setting the terminal completion
may change globally. Thirteen counts exterior assignments, not whole-partition blocks.

Section 10 assumes a complete join and all exterior blocks of order five.
Proposition 10.2 assumes two already legal complete liftings and q≥2p−1; it has no
small-load hypothesis or upper bound on q. Lean carries arbitrary finite load
bounds for these liftings, without requiring a uniform bound in terms of h.
Its retained-family conclusion is physical: old terminal triangles avoiding the new
lifting are retained. The 34k/68k bounds apply to the full families of vertex-set
blocks, not merely an abstract coloring distance.

Theorem 10.3 additionally requires 2p−1≤q≤2p+1, p≥63h, and load≤7h in both
endpoint states and throughout the path. In a complete join h=editDegree=Δ(H).
`BlockPath` records actual partitions at every state and block symmetric difference
at every step. The induction first protects target-aligned exterior assignments,
then protects shared target terminal triangles. This is restricted connectivity;
mixed K4/K5 optima and unbounded-load all-K5 optima remain outside its conclusion.
The stronger terminal-phase endpoint bounds the number of steps by the number of
target terminal triangles missing from the initial state. No sharpness or running-time
claim is made for these recourse and path constants.

Theorem E counts labeled families of vertex sets, not ordered lists or isomorphism
classes. The formal statement gives the explicit finite bounds, including the floor
in the lower exponent. The elementary logarithmic asymptotic is deduced in the
manuscript; it is not a separate formal premise.

Fractional partitions have equality on every edge and real nonnegative weights.
This is not fractional covering with inequalities and not integrality of the entire
polytope for arbitrary objectives. The triangle-packing fractional optimum is likewise
over the canonical real model.


## 4. Proved dependencies, build and axiom audit

Häggkvist–Janssen and ordinary Vizing are proved dependencies in the supplied import closure, not assumed mathematical axioms. The former supplies the residual list-edge-coloring completion. The latter supplies the counting step. The author's registered formalizations are Häggkvist–Janssen, Palomar `PALOMAR-2026-10-15-000003`, version 1, repository `jtraverso/haggkvist-janssen`, commit `807e08bd7c480d4fae80c1b78377d23989d39ab0`; and Vizing, Palomar `PALOMAR-2026-10-15-000004`, version 1, repository `jtraverso/vizing`, commit `01c72ed7efde2353a4bb1654f69b5c0bc5038863`. Registration is provenance; the final local build and transitive axiom audit establish the status of the dependencies actually imported here. No equitable list-completion theorem is inferred from ordinary Vizing.

The aggregate build for Preprint 1.0 and the separate exported-type check both exit zero. The check covers 32 exported types and their axiom footprints. The all-declaration audit checks 1836 local declarations in 79 modules and visits 3421 declarations transitively, with zero nonstandard axioms. Its axiom union is exactly `propext`, `Classical.choice` and `Quot.sound`. Every listed module must be present in the imported environment; a missing module causes the audit to fail. A separate map matches source files, actual imports and declaration counts. An active-source scan, masking comments and strings, finds no `sorry`, `admit`, project `axiom`, `native_decide`, `implemented_by` or `extern` escape.

The build used the pinned Mathlib cache and compatible local build outputs. Lake rebuilt the sources with new licensing headers and their affected imports. The final checks ran against that aggregate. It was not a cache-free reconstruction. Deprecation and inherited linter warnings remain in the logs; no warning-free claim is made. Authoritative logs are `BUILD_PUBLIC_1_0.portable.log`, `ENDPOINTS_PUBLIC_1_0.portable.log` and `FULL_AUDIT_PUBLIC_1_0.portable.log`, each with its recorded zero exit. The source manifest and freeze receipt bind these records to the final sources.

## 5. Reproducing the formal checks

Extract `formal_sources/PAPER_VI_Preprint1.0_LEAN435_FORMAL_SOURCE_FREEZE.zip` into a fresh directory, install its pinned Lean toolchain, and run the following from that project root. The archive contains all local sources and configuration, but no `.lake` cache or machine-specific junction.

```
lake exe cache get
lake build PaperVIRelease
lake env lean -j1 -s32768 EndpointGate.lean
lake env lean -j1 -s32768 FreezeFullAudit.lean
```

Keep the supplied `lake-manifest.json` unchanged. The cache command obtains compatible files for those pinned dependencies; do not delete or update the manifest to select dependency versions. A build of a single intermediate module is not a substitute for the canonical aggregate and its two final checks.

## 6. Finite certificates and adversarial regression checks

The finite-certificate package in `03_reproducibility/` contains 33 literal-graph certificates: 18 local A–C cases and 15 exceptional cases. Local cases include the balanced boundary p = 18h, the general boundary p = 18h + 1, all three allowed exterior sizes, simultaneous core and crossing deletions with exterior additions, concentrated degree-two stars, an exterior cycle, and mixed K4/K5 prescriptions at p = 63h. The exceptional cases use p = 2, q = 5, all a = 0,1,2 and b = 0,1,2,3,4; they include empty neighbor sets and the a = 2, b = 1 K4 branch.

The generator uses a finite greedy completion heuristic, not an implementation of the universal Häggkvist–Janssen proof. An independent checker imports no generator code. It reconstructs every clique and edge multiplicity, checks types, prescriptions and exact counts, and checks signed dual bounds for the exceptional fractional partition objective. It also checks actual triangle partitions against nonnegative triangle-cover duals. These finite primal–dual equalities certify the examples; the universal results have their separate written and Lean proofs.

Certo generates and replays six exact-cover certificates against their exact specifications: a three-edit-class A case, a concentrated-star triangle case, two boundary prescription cases, and two exceptional cases. Certo's exact-cover result verifies the supplied partition; global optimality in those finite cases is justified separately by the checked integer dual. Three independent corruptions are rejected: missing coverage, repeated coverage and an incorrect prescription. A fourth Certo control changes the specification identity and is refused by provenance checking. That refusal is not reported as a solver rejection or a mathematical counterexample.

A separate two-exterior-edge complete-join example has three actual optimal states. One K5 lifting is protected while the other changes. The checker confirms 1938 retained compatible terminal triangles, 24 lost old blocks, symmetric difference 48, and a final terminal recoloring of distance 6. All states lie in the stated bounded-load all-K5 class; the two-step path fits the finite bound 1949 and the uniform step bound 884. Understated distance and load bounds are rejected as negative controls. Three additional Certo certificates validate exact edge coverage in each supplied state. Path distances, preservation and bounded-load membership are checked independently. This is a finite path example, not an exhaustive connectivity computation.

Run the following from `03_reproducibility/`. The independent Python checkers use only the standard library. The Certo replay additionally requires the recorded Certo installation. The supplied certificates retain their specification identity; regeneration creates certificates for the local specification paths.

```
python generate_v06.py
python verify_v06.py
python recourse_v06.py
python verify_recourse_v06.py
python run_certo_v06.py
python run_certo_recourse_v06.py
```

No finite census is a proof premise of a universal theorem. The supplied scripts and independently checked certificates support only their stated finite instances.

## 7. Mathematical and bibliographic scope

The source package proves the encoded statements with their explicit hypotheses. It does not establish a historical-priority claim or replace independent mathematical review. The directed comparison includes full-text checks of EFO, CEO, the EOZ author galley, Ma's threshold bounds, McGuinness–Rees's line-graph enumeration and Wallis–Zhang's independent-join characterization. Wallis–Zhang's Proposition 3.2 and Corollary 3.3 include the boundary of Theorem D in which the exceptional vertex is adjacent to every ordinary exterior vertex.

The relevant Pullman–Donald result is credited through the inspected EFO article (p. 94) and Wallis–Zhang (Corollary 3.3); its original article was not available for direct inspection. Wallis–Wu91 is compared through its primary abstract and the authors' announcement. These limitations preclude an exhaustive historical-priority assertion. Okechukwu's Lemma 4.2 supplies a triangle-partition upper bound under its own coloring, capacity and defect hypotheses; overlap with Theorem B is asserted only in the subcases satisfying those hypotheses, not across the full local-edit window.

Paper IV proves the sharp bound for sufficiently large chordal graphs, together with an all-orders bound with an absolute additive constant. Paper VI studies exact formulas and additional structure under its own hypotheses. The separate IV–VI application note has its own entry point and validation; this source package does not certify that note's source closure. Arbitrary mixed K4/K5 connectivity and unbounded-load connectivity are outside Section 10.
