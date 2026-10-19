# Formal companion to Paper IV

**Juan Pablo Traverso Gianini**

**Preprint:** version 1.24, October 19, 2026.

This document describes the frozen formalization supporting *Clique partitions with rooted simplicial defect: quantitative stability and sharp eventual bounds*. It accompanies the editorial revision of the manuscript; the mathematical statements and the Lean source freeze are unchanged. Section, equation and theorem numbers refer to the main manuscript unless otherwise specified. References [1–23] retain its bibliography.

## 1. Source identity and verification scope

| Item | Frozen value |
|:--|:--|
| Lean and Mathlib | v4.28.0 |
| Source cut | `piv-v12-fb459343d234` |
| Main source modules | 607 |
| Source/configuration/documentation manifest entries | 615 |
| Selected audit targets | 19 |
| Literal exports through `import PaperIV` | 224 |
| Recorded axiom outputs | 461; not a count of distinct theorems |

The source manifest SHA-256 is `fb459343d234f968d7d32eff1491ea8a09aa2e135b313a80623012e7449042f5`. The source-only archive SHA-256 is `cb2741454380736ffe01b59933057b5079fa9f865d5bbdd3f67534bf808a62e6`. These identify the original formal source package, not the new editorial PDFs.

The [frozen package](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/ef31294ad67dfe3f44bc47cec4791c836f55e8aa/preprints/PAPER_IV/05_formalization) and [recorded build evidence](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/ef31294ad67dfe3f44bc47cec4791c836f55e8aa/preprints/PAPER_IV/03_reproducibility) are available in the series repository. The series concept DOI is [10.5281/zenodo.21273143](https://doi.org/10.5281/zenodo.21273143). The preceding manuscript edition and its deposit remain available; the source freeze is the same.

The identified Lean supplement for this version uses Lean and Mathlib v4.28.0. The final declarations do not take rounding, existence of an optimum or the near constructor as arguments: they invoke them as proved theorems in their dependencies. The permitted foundational axioms are distinguished from any additional mathematical hypothesis.

The recorded reconstruction covers all 607 modules: 421 objects built in the first segment were verified and reused after a restart, and the resumed segment compiled 186 modules. All 19 selected targets were freshly executed with exit code zero. Their 461 axiom outputs use only `propext`, `Classical.choice` and `Quot.sound`, or subsets. The records distinguish source identity, compilation, export availability and transitive axiom checks. None of these counts is a claim that every manuscript sentence is a separately exported theorem.

The consolidated external report for v1.22-r4 records PASS for E0–E8 within its documented scope. That report and the build logs remain evidence for the identified frozen source. They are not a fresh external review of v1.24. The present editorial review checks relocation, statement preservation and document rendering; no Lean build or new mathematical verification is claimed.

## 2. Mathematical statements and exported declarations

The common prefix `PaperIV` is omitted where indicated. The following map preserves the original theorem labels; moving it out of the main manuscript has not changed the formal interface.

| Result | Lean declaration |
|:--|:--|
| Theorem A, additive form | `Erdos81AllOrders.erdos81_all_orders_additive` |
| Theorem B, upper bound | `Erdos81Unconditional.erdos81_cliquePartition` |
| Theorem B, maximum | `PaperTheorems.erdos81_max_eq` |
| Theorem 3.1 | `RC01Final.rc01_uniformRoundingTarget` |
| Corollary 3.5 | `FarRegimeAllGraphs.farRegime_cliquePartition_allGraphs` |
| Dichotomy (1.5) | `HybridDichotomy.chordal_far_or_nearStructure` |
| Theorem 5.0, strengthened window | `NearH1LocalConstructor.exists_near_partition_paid_by_root_sharp` |
| Theorem 5.0, previous interface | `NearH1LocalConstructor.exists_near_partition_paid_by_root` |
| Corollary 5.4, size and density | `NearCriticalDichotomy.chordal_far_or_criticalRoot`, `chordal_far_or_edge_density` |
| Optimal quadratic coefficient | `SharpConstantOptimality.erdos81_quadratic_constant_optimal`, `erdos81_quadratic_constant_isLeast` |
| Theorem 6.1, strengthened form | `IntegralStability.chordal_linear_stability_sixteen` |
| Theorem 6.1, earlier interface | `IntegralStability.chordal_linear_stability` |
| Corollary 6.1a, piece count | `RootPartitionStability.chordal_partition_stability` |
| Corollary 6.1a, joint real piece and edge bounds | `SublinearResearch.chordal_joint_stability_real` in `PublicationStability` |
| Identity (6.7b) | `RootPartitionStability.sum_rootPieceDefect_eq` |
| Corollary 6.2 | `ExtremalClassification.chordal_extremal_classification` |
| Proposition D.3 | `SplitMixedGap.mixed_gap_zero` together with the bounded construction in `SplitCompleteSharpValue` |

For the extension table below, the prefix is `PaperIV.SublinearResearch`, except for the named E32 entry.

| Statement | Declaration |
|:--|:--|
| Real same-root chordal bounds, including edge mass | `chordal_joint_stability_real` |
| Theorem C′ and (6.12)–(6.13) | `fixed_defect_joint_stability_real` |
| Explicit parameters and classification | `FixedExplicit.fixed_defect_stability_explicit` |
| Optimal-size edit bound (6.17) | `fixed_defect_exact_extremal_edit_real` |
| Unrestricted equality classification | `E32.cp_classification_of_theoremCPrimeC`, with the proved classification above and the historical induced-removal assembly [23] (see companion §3) |
| Finite bound (6.22) | `certified_shifted_fractional_bound_all_orders` |
| Finite bound (6.23) | `certified_refined_fractional_bound_all_orders` |
| Uniform integral versions | `uniform_shifted_partition_bound`; `uniform_refined_partition_bound` |
| Arbitrary-order sequence approximation | `sequence_arbitrary_orders_partition_bound` |
| One-root sequence stability | `sequence_arbitrary_orders_stability` |

The finite same-root interfaces take real deficits. The sequence interface records rational error and excess parameters. That difference is retained when comparing the manuscript with elaborated types.

**Literal definitions.** The following excerpts reproduce definitions and theorem headers, omitting proofs but not hypotheses. The first excerpt is in the namespace `SimpleGraph`; the next three are in `PaperIV.FarRounding`, with finite \(V\), decidable equality and decidable adjacency for \(G\). The last definition is in `PaperIV`. The source locations are `PaperIV/ChordalStructure.lean` (chordality), `PaperIV/FarRounding.lean` (pairs and partitions), and `PaperIV/TargetEnvelope.lean` (target size), within the frozen package linked in §1 of this companion.

```lean
def IsChordal (G : SimpleGraph V) : Prop :=
  ∀ ⦃v : V⦄ (c : G.Walk v v), c.IsCycle → 4 ≤ c.length →
    ∃ x y : V, x ∈ c.support ∧ y ∈ c.support ∧ G.Adj x y ∧ s(x, y) ∉ c.edges
```

```lean
def pairs (K : Finset V) : Finset (Sym2 V) := K.sym2.filter fun e => ¬ e.IsDiag

structure CliquePartition where
  pieces : Finset (Finset V)
  isClique : ∀ K ∈ pieces, ∀ a ∈ K, ∀ b ∈ K, a ≠ b → G.Adj a b
  two_le_card : ∀ K ∈ pieces, 2 ≤ K.card
  edgeDisjoint : ∀ K ∈ pieces, ∀ L ∈ pieces, K ≠ L → Disjoint (pairs K) (pairs L)
  covers : pieces.biUnion pairs = G.edgeFinset

def CliquePartition.size (Q : CliquePartition G) : ℕ := Q.pieces.card

def CliquePartition.OrderAtMost (Q : CliquePartition G) (r : ℕ) : Prop :=
  ∀ K ∈ Q.pieces, K.card ≤ r
```

```lean
def targetSize (n : ℕ) : ℕ := n * (n + 1) / 6
```

Natural-number division implements the floor in \(M(n)\). The expository symbol \(c_4\) denotes the minimum over these partitions with `OrderAtMost 4`; the exported statement does not assume a minimum function, but directly supplies a witness partition. Chordality in `FarRounding` is a literal alias of the preceding cycle-based definition.

**Exported theorems.** In `PaperIV.Erdos81AllOrders` and `PaperIV.Erdos81Unconditional`, respectively, the exact headers are:

```lean
theorem erdos81_all_orders_additive :
    ∃ b : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ PaperIV.targetSize n + b
```

```lean
theorem erdos81_cliquePartition :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize n
```

These headers allow the quantifier order and exact coverage to be checked without inferring them from theorem names. The recorded audit contains no `sorryAx` among the axioms of the examined declarations. The supplementary report distinguishes that transitive check from the textual search for `native_decide` in project sources and from a complete rebuild of dependencies.

## 3. Dependencies, adapters and attribution

| Result in the text | Reference module |
|:--|:--|
| **Inputs and construction** | |
| Attained rational optimum | `PaperI.FiniteLPDuality`, `CertifiedOptimumExistence` |
| Uniform mixed rounding, Theorem 3.1 | `RC01Final`, `MixedRoundingAdapter`; `Nibble.*` infrastructure from Paper III |
| Corollary 3.5, far regime for all graphs | `FarRegimeAllGraphs.farRegime_cliquePartition_allGraphs`; explicit version in `E17.ExplicitFarAssembly` |
| Complete improved cleaning and explicit threshold | `E17.Cleanup`, `E17.FarBudget`, `E17.ExplicitFarRounding`, `E17.ExplicitFarAssembly`; constants from `E18` and `E19` |
| Fractional nibble selection, Paper III | `Nibble.FracNibbleLE`, `Nibble.FracNibbleRepaired`; adapters `PaperIIISlackNibbleAdapter`, `PaperIIINibbleAdapter` |
| Localization, root and critical window | `NearH1Localization`, `NearRootWindow`, `RootRegularizationBridge` |
| Dichotomy and absorbable interface | `HybridDichotomy`, `SeparationAbsorptionRoute` |
| Accounting and near partition | `RD09PhysicalLedger`, `NearH1FinalAssembly`, `NearH1LocalConstructor` |
| **Extremal conclusions** | |
| Sharp bound and eventual maximum | `Erdos81Unconditional`, `PaperTheorems` |
| Bounds for all orders | `Erdos81AllOrders`; explicit bound in `ExplicitThreshold` |
| Fixed rooted defect and maximum, Theorem C | `DefectExplicitPublication`; explicit assembly `E34.L11Main`; lower witness `DefectSharpPublication` |
| Necessity of order four, Proposition D.2 | `DefectSharpPublication.order_three_insufficient`, `E11K10` |
| General budget and passage to \(\operatorname{cp}\) | `LossBudget`, `SplitMixedGap` |
| Graph stability, partition stability and extremal classification | `IntegralStability`, `RootPartitionStability`, `ExtremalClassification` |
| Complete-split value and cores | `SplitCompleteSharpValue`, `SplitCompleteRigidity` |
| Partition defect and optimal coefficients | `SplitCompleteDefect`, `LinearCoefficient`, `SharpConstantOptimality` |
| Edge density in the critical branch | `NearEdgeDensity`, `NearCriticalDichotomy` |
| Equality of mixed optima, Appendix D.2 | `SplitMixedGap`, `SplitCompleteSharpValue` |
| **Complementary tools** | |
| Budgeted compatible absorption | `SpreadAbsorptionCompatibility` |
| Balanced reserve, Appendix B.2 | `BalancedReserve`, `Nibble.BeckFiala` from Paper III |
| Four-host completion, Appendix B.3 | `FourHostClosure`; Vizing and `MultiHostTriangleLift` |
| Exact reserve and threshold sensitivity | `ReserveIdentity`, `NearThresholdSensitivity` |
| Reusable chordal structure | `CliqueTree` |

**Module map.** The prefixes `PaperI`, `Nibble` and `MixedRounding` indicate, respectively, the rational development associated with Paper I, the nibble infrastructure of Paper III and the neutral mixed-model library. The prefixes `E17`, `E18`, `E19` and `A4S1` identify the increment modules integrated into the project; other unprefixed names belong to `PaperIV`; `MixedRoundingAdapter` adapts that namespace to the `MixedRounding` library. RC01 incorporates and adapts tools from Paper III, but its two-quota mixed assembly is the one in Section 3 of the present work. The table relates results to sources; the supplement retains the exact dependency list.

Chordal structure and Dirac's theorem come from the Paper II contribution, ported into `ChordalStructure`. Szemerédi's regularity lemma is reused from Mathlib; the construction and adapters for clean profiles and mixed selection belong to Paper IV. This provenance is distinct from a file's current location under `PaperIV`.

The configuration declares Mathlib as a third-party package and a selection of Paper III `Nibble` modules as a local dependency of the series. `ConeAudit` traverses the types and proof terms of the selected declarations and checks that their transitive dependencies contain no names under the root `Erdos81`, used by [5]. Our modules `PaperIV.Erdos81Unconditional` and `PaperIV.Erdos81AllOrders` have namespace root `PaperIV`; they are not the excluded root Erdos81 used by [5]. The absence of these names is a reproducible audit result, not an inference from the import list. Its scope is precise: it certifies that exclusion in the examined snapshot; it would not by itself detect relocated and renamed code or determine the historical provenance of each argument. Source attribution is documented separately. The same namespace check cannot yield a verdict on [15]. The extension uses the signed-star method of [15, Lemma 3.1] and the removal method of [22]; proving their implementations in this supplement does not make those methods new.

The public interface for Theorem C in this revision is `DefectExplicitPublication`: it uses `E34.theoremC_fully_explicit_final` and the unrestricted lower witness already proved in `DefectSharpPublication`. The older existential assembly is not the proof selected for Theorem C. Its localization uses induced removal of Alon–Shapira [23]; the selected explicit assembly instead uses the polynomial chordal-removal development of [22]. The additional `FDCheck.ASCheck` traverses proof terms and types to test exclusion of the named removal results in these selected declarations. This is not exclusion of the `AlonShapira` namespace: shared definitions of chordality, edit distance and induced copies remain in use.

There is a specific exception to this dependency comparison. The unrestricted equality classification in Corollary 6.3, (6.18), is exported through `E32.cp_classification_of_theoremCPrimeC`; that declaration and `E32.ref15Theorem11_of_theoremCPrimeC` still use the historical assembly through `E32.theoremC_at`. Their proofs therefore include the induced-removal chain of [23]. All those lemmas are proved in the frozen sources with standard axioms. The exclusion check for the explicit Theorem C and the selected stability declarations must not be extended to these classification wrappers.

### 3.1. Resources and the two gain conventions

The representation refinement in the original proof map is verified in `MixedRoundingAdapter`. The adapter identifies a piece's edges and the admissible-copy predicate, transports fractional packing capacities, and proves equality of values via `value_toFarFrac`. For an integral packing, `gain_toFarPacking` preserves gain. Thus Theorem 3.1 can be used through this neutral presentation without changing budget (1.3). This is not a new proof of rounding.

Two functions named `gainOf` must be distinguished by their domain of use. `Model.gainOf` is two at cardinality three, five at cardinality four, and zero at all other cardinalities. `FarRounding.gainOf` is \(\binom{|K|}{2}\mathbin{\dot-}1\), where \(\dot-\) denotes truncated subtraction in the naturals. They agree at cardinalities zero through four, but cease to agree from five onwards. Mixed items have cardinality three or four, so the transport is legitimate. For unrestricted partitions, such as those in Section 6.4, one uses edge accounting or `FarRounding.gainOf`; it is never replaced by the bounded gain function from `Model`. Since partition pieces have at least two vertices, truncated subtraction there agrees with ordinary subtraction.

### 3.2. Construction and retained accounts

The bounded-rank nibble is reused through `PaperIIISlackNibbleAdapter.boundedRankNibbleAt`. The two-quota construction is in `MarkedQuotaSlackGate.slackMarkedQuotaNibbleAt_proved`; the pairing of triangular supports and its physical realization are in `MarkedQuotaPairing` and `JointTwoQuotaPhysical`. The joint codegree scale corresponds to `RC01CleanedGate.cleanedPacking_joint_codegree_le_of_served_patterns`. Profile mass is at most \(t^2\), not one: this is the physical normalization of `RC01PatternMassScale`.

For the mixed path, `VertexCopyMonotone.two_mul_F4_le_add` proves the two-direction inequality. `VertexCopyGate` selects the step and its finite potential; `GatedTerminalSplit.exists_split_terminal_symmetrizationPath` supplies the complete sequence. Local accounting is constructed in `NearH1WindowAccounts` before being imported into `NearH1Localization`. This dependency direction matches the logical order explained in Lemma 4.2.

Clique extraction and calibration are in `ChordalCoreMissing` and `NearH1CalibratedRoot`. `Regularization`, `RegularizationBounds` and `RegularizedRootGoal` prove the root properties used by `RootRegularizationBridge`. Finally, `NearH1PhaseI`, `RD09FactorCandidateMoments` and `RD09FactorCandidateAverage` produce the two accounts; `NearH1FinalAssembly` combines them using the same first assignment and its occupied links. The second phase is not applied to an independent copy of the resources.

Theorem 5.0 has a strengthened form, `NearH1LocalConstructor.exists_near_partition_paid_by_root_sharp`, which adds \(|3|R|-n|\le n/50\) to the physical constructor; the previous interface `exists_near_partition_paid_by_root` remains as a corollary. The strengthened reserve in (5.15a) is retained for the same witness in `NearStructureWitness.accounts_count_le_improved`; `IntegralStability.chordal_linear_stability_sixteen` and `RootPartitionStability.chordal_partition_stability` use it without recombining roots or packings. The cyclic selection in phase I is in `RD09PaddedL1Mass`; the final evaluation of phase II, in `H1ImprovedConstants.l10_of_raw_rd09L2`. The comparator regimes in (5.1a) are checked in `SplitComparatorResidual.residual_sq_le_of_near_split_universal`. Reserve (D.8) is `ReserveIdentity.targetSize_eq_baseline_add_reserve`; the improved contraction corresponds to `NearThresholdSensitivity.descent_threshold_maximal_barrier` and `near_threshold_binding`. The critical-geometry results are in `NearRootWindow`, `NearEdgeDensity` and `NearCriticalDichotomy`.

The extension results have separate public entry points. Theorem C and its maximum are `PaperIV.DefectExplicitPublication.rooted_defect_eventual` and `rooted_defect_maximum`; the historical `DefectSharpPublication` namespace retains the lower witness and `order_three_insufficient` for Proposition D.2. `E35.theoremC_tower` and its uniform variants give Corollary 6.6. The complete account (3.11) is `E17Bridge.improved_far_loss_explicit`. Corollary 3.5 with an explicit threshold is `E17Bridge.ExplicitAssembly.farRegime_allGraphs_explicit`. Finally, `PaperIV.ExplicitThreshold.erdos81_sharp_explicit` and `erdos81_all_orders_bounded_additive` give the global result with the tower of §6.3. These names identify declarations, not new hypotheses.

### 3.3. Scope relative to other formal developments

The formal scope differs from that documented by [5] at the cited commit. Its `lean/FORMALIZATION_STATUS.md` file declares verification conditional on `ExternalInputs.Inputs`: Vizing, Häggkvist–Janssen and a packing transfer that includes certificates of rational optimality. These inputs are explicit parameters, not hidden axioms. Here the inputs used by our chain, including Vizing, are discharged; Häggkvist–Janssen is not used. The comparison concerns what each Lean development checks: it does not assert that the mathematical proof of [5] is conditional on conjectures.

Reusable contributions have their own references. Sum-zero triangle packing corresponds to Lean Pool PR #348 [12], <https://github.com/Vilin97/lean-pool/pull/348>, merged at commit `540d8e3`. Minimum-degree matchings and their weighted selection correspond to PR #420 [9], <https://github.com/Vilin97/lean-pool/pull/420>, merged at `d1de6d2`. The series sources retain the antecedents and adaptations of Vizing and Beck–Fiala. Attribution of formalizations is distinguished from authorship of the classical theorems.

Lean [10] and Mathlib [11] provide the verification environment. Code auditing does not replace human review of definitions or of the correspondence between a formal statement and its expression in the manuscript. Experiments guided the search and detected false assertions; they are not premises of universality.

The formal constructor used here invokes neither the results of [15] nor the historical modules of the replaced construction. The list bound and first-phase capacity window have the same form as conditions in [15, Lemma 4.1 and (4.4)]. Here they are justified by dyadic hosting, averaging over cyclic shifts, and balanced absorption. This comparison identifies the mechanisms and their shared conditions; it claims neither priority for those conditions nor historical independence on the basis of the dependency check in §3 of this companion.

## 4. Precision notes for the manuscript

The following distinctions survive the removal of implementation names from the exposition. They prevent a mathematical statement from being identified with a stronger or differently quantified Lean type.

- The construction in §6.1 uses triangles and edges; the audited public interface supplies a partition of order at most four and an unrestricted lower bound.
- The quadratic and linear optimality declarations use rational coefficients. The manuscript explains the passage to real coefficients by rational approximation.
- `recover_clique_from_edit` takes rational \(u\ge0\); the written proof also applies to real \(u\ge0\).
- Proposition G.1 uses a rational precision parameter in the Lean declaration and real exponential comparisons.
- The width formulation in Appendix G.1 uses clique trees with bags of bounded cardinality; it does not rely on a general Mathlib treewidth definition.
- No chordal restriction of the cleanup-to-rounding implication is formalized by Appendix G.2. The universal obstruction is not a lower bound for every chordal rounding method.

### 4.1. An existing numerical premise made explicit

The old prose in F.5 referred to `thm2_ineq` by name. The new prose prints its existing conclusion, with \(m=m_{11}(\varepsilon,K)\), \(B=B_{11}(\varepsilon,K)\) and \(\delta_{11}\) as in (F.11). The source is `E34/L11Params.lean`, lines 289–292. Its assumptions are \(0<\varepsilon<1\) and \(1\le K\); the preceding paragraph of F.5 supplies the stronger \(\varepsilon<1/2\) and \(K\ge1\). This is an expansion of a cited premise, not a new estimate or proof.

### 4.2. Source map for relocated inline references

| Manuscript location | Formal declarations or modules |
|:--|:--|
| 1.1. The common condition: a loss budget | `LossBudget.budget_iff` |
| 1.2. Structural dichotomy and resolution mechanisms | `NearStructureWitness` |
| 5.3. The three accounts that pay for the construction | `isSpokeCompatible_surviving_canonicalBad`, `RD09SpokeCompatibility.card_union_phases` |
| 6.2. The eventual maximum | `SplitCompleteRigidity.optimal_cores` |
| 6.2. The eventual maximum | `PaperTheorems.splitGraph_isChordal` |
| 6.3. All orders and optimality of the linear term | `SharpConstantOptimality.erdos81_quadratic_constant_optimal`, `erdos81_quadratic_constant_isLeast` |
| 6.3. All orders and optimality of the linear term | `LinearCoefficient.linear_coefficient_optimal` |
| 6.3. All orders and optimality of the linear term | `LossBudget.erdos81_cp_form_all_orders`, `erdos81_cp_form` |
| 6.6. Fixed-defect stability on one root | `NormalizedDeficit`, `ResidualExcess`, `NormalizedCliqueCore`, `RootPartition`, `NormalizedStability` |
| 6.7. Uniform bounds and sublinear defect | `E35.Fexp_le_tower` |
| B.1. Budgeted compatible absorption | `SpreadAbsorptionCompatibility.exists_budgeted_compatible_spread_absorber` |
| B.2. Balanced reserves | `BalancedReserve.exists_balanced_reserve` |
| B.3. Completion with four hosts | `FourHostClosure.exists_fourHost_packing` |
| C.2. What is discarded and why the threshold is uniform | `RC01CleanFiber`, `RC01DeviationCleanup` |
| C.3. An explicit schedule and its propagation | `SzemerediRegularity.initialBound` |
| C.3. An explicit schedule and its propagation | `E18.NibbleSchedule`, `NibbleOracle`, `NibbleChain` |
| C.3. An explicit schedule and its propagation | `E19.ScheduleBounds`, `E19.ChainBounds`, `E19.GateBounds` |
| C.3. An explicit schedule and its propagation | `E18.Numeric`, `E19.Main` |
| C.3. An explicit schedule and its propagation | `E35.NfarE_le_tower_poly` |
| D.1. The complete graph at every order | `ThreeRegime.CompleteStateAllOrders` |
| D.1. The complete graph at every order | `HalvingFrames` |
| D.1. The complete graph at every order | `exists_packing`, `complete_state_closes` |
| D.2. Equality of mixed optima in complete-split graphs | `SplitMixedGap.mixed_gap_zero`, `SplitCompleteSharpValue` |
| E.1. Constructor and accounting | `IndepAllBounds`, `IndepAllParams` |
| E.1. Constructor and accounting | `IndepAllPeel`, `IndepAllObstr` |
| E.1. Constructor and accounting | `IndepAllBudget` |
| E.1. Constructor and accounting | `IndepAllMain`, `ConstructorBudget` |
| E.2. From the terminal to the eventual theorem | `E34.theoremC_fully_explicit_final` |
| E.4. Retained accounts for same-root stability | `StrictParams` |
| E.4. Retained accounts for same-root stability | `StrictBudget` |
| E.4. Retained accounts for same-root stability | `ResidualExcess` |
| E.4. Retained accounts for same-root stability | `AllInput.no_core_pairs` |
| E.4. Retained accounts for same-root stability | `CoreCliqueAlternative` |
| E.4. Retained accounts for same-root stability | `TemplateDistance`, `RootPartition`, `CliqueShiftArithmetic` |
| F.1. Explicit fixed-defect parameters | `ExplicitFixedStability`, `E33.Assembly`, `E33.LocExplicit`, `E34.L11Main` |
| F.1. Explicit fixed-defect parameters | `fixed_defect_stability_explicit` |
| F.2. Fractional star accounting and small orders | `RefinedFractionalBound`, `UniformFractionalBound`, `SmallOrderFractional` |
| F.3. Uniform localization through a chordal edit | `SublinearEdit` |
| F.3. Uniform localization through a chordal edit | `exists_clique_additive_defect`, `recover_clique_from_edit` |
| F.3. Uniform localization through a chordal edit | `SublinearStabilityTransfer` |
| F.5. Auxiliary lemmas and adaptations of chordal removal | `E34.indCopies_cycle_le` |
| F.5. Auxiliary lemmas and adaptations of chordal removal | `E34.coBipartite_edit_le` |
| F.5. Auxiliary lemmas and adaptations of chordal removal | `E34.exists_large_clique` |
| F.5. Auxiliary lemmas and adaptations of chordal removal | `E34.lemma3` |
| F.5. Auxiliary lemmas and adaptations of chordal removal | `E34.transfer` |
| F.5. Auxiliary lemmas and adaptations of chordal removal | `E34.lemma11_V` |
| F.5. Auxiliary lemmas and adaptations of chordal removal | `properOn_of_pinned` |
| F.5. Auxiliary lemmas and adaptations of chordal removal | `thm2_ineq` |
| F.5. Auxiliary lemmas and adaptations of chordal removal | `claim5_count`, `block_ineq` |
| F.5. Auxiliary lemmas and adaptations of chordal removal | `l11_caseA`, `l11_caseB1`, `l11_caseB2`, `E34.L11Main` |
| F.5. Auxiliary lemmas and adaptations of chordal removal | `E35.theoremC_tower`, `theoremC_tower_uniform`, `theoremC_tower_uniform_sMax`, `NfarE_le_tower_poly`, `PaperIV.DefectExplicitPublication`, `FDCheck.ASCheck`, `PaperIV.OptimalTemplateObstruction.shifted_template_witness`, `shifted_template_sqrt_witness`, `no_linear_optimal_template_bound`, `optimal_family_nonempty` |
| G.1. The all-order bound and packing gaps | `BoundedCliqueGap` |
| G.1. The all-order bound and packing gaps | `BoundedCliqueGap.chordal_gap_linear_cliqueFree` |
| G.1. The all-order bound and packing gaps | `exists_cliqueTree_width_le_iff_cliqueFree` |
| G.2. A quantitative obstruction to codegree cleanup | `CleanupAtWith` |
| G.2. A quantitative obstruction to codegree cleanup | `threshold_gt_exp`, `threshold_gt_exp_seventy_two`, `FarExploration.CleanupRigidVerdict` |
| G.2. A quantitative obstruction to codegree cleanup | `threshold_superpolynomial` |
| G.2. A quantitative obstruction to codegree cleanup | `CodegreeCleanupAt`, `UniformRoundingTarget` |

## 5. Reproduction and separate annex

Run the following from the extracted, unchanged source archive with the toolchain pinned by `lean-toolchain` and dependencies pinned by `lake-manifest.json`. The command is documented for reproduction; it was not executed for this editorial revision.

```text
python tools/audit_publication.py
```

It reads the 19 targets in `FREEZE_SCOPE.json`, runs them serially and keeps individual logs. Reimporting a compiled audit module is not equivalent to rerunning its commands. The recorded run is under `03_reproducibility/full_rebuild_v12_20260929_resume/`, with provenance links to the first segment. `ReleaseExportCheck` uses only `import PaperIV`; the named audits inspect their own lists of types and proof terms.

| Target |
|:--|
| `PaperIV` |
| `PaperIV.Audit` |
| `PaperIV.ConeAudit` |
| `PaperIV.PublicationIncrementAudit` |
| `A4S1.IndepAllAudit` |
| `ThreeRegime.AxiomCheck` |
| `FarExploration.AxiomCheck` |
| `PaperIV.CliqueTreeAudit` |
| `E17.ImprovedFarRoundingAudit` |
| `E17.ExplicitFarAudit` |
| `PaperIV.ExplicitThresholdAudit` |
| `ReleaseExportCheck` |
| `PaperIVEditorial.ConstructorBudgetAudit` |
| `ResearchAudit` |
| `FDCheck.FinalAudit` |
| `E35.Audit` |
| `FDCheck.ASCheck` |
| `E34.Audit` |
| `PaperIV.OptimalTemplateObstructionAudit` |

The literal source manifest is `03_reproducibility/build_piv-v12-fb459343d234/SOURCE_MANIFEST.json`. The export log records 224 literal `#check` commands. The constructor audit covers `PaperIV.Editorial.ConstructorBudget`, which keeps both conclusions for one partition. The old extraction workspaces and superseded source cuts remain historical records in the series repository; they are not extra modules of the freeze described here.

`BoundedCliqueGap` is a separate source annex supporting Appendix G.1; it is not an input to the main extremal proof. Its source archive SHA-256 is `2847a422865e06880d457ea806aae5b9f749d22359eff325349c09c01cb4837d`. Its 38 source modules and 50-module build closure belong to its distinct recorded build, not to the count of 607 above.

## 6. Written-proof review and limits

**Scope of the written proof.** The table below records seven derivations examined in the consolidated external review. Its assessment, ACCEPTABLE_SUMMARY for each row, retains the stated expository limit concerning the cited second-moment estimates in C.2. A successful build checks formal derivations, not completeness of exposition; the written-proof assessment remains distinct from compilation and from human peer review. The audit history and detailed assessments are retained with the supplementary evidence.

| Location | Derivation to review, including the expanded accounts |
|:--|:--|
| §5.1, (5.4) and (5.7) | Regularization mass, degree, palette and width estimates |
| C.2, (3.8) and (3.10) | Discard counts and retention under the partition conventions |
| Lemma 3.2 and C.1–C.2 | Fibre lower bounds from regular pairs and their normalization |
| C.3, Table C.1 | Numerical domination of the nibble constants and tower iterations |
| E.1 | Normalization bounds preceding the terminal construction |
| E.1, (E.2b) and (E.2d) | Terminal estimates and the three-case budget |
| D.1 | Bose/Skolem frame constructions underlying the residue table |

Experimental checks of small orders are not used as premises. Their documentation, including completeness and certification requirements, belongs to the separate research record.

The clique-tree library retains counterexamples to formulations missing the appropriate hypotheses: a leaf alone is not equivalent to a unique simplicial vertex, and separator statements must account for repeated bags and degenerate cases. These results delimit the library's use; they add no assumptions to the main theorem.

The editorial ledger retains the exact source paragraphs and every replacement. Automated checks compare displayed equations, labels and result headings; hypotheses and proof dependencies are also reviewed in the source-to-manuscript comparison. These checks do not automatically certify semantic equivalence of all prose. The AI/tools disclosure retains its attribution and responsibility statements; the superseded draft-status sentence has been removed.

## Use of artificial intelligence and computational tools

Claude, by Anthropic, and ChatGPT/Codex, by OpenAI, were used to explore and check arguments and to prepare the manuscript. Aristotle, by Harmonic, contributed to exploring approaches, searching for counterexamples, developing proofs, and formalizing and reviewing them in Lean; its role was not limited to translating finished proofs.

Certo [13], <https://github.com/jtraverso/certo-math>, and Jacobian [14], <https://github.com/morluto/jacobian>, were the computational tools used to explore instances, check identities, and assess candidates. Jacobian is also credited by the project behind [5]; its use here is acknowledged separately from the logical dependencies of our formal proof. Computations were reviewed within their stated scope; a finite search does not replace a universal proof.

The author remains responsible for the arguments, citations, code, and presentation. No AI system is listed as an author.

## References

[1] P. Erdős, E. T. Ordman, and Y. Zalcstein, “Clique partitions of chordal graphs,” *Combinatorics, Probability and Computing* **2** (1993), 409–415.

[2] J. P. Traverso Gianini, *Affine Profile Reduction for Fractional Triangle Packings in Split Graphs*, Paper I, preprint v1.3, 22 August 2026. Spanish and English editions in the joint v3 deposit, 23 August 2026. Version DOI consulted: <https://doi.org/10.5281/zenodo.22064657>; concept DOI: <https://doi.org/10.5281/zenodo.21273143>. Supplementary material: <https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/main/preprints/PAPER_I>.

[3] J. P. Traverso Gianini, *Complete-Split Extremizers for a Fractional Triangle-Cover Functional on Chordal Graphs*, Paper II, preprint v1.2, 22 August 2026. Spanish and English editions in the joint v3 deposit, 23 August 2026. Version DOI consulted: <https://doi.org/10.5281/zenodo.22064657>; concept DOI: <https://doi.org/10.5281/zenodo.21273143>. Supplementary material: <https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/main/preprints/PAPER_II>.

[4] J. P. Traverso Gianini, *Linear-Error Clique Partitions of Split Graphs via Structured Triangle Packing*, Paper III, preprint v1.5, 23 August 2026. Spanish and English editions in the joint v3 deposit of that date. Version DOI consulted: <https://doi.org/10.5281/zenodo.22064657>; concept DOI: <https://doi.org/10.5281/zenodo.21273143>. Supplementary material: <https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/main/preprints/PAPER_III>.

[5] Anonymous, *Clique partitions of chordal graphs with linear error*, preprint, 8 September 2026. Version consulted on 20 September 2026, commit `cbde8a0a0563372b23b1b39a44180d2c0fb02f44`. Manuscript: <https://github.com/N0zoM1z0/erdos-81/blob/cbde8a0a0563372b23b1b39a44180d2c0fb02f44/manuscript/main.pdf>. The attribution printed in the document is retained. The README at that same commit credits Morluto for the mathematical proof, N0zoM1z0 for the manuscript and Lean implementation, and Jacobian at Preference Labs as part of the project: <https://github.com/N0zoM1z0/erdos-81/blob/cbde8a0a0563372b23b1b39a44180d2c0fb02f44/README.md>. These repository credits are distinguished from the signature printed on the manuscript.

[6] P. E. Haxell and V. Rödl, “Integer and fractional packings in dense graphs,” *Combinatorica* **21** (2001), 13–38.

[7] R. Yuster, “Integer and fractional packing of families of graphs,” *Random Structures & Algorithms* **26** (2005), 110–118.

[8] T. F. Bloom, “Erdős Problem #81,” *Erdős Problems*. Available at <https://www.erdosproblems.com/81>. Cited to identify the problem; this article does not certify the current review status of published proposals.

[9] J. P. Traverso Gianini and contributors to the assisted formalization, “Minimum-degree and spread matching theorems,” contribution to *lean-pool*, PR #420, 2026. Available at <https://github.com/Vilin97/lean-pool/pull/420>; merge commit `d1de6d2`, 13 September 2026. The history and file headers retain the attribution of the Aristotle-assisted contribution.

[10] L. de Moura and S. Ullrich, “The Lean 4 Theorem Prover and Programming Language,” in *Automated Deduction – CADE 28*, LNCS **12699**, Springer, 2021, 625–635.

[11] The mathlib Community, “The Lean Mathematical Library,” in *CPP 2020*, ACM, 2020, 367–381.

[12] J. P. Traverso Gianini, “Sum-zero triangle packing formalization,” Paper III contribution to *lean-pool*, PR #348, 2026. Available at <https://github.com/Vilin97/lean-pool/pull/348>; merge commit `540d8e3`, 25 August 2026. See the formalization and assistance credits in the sources.

[13] J. P. Traverso Gianini, *Certo: herramientas computacionales con certificados verificables*. Available at <https://github.com/jtraverso/certo-math>. The version used in the experiments must be fixed together with its certificates in the supplement.

[14] Morluto and contributors, *Jacobian: herramientas matemáticas componibles*. Available at <https://github.com/morluto/jacobian>. Component attribution and versions are retained in the repository.

[15] O. Okechukwu, *Clique partitions and bounded simplicial defect*, arXiv:2609.20871v1, 15 September 2026. Available at <https://arxiv.org/abs/2609.20871v1>. Accessed 27 September 2026.

[16] C. Henderson, H. Koerts, E. Roberge, S. Spirkl, and R. Whitman, *Clique Partitions of Split Graphs*, project announced as in preparation on R. Whitman's research page: <https://sites.google.com/view/rebeccawhitman/research>. Accessed 27 September 2026; the page consulted links no manuscript against which to compare its results.

[17] F. A. Behrend, “On Sets of Integers Which Contain No Three Terms in Arithmetical Progression,” *Proceedings of the National Academy of Sciences* **32** (1946), 331–332. <https://doi.org/10.1073/pnas.32.12.331>. The constant used in Appendix G.2 corresponds to `Behrend.roth_lower_bound` in Mathlib v4.28.0.

[18] I. Z. Ruzsa and E. Szemerédi, “Triple systems with no six points carrying three triangles,” *Combinatorics*, vol. II, Colloquia Mathematica Societatis János Bolyai **18**, North-Holland, 1978, 939–945. Author's bibliographic record: <https://www.renyi.hu/~szemered/pub.html>.

[19] R. C. Bose, “On the construction of balanced incomplete block designs,” *Annals of Eugenics* **9** (1939), 353–399. <https://doi.org/10.1111/j.1469-1809.1939.tb02219.x>.

[20] T. Skolem, “Some Remarks on the Triple Systems of Steiner,” *Mathematica Scandinavica* **6** (1958), 273–280. <https://tidsskrift.dk/math/article/view/10551>.

[21] R. Cipollini, partial proof announcement for Erdős Problem #81, 10 August 2026. Author's summary: <https://www.erdosproblems.com/forum/thread/81/proof-claims#proof-claim-201>; linked manuscript: <https://www.overleaf.com/read/thjptfhgnmxc>. Cited for the announced subquadratic-error bound, not as an independently audited input.

[22] R. de Joannis de Verclos, *Chordal graphs are easily testable*, arXiv:1902.06135v1, 16 February 2019. Available at <https://arxiv.org/abs/1902.06135v1>. The removal argument underlying Appendix F.3 is attributed to this work; its implementation and adaptations are documented in Appendix F.5.

[23] N. Alon and A. Shapira, *A characterization of the (natural) graph properties testable with one-sided error*, SIAM Journal on Computing **37** (2008), 1703–1727. DOI: <https://doi.org/10.1137/06064888X>. Used by the historical existential assembly and by the unrestricted-classification wrappers identified in §3 of this companion, not as the removal theorem selected for the explicit public Theorem C.

