/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Original mathematical attributions and third-party notices are retained below.
-/

/-
Paper V formalization and integration.
Authors: Juan Pablo Traverso Gianini

Original mathematical attributions and existing source/port provenance are
retained below; this author credit does not reattribute those prior results.
-/

/-
Paper V v1.8 — canonical 4.35 baseline headline signature/axiom gate.
The preserved baseline declaration inventory is queried freshly. Validation is
confirmed only by a successful current run and its saved log. Allowed axioms:
propext, Classical.choice, Quot.sound. New F1-F8 endpoints have separate gates.
-/
module

public import PaperV

-- §3 core engine
#check @PaperV.splitting
#print axioms PaperV.splitting
#check @PaperV.splitting_half
#print axioms PaperV.splitting_half
#check @PaperV.SplittingQ.splitting_q
#print axioms PaperV.SplittingQ.splitting_q
#check @PaperV.SplittingQ.splitting_ceil
#print axioms PaperV.SplittingQ.splitting_ceil
#check @PaperV.transfer_q
#print axioms PaperV.transfer_q
#check @PaperV.transfer_half
#print axioms PaperV.transfer_half
#check @PaperV.transfer_q_weighted
#print axioms PaperV.transfer_q_weighted
#check @PaperV.parity_localization
#print axioms PaperV.parity_localization
-- 3.2a / 3.2b and the cover-to-private-witness interface
#check @PaperV.cover_defect_lower
#print axioms PaperV.cover_defect_lower
#check @PaperV.rigidity_at_equality
#print axioms PaperV.rigidity_at_equality
#check @PaperV.multSize_witnessMultiset
#print axioms PaperV.multSize_witnessMultiset
#check @PaperV.witness_feasible_compat
#print axioms PaperV.witness_feasible_compat
#check @PaperV.cover_witness_defect
#print axioms PaperV.cover_witness_defect
#check @PaperV.conflict_rigidity
#print axioms PaperV.conflict_rigidity
#check @PaperV.triangle_cover_defect
#print axioms PaperV.triangle_cover_defect
-- §3.6 structural calculus
#check @PaperV.Dq_antitone
#print axioms PaperV.Dq_antitone
#check @PaperV.Dq_le_oct
#print axioms PaperV.Dq_le_oct
#check @PaperV.Dq_mono_left
#print axioms PaperV.Dq_mono_left
#check @PaperV.Dq_eq_zero_iff_chromatic
#print axioms PaperV.Dq_eq_zero_iff_chromatic
#check @PaperV.oct_eq_zero_iff
#print axioms PaperV.oct_eq_zero_iff
#check @PaperV.Dq_pos_iff_lt_chromatic
#print axioms PaperV.Dq_pos_iff_lt_chromatic
#check @PaperV.Dq_ge_card_sub
#print axioms PaperV.Dq_ge_card_sub
#check @PaperV.defect_tight_all_max
#print axioms PaperV.defect_tight_all_max
#check @PaperV.Dq_sum
#print axioms PaperV.Dq_sum
#check @PaperV.oct_sum
#print axioms PaperV.oct_sum
#check @PaperV.Dq_top
#print axioms PaperV.Dq_top
#check @PaperV.oct_top
#print axioms PaperV.oct_top
#check @PaperV.oct_cycleGraph_even
#print axioms PaperV.oct_cycleGraph_even
#check @PaperV.oct_cycleGraph_odd
#print axioms PaperV.oct_cycleGraph_odd
#check @PaperV.conflict_defect_lower
#print axioms PaperV.conflict_defect_lower
#check @PaperV.conflict_oct_eq_zero_iff
#print axioms PaperV.conflict_oct_eq_zero_iff
-- 3.6L line-graph interface, Vizing, edge-defect profile
#check @PaperV.lineGraph_matching_defect
#print axioms PaperV.lineGraph_matching_defect
#check @PaperV.lineGraph_matching_defect_q
#print axioms PaperV.lineGraph_matching_defect_q
#check @PaperV.multiLineGraph_matching_defect
#print axioms PaperV.multiLineGraph_matching_defect
#check @PaperV.multiLineGraph_matching_defect_q
#print axioms PaperV.multiLineGraph_matching_defect_q
#check @PaperV.maxDegree_le_edgeChromaticNumber
#print axioms PaperV.maxDegree_le_edgeChromaticNumber
#check @PaperV.edgeChromaticNumber_le_maxDegree_add_one
#print axioms PaperV.edgeChromaticNumber_le_maxDegree_add_one
#check @PaperV.edgeChromaticNumber_bounds
#print axioms PaperV.edgeChromaticNumber_bounds
#check @PaperV.edgeChromaticNumber_eq_maxDegree_or
#print axioms PaperV.edgeChromaticNumber_eq_maxDegree_or
#check @PaperV.Dq_lineGraph_eq_zero_iff
#print axioms PaperV.Dq_lineGraph_eq_zero_iff
#check @PaperV.Dq_lineGraph_pos_iff
#print axioms PaperV.Dq_lineGraph_pos_iff
-- 3.11 P4-133 and its tools
#check @PaperV.TerminalPair.p4_133_existence
#print axioms PaperV.TerminalPair.p4_133_existence
#check @beck_fiala
#print axioms beck_fiala
#check @beck_fiala_zero_counterexample
#print axioms beck_fiala_zero_counterexample
-- Brooks Δ=3 chain
#check @PaperV.Brooks.brooks_cubic
#print axioms PaperV.Brooks.brooks_cubic
#check @PaperV.oct_le_third_of_cubic
#print axioms PaperV.oct_le_third_of_cubic
-- §4 copy inequalities and host-clique model
#check @PaperV.copy_integral_struct
#print axioms PaperV.copy_integral_struct
#check @PaperV.copy_fractional
#print axioms PaperV.copy_fractional
#check @PaperV.copy_integral
#print axioms PaperV.copy_integral
#check @PaperV.tight_oct
#print axioms PaperV.tight_oct
#check @PaperV.copy_triple_bound
#print axioms PaperV.copy_triple_bound
#check @PaperV.k4_of_three_triangles
#print axioms PaperV.k4_of_three_triangles
#check @PaperV.card_le_four_of_pairwise_share
#print axioms PaperV.card_le_four_of_pairwise_share
#check @PaperV.PureProfile.prop43_nu
#print axioms PaperV.PureProfile.prop43_nu
#check @PaperV.PureProfile.prop43_muMat
#print axioms PaperV.PureProfile.prop43_muMat
#check @PaperV.PureProfile.hostClique_gap_zero
#print axioms PaperV.PureProfile.hostClique_gap_zero
#check @PaperV.PureProfile.hostClique_gap_le_third
#print axioms PaperV.PureProfile.hostClique_gap_le_third
#check @PaperV.PureProfile.gap_third_tight
#print axioms PaperV.PureProfile.gap_third_tight
#check @PaperV.oct_le_min_tau_third
#print axioms PaperV.oct_le_min_tau_third
#check @PaperV.apost_certificate
#print axioms PaperV.apost_certificate
-- §5 finite counterexamples
#check @PaperV.BK.bk_nu
#print axioms PaperV.BK.bk_nu
#check @PaperV.clon2_oct
#print axioms PaperV.clon2_oct
#check @PaperV.StarT2.star_t2_nu
#print axioms PaperV.StarT2.star_t2_nu
-- §6 SEAL: 6.1 feasibility, 6.2 termination count
#check @PaperV.feasible_run
#print axioms PaperV.feasible_run
#check @PaperV.card_le_cov
#print axioms PaperV.card_le_cov
#check @PaperV.accepted_repairs_le_cov
#print axioms PaperV.accepted_repairs_le_cov
#check @PaperV.accepted_repairs_le_audit
#print axioms PaperV.accepted_repairs_le_audit
-- Appendix A: unit-boundary kernels, glue, witnesses
#check @PaperV.UnitBoundary.unitBoundary_completion_optimal
#print axioms PaperV.UnitBoundary.unitBoundary_completion_optimal
#check @PaperV.UnitBoundary.endpoint_repacking_card_bound
#print axioms PaperV.UnitBoundary.endpoint_repacking_card_bound
#check @PaperV.UnitBoundary.endpoint_repacking_nonloss
#print axioms PaperV.UnitBoundary.endpoint_repacking_nonloss
#check @PaperV.UnitBoundary.nu_resCS
#print axioms PaperV.UnitBoundary.nu_resCS
#print axioms PaperV.UnitBoundary.w1_lemmaA_check
#print axioms PaperV.UnitBoundary.w2_weights_fail
#print axioms PaperV.UnitBoundary.w3_normPack_small
#print axioms PaperV.UnitBoundary.w4_tight
-- Remark C1r: quadratic-defect construction (Steiner S(2,4,n) / affine lines over GF(4))
#check @PaperV.Steiner.quadratic_defect
#print axioms PaperV.Steiner.quadratic_defect
#check @PaperV.Steiner.oct_steinerX
#print axioms PaperV.Steiner.oct_steinerX
#check @PaperV.Steiner.load_two_bound
#print axioms PaperV.Steiner.load_two_bound
#check @PaperV.Steiner.affine_isSteinerK4
#print axioms PaperV.Steiner.affine_isSteinerK4
#check @PaperV.Steiner.exists_quadratic_defect
#print axioms PaperV.Steiner.exists_quadratic_defect
-- C1r, clause-level declarations (multiplicity ≤ 1, load 2, half-integral optimality) + full-LP optimality
#check @PaperV.Steiner.steinerX_le_one
#print axioms PaperV.Steiner.steinerX_le_one
#check @PaperV.Steiner.load_steinerX
#print axioms PaperV.Steiner.load_steinerX
#check @PaperV.Steiner.steinerX_optimal
#print axioms PaperV.Steiner.steinerX_optimal
#check @PaperV.Steiner.frac_packing_bound
#print axioms PaperV.Steiner.frac_packing_bound
#check @PaperV.Steiner.steinerX_half_optimal
#print axioms PaperV.Steiner.steinerX_half_optimal
#check @PaperV.Steiner.half_steinerX_ge_frac
#print axioms PaperV.Steiner.half_steinerX_ge_frac
#check @PaperV.Steiner.exists_quadratic_defect_frac
#print axioms PaperV.Steiner.exists_quadratic_defect_frac
-- Paper V wave 1: D_1 identity and the scope of Proposition 3.10
#check @PaperV.Dq_one_eq
#print axioms PaperV.Dq_one_eq
#check @PaperV.Dq_one_lineGraph
#print axioms PaperV.Dq_one_lineGraph
#check @PaperV.profile_zero_set_not_values
#print axioms PaperV.profile_zero_set_not_values
-- rational LP certificate contract (C1) and V-CLEAN (C2)
#check @PaperV.FiniteLP.gap_identity
#print axioms PaperV.FiniteLP.gap_identity
#print axioms PaperV.FiniteLP.weak_duality
#print axioms PaperV.FiniteLP.equal_value_of_complementarity
#print axioms PaperV.FiniteLP.complementarity_of_equal_value
#print axioms PaperV.FiniteLP.optimal_of_equal
#check @PaperV.FiniteLP.discarded_value_le
#print axioms PaperV.FiniteLP.discarded_value_le
-- certificate form of the weighted transfer, cleanup transfer core (C3), owned union (C5)
#check @PaperV.transfer_q_weighted_cert
#print axioms PaperV.transfer_q_weighted_cert
#check @PaperV.cleanup_transfer_cert
#print axioms PaperV.cleanup_transfer_cert
#print axioms PaperV.discarded_scaled_le
#check @PaperV.UnitBoundary.ResFeasible_biUnion_of_owner
#print axioms PaperV.UnitBoundary.ResFeasible_biUnion_of_owner
#print axioms PaperV.UnitBoundary.wsum_biUnion_of_owner
-- weighted Appendix A (Theorems E, E.1)
#check @PaperV.UnitBoundary.Weighted.weighted_optimum_eq
#print axioms PaperV.UnitBoundary.Weighted.weighted_optimum_eq
#check @PaperV.UnitBoundary.Weighted.weighted_transport
#print axioms PaperV.UnitBoundary.Weighted.weighted_transport
#print axioms PaperV.UnitBoundary.Weighted.w2_weighted_check
-- Theorem A2: mixed weighted copies
#check @PaperV.mixed_copy_integral
#print axioms PaperV.mixed_copy_integral
#check @PaperV.mixed_copy_integral_opt
#print axioms PaperV.mixed_copy_integral_opt
#print axioms PaperV.copyMap_mem_cliqueFinset
-- Paper V wave 2a: realizers and Realizable-Class Transfer (RCT, RCT0)
#check @PaperV.realizable_class_transfer
#print axioms PaperV.realizable_class_transfer
#check @PaperV.realizable_transfer_cert
#print axioms PaperV.realizable_transfer_cert
#check @PaperV.realizable_transfer_exact
#print axioms PaperV.realizable_transfer_exact
-- realizability defect D_{q,R}^w, RDT, monotonicity, identity recovers the engine
#check @PaperV.realizability_defect_transfer
#print axioms PaperV.realizability_defect_transfer
#print axioms PaperV.wRDq_mono
#check @PaperV.wRDq_le_wDq
#print axioms PaperV.wRDq_le_wDq
#check @PaperV.wRDq_identity_eq_wDq
#print axioms PaperV.wRDq_identity_eq_wDq
#print axioms PaperV.realizability_transfer_identity
#print axioms PaperV.realizability_transfer_of_containsIdentity
-- host realizer: physical soundness of proper list host assignments, host-lifted transfer
#check @PaperV.Host.resFeasible_of_properOn
#print axioms PaperV.Host.resFeasible_of_properOn
#print axioms PaperV.Host.nu_hostCS_le
#check @PaperV.Host.host_transfer
#print axioms PaperV.Host.host_transfer
-- strict separation K_{r,r}: D_1 = r^2 - r vs D_{1,host} = 0; nu(hostCS) = r^2
#check @PaperV.Strictness.Dq_one_krGraph
#print axioms PaperV.Strictness.Dq_one_krGraph
#check @PaperV.Strictness.strict_separation
#print axioms PaperV.Strictness.strict_separation
#print axioms PaperV.Strictness.strict_separation_pos
#check @PaperV.Strictness.nu_hostCS_kr
#print axioms PaperV.Strictness.nu_hostCS_kr
-- Paper V wave 2a': realizer combinators, lower bound and optimality criterion
#print axioms PaperV.subsetRealizer
#print axioms PaperV.ClassRealizer.union_exact
#check @PaperV.wRDq_ge
#print axioms PaperV.wRDq_ge
#check @PaperV.wRDq_eq_of_cost
#print axioms PaperV.wRDq_eq_of_cost
-- rational weights by scaling
#check @PaperV.wNuQ_scale
#print axioms PaperV.wNuQ_scale
#check @PaperV.realizable_transfer_rational
#print axioms PaperV.realizable_transfer_rational
#print axioms PaperV.transfer_q_weighted_rational
#print axioms PaperV.exists_scaleW
-- LP -> multiset bridge
#check @PaperV.lp_value_eq
#print axioms PaperV.lp_value_eq
#print axioms PaperV.isQMultiset_of_le_one
#check @PaperV.lp_transfer
#print axioms PaperV.lp_transfer
#print axioms PaperV.lp_realizable_transfer
#print axioms PaperV.lp_realizability_defect_transfer
-- Galvin list edge colouring (port of Paper III Appendix D) and Konig
#check @PaperV.Galvin.kernel_coloring
#print axioms PaperV.Galvin.kernel_coloring
#check @PaperV.Galvin.gale_shapley
#print axioms PaperV.Galvin.gale_shapley
#check @PaperV.Galvin.konig_edge_coloring
#print axioms PaperV.Galvin.konig_edge_coloring
#check @PaperV.Galvin.galvin_max_degree
#print axioms PaperV.Galvin.galvin_max_degree
-- Galvin -> HostAssignment; Galvin/Konig + weighted transfer -> WeightedHostSelection
#check @PaperV.Host.galvin_host_assignment
#print axioms PaperV.Host.galvin_host_assignment
#check @PaperV.Host.galvin_full_packing
#print axioms PaperV.Host.galvin_full_packing
#check @PaperV.Host.weighted_host_selection
#print axioms PaperV.Host.weighted_host_selection
#check @PaperV.Host.weighted_host_selection_nu
#print axioms PaperV.Host.weighted_host_selection_nu
#check @PaperV.Host.konig_weighted_host_selection
#print axioms PaperV.Host.konig_weighted_host_selection
#check @PaperV.Host.galvin_heavy_single_host
#print axioms PaperV.Host.galvin_heavy_single_host
#print axioms PaperV.Host.instDecidableProperOn
-- Galvin realizers in the realizability framework; Galvin-Lifted Transfer (GLT)
#print axioms PaperV.Host.galvinRealizer_mem
#check @PaperV.Host.galvin_lifted_transfer
#print axioms PaperV.Host.galvin_lifted_transfer
#check @PaperV.Host.wRDq_host_le_of_galvin
#print axioms PaperV.Host.wRDq_host_le_of_galvin
-- Farkas over Q (Fourier-Motzkin) and strong duality of the finite rational packing LP
#check @PaperV.RationalFarkas.farkas
#print axioms PaperV.RationalFarkas.farkas
#print axioms PaperV.RationalFarkas.not_sat_of_cert
#check @PaperV.FiniteLP.exists_equal_primal_dual
#print axioms PaperV.FiniteLP.exists_equal_primal_dual
-- Theorem A1 (fractional weighted copy inequality, mixed family)
#check @PaperV.Mixed.mixed_copy_fractional
#print axioms PaperV.Mixed.mixed_copy_fractional
-- GALVIN-BKW-LOCAL: multigraph Galvin engine, Konig/stable matchings for multigraphs, Theorems A and B, host adapters
#check @PaperV.Galvin.stable_matching_multi
#print axioms PaperV.Galvin.stable_matching_multi
#check @PaperV.Galvin.konig_multigraph
#print axioms PaperV.Galvin.konig_multigraph
#check @PaperV.Galvin.ranks_exist
#print axioms PaperV.Galvin.ranks_exist
#check @PaperV.Galvin.galvin_engine
#print axioms PaperV.Galvin.galvin_engine
#check @PaperV.Galvin.galvin_multigraph_max_degree
#print axioms PaperV.Galvin.galvin_multigraph_max_degree
#check @PaperV.Galvin.galvin_bkw_local
#print axioms PaperV.Galvin.galvin_bkw_local
#check @PaperV.Host.bkw_host_assignment
#print axioms PaperV.Host.bkw_host_assignment
#print axioms PaperV.Host.bkw_full_packing
#check @PaperV.Host.galvin_local_lifted_transfer
#print axioms PaperV.Host.galvin_local_lifted_transfer
-- Theorem D: weighted completion by paired factors (finite averaging core)
#check @PaperV.PairedFactors.exists_paired_completion
#print axioms PaperV.PairedFactors.exists_paired_completion
-- Konig for the edge-defect profile: bipartite graphs are Class 1, zero set of q -> D_q(L(G)) starts exactly at Delta
#check @PaperV.Konig.lineGraph_colorable_maxDegree_of_bipartite
#print axioms PaperV.Konig.lineGraph_colorable_maxDegree_of_bipartite
#check @PaperV.Konig.Dq_lineGraph_maxDegree_eq_zero
#print axioms PaperV.Konig.Dq_lineGraph_maxDegree_eq_zero
#check @PaperV.Konig.isClassOne_of_bipartite
#print axioms PaperV.Konig.isClassOne_of_bipartite
#check @PaperV.Konig.Dq_lineGraph_eq_zero_iff_of_bipartite
#print axioms PaperV.Konig.Dq_lineGraph_eq_zero_iff_of_bipartite
-- intermediate regime: 0 < D_{1,host} = 1 < D_1 = 2 on K_{1,3} with two hosts
#check @PaperV.StarExample.intermediate_defect
#print axioms PaperV.StarExample.intermediate_defect
-- P4-133 sharp division-free form: a*|Pall| < m*(|S'| + 5 + 10|X|)
#check @PaperV.TerminalPair.p4_133_existence_sharp
#print axioms PaperV.TerminalPair.p4_133_existence_sharp
-- generic fractional copy inequality (shared core of Theorem 4.1 and Theorem A1)
#check @PaperV.FracCopy.copy_fractional_generic
#print axioms PaperV.FracCopy.copy_fractional_generic
-- SEAL bridge (Section 8): proper list host assignments are SEAL-feasible; exact Galvin/BKW regime; Konig guarantee
#check @PaperV.SealBridge.sealFeasible_of_properOn
#print axioms PaperV.SealBridge.sealFeasible_of_properOn
#check @PaperV.SealBridge.seal_galvin_regime
#print axioms PaperV.SealBridge.seal_galvin_regime
#check @PaperV.SealBridge.seal_bkw_regime
#print axioms PaperV.SealBridge.seal_bkw_regime
#check @PaperV.SealBridge.seal_konig_guarantee
#print axioms PaperV.SealBridge.seal_konig_guarantee

-- Global pure-profile two-thirds bound (PureProfileGap)
#check @PaperV.PureProfile.muMatDeg_le_min
#print axioms PaperV.PureProfile.muMatDeg_le_min
#check @PaperV.PureProfile.nu_ge_frac_muMatDeg
#print axioms PaperV.PureProfile.nu_ge_frac_muMatDeg
#check @PaperV.PureProfile.nu_ge_two_thirds_muMatDeg
#print axioms PaperV.PureProfile.nu_ge_two_thirds_muMatDeg
#check @PaperV.PureProfile.nu_ge_muMatDeg_two
#print axioms PaperV.PureProfile.nu_ge_muMatDeg_two

-- Exact host completion: nu(hostCS restricted to B) = |B| (HostCompletion)
#check @PaperV.Host.nu_hostCSOn_le
#print axioms PaperV.Host.nu_hostCSOn_le
#check @PaperV.Host.nu_hostCSOn_eq_of_properOn
#print axioms PaperV.Host.nu_hostCSOn_eq_of_properOn
#check @PaperV.Host.galvin_host_completion_exact
#print axioms PaperV.Host.galvin_host_completion_exact
#check @PaperV.Host.bkw_host_completion_exact
#print axioms PaperV.Host.bkw_host_completion_exact
#check @PaperV.Host.nu_hostCS_eq_card_of_properOn_univ
#print axioms PaperV.Host.nu_hostCS_eq_card_of_properOn_univ

/-! ## Manuscript parity (v1.7): definitional anchors and remaining cited statements -/

-- Definitions 2.1-2.2 (conflict system, feasibility, nu, copies, conflict graph, q-multiset)
#check @PaperV.ConflictSystem
#print axioms PaperV.ConflictSystem
#check @PaperV.CSFeasible
#print axioms PaperV.CSFeasible
#check @PaperV.nu
#print axioms PaperV.nu
#check @PaperV.Copies
#print axioms PaperV.Copies
#check @PaperV.Hgraph
#print axioms PaperV.Hgraph
#check @PaperV.IsQMultiset
#print axioms PaperV.IsQMultiset
-- Definition 2.3 (colorability defect and its q = 2 case) and the weighted defect of Theorem 3.4w
#check @PaperV.Dq
#print axioms PaperV.Dq
#check @PaperV.oct
#print axioms PaperV.oct
#check @PaperV.wDq
#print axioms PaperV.wDq
-- Definitions 2.4-2.5 (resource incidence, packing optimum) and the Appendix C glue
#check @PaperV.UnitBoundary.resCS
#print axioms PaperV.UnitBoundary.resCS
#check @PaperV.UnitBoundary.packOpt
#print axioms PaperV.UnitBoundary.packOpt
#check @PaperV.UnitBoundary.csFeasible_resCS_iff
#print axioms PaperV.UnitBoundary.csFeasible_resCS_iff
-- Definitions 4.1 and 4.3 (realizer, realizability certificate, realizability defect)
#check @PaperV.ClassRealizer
#print axioms PaperV.ClassRealizer
#check @PaperV.RealCert
#print axioms PaperV.RealCert
#check @PaperV.wRDq
#print axioms PaperV.wRDq
-- Target systems of Sections 5 and 7.3
#check @PaperV.Host.hostCS
#print axioms PaperV.Host.hostCS
#check @PaperV.Host.hostCSOn
#print axioms PaperV.Host.hostCSOn
#check @PaperV.mixedCS
#print axioms PaperV.mixedCS
-- Corollary 3.2 (ceiling form) and the unit-weight specializations of Theorem 3.4w
#check @PaperV.nu_ge_ceil
#print axioms PaperV.nu_ge_ceil
#check @PaperV.transfer_q_weighted_one
#print axioms PaperV.transfer_q_weighted_one
#check @PaperV.wNu_one
#print axioms PaperV.wNu_one
#check @PaperV.wDq_one
#print axioms PaperV.wDq_one
-- Proposition 3.10 (Class 1 / Class 2 predicates) and Corollary 3.11 (coarse form)
#check @PaperV.IsClassOne
#print axioms PaperV.IsClassOne
#check @PaperV.IsClassTwo
#print axioms PaperV.IsClassTwo
#check @PaperV.TerminalPair.p4_133_existence_coarse
#print axioms PaperV.TerminalPair.p4_133_existence_coarse
-- Corollary 6.2a (auxiliary form) and Lemma 6.2k (clique bound in the triangle system)
#check @PaperV.copy_triple_bound_of
#print axioms PaperV.copy_triple_bound_of
#check @PaperV.triCS_clique_card_le_four
#print axioms PaperV.triCS_clique_card_le_four

-- Corollary to Theorem 7.3 (MixedCopyAsymptotic)
#check @PaperV.Mixed.wNu_le_Wstar
#print axioms PaperV.Mixed.wNu_le_Wstar
#check @PaperV.Mixed.RoundingGap
#print axioms PaperV.Mixed.RoundingGap
#check @PaperV.Mixed.mixed_copy_integral_of_roundingGap
#print axioms PaperV.Mixed.mixed_copy_integral_of_roundingGap
#check @PaperV.Mixed.mixed_copy_integral_of_integral_lp
#print axioms PaperV.Mixed.mixed_copy_integral_of_integral_lp

-- Audit findings on pure profiles (PureProfileSharp)
#check @PaperV.PureProfile.nu_le_muMatDeg
#print axioms PaperV.PureProfile.nu_le_muMatDeg
#check @PaperV.PureProfile.nu_eq_muMatDeg_of_even
#print axioms PaperV.PureProfile.nu_eq_muMatDeg_of_even

#check @PaperV.PureProfile.muMatDeg_eq_min
#print axioms PaperV.PureProfile.muMatDeg_eq_min
#check @PaperV.PureProfile.nu_eq_frac_muMatDeg_of_odd
#print axioms PaperV.PureProfile.nu_eq_frac_muMatDeg_of_odd

-- Preprint 1.0: specified packing-image interfaces.
#check @PaperV.triangleImageMultiset
#print axioms PaperV.triangleImageMultiset
#check @PaperV.triangleImageMultiset_size
#print axioms PaperV.triangleImageMultiset_size
#check @PaperV.triangleImageMultiset_isQMultiset
#print axioms PaperV.triangleImageMultiset_isQMultiset
#check @PaperV.copy_integral_for_packings
#print axioms PaperV.copy_integral_for_packings
#check @PaperV.copy_integral_for_optimal_packings
#print axioms PaperV.copy_integral_for_optimal_packings
#check @PaperV.mixed_copy_integral
#print axioms PaperV.mixed_copy_integral
