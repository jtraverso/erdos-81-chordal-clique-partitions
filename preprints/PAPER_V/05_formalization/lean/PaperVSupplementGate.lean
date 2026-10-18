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

module

public import PaperV

-- Ancillary retained: Proposition 3.6
#check @PaperV.Dq_antitone
#print axioms PaperV.Dq_antitone
#check @PaperV.Dq_le_oct
#print axioms PaperV.Dq_le_oct
#check @PaperV.Dq_mono_left
#print axioms PaperV.Dq_mono_left
-- Ancillary retained: Proposition 3.7
#check @PaperV.Dq_eq_zero_iff
#print axioms PaperV.Dq_eq_zero_iff
#check @PaperV.oct_eq_zero_iff
#print axioms PaperV.oct_eq_zero_iff
#check @PaperV.Dq_eq_zero_iff_chromatic
#print axioms PaperV.Dq_eq_zero_iff_chromatic
#check @PaperV.Dq_pos_iff_lt_chromatic
#print axioms PaperV.Dq_pos_iff_lt_chromatic
-- Ancillary retained: Proposition 3.8
#check @PaperV.Dq_ge_card_sub
#print axioms PaperV.Dq_ge_card_sub
#check @PaperV.defect_tight_all_max
#print axioms PaperV.defect_tight_all_max
#check @PaperV.defect_eq_of_survivors
#print axioms PaperV.defect_eq_of_survivors
#check @PaperV.Manuscript.minimum_coloring_rigidity_iff
#print axioms PaperV.Manuscript.minimum_coloring_rigidity_iff
-- Ancillary retained: Proposition 3.9
#check @PaperV.Dq_sum
#print axioms PaperV.Dq_sum
#check @PaperV.oct_sum
#print axioms PaperV.oct_sum
-- Ancillary retained: Proposition 3.10
#check @PaperV.Dq_lineGraph_eq_zero_iff
#print axioms PaperV.Dq_lineGraph_eq_zero_iff
#check @PaperV.Dq_lineGraph_pos_iff
#print axioms PaperV.Dq_lineGraph_pos_iff
#check @PaperV.Dq_one_lineGraph
#print axioms PaperV.Dq_one_lineGraph
#check @PaperV.profile_zero_set_not_values
#print axioms PaperV.profile_zero_set_not_values
-- Ancillary retained: Corollary 3.11
#check @PaperV.TerminalPair.p4_133_existence_sharp
#print axioms PaperV.TerminalPair.p4_133_existence_sharp
#check @PaperV.TerminalPair.p4_133_existence_coarse
#print axioms PaperV.TerminalPair.p4_133_existence_coarse
-- Ancillary retained: Theorem 7.4
#check @PaperV.PairedFactors.exists_paired_completion
#print axioms PaperV.PairedFactors.exists_paired_completion
-- Ancillary retained: Proposition 7.5
#check @PaperV.FiniteLP.gap_identity
#print axioms PaperV.FiniteLP.gap_identity
#check @PaperV.FiniteLP.weak_duality
#print axioms PaperV.FiniteLP.weak_duality
#check @PaperV.FiniteLP.complementarity_of_equal_value
#print axioms PaperV.FiniteLP.complementarity_of_equal_value
#check @PaperV.RationalFarkas.farkas
#print axioms PaperV.RationalFarkas.farkas
#check @PaperV.RationalFarkas.not_sat_of_cert
#print axioms PaperV.RationalFarkas.not_sat_of_cert
#check @PaperV.FiniteLP.exists_equal_primal_dual
#print axioms PaperV.FiniteLP.exists_equal_primal_dual
-- Ancillary retained: Corollary 5.4
#check @PaperV.Host.weighted_host_selection
#print axioms PaperV.Host.weighted_host_selection
#check @PaperV.Host.weighted_host_selection_nu
#print axioms PaperV.Host.weighted_host_selection_nu
#check @PaperV.Host.konig_weighted_host_selection
#print axioms PaperV.Host.konig_weighted_host_selection
#check @PaperV.Host.galvin_heavy_single_host
#print axioms PaperV.Host.galvin_heavy_single_host
-- Ancillary retained: Lemma C.1
#check @PaperV.UnitBoundary.unitBoundary_completion_optimal
#print axioms PaperV.UnitBoundary.unitBoundary_completion_optimal
#check @PaperV.UnitBoundary.exists_optimal_normPack
#print axioms PaperV.UnitBoundary.exists_optimal_normPack
-- Ancillary retained: Lemma C.2
#check @PaperV.UnitBoundary.endpoint_repacking_card_bound
#print axioms PaperV.UnitBoundary.endpoint_repacking_card_bound
#check @PaperV.UnitBoundary.endpoint_repacking_nonloss
#print axioms PaperV.UnitBoundary.endpoint_repacking_nonloss

#check @PaperV.UnitBoundary.completion_optimal_unconditional
#print axioms PaperV.UnitBoundary.completion_optimal_unconditional
#check @PaperV.UnitBoundary.exists_endpoint_repacking
#print axioms PaperV.UnitBoundary.exists_endpoint_repacking

-- Ancillary unnumbered BK exact certificates (main section9.1).
#check @PaperV.BK.resource_upper_bound
#print axioms PaperV.BK.resource_upper_bound
#check @PaperV.BK.real_resource_attainment
#print axioms PaperV.BK.real_resource_attainment
#check @PaperV.BK.residual_two_attained
#print axioms PaperV.BK.residual_two_attained
