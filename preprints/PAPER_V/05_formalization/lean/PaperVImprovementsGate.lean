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
set_option pp.universes true
set_option pp.explicit true

#check @PaperV.ResourceCertificate.resource_gap_identity
#print axioms PaperV.ResourceCertificate.resource_gap_identity
#check @PaperV.ResourceCertificate.two_error_certificate
#print axioms PaperV.ResourceCertificate.two_error_certificate
#check @PaperV.ResourceCertificate.two_error_real_optimum
#print axioms PaperV.ResourceCertificate.two_error_real_optimum
#check @PaperV.ResourceCertificate.exists_real_optimum
#print axioms PaperV.ResourceCertificate.exists_real_optimum
#check @PaperV.ResourceCertificate.System.packing_union
#print axioms PaperV.ResourceCertificate.System.packing_union
#check @PaperV.ResourceCertificate.System.compatible_realization_union
#print axioms PaperV.ResourceCertificate.System.compatible_realization_union
#check @PaperV.ResourceCertificate.portfolio_selection
#print axioms PaperV.ResourceCertificate.portfolio_selection
#check @PaperV.Host.greedy_host_assignment
#print axioms PaperV.Host.greedy_host_assignment
#check @PaperV.Host.assigned_weight
#print axioms PaperV.Host.assigned_weight
#check @PaperV.Host.compatible_background_union
#print axioms PaperV.Host.compatible_background_union
#check @PaperV.Host.proper_assignment_avoids_background
#print axioms PaperV.Host.proper_assignment_avoids_background
#check @PaperV.Host.paired_factor_assignment
#print axioms PaperV.Host.paired_factor_assignment
#check @PaperV.Host.empty_factor_completion
#print axioms PaperV.Host.empty_factor_completion
#check @PaperV.MixedPromotion.face_count
#print axioms PaperV.MixedPromotion.face_count
#check @PaperV.MixedPromotion.load_promote
#print axioms PaperV.MixedPromotion.load_promote
#check @PaperV.MixedPromotion.feasible_promote
#print axioms PaperV.MixedPromotion.feasible_promote
#check @PaperV.MixedPromotion.gain_promote
#print axioms PaperV.MixedPromotion.gain_promote
#check @PaperV.MixedPromotion.pricedValue_promote
#print axioms PaperV.MixedPromotion.pricedValue_promote
#check @PaperV.MixedPromotion.optimal_support_exclusion
#print axioms PaperV.MixedPromotion.optimal_support_exclusion
#check @PaperV.MixedPromotion.support_decreases
#print axioms PaperV.MixedPromotion.support_decreases
#check @PaperV.MixedPromotion.exists_normalized
#print axioms PaperV.MixedPromotion.exists_normalized
#check @PaperV.MixedBudget.fractionalSlack_nonneg
#print axioms PaperV.MixedBudget.fractionalSlack_nonneg
#check @PaperV.MixedBudget.mixed_copy_gap_budget
#print axioms PaperV.MixedBudget.mixed_copy_gap_budget

#check @PaperV.Host.exists_paired_host_completion
#print axioms PaperV.Host.exists_paired_host_completion
#check @PaperV.MixedBudget.CopyTree.gap_budget
#print axioms PaperV.MixedBudget.CopyTree.gap_budget
#check @PaperV.MixedBudget.CopyTree.slack_telescopes
#print axioms PaperV.MixedBudget.CopyTree.slack_telescopes

#check @PaperV.FiniteValueStability.minimum_le
#print axioms PaperV.FiniteValueStability.minimum_le
#check @PaperV.FiniteValueStability.exists_minimizer
#print axioms PaperV.FiniteValueStability.exists_minimizer
#check @PaperV.FiniteValueStability.sensitivity
#print axioms PaperV.FiniteValueStability.sensitivity
#check @PaperV.FiniteValueStability.convexHull_minimum
#print axioms PaperV.FiniteValueStability.convexHull_minimum
#check @PaperV.FiniteValueStability.continuous_minimum
#print axioms PaperV.FiniteValueStability.continuous_minimum
#check @PaperV.FiniteValueStability.dense_minimizers
#print axioms PaperV.FiniteValueStability.dense_minimizers
#check @PaperV.FiniteValueStability.exists_positive_gap
#print axioms PaperV.FiniteValueStability.exists_positive_gap
#check @PaperV.FiniteValueStability.unique_minimizer_stability
#print axioms PaperV.FiniteValueStability.unique_minimizer_stability
#check @PaperV.FiniteValueStability.unique_on_convexHull
#print axioms PaperV.FiniteValueStability.unique_on_convexHull
#check @PaperV.FiniteValueStability.stable_convexHull_minimizer
#print axioms PaperV.FiniteValueStability.stable_convexHull_minimizer

#check @PaperV.MixedPromotion.promote_rational
#print axioms PaperV.MixedPromotion.promote_rational
#check @PaperV.MixedPromotion.exists_normalized_rational
#print axioms PaperV.MixedPromotion.exists_normalized_rational
