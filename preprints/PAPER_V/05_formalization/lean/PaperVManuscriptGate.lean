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
public import PaperV.ManuscriptEndpoints
public import PaperV.ResourceOptimum

-- Definition 2.1
#check @PaperV.ConflictSystem
#print axioms PaperV.ConflictSystem
#check @PaperV.CSFeasible
#print axioms PaperV.CSFeasible
#check @PaperV.nu
#print axioms PaperV.nu
-- Definition 2.2
#check @PaperV.Copies
#print axioms PaperV.Copies
#check @PaperV.Hgraph
#print axioms PaperV.Hgraph
#check @PaperV.IsQMultiset
#print axioms PaperV.IsQMultiset
-- Definition 2.3
#check @PaperV.Dq
#print axioms PaperV.Dq
#check @PaperV.oct
#print axioms PaperV.oct
#check @PaperV.Dq_one_eq
#print axioms PaperV.Dq_one_eq
-- Definition 2.4
#check @PaperV.Manuscript.ResourceRelaxation
#print axioms PaperV.Manuscript.ResourceRelaxation
#check @PaperV.ResourceCertificate.System
#print axioms PaperV.ResourceCertificate.System
#check @PaperV.ResourceCertificate.System.incidence
#print axioms PaperV.ResourceCertificate.System.incidence
-- Definition 2.5
#check @PaperV.Manuscript.ResourceRelaxation
#print axioms PaperV.Manuscript.ResourceRelaxation
#check @PaperV.Manuscript.ResourceRelaxation.Optimum
#print axioms PaperV.Manuscript.ResourceRelaxation.Optimum
-- Lemma 3.1
#check @PaperV.splitting
#print axioms PaperV.splitting
-- Corollary 3.2
#check @PaperV.nu_ge_ceil
#print axioms PaperV.nu_ge_ceil
-- Corollary 3.2a
#check @PaperV.cover_witness_defect
#print axioms PaperV.cover_witness_defect
#check @PaperV.triangle_cover_defect
#print axioms PaperV.triangle_cover_defect
-- Corollary 3.2b
#check @PaperV.Manuscript.minimum_coloring_rigidity_iff
#print axioms PaperV.Manuscript.minimum_coloring_rigidity_iff
-- Theorem 3.3
#check @PaperV.Manuscript.resource_half_integral_transfer
#print axioms PaperV.Manuscript.resource_half_integral_transfer
-- Theorem 3.4
#check @PaperV.Manuscript.resource_integral_transfer
#print axioms PaperV.Manuscript.resource_integral_transfer
-- Theorem 3.4w
#check @PaperV.transfer_q_weighted
#print axioms PaperV.transfer_q_weighted
-- Lemma 3.5
#check @PaperV.parity_localization
#print axioms PaperV.parity_localization
-- Definition 4.1
#check @PaperV.ClassRealizer
#print axioms PaperV.ClassRealizer
#check @PaperV.RealCert
#print axioms PaperV.RealCert
#check @PaperV.RealCert.cost
#print axioms PaperV.RealCert.cost
-- Theorem 4.2
#check @PaperV.realizable_class_transfer
#print axioms PaperV.realizable_class_transfer
#check @PaperV.realizable_transfer_cert
#print axioms PaperV.realizable_transfer_cert
-- Definition 4.3
#check @PaperV.wRDq
#print axioms PaperV.wRDq
-- Theorem 4.4
#check @PaperV.wRDq_identity_eq_wDq
#print axioms PaperV.wRDq_identity_eq_wDq
#check @PaperV.wRDq_le_wDq
#print axioms PaperV.wRDq_le_wDq
-- Example 4.5
#check @PaperV.StarExample.intermediate_defect
#print axioms PaperV.StarExample.intermediate_defect
-- Corollary 4.6
#check @PaperV.ResourceCertificate.two_error_real_optimum
#print axioms PaperV.ResourceCertificate.two_error_real_optimum
#check @PaperV.ResourceCertificate.resource_gap_identity
#print axioms PaperV.ResourceCertificate.resource_gap_identity
#check @PaperV.ResourceCertificate.exists_real_optimum
#print axioms PaperV.ResourceCertificate.exists_real_optimum
-- Proposition 5.1
#check @PaperV.Host.csFeasible_hostCS_of_properOn
#print axioms PaperV.Host.csFeasible_hostCS_of_properOn
-- Theorem 5.2
#check @PaperV.Galvin.galvin_multigraph_max_degree
#print axioms PaperV.Galvin.galvin_multigraph_max_degree
#check @PaperV.Galvin.galvin_bkw_local
#print axioms PaperV.Galvin.galvin_bkw_local
-- Corollary 5.3
#check @PaperV.Host.galvin_host_completion_exact
#print axioms PaperV.Host.galvin_host_completion_exact
#check @PaperV.Host.bkw_host_completion_exact
#print axioms PaperV.Host.bkw_host_completion_exact
#check @PaperV.Host.galvin_lifted_transfer
#print axioms PaperV.Host.galvin_lifted_transfer
#check @PaperV.Host.galvin_local_lifted_transfer
#print axioms PaperV.Host.galvin_local_lifted_transfer
-- Example 5.5
#check @PaperV.Strictness.strict_separation
#print axioms PaperV.Strictness.strict_separation
#check @PaperV.Strictness.nu_hostCS_kr
#print axioms PaperV.Strictness.nu_hostCS_kr
-- Subsidiary Claim 6.1a
#check @PaperV.copy_integral_edgeLoad_le_two
#print axioms PaperV.copy_integral_edgeLoad_le_two
-- Theorem 6.1
#check @PaperV.copy_fractional
#print axioms PaperV.copy_fractional
-- Theorem 6.2
#check @PaperV.copy_integral
#print axioms PaperV.copy_integral
-- Lemma 6.2k
#check @PaperV.third_subset_union
#print axioms PaperV.third_subset_union
#check @PaperV.k4_of_three_triangles
#print axioms PaperV.k4_of_three_triangles
#check @PaperV.triCS_clique_card_le_four
#print axioms PaperV.triCS_clique_card_le_four
-- Corollary 6.2a
#check @PaperV.copy_triple_bound
#print axioms PaperV.copy_triple_bound
#check @PaperV.tight_oct
#print axioms PaperV.tight_oct
-- Proposition 7.1
#check @PaperV.PureProfile.prop43_nu
#print axioms PaperV.PureProfile.prop43_nu
#check @PaperV.PureProfile.prop43_muMat
#print axioms PaperV.PureProfile.prop43_muMat
-- Proposition 7.1a
#check @PaperV.PureProfile.nu_ge_frac_muMatDeg
#print axioms PaperV.PureProfile.nu_ge_frac_muMatDeg
#check @PaperV.PureProfile.nu_ge_two_thirds_muMatDeg
#print axioms PaperV.PureProfile.nu_ge_two_thirds_muMatDeg
#check @PaperV.PureProfile.nu_ge_muMatDeg_two
#print axioms PaperV.PureProfile.nu_ge_muMatDeg_two
-- Proposition 7.1b
#check @PaperV.PureProfile.muMatDeg_eq_min
#print axioms PaperV.PureProfile.muMatDeg_eq_min
#check @PaperV.PureProfile.nu_eq_muMatDeg_of_even
#print axioms PaperV.PureProfile.nu_eq_muMatDeg_of_even
#check @PaperV.PureProfile.nu_eq_frac_muMatDeg_of_odd
#print axioms PaperV.PureProfile.nu_eq_frac_muMatDeg_of_odd
-- Theorem 7.3
#check @PaperV.Mixed.mixed_copy_fractional
#print axioms PaperV.Mixed.mixed_copy_fractional
#check @PaperV.mixed_copy_integral_opt
#print axioms PaperV.mixed_copy_integral_opt
-- Corollary 7.3a
#check @PaperV.Mixed.mixed_copy_integral_of_roundingGap
#print axioms PaperV.Mixed.mixed_copy_integral_of_roundingGap
-- Proposition 8.1
#check @PaperV.feasible_run
#print axioms PaperV.feasible_run
#check @PaperV.SealBridge.sealFeasible_of_properOn
#print axioms PaperV.SealBridge.sealFeasible_of_properOn
-- Proposition 8.2
#check @PaperV.accepted_repairs_le_cov
#print axioms PaperV.accepted_repairs_le_cov
#check @PaperV.accepted_repairs_le_audit
#print axioms PaperV.accepted_repairs_le_audit
-- Theorem 8.3
#check @PaperV.SealBridge.seal_galvin_regime
#print axioms PaperV.SealBridge.seal_galvin_regime
#check @PaperV.SealBridge.seal_bkw_regime
#print axioms PaperV.SealBridge.seal_bkw_regime
#check @PaperV.SealBridge.seal_konig_guarantee
#print axioms PaperV.SealBridge.seal_konig_guarantee
-- Proposition 9.3
#check @PaperV.Steiner.exists_quadratic_defect_frac
#print axioms PaperV.Steiner.exists_quadratic_defect_frac

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
