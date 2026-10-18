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

public import PaperV.ResourceComposition
public import PaperV.HostConstructionAdapters

#check @PaperV.ResourceCertificate.System.disjoint_of_cross_resources
#print axioms PaperV.ResourceCertificate.System.disjoint_of_cross_resources
#check @PaperV.ResourceCertificate.System.packing_union
#print axioms PaperV.ResourceCertificate.System.packing_union
#check @PaperV.ResourceCertificate.System.packing_biUnion
#print axioms PaperV.ResourceCertificate.System.packing_biUnion
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
#check @PaperV.Host.exists_paired_host_completion
#print axioms PaperV.Host.exists_paired_host_completion
#check @PaperV.Host.empty_factor_completion
#print axioms PaperV.Host.empty_factor_completion
