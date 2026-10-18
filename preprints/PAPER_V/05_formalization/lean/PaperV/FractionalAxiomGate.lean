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

public import PaperV.FractionalIntegral

@[expose] public section

/-! Axiom gate for the fractional unit-boundary development: each line must report only
`propext`, `Classical.choice`, `Quot.sound`. -/

open PaperV.FractionalUnitBoundary

#check @extend
#print axioms extend
#check @extend_central
#print axioms extend_central
#check @extend_Z
#print axioms extend_Z
#check @extend_value
#print axioms extend_value
#check @restrict
#print axioms restrict
#check @value_le_restrict
#print axioms value_le_restrict
#check @opt_value_eq
#print axioms opt_value_eq
#check @privRes_injOn
#print axioms privRes_injOn
#check @liftDual
#print axioms liftDual
#check @liftPrice_shared
#print axioms liftPrice_shared
#check @liftPrice_chosen
#print axioms liftPrice_chosen
#check @liftPrice_other
#print axioms liftPrice_other
#check @liftDual_value
#print axioms liftDual_value
#check @lifted_gap_eq
#print axioms lifted_gap_eq
#check @rat_optimum
#print axioms rat_optimum
#check @exists_rat_full_optimum
#print axioms exists_rat_full_optimum
#check @exists_rat_central_optimum
#print axioms exists_rat_central_optimum
#check @real_optimum
#print axioms real_optimum
#check @real_opt_value_eq
#print axioms real_opt_value_eq
#check @real_full_opt_eq_rat
#print axioms real_full_opt_eq_rat
#check @real_central_opt_eq_rat
#print axioms real_central_opt_eq_rat
#check @exists_common_denom
#print axioms exists_common_denom
#check @integral_formula
#print axioms integral_formula
#check @conserved_gap
#print axioms conserved_gap
#check @conserved_gap_real
#print axioms conserved_gap_real
