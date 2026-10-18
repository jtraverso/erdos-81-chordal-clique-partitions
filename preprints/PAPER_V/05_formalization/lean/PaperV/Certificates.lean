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
Paper IV — §5.1 a posteriori upper-bound certificates.

The manuscript's §5.1 is a weak-duality / relaxation statement: for ANY feasible packing `R`,
`|R| ≤ ν ≤ ⌊μ*_mat⌋`, because the master matching LP is a relaxation and `ν` is an integer;
`β̂_LP := ⌊μ*_mat⌋ − |R|` bounds `ν − |R|`, and `β̂_LP = 0` certifies `R` maximum. A
solver-independent dual value `U ≥ μ*_mat` gives `ν ≤ ⌊U⌋`, and `|R| = ⌊U⌋` certifies optimality.

We formalise this at the level of a `ConflictSystem`: the only property of `μ*_mat` (or of a dual
value `U`) that the certificate uses is that it upper-bounds the size of every feasible object set
(that is exactly what "relaxation" / "dual-feasible" provides). This is faithful to the paper's
argument, which invokes nothing about the LP beyond `ν ≤ μ*_mat`.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.ConflictGraph

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Set

public import Mathlib.Data.Rat.Floor

@[expose] public section

open Finset

namespace PaperV

variable {C : ConflictSystem}

/-- The independence number bounds every feasible object set. -/
theorem card_le_nu {R : Finset C.O} (hR : CSFeasible C R) : R.card ≤ nu C := by
  classical
  apply Finset.le_sup (f := Finset.card)
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hR⟩

/-- The independence number is attained by some feasible object set. -/
theorem exists_nu_witness : ∃ R : Finset C.O, CSFeasible C R ∧ R.card = nu C := by
  classical
  have hne : (univ.filter (fun S : Finset C.O => CSFeasible C S)).Nonempty := by
    refine ⟨∅, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by intro a ha; simp at ha⟩
  obtain ⟨M, hM, hMeq⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  rw [Finset.mem_filter] at hM
  exact ⟨M, hM.2, hMeq.symm⟩

/-- **§5.1 LP certificate.** If `U` upper-bounds the size of every feasible object set (e.g.
`U = μ*_mat`, a relaxation optimum, or any dual-feasible value), then for every feasible packing
`R`: `|R| ≤ ν ≤ ⌊U⌋`, and `⌊U⌋ = |R|` certifies that `R` is maximum. -/
theorem apost_certificate {U : ℚ}
    (hU : ∀ S : Finset C.O, CSFeasible C S → (S.card : ℚ) ≤ U)
    {R : Finset C.O} (hR : CSFeasible C R) :
    (R.card ≤ nu C) ∧ ((nu C : ℤ) ≤ ⌊U⌋) ∧ (⌊U⌋ = (R.card : ℤ) → R.card = nu C) := by
  have h1 : R.card ≤ nu C := card_le_nu hR
  obtain ⟨M, hMfeas, hMeq⟩ := exists_nu_witness (C := C)
  have hMU : (M.card : ℚ) ≤ U := hU M hMfeas
  have h2 : (nu C : ℤ) ≤ ⌊U⌋ := by
    rw [Int.le_floor]
    rw [← hMeq]
    push_cast
    exact_mod_cast hMU
  refine ⟨h1, h2, ?_⟩
  intro hfloor
  have : (R.card : ℤ) ≤ (nu C : ℤ) := by exact_mod_cast h1
  omega

end PaperV
