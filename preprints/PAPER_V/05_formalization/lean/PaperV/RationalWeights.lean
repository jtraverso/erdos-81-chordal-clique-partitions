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
Paper V — Rational weights by scaling (wave 2a′, item 4).

The transfer statements are proved with weights in `ℕ`. Nonnegative rational weights `w_ℚ` have a common
denominator `d` with `w_ℚ = w/d` for integer `w`; all weighted quantities scale by `1/d`, so RCT/RDT and
the weighted transfer hold verbatim over `ℚ`:

  `|X|_{w_ℚ} ≤ q · ν_{w_ℚ}(P) + cost_ℚ`,   `|X|_{w_ℚ} ≤ q · ν_{w_ℚ}(C) + D_q^{w}/d`.

Here `ν_{w_ℚ}` is the rational packing optimum (sup over feasible sets), shown equal to `ν_w/d`.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.RealizabilityDefect

import Lean.Elab.Tactic.NormCast
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set

public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

open Finset

namespace PaperV

variable (C : ConflictSystem)

/-- Rational weighted size `Σ_o w_ℚ(o) · X(o)`. -/
def wMultSizeQ (wq : C.O → ℚ) (X : C.O → ℕ) : ℚ := ∑ o : C.O, wq o * X o

open Classical in
/-- Rational packing optimum: maximum `Σ_{o∈S} w_ℚ(o)` over feasible `S` (the empty set is feasible). -/
noncomputable def wNuQ (wq : C.O → ℚ) : ℚ :=
  (univ.filter (fun S : Finset C.O => CSFeasible C S)).sup' ⟨∅, by exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by intro a ha; exact False.elim (Finset.notMem_empty a ha)⟩⟩
    (fun S => ∑ o ∈ S, wq o)

theorem csFeasible_wsum_le_wNuQ (wq : C.O → ℚ) (T : Finset C.O) (hT : CSFeasible C T) :
    ∑ o ∈ T, wq o ≤ wNuQ C wq := by
  classical
  unfold wNuQ
  exact Finset.le_sup' (f := fun S => ∑ o ∈ S, wq o) (by simp [hT])

theorem wNuQ_le (wq : C.O → ℚ) {b : ℚ} (h : ∀ T, CSFeasible C T → ∑ o ∈ T, wq o ≤ b) :
    wNuQ C wq ≤ b := by
  classical
  unfold wNuQ
  apply Finset.sup'_le
  intro T hT
  exact h T (Finset.mem_filter.mp hT).2

/-- Scaled weights `w/d`. -/
def scaleW (w : C.O → ℕ) (d : ℕ) : C.O → ℚ := fun o => (w o : ℚ) / d

theorem wMultSizeQ_scale (w : C.O → ℕ) (d : ℕ) (X : C.O → ℕ) :
    wMultSizeQ C (scaleW C w d) X = (wMultSize C w X : ℚ) / d := by
  unfold wMultSizeQ scaleW wMultSize
  push_cast
  rw [Finset.sum_div]
  congr 1; ext o; ring

theorem wsum_scale (w : C.O → ℕ) (d : ℕ) (S : Finset C.O) :
    ∑ o ∈ S, scaleW C w d o = (∑ o ∈ S, w o : ℕ) / (d : ℚ) := by
  unfold scaleW
  push_cast
  rw [Finset.sum_div]

/-- `ν_{w/d} = ν_w / d`. -/
theorem wNuQ_scale (w : C.O → ℕ) (d : ℕ) (hd : 0 < d) :
    wNuQ C (scaleW C w d) = (wNu C w : ℚ) / d := by
  classical
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  apply le_antisymm
  · apply wNuQ_le
    intro T hT
    rw [wsum_scale]
    have := csFeasible_wsum_le_wNu C w T hT
    exact div_le_div_of_nonneg_right (by exact_mod_cast this) hdq.le
  · -- ν_w is attained by some feasible set
    unfold wNu
    obtain ⟨T, hT, hTeq⟩ := Finset.exists_mem_eq_sup
      (univ.filter (fun S : Finset C.O => CSFeasible C S)) ⟨∅, by exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by intro a ha; exact False.elim (Finset.notMem_empty a ha)⟩⟩
      (fun S => ∑ o ∈ S, w o)
    rw [hTeq]
    have hfeas : CSFeasible C T := (Finset.mem_filter.mp hT).2
    have := csFeasible_wsum_le_wNuQ C (scaleW C w d) T hfeas
    rw [wsum_scale] at this
    exact this

variable {C}
variable {P : ConflictSystem}

/-- Rational cost of a certificate: `(w(Z) + Σ r_i)/d`. -/
theorem realCert_cost_scale {w : C.O → ℕ} {wP : P.O → ℕ} {X : C.O → ℕ} {q : ℕ}
    (cert : RealCert C P w wP X q) (d : ℕ) :
    ((cert.cost : ℕ) : ℚ) / d = ((∑ c ∈ cert.Z, copyWeight C w c : ℕ) : ℚ) / d +
      ((∑ i : Fin q, (cert.real i).loss : ℕ) : ℚ) / d := by
  unfold RealCert.cost
  push_cast
  rw [add_div]

/-- **RCT over ℚ** (weights `w/d`, `w_P/d`): `|X|_{w/d} ≤ q · ν_{w_P/d}(P) + cost/d`. -/
theorem realizable_transfer_rational {w : C.O → ℕ} {wP : P.O → ℕ} {X : C.O → ℕ} {q : ℕ}
    (hq : 1 ≤ q) (cert : RealCert C P w wP X q) (d : ℕ) (hd : 0 < d) :
    wMultSizeQ C (scaleW C w d) X ≤ q * wNuQ P (scaleW P wP d) + (cert.cost : ℚ) / d := by
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have h := realizable_transfer_cert hq cert
  rw [wMultSizeQ_scale, wNuQ_scale P wP d hd]
  have h' : ((wMultSize C w X : ℕ) : ℚ) ≤ (q : ℚ) * (wNu P wP : ℚ) + (cert.cost : ℚ) := by
    exact_mod_cast h
  calc ((wMultSize C w X : ℕ) : ℚ) / d ≤ ((q : ℚ) * (wNu P wP : ℚ) + (cert.cost : ℚ)) / d :=
        div_le_div_of_nonneg_right h' hdq.le
    _ = q * ((wNu P wP : ℚ) / d) + (cert.cost : ℚ) / d := by ring

/-- **Weighted transfer over ℚ**: `|X|_{w/d} ≤ q · ν_{w/d}(C) + D_q^w(H[X])/d`. -/
theorem transfer_q_weighted_rational (w : C.O → ℕ) (X : C.O → ℕ) (q : ℕ) (hq : 1 ≤ q)
    (d : ℕ) (hd : 0 < d) :
    wMultSizeQ C (scaleW C w d) X ≤ q * wNuQ C (scaleW C w d) + (wDq C w X q : ℚ) / d := by
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have h := transfer_q_weighted C w X q hq
  rw [wMultSizeQ_scale, wNuQ_scale C w d hd]
  have h' : ((wMultSize C w X : ℕ) : ℚ) ≤ (q : ℚ) * (wNu C w : ℚ) + (wDq C w X q : ℚ) := by
    exact_mod_cast h
  calc ((wMultSize C w X : ℕ) : ℚ) / d ≤ ((q : ℚ) * (wNu C w : ℚ) + (wDq C w X q : ℚ)) / d :=
        div_le_div_of_nonneg_right h' hdq.le
    _ = q * ((wNu C w : ℚ) / d) + (wDq C w X q : ℚ) / d := by ring

/-- Every nonnegative rational weight function is a scaled integer weight function. -/
theorem exists_scaleW (wq : C.O → ℚ) (hw : ∀ o, 0 ≤ wq o) :
    ∃ (w : C.O → ℕ) (d : ℕ), 0 < d ∧ wq = scaleW C w d := by
  classical
  let d : ℕ := ∏ o : C.O, (wq o).den
  have hd : 0 < d := Finset.prod_pos (fun o _ => (wq o).den_pos)
  have hdvd : ∀ o, (wq o).den ∣ d := fun o => Finset.dvd_prod_of_mem _ (Finset.mem_univ o)
  refine ⟨fun o => (wq o * d).num.toNat, d, hd, ?_⟩
  funext o
  unfold scaleW
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  -- `wq o * d` is a nonnegative integer
  have hint : (wq o * d) = ((wq o).num * ((d / (wq o).den : ℕ) : ℤ) : ℤ) := by
    obtain ⟨k, hk⟩ := hdvd o
    have hden : ((wq o).den : ℚ) ≠ 0 := by exact_mod_cast (wq o).den_pos.ne'
    rw [hk, Nat.mul_div_cancel_left _ (wq o).den_pos]
    push_cast
    calc wq o * ((wq o).den * (k : ℚ)) = (wq o * (wq o).den) * k := by ring
      _ = ((wq o).num : ℚ) * k := by rw [Rat.mul_den_eq_num]
  have hnn : 0 ≤ (wq o).num * ((d / (wq o).den : ℕ) : ℤ) :=
    mul_nonneg (Rat.num_nonneg.mpr (hw o)) (Int.natCast_nonneg _)
  have hnum : (wq o * d).num = (wq o).num * ((d / (wq o).den : ℕ) : ℤ) := by
    rw [hint]; exact Rat.num_intCast _
  show wq o = (((wq o * d).num.toNat : ℕ) : ℚ) / d
  have hcast : ((((wq o).num * ((d / (wq o).den : ℕ) : ℤ)).toNat : ℕ) : ℚ) =
      (((wq o).num * ((d / (wq o).den : ℕ) : ℤ) : ℤ) : ℚ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
  rw [hnum, hcast, ← hint]
  field_simp

end PaperV
