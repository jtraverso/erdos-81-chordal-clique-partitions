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

public import PaperV.FractionalOptimum
import Lean.Elab.Tactic.NormCast
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

@[expose] public section

/-!
# Paper V: integral formula with nonnegative rational weights and the conserved gap

The existing natural-weight theorem `PaperV.UnitBoundary.Weighted.weighted_optimum_eq` is
transported to nonnegative rational weights by a proved common-denominator argument
(`exists_common_denom`, `piW_scale`, `packW_scale`, `redW_scale`).  Combined with the fractional
identity this gives `Wstar - W = Wredstar - Wred` for the actual resource packing problem and the
actual (rational or real) resource LP.
-/

open Finset Classical

namespace PaperV
namespace FractionalUnitBoundary

open UnitBoundary UnitBoundary.Weighted ResourceCertificate System

variable {I E : Type*} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]

/-! ### Integral optima with rational weights -/

section Defs

variable (R : System I E) (Q D : Finset I) (S : Finset E) (w : I → ℚ)

omit [DecidableEq I] in
theorem packing_empty : R.Packing ∅ := fun a ha => absurd ha (Finset.notMem_empty a)

theorem packFams_nonempty (U : Finset I) : (U.powerset.filter R.Packing).Nonempty :=
  ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset U, packing_empty R⟩⟩

/-- `W`: the maximum rational weight of an actual resource packing (all objects). -/
noncomputable def packW : ℚ :=
  ((Finset.univ : Finset I).powerset.filter R.Packing).sup' (packFams_nonempty R _) (R.gain w)

/-- `Wred`: the maximum signed reduced weight of an actual central resource packing. -/
noncomputable def redW : ℚ :=
  (D.powerset.filter R.Packing).sup' (packFams_nonempty R D)
    (fun C => ∑ d ∈ C, wred R.resources Q S w d)

end Defs

variable {R : System I E} {Q D : Finset I} {S : Finset E} {w : I → ℚ}

theorem le_packW {P : Finset I} (hP : R.Packing P) : R.gain w P ≤ packW R w :=
  Finset.le_sup' (R.gain w) (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ P), hP⟩)

theorem exists_packW : ∃ P, R.Packing P ∧ R.gain w P = packW R w := by
  obtain ⟨P, hP, h⟩ := Finset.exists_mem_eq_sup' (packFams_nonempty R Finset.univ) (R.gain w)
  exact ⟨P, (Finset.mem_filter.mp hP).2, h.symm⟩

theorem le_redW {C : Finset I} (hC : C ⊆ D) (hP : R.Packing C) :
    ∑ d ∈ C, wred R.resources Q S w d ≤ redW R Q D S w :=
  Finset.le_sup' (fun C => ∑ d ∈ C, wred R.resources Q S w d)
    (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hC, hP⟩)

theorem exists_redW : ∃ C ⊆ D, R.Packing C ∧ ∑ d ∈ C, wred R.resources Q S w d = redW R Q D S w := by
  obtain ⟨C, hC, h⟩ := Finset.exists_mem_eq_sup' (packFams_nonempty R D)
    (fun C => ∑ d ∈ C, wred R.resources Q S w d)
  obtain ⟨hC1, hC2⟩ := Finset.mem_filter.mp hC
  exact ⟨C, Finset.mem_powerset.mp hC1, hC2, h.symm⟩

/-! ### Common denominator -/

omit [DecidableEq I] in
/-- Nonnegative rational weights have a common denominator. -/
theorem exists_common_denom (w : I → ℚ) (hw : ∀ o, 0 ≤ w o) :
    ∃ q : ℕ, 0 < q ∧ ∃ n : I → ℕ, ∀ o, (n o : ℚ) = q * w o := by
  refine ⟨∏ o, (w o).den, Finset.prod_pos (fun o _ => (w o).den_pos), ?_⟩
  have h : ∀ o, ∃ k : ℕ, (k : ℚ) = (∏ o, (w o).den : ℕ) * w o := by
    intro o
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun o => (w o).den) (Finset.mem_univ o)
    refine ⟨m * (w o).num.toNat, ?_⟩
    have h1 : (((w o).num.toNat : ℤ) : ℚ) = (w o).num := by
      rw [Int.toNat_of_nonneg (Rat.num_nonneg.mpr (hw o))]
    rw [hm]
    push_cast
    rw [show (((w o).num.toNat : ℕ) : ℚ) = (((w o).num.toNat : ℤ) : ℚ) by norm_cast, h1,
      ← Rat.mul_den_eq_num]
    ring
  choose n hn using h
  exact ⟨n, hn⟩

section Scale

variable {q : ℕ} {n : I → ℕ} (hq : 0 < q) (hn : ∀ o, (n o : ℚ) = q * w o)
include hq hn

omit [Fintype I] [DecidableEq I] in
theorem w_eq_div (o : I) : w o = n o / q := by
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [hn o]; field_simp

theorem piW_scale (e : E) : (aW R.resources Q S n e : ℚ) = q * piW R.resources Q S w e := by
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  have hw : ∀ o, 0 ≤ w o := fun o => by
    have := w_eq_div hq hn o; rw [this]; positivity
  by_cases h : (Rep R.resources Q S e).Nonempty
  · obtain ⟨o, ho, hmax⟩ := Finset.exists_mem_eq_sup _ h n
    apply le_antisymm
    · have : aW R.resources Q S n e = n o := hmax
      rw [this, hn o]
      exact mul_le_mul_of_nonneg_left (le_piW ho) hq'.le
    · rw [← le_div_iff₀' hq']
      apply piW_le (by positivity)
      intro o' ho'
      rw [w_eq_div hq hn o']
      exact div_le_div_of_nonneg_right (by exact_mod_cast le_aW ho' n) hq'.le
  · have h0 := Finset.not_nonempty_iff_eq_empty.mp h
    rw [aW_eq_zero_of_empty n h0, piW_eq_zero h0]
    simp

theorem wmod_scale (d : I) : (wmod R.resources Q S n d : ℚ) = q * wred R.resources Q S w d := by
  unfold wmod wred
  push_cast
  rw [mul_sub, Finset.mul_sum, hn d]
  congr 1
  exact Finset.sum_congr rfl (fun e _ => piW_scale hq hn e)

omit [DecidableEq I] hq in
theorem wt_scale (P : Finset I) : (wt n P : ℚ) = q * R.gain w P := by
  unfold wt System.gain
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun o _ => hn o)

theorem wmodSum_scale (C : Finset I) :
    (wmodSum R.resources Q S n C : ℚ) = q * ∑ d ∈ C, wred R.resources Q S w d := by
  unfold wmodSum
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun d _ => wmod_scale hq hn d)

theorem packW_scale : (wOpt R.resources n Finset.univ : ℚ) = q * packW R w := by
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  apply le_antisymm
  · obtain ⟨P, _, hf, hP⟩ := exists_wOpt R.resources n Finset.univ
    rw [← hP, wt_scale (R := R) hn]
    exact mul_le_mul_of_nonneg_left (le_packW hf) hq'.le
  · obtain ⟨P, hf, hP⟩ := exists_packW (R := R) (w := w)
    rw [← hP, ← wt_scale (R := R) hn]
    exact_mod_cast le_wOpt R.resources n (Finset.subset_univ P) hf

theorem redW_scale : (centralOpt R.resources Q D S n : ℚ) = q * redW R Q D S w := by
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  apply le_antisymm
  · obtain ⟨C, hC, hf, hP⟩ := exists_centralOpt (res := R.resources) (Q := Q) (D := D) (SR := S) n
    rw [← hP, wmodSum_scale hq hn]
    exact mul_le_mul_of_nonneg_left (le_redW hC hf) hq'.le
  · obtain ⟨C, hC, hf, hP⟩ := exists_redW (R := R) (Q := Q) (D := D) (S := S) (w := w)
    rw [← hP, ← wmodSum_scale hq hn]
    exact_mod_cast wmodSum_le_centralOpt hC hf n

end Scale

/-! ### Result 4: the integral formula over nonnegative rationals -/

theorem integral_formula_of_isEmpty [IsEmpty I] :
    packW R w = B0 R.resources Q S w + redW R Q D S w := by
  have hU : ∀ U : Finset I, U = ∅ := fun U => Finset.eq_empty_of_isEmpty U
  have h1 : packW R w = 0 := by
    obtain ⟨P, _, hP⟩ := exists_packW (R := R) (w := w)
    rw [← hP, hU P]; simp [System.gain]
  have h2 : redW R Q D S w = 0 := by
    obtain ⟨C, _, _, hC⟩ := exists_redW (R := R) (Q := Q) (D := D) (S := S) (w := w)
    rw [← hC, hU C]; simp
  have h3 : B0 R.resources Q S w = 0 := by
    unfold B0
    rw [hU (Z R.resources Q S), Finset.sum_empty, zero_add]
    exact Finset.sum_eq_zero (fun e _ => piW_eq_zero (hU _))
  rw [h1, h2, h3]; ring

/-- **Result 4 (integral formula).** For nonnegative rational weights, the actual maximum-weight
resource packing satisfies `W = B0 + Wred`. -/
theorem integral_formula (cfg : Config R.resources Q D S) (hQD : ∀ o, o ∈ Q ∨ o ∈ D)
    (hw : ∀ o, 0 ≤ w o) : packW R w = B0 R.resources Q S w + redW R Q D S w := by
  rcases isEmpty_or_nonempty I with hI | hI
  · exact integral_formula_of_isEmpty
  · haveI : Inhabited I := Classical.inhabited_of_nonempty hI
    obtain ⟨q, hq, n, hn⟩ := exists_common_denom w hw
    obtain ⟨wr⟩ := exists_wreps R.resources Q S n
    have hE := weighted_optimum_eq cfg wr
    have huniv : Q ∪ D = Finset.univ := by
      ext o; simp only [Finset.mem_univ, Finset.mem_union, iff_true]; exact hQD o
    rw [huniv] at hE
    have hE' : (wOpt R.resources n Finset.univ : ℚ) =
        (wt n (Z R.resources Q S) : ℚ) + ((∑ b ∈ S, aW R.resources Q S n b : ℕ) : ℚ) +
          (centralOpt R.resources Q D S n : ℚ) := by
      exact_mod_cast hE
    rw [packW_scale hq hn, wt_scale (R := R) hn, redW_scale hq hn] at hE'
    push_cast at hE'
    simp only [piW_scale hq hn] at hE'
    rw [← Finset.mul_sum] at hE'
    have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
    have : (q : ℚ) * packW R w = q * (B0 R.resources Q S w + redW R Q D S w) := by
      rw [hE']; unfold B0 System.gain; ring
    exact mul_left_cancel₀ hq' this

/-- **Result 4 (conserved gap, rational LP).** For any optimal rational full vector `p` and any
optimal rational central vector `u`: `Wstar - W = Wredstar - Wred`. -/
theorem conserved_gap (cfg : Config R.resources Q D S) (hQD : ∀ o, o ∈ Q ∨ o ∈ D)
    (hw : ∀ o, 0 ≤ w o) (p : FiniteLP.PrimalFeasible R.incidence)
    (hp : ∀ p' : FiniteLP.PrimalFeasible R.incidence,
      FiniteLP.primalValue w p' ≤ FiniteLP.primalValue w p)
    (u : FiniteLP.PrimalFeasible (centralInc D S R.incidence))
    (hu : ∀ u' : FiniteLP.PrimalFeasible (centralInc D S R.incidence),
      FiniteLP.primalValue (centralGain R.resources Q D S w) u' ≤
        FiniteLP.primalValue (centralGain R.resources Q D S w) u) :
    FiniteLP.primalValue w p - packW R w =
      FiniteLP.primalValue (centralGain R.resources Q D S w) u - redW R Q D S w := by
  rw [opt_value_eq cfg hQD (isIncidence_rat R) hw p hp u hu, integral_formula cfg hQD hw]
  ring

/-- **Result 4 (conserved gap, real LP).** For any optimal real full vector and any optimal real
central vector: `Wstar - W = Wredstar - Wred`. -/
theorem conserved_gap_real (cfg : Config R.resources Q D S) (hQD : ∀ o, o ∈ Q ∨ o ∈ D)
    (hw : ∀ o, 0 ≤ w o) (pR : FiniteLP.PrimalFeasible (realIncidence R))
    (hpR : ∀ p' : FiniteLP.PrimalFeasible (realIncidence R),
      FiniteLP.primalValue (fun o => (w o : ℝ)) p' ≤ FiniteLP.primalValue (fun o => (w o : ℝ)) pR)
    (uR : FiniteLP.PrimalFeasible (centralInc D S (realIncidence R)))
    (huR : ∀ u' : FiniteLP.PrimalFeasible (centralInc D S (realIncidence R)),
      FiniteLP.primalValue (centralGain R.resources Q D S (fun o => (w o : ℝ))) u' ≤
        FiniteLP.primalValue (centralGain R.resources Q D S (fun o => (w o : ℝ))) uR) :
    FiniteLP.primalValue (fun o => (w o : ℝ)) pR - ((packW R w : ℚ) : ℝ) =
      FiniteLP.primalValue (centralGain R.resources Q D S (fun o => (w o : ℝ))) uR -
        ((redW R Q D S w : ℚ) : ℝ) := by
  rw [real_opt_value_eq cfg hQD hw pR hpR uR huR, integral_formula cfg hQD hw]
  push_cast
  ring

end FractionalUnitBoundary
end PaperV
