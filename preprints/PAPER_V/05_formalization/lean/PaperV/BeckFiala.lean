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

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.Interval.Finset.Nat

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-!
Beck–Fiala integer-making (the discrepancy input to P4-133). Set system given by a 0/1
incidence matrix `A : Fin m → Fin N → ℤ` where each COLUMN (element) has at most `t` ones
(element degree ≤ t). Given a fractional `x : Fin N → ℚ` with `0 ≤ x i ≤ 1`, there is an
integral `y : Fin N → ℤ` with `y i ∈ {0,1}` such that every row-discrepancy is `< t`:
`|∑ i, A j i * (y i - x i)| < t`. (Classical Beck–Fiala; `f(t) ≤ t-1`. Not in Mathlib.)
-/

open Finset

namespace BeckFiala

variable {m N : ℕ}

/-- The set of *floating* coordinates of `x`: those strictly between `0` and `1`. -/
def Floating (x : Fin N → ℚ) : Finset (Fin N) :=
  univ.filter (fun i => 0 < x i ∧ x i < 1)

/-- The *floating degree* of row `j`: the number of floating coordinates in that row. -/
def fdeg (A : Fin m → Fin N → ℤ) (x : Fin N → ℚ) (j : Fin m) : ℕ :=
  ((Floating x).filter (fun i => A j i = 1)).card

lemma mem_Floating {x : Fin N → ℚ} {i : Fin N} :
    i ∈ Floating x ↔ 0 < x i ∧ x i < 1 := by
  simp [Floating]

/-- A coordinate that is not floating and lies in `[0,1]` is `0` or `1`. -/
lemma eq_zero_or_one_of_not_floating {x : Fin N → ℚ} {i : Fin N}
    (hx : 0 ≤ x i ∧ x i ≤ 1) (h : i ∉ Floating x) : x i = 0 ∨ x i = 1 := by
  rw [mem_Floating] at h
  push_neg at h
  rcases lt_or_eq_of_le hx.1 with h0 | h0
  · exact Or.inr (le_antisymm hx.2 (h h0))
  · exact Or.inl h0.symm

/-! ### Slack rows: the direct discrepancy bound -/

/-- If `y` is a `0/1` vector agreeing with `x` off the floating set, then on a row whose
floating degree is at most `t` (a *slack* row) the discrepancy is `< t`. -/
lemma slack_row_bound {t : ℕ} (ht : 1 ≤ t) (A : Fin m → Fin N → ℤ)
    (hA : ∀ j i, A j i = 0 ∨ A j i = 1) (x : Fin N → ℚ)
    (y : Fin N → ℤ) (hy01 : ∀ i, y i = 0 ∨ y i = 1)
    (hagree : ∀ i ∉ Floating x, (y i : ℚ) = x i) (j : Fin m) (hj : fdeg A x j ≤ t) :
    |∑ i, (A j i : ℚ) * ((y i : ℚ) - x i)| < (t : ℚ) := by
  classical
  have htQ : (1 : ℚ) ≤ (t : ℚ) := by exact_mod_cast ht
  set S := (Floating x).filter (fun i => A j i = 1) with hS
  have hScard : (S.card : ℚ) ≤ (t : ℚ) := by
    have : S.card ≤ t := hj
    exact_mod_cast this
  have hsum : ∑ i, (A j i : ℚ) * ((y i : ℚ) - x i) = ∑ i ∈ S, ((y i : ℚ) - x i) := by
    rw [← Finset.sum_subset (Finset.subset_univ S)]
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      have h1 : A j i = 1 := (Finset.mem_filter.mp hi).2
      rw [h1]; push_cast; ring
    · intro i _ hi
      simp only [hS, Finset.mem_filter, not_and] at hi
      by_cases hfl : i ∈ Floating x
      · have h0 : A j i = 0 := (hA j i).resolve_right (hi hfl)
        rw [h0]; simp
      · rw [hagree i hfl]; ring
  rw [hsum]
  rcases S.eq_empty_or_nonempty with he | hne
  · rw [he]
    simpa using lt_of_lt_of_le zero_lt_one htQ
  · have hterm : ∀ i ∈ S, |(y i : ℚ) - x i| < 1 := by
      intro i hi
      have hfl : i ∈ Floating x := (Finset.mem_filter.mp hi).1
      rw [mem_Floating] at hfl
      rcases hy01 i with h | h <;> rw [h] <;> push_cast <;> rw [abs_lt] <;>
        constructor <;> linarith [hfl.1, hfl.2]
    calc |∑ i ∈ S, ((y i : ℚ) - x i)| ≤ ∑ i ∈ S, |(y i : ℚ) - x i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ < ∑ _i ∈ S, (1 : ℚ) := Finset.sum_lt_sum_of_nonempty hne hterm
      _ = (S.card : ℚ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (t : ℚ) := hScard

/-! ### The counting lemma: `#tight < #floating` -/

/-- Double counting: `(t+1) * #tight ≤ t * #floating`. -/
lemma tight_card_mul_le {t : ℕ} (A : Fin m → Fin N → ℤ)
    (hdeg : ∀ i, (univ.filter (fun j => A j i = 1)).card ≤ t) (x : Fin N → ℚ) :
    (univ.filter (fun j => t < fdeg A x j)).card * (t + 1) ≤ (Floating x).card * t := by
  classical
  set F := Floating x with hF
  set T := univ.filter (fun j => t < fdeg A x j) with hT
  have key : ∀ j ∈ T, t + 1 ≤ fdeg A x j := by
    intro j hj
    simp only [hT, mem_filter, mem_univ, true_and] at hj
    omega
  have h2 : ∑ j ∈ T, fdeg A x j = ∑ i ∈ F, (T.filter (fun j => A j i = 1)).card := by
    simp only [fdeg, Finset.card_filter, ← hF]
    exact Finset.sum_comm
  have h3 : ∀ i ∈ F, (T.filter (fun j => A j i = 1)).card ≤ t := by
    intro i _
    refine le_trans (card_le_card ?_) (hdeg i)
    intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj ⊢
    exact hj.2
  calc T.card * (t + 1) = ∑ _j ∈ T, (t + 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ j ∈ T, fdeg A x j := Finset.sum_le_sum key
    _ = ∑ i ∈ F, (T.filter (fun j => A j i = 1)).card := h2
    _ ≤ ∑ _i ∈ F, t := Finset.sum_le_sum h3
    _ = F.card * t := by rw [Finset.sum_const, smul_eq_mul]

/-- The number of tight rows is strictly smaller than the number of floating variables. -/
lemma tight_card_lt {t : ℕ} (A : Fin m → Fin N → ℤ)
    (hdeg : ∀ i, (univ.filter (fun j => A j i = 1)).card ≤ t) (x : Fin N → ℚ)
    (hne : (Floating x).Nonempty) :
    (univ.filter (fun j => t < fdeg A x j)).card < (Floating x).card := by
  have h := tight_card_mul_le A hdeg x
  have hpos : 0 < (Floating x).card := card_pos.mpr hne
  by_contra hcon
  push_neg at hcon
  nlinarith [Nat.mul_le_mul_right (t + 1) hcon]

/-! ### The null-space step -/

/-- An underdetermined homogeneous system has a nonzero solution supported on `F`. -/
lemma exists_nullvec (A : Fin m → Fin N → ℤ) (F : Finset (Fin N)) (T : Finset (Fin m))
    (hcard : T.card < F.card) :
    ∃ v : Fin N → ℚ, (∀ i ∉ F, v i = 0) ∧ (∃ i ∈ F, v i ≠ 0) ∧
      ∀ j ∈ T, ∑ i, (A j i : ℚ) * v i = 0 := by
  classical
  -- the linear map `ℚ^F → ℚ^T` given by the tight rows of `A`
  let L : ({i // i ∈ F} → ℚ) →ₗ[ℚ] ({j // j ∈ T} → ℚ) :=
    { toFun := fun w j => ∑ i : {i // i ∈ F}, (A j.1 i.1 : ℚ) * w i
      map_add' := by
        intro w1 w2; funext j
        simp only [Pi.add_apply, mul_add]
        rw [Finset.sum_add_distrib]
      map_smul' := by
        intro c w; funext j
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring) }
  -- since `#T < #F`, `L` cannot be injective
  have hninj : ¬ Function.Injective L := by
    intro hinj
    have h1 := LinearMap.finrank_le_finrank_of_injective (f := L) hinj
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at h1
    simp only [Fintype.card_coe] at h1
    omega
  obtain ⟨w1, w2, hEq, hne⟩ := Function.not_injective_iff.mp hninj
  refine ⟨fun i => if h : i ∈ F then (w1 - w2) ⟨i, h⟩ else 0, ?_, ?_, ?_⟩
  · intro i hi; simp [hi]
  · have hwne : w1 - w2 ≠ 0 := sub_ne_zero.mpr hne
    obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hwne
    exact ⟨i0.1, i0.2, by simpa using hi0⟩
  · intro j hj
    have hw0 : L (w1 - w2) = 0 := by rw [map_sub, hEq, sub_self]
    have hzero := congrFun hw0 ⟨j, hj⟩
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hzero
    calc ∑ i, (A j i : ℚ) * (if h : i ∈ F then (w1 - w2) ⟨i, h⟩ else 0)
        = ∑ i ∈ F, (A j i : ℚ) * (if h : i ∈ F then (w1 - w2) ⟨i, h⟩ else 0) :=
          (Finset.sum_subset (Finset.subset_univ F) (by intro i _ hi; simp [hi])).symm
      _ = ∑ i ∈ F.attach, (A j i.1 : ℚ) * (w1 - w2) i := by
          rw [← Finset.sum_attach F
            (fun i => (A j i : ℚ) * (if h : i ∈ F then (w1 - w2) ⟨i, h⟩ else 0))]
          exact Finset.sum_congr rfl (fun i _ => by simp [i.2])
      _ = 0 := hzero

/-- Walking along a direction `v` supported on the floating set until a coordinate hits
`0` or `1`. -/
lemma exists_step_along (x : Fin N → ℚ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (F : Finset (Fin N)) (hF : ∀ i ∈ F, 0 < x i ∧ x i < 1)
    (v : Fin N → ℚ) (hv0 : ∀ i ∉ F, v i = 0) (i0 : Fin N) (hi0 : i0 ∈ F) (hvi0 : v i0 ≠ 0) :
    ∃ s : ℚ, 0 < s ∧ (∀ i, 0 ≤ x i + s * v i ∧ x i + s * v i ≤ 1) ∧
      ∃ i ∈ F, x i + s * v i = 0 ∨ x i + s * v i = 1 := by
  classical
  set G := F.filter (fun i => v i ≠ 0) with hG
  have hGne : G.Nonempty := ⟨i0, by simp [hG, hi0, hvi0]⟩
  set b : Fin N → ℚ := fun i => if 0 < v i then (1 - x i) / v i else (-x i) / v i with hb
  set s := G.inf' hGne b with hsdef
  have hmemG : ∀ i ∈ G, i ∈ F ∧ v i ≠ 0 := by
    intro i hi; simpa [hG] using mem_filter.mp hi
  have hbpos : ∀ i ∈ G, 0 < b i := by
    intro i hi
    obtain ⟨hiF, hvne⟩ := hmemG i hi
    obtain ⟨h0, h1⟩ := hF i hiF
    by_cases hv : 0 < v i
    · simp only [hb, if_pos hv]
      exact div_pos (by linarith) hv
    · have hvneg : v i < 0 := lt_of_le_of_ne (not_lt.mp hv) hvne
      simp only [hb, if_neg hv]
      exact div_pos_iff.mpr (Or.inr ⟨by linarith, hvneg⟩)
  have hs : 0 < s := (Finset.lt_inf'_iff hGne).mpr hbpos
  have hsle : ∀ i ∈ G, s ≤ b i := fun i hi => Finset.inf'_le b hi
  have hrange : ∀ i, 0 ≤ x i + s * v i ∧ x i + s * v i ≤ 1 := by
    intro i
    by_cases hvz : v i = 0
    · simp [hvz]; exact hx i
    · have hiF : i ∈ F := by by_contra h; exact hvz (hv0 i h)
      have hiG : i ∈ G := by simp [hG, hiF, hvz]
      obtain ⟨h0, h1⟩ := hF i hiF
      have hle := hsle i hiG
      by_cases hv : 0 < v i
      · simp only [hb, if_pos hv] at hle
        have : s * v i ≤ 1 - x i := (le_div_iff₀ hv).mp hle
        have hpos : 0 < s * v i := mul_pos hs hv
        constructor <;> linarith
      · have hvneg : v i < 0 := lt_of_le_of_ne (not_lt.mp hv) hvz
        simp only [hb, if_neg hv] at hle
        have : -x i ≤ s * v i := (le_div_iff_of_neg hvneg).mp hle
        have hneg : s * v i < 0 := mul_neg_of_pos_of_neg hs hvneg
        constructor <;> linarith
  obtain ⟨i1, hi1G, hi1eq⟩ := Finset.exists_mem_eq_inf' hGne b
  obtain ⟨hi1F, hi1v⟩ := hmemG i1 hi1G
  refine ⟨s, hs, hrange, i1, hi1F, ?_⟩
  by_cases hv : 0 < v i1
  · right
    rw [hsdef, hi1eq]
    simp only [hb, if_pos hv]
    field_simp
    ring
  · left
    rw [hsdef, hi1eq]
    simp only [hb, if_neg hv]
    field_simp
    ring

/-- One rounding step: if some row is tight, we can strictly decrease the number of floating
coordinates while keeping the frozen coordinates and all tight-row sums fixed. -/
lemma exists_rounding_step {t : ℕ} (A : Fin m → Fin N → ℤ)
    (hdeg : ∀ i, (univ.filter (fun j => A j i = 1)).card ≤ t)
    (x : Fin N → ℚ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (j0 : Fin m) (hj0 : t < fdeg A x j0) :
    ∃ x' : Fin N → ℚ, (∀ i, 0 ≤ x' i ∧ x' i ≤ 1) ∧
      (∀ i ∉ Floating x, x' i = x i) ∧
      (Floating x').card < (Floating x).card ∧
      (∀ j, t < fdeg A x j → ∑ i, (A j i : ℚ) * x' i = ∑ i, (A j i : ℚ) * x i) := by
  classical
  set F := Floating x with hFdef
  set T := univ.filter (fun j => t < fdeg A x j) with hTdef
  have hj0T : j0 ∈ T := by simp [hTdef, hj0]
  have hFne : F.Nonempty := by
    have : 0 < ((Floating x).filter (fun i => A j0 i = 1)).card := by
      have := hj0; simp only [fdeg] at this; omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp this
    exact ⟨i, (Finset.mem_filter.mp hi).1⟩
  have hcard : T.card < F.card := tight_card_lt A hdeg x hFne
  obtain ⟨v, hv0, ⟨i0, hi0F, hvi0⟩, hvnull⟩ := exists_nullvec A F T hcard
  have hFmem : ∀ i ∈ F, 0 < x i ∧ x i < 1 := fun i hi => mem_Floating.mp hi
  obtain ⟨s, hs, hrange, i1, hi1F, hi1⟩ :=
    exists_step_along x hx F hFmem v hv0 i0 hi0F hvi0
  refine ⟨fun i => x i + s * v i, hrange, ?_, ?_, ?_⟩
  · intro i hi
    simp only [hv0 i hi, mul_zero, add_zero]
  · have hsub : Floating (fun i => x i + s * v i) ⊆ F := by
      intro i hi
      by_contra hiF
      rw [mem_Floating] at hi
      simp only [hv0 i hiF, mul_zero, add_zero] at hi
      exact hiF (mem_Floating.mpr hi)
    have hi1not : i1 ∉ Floating (fun i => x i + s * v i) := by
      rw [mem_Floating]
      rcases hi1 with h | h <;> simp [h]
    exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨i1, hi1F, hi1not⟩)
  · intro j hj
    have hjT : j ∈ T := by simp [hTdef, hj]
    have := hvnull j hjT
    calc ∑ i, (A j i : ℚ) * (x i + s * v i)
        = (∑ i, (A j i : ℚ) * x i) + s * ∑ i, (A j i : ℚ) * v i := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = ∑ i, (A j i : ℚ) * x i := by rw [this]; ring

/-- If every row is slack, rounding all floating coordinates down already works. -/
lemma exists_round_all_slack {t : ℕ} (ht : 1 ≤ t) (A : Fin m → Fin N → ℤ)
    (hA : ∀ j i, A j i = 0 ∨ A j i = 1) (x : Fin N → ℚ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hall : ∀ j, fdeg A x j ≤ t) :
    ∃ y : Fin N → ℤ, (∀ i, y i = 0 ∨ y i = 1) ∧
      (∀ i ∉ Floating x, (y i : ℚ) = x i) ∧
      ∀ j, |∑ i, (A j i : ℚ) * ((y i : ℚ) - x i)| < (t : ℚ) := by
  classical
  refine ⟨fun i => if x i = 1 then 1 else 0, fun i => ?_, ?_, ?_⟩
  · by_cases h : x i = 1 <;> simp [h]
  · intro i hi
    rcases eq_zero_or_one_of_not_floating (hx i) hi with h | h <;> simp [h]
  · intro j
    refine slack_row_bound ht A hA x _ (fun i => ?_) (fun i hi => ?_) j (hall j)
    · by_cases h : x i = 1 <;> simp [h]
    · rcases eq_zero_or_one_of_not_floating (hx i) hi with h | h <;> simp [h]

/-! ### The main induction -/

/-- The induction on the number of floating coordinates. -/
lemma beck_fiala_ind {t : ℕ} (ht : 1 ≤ t) (A : Fin m → Fin N → ℤ)
    (hA : ∀ j i, A j i = 0 ∨ A j i = 1)
    (hdeg : ∀ i, (univ.filter (fun j => A j i = 1)).card ≤ t) :
    ∀ n : ℕ, ∀ x : Fin N → ℚ, (Floating x).card ≤ n → (∀ i, 0 ≤ x i ∧ x i ≤ 1) →
      ∃ y : Fin N → ℤ, (∀ i, y i = 0 ∨ y i = 1) ∧
        (∀ i ∉ Floating x, (y i : ℚ) = x i) ∧
        ∀ j, |∑ i, (A j i : ℚ) * ((y i : ℚ) - x i)| < (t : ℚ) := by
  intro n
  induction n with
  | zero =>
      intro x hcard hx
      refine exists_round_all_slack ht A hA x hx (fun j => ?_)
      have : fdeg A x j ≤ (Floating x).card :=
        card_le_card (filter_subset _ _)
      omega
  | succ n ih =>
      intro x hcard hx
      by_cases hall : ∀ j, fdeg A x j ≤ t
      · exact exists_round_all_slack ht A hA x hx hall
      · push_neg at hall
        obtain ⟨j0, hj0⟩ := hall
        obtain ⟨x', hx', hfix, hlt, htight⟩ :=
          exists_rounding_step A hdeg x hx j0 hj0
        obtain ⟨y, hy01, hagree', hbd'⟩ := ih x' (by omega) hx'
        have hagree : ∀ i ∉ Floating x, (y i : ℚ) = x i := by
          intro i hi
          have hxx : x' i = x i := hfix i hi
          have : i ∉ Floating x' := by
            rw [mem_Floating, hxx]
            rcases eq_zero_or_one_of_not_floating (hx i) hi with h | h <;> simp [h]
          rw [hagree' i this, hxx]
        refine ⟨y, hy01, hagree, fun j => ?_⟩
        by_cases hs : fdeg A x j ≤ t
        · exact slack_row_bound ht A hA x y hy01 hagree j hs
        · push_neg at hs
          have hsum : ∑ i, (A j i : ℚ) * ((y i : ℚ) - x i)
              = ∑ i, (A j i : ℚ) * ((y i : ℚ) - x' i) := by
            have h1 : ∀ z : Fin N → ℚ, ∑ i, (A j i : ℚ) * ((y i : ℚ) - z i)
                = (∑ i, (A j i : ℚ) * (y i : ℚ)) - ∑ i, (A j i : ℚ) * z i := by
              intro z
              rw [← Finset.sum_sub_distrib]
              exact Finset.sum_congr rfl (fun i _ => by ring)
            rw [h1, h1, htight j hs]
          rw [hsum]
          exact hbd' j

/-- Strengthened Beck–Fiala statement: the rounding can be chosen to fix all coordinates
that are already integral. -/
theorem beck_fiala_aux {t : ℕ} (ht : 1 ≤ t) (A : Fin m → Fin N → ℤ)
    (hA : ∀ j i, A j i = 0 ∨ A j i = 1)
    (hdeg : ∀ i, (univ.filter (fun j => A j i = 1)).card ≤ t)
    (x : Fin N → ℚ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    ∃ y : Fin N → ℤ, (∀ i, y i = 0 ∨ y i = 1) ∧
      (∀ i ∉ Floating x, (y i : ℚ) = x i) ∧
      ∀ j, |∑ i, (A j i : ℚ) * ((y i : ℚ) - x i)| < (t : ℚ) :=
  beck_fiala_ind ht A hA hdeg (Floating x).card x le_rfl hx

end BeckFiala

/-
The statement recorded in this comment is NOT part of the development (it is not elaborated,
has no proof, and is kept only for the record): it is false.

The originally requested statement, without the hypothesis `1 ≤ t`, is FALSE: for `t = 0`
the degree hypothesis forces `A = 0`, so every row sum is `0`, and the conclusion would
read `|0| < 0`.  (See `beck_fiala_zero_counterexample` below for a formal proof of this.)
The statement is therefore recorded below with the minimal extra hypothesis `1 ≤ t`.

theorem beck_fiala {m N t : ℕ}
    (A : Fin m → Fin N → ℤ)
    (hA : ∀ j i, A j i = 0 ∨ A j i = 1)
    (hdeg : ∀ i, (Finset.univ.filter (fun j => A j i = 1)).card ≤ t)
    (x : Fin N → ℚ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    ∃ y : Fin N → ℤ, (∀ i, y i = 0 ∨ y i = 1) ∧
      ∀ j, |∑ i, (A j i : ℚ) * ((y i : ℚ) - x i)| < (t : ℚ)
  -- no proof: FALSE for t = 0 (see `beck_fiala_zero_counterexample`)
-/

open BeckFiala in
/-- **Beck–Fiala integer-making theorem.**  If every element lies in at most `t` sets of a
set system (i.e. every column of the 0/1 incidence matrix `A` has at most `t` ones) and
`x ∈ [0,1]^N` is fractional, then `x` can be rounded to an integral `y ∈ {0,1}^N` whose
discrepancy on every row is `< t`.

(The extra hypothesis `1 ≤ t` is necessary; see `beck_fiala_zero_counterexample` below.) -/
theorem beck_fiala {m N t : ℕ} (ht : 1 ≤ t)
    (A : Fin m → Fin N → ℤ)
    (hA : ∀ j i, A j i = 0 ∨ A j i = 1)
    (hdeg : ∀ i, (Finset.univ.filter (fun j => A j i = 1)).card ≤ t)
    (x : Fin N → ℚ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    ∃ y : Fin N → ℤ, (∀ i, y i = 0 ∨ y i = 1) ∧
      ∀ j, |∑ i, (A j i : ℚ) * ((y i : ℚ) - x i)| < (t : ℚ) := by
  obtain ⟨y, hy, -, hbd⟩ := beck_fiala_aux ht A hA hdeg x hx
  exact ⟨y, hy, hbd⟩

/-- The hypothesis `1 ≤ t` cannot be dropped: for `t = 0` the conclusion would read
`|0| < 0`. -/
theorem beck_fiala_zero_counterexample :
    ¬ (∀ (m N t : ℕ) (A : Fin m → Fin N → ℤ), (∀ j i, A j i = 0 ∨ A j i = 1) →
        (∀ i, (Finset.univ.filter (fun j => A j i = 1)).card ≤ t) →
        ∀ x : Fin N → ℚ, (∀ i, 0 ≤ x i ∧ x i ≤ 1) →
        ∃ y : Fin N → ℤ, (∀ i, y i = 0 ∨ y i = 1) ∧
          ∀ j, |∑ i, (A j i : ℚ) * ((y i : ℚ) - x i)| < (t : ℚ)) := by
  intro h
  obtain ⟨y, -, hbd⟩ := h 1 1 0 (fun _ _ => 0) (fun _ _ => Or.inl rfl)
    (by intro i; simp) (fun _ => 0) (by intro i; norm_num)
  have := hbd 0
  simp at this
