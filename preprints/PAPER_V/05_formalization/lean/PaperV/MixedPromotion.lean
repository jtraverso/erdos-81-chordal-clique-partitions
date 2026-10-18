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

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Tauto
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-! A physical four-clique trade. Coordinates are all vertex subsets; unsupported
coordinates are zero. This is a finite graph resource LP, with one capacity per
pair of distinct vertices. No cancellation of edge loads is an input hypothesis. -/
@[expose] public section
namespace PaperV.MixedPromotion
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def load (y : Finset V → ℝ) (a b : V) : ℝ :=
  ∑ T ∈ (univ : Finset (Finset V)).filter (fun T => a ∈ T ∧ b ∈ T), y T

def Feasible (G : SimpleGraph V) (y : Finset V → ℝ) : Prop :=
  (∀ T, 0 ≤ y T) ∧
  (∀ T, y T ≠ 0 → G.IsClique (T : Set V) ∧ (T.card = 3 ∨ T.card = 4)) ∧
  (∀ a b, a ≠ b → load y a b ≤ 1)

noncomputable def promote (y : Finset V → ℝ) (Q : Finset V) (α : ℝ)
    (T : Finset V) : ℝ :=
  y T + (if T = Q then 2 * α else 0) - (if T ∈ Q.powersetCard 3 then α else 0)

omit [Fintype V] in
theorem face_count (Q : Finset V) (hQ : Q.card = 4) (a b : V) (hab : a ≠ b) :
    ((Q.powersetCard 3).filter (fun T => a ∈ T ∧ b ∈ T)).card =
      if a ∈ Q ∧ b ∈ Q then 2 else 0 := by
  classical
  by_cases hm : a ∈ Q ∧ b ∈ Q
  · have hs : ({a, b} : Finset V) ⊆ Q := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl <;> tauto
    have hc : ({a, b} : Finset V).card = 2 := by simp [hab]
    have he : (Q.powersetCard 3).filter (fun T => a ∈ T ∧ b ∈ T) =
        (Q.powersetCard 3).filter (fun T => ({a, b} : Finset V) ⊆ T) := by
      ext T
      simp only [Finset.mem_filter]
      have he : ({a, b} : Finset V) ⊆ T ↔ a ∈ T ∧ b ∈ T := by
        constructor
        · intro hs; exact ⟨hs (by simp), hs (by simp)⟩
        · intro hs v hv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl <;> tauto
      rw [he]
    rw [he, Finset.card_filter_powersetCard_subset _ _ _ hs (by omega), hQ, hc]
    simp [hm]
  · have he : (Q.powersetCard 3).filter (fun T => a ∈ T ∧ b ∈ T) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro T ht
      obtain ⟨hT, ha, hb⟩ := Finset.mem_filter.mp ht
      have hsub := (Finset.mem_powersetCard.mp hT).1
      exact hm ⟨hsub ha, hsub hb⟩
    simp [he, hm]

theorem load_promote (y : Finset V → ℝ) (Q : Finset V) (hQ : Q.card = 4)
    (α : ℝ) (a b : V) (hab : a ≠ b) :
    load (promote y Q α) a b = load y a b := by
  classical
  let S := (univ : Finset (Finset V)).filter (fun T => a ∈ T ∧ b ∈ T)
  have hplus : (∑ T ∈ S, if T = Q then 2 * α else 0) =
      if a ∈ Q ∧ b ∈ Q then 2 * α else 0 := by
    simp [S]
  have hminus : (∑ T ∈ S, if T ∈ Q.powersetCard 3 then α else 0) =
      (((Q.powersetCard 3).filter (fun T => a ∈ T ∧ b ∈ T)).card : ℝ) * α := by
    rw [← Finset.sum_filter]
    have he : S.filter (fun T => T ∈ Q.powersetCard 3) =
        (Q.powersetCard 3).filter (fun T => a ∈ T ∧ b ∈ T) := by
      ext T; simp [S, and_comm, and_left_comm]
    rw [he]; simp
  change (∑ T ∈ S, promote y Q α T) = ∑ T ∈ S, y T
  simp only [promote, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hplus, hminus, face_count Q hQ a b hab]
  by_cases hm : a ∈ Q ∧ b ∈ Q <;> simp [hm]

theorem feasible_promote (G : SimpleGraph V) {y : Finset V → ℝ}
    (hy : Feasible G y) (Q : Finset V) (hQ : Q.card = 4)
    (hcl : G.IsClique (Q : Set V)) (α : ℝ) (hα : 0 ≤ α)
    (hface : ∀ T ∈ Q.powersetCard 3, α ≤ y T) :
    Feasible G (promote y Q α) := by
  classical
  have hn : Q ∉ Q.powersetCard 3 := by simp [hQ]
  refine ⟨?_, ?_, ?_⟩
  · intro T
    by_cases hT : T = Q
    · subst T
      simpa [promote, hn] using add_nonneg (hy.1 Q) (mul_nonneg (by norm_num) hα)
    · by_cases hf : T ∈ Q.powersetCard 3
      · simpa [promote, hT, hf] using sub_nonneg.mpr (hface T hf)
      · simpa [promote, hT, hf] using hy.1 T
  · intro T hT
    by_cases heq : T = Q
    · subst T; exact ⟨hcl, Or.inr hQ⟩
    · by_cases hf : T ∈ Q.powersetCard 3
      · have hp := Finset.mem_powersetCard.mp hf
        refine ⟨?_, Or.inl hp.2⟩
        intro a ha b hb hab
        exact hcl (hp.1 ha) (hp.1 hb) hab
      · exact hy.2.1 T (by simpa [promote, heq, hf] using hT)
  · intro a b hab
    rw [load_promote y Q hQ α a b hab]
    exact hy.2.2 a b hab

noncomputable def value (w y : Finset V → ℝ) : ℝ := ∑ T, w T * y T

theorem value_promote (w y : Finset V → ℝ) (Q : Finset V) (α : ℝ) :
    value w (promote y Q α) =
      value w y + α * (2 * w Q - ∑ T ∈ Q.powersetCard 3, w T) := by
  classical
  have hp : (∑ T : Finset V, w T * (if T = Q then 2 * α else 0)) =
      w Q * (2 * α) := by simp [mul_ite]
  have hm : (∑ T : Finset V, w T * (if T ∈ Q.powersetCard 3 then α else 0)) =
      (∑ T ∈ Q.powersetCard 3, w T) * α := by
    simp_rw [mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    have he : (univ : Finset (Finset V)).filter (fun T => T ∈ Q.powersetCard 3) =
        Q.powersetCard 3 := by ext T; simp
    rw [he, Finset.sum_mul]
  unfold value
  simp only [promote, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hp, hm]
  ring

def gain (T : Finset V) : ℝ := if T.card = 3 then 2 else if T.card = 4 then 5 else 0

theorem gain_promote (y : Finset V → ℝ) (Q : Finset V) (hQ : Q.card = 4) (α : ℝ) :
    value gain (promote y Q α) = value gain y + 2 * α := by
  classical
  have hf : (∑ T ∈ Q.powersetCard 3, gain T) = 8 := by
    calc
      _ = ∑ _T ∈ Q.powersetCard 3, (2 : ℝ) := by
        apply Finset.sum_congr rfl
        intro T hT
        simp [gain, (Finset.mem_powersetCard.mp hT).2]
      _ = 8 := by norm_num [Finset.card_powersetCard, hQ]
  rw [value_promote, hf]
  norm_num [gain, hQ, mul_comm]

/-- Arbitrary ordered edge prices; for an unordered price use half its value in
each orientation. Diagonal entries have no effect. -/
noncomputable def pricedValue (π : V → V → ℝ) (y : Finset V → ℝ) : ℝ :=
  value gain y - ∑ a, ∑ b, if a ≠ b then π a b * load y a b else 0

theorem pricedValue_promote (π : V → V → ℝ) (y : Finset V → ℝ)
    (Q : Finset V) (hQ : Q.card = 4) (α : ℝ) :
    pricedValue π (promote y Q α) = pricedValue π y + 2 * α := by
  classical
  have he : (∑ a, ∑ b, if a ≠ b then π a b * load (promote y Q α) a b else 0) =
      ∑ a, ∑ b, if a ≠ b then π a b * load y a b else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases hab : a ≠ b
    · simp [hab, load_promote y Q hQ α a b hab]
    · simp [hab]
  unfold pricedValue
  rw [gain_promote y Q hQ α, he]
  ring

/-- An optimum cannot have strictly positive mass on all four faces of a
physical four-clique. This includes arbitrary edge-price objectives. -/
theorem optimal_support_exclusion (G : SimpleGraph V) {y : Finset V → ℝ}
    (hy : Feasible G y) (π : V → V → ℝ)
    (hopt : ∀ z, Feasible G z → pricedValue π z ≤ pricedValue π y)
    (Q : Finset V) (hQ : Q.card = 4) (hcl : G.IsClique (Q : Set V)) :
    ∃ T ∈ Q.powersetCard 3, y T = 0 := by
  classical
  have hne : (Q.powersetCard 3).Nonempty := by
    rw [Finset.powersetCard_nonempty, hQ]; norm_num
  obtain ⟨T, hT, hmin⟩ := Finset.exists_min_image (Q.powersetCard 3) y hne
  by_cases hz : y T = 0
  · exact ⟨T, hT, hz⟩
  · have hpos : 0 < y T := lt_of_le_of_ne (hy.1 T) (Ne.symm hz)
    have hnew := feasible_promote G hy Q hQ hcl (y T) (le_of_lt hpos) hmin
    have hb := hopt (promote y Q (y T)) hnew
    rw [pricedValue_promote π y Q hQ] at hb
    linarith

end PaperV.MixedPromotion
