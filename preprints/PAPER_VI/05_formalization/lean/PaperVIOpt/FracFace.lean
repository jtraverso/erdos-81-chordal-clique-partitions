/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
SPDX-License-Identifier: Apache-2.0

The Apache-2.0 grant applies to the author-written formalization in this file.
Existing mathematical attributions, author credits and provenance below are retained.
-/

/-
Author: Juan Pablo Traverso Gianini.
Existing third-party credits below are retained.
-/
/-
Paper VI optimisation round — Priority 2 (continued): the projection of the optimal face of the
equality-constrained fractional clique-partition problem onto the `K_5`-weights of the
exterior edges.

For a fractional clique partition `x` and an exterior edge `e`, let `z_e(x)` be the total
weight of the blocks of type `(3,2)` containing `e`. Every fractional partition has
`0 ≤ z_e(x) ≤ 1` (coverage equation). Under Theorem B (`p ≥ 63h`) every vector of `[0,1]^{E(H)}`
is `z(x)` for an optimal fractional partition `x` (value `cp(G)`), obtained as a convex
combination (product weights) of the `2^m` prescribed integral optima. Hence the projection of
the optimal face is exactly the cube `[0,1]^{E(H)}`. This says nothing about integrality of the
whole optimal face.

Version note: the fractional model of the Lean 4.28 staging copy uses rational weights; the
canonical Lean 4.35 freeze uses real weights. The proofs below only use ordered-field
arithmetic; the scalar field is fixed by the local notation `𝕂` and must be set to `ℝ` for the
4.35 freeze.
-/
module

public import PaperVIOpt.Secondary
public import PaperVI.Fractional
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

namespace PaperVI

open Finset

/-- The scalar field of the fractional model (`ℚ` in the 4.28 staging copy). -/
local notation "𝕂" => ℝ

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

/-- `z_e(x)`: the total weight of the blocks of type `(3,2)` containing `e`. -/
def k5Weight (x : Finset V → 𝕂) (e : Sym2 V) : 𝕂 :=
  ∑ Q ∈ univ.filter (fun Q : Finset V => (∀ v ∈ e.toFinset, v ∈ Q) ∧
    coreSize P Q = 3 ∧ extSize P Q = 2), x Q

/-- **Containment.** For every fractional clique partition and every exterior edge,
`0 ≤ z_e(x) ≤ 1`. -/
theorem k5Weight_mem_Icc {x : Finset V → 𝕂} (hx : IsFracPartition G x) {e : Sym2 V}
    (he : e ∈ extEdges G P) : 0 ≤ k5Weight P x e ∧ k5Weight P x e ≤ 1 := by
  refine ⟨sum_nonneg fun Q _ => hx.nonneg Q, ?_⟩
  induction e using Sym2.ind with
  | h u v =>
    have hadj : G.Adj u v := ((mem_extEdges G P).mp he).1
    rw [← hx.edge u v hadj]
    refine sum_le_sum_of_subset_of_nonneg ?_ (fun Q _ _ => hx.nonneg Q)
    intro Q hQ
    simp only [mem_filter, mem_univ, true_and, Sym2.toFinset_mk_eq, mem_insert,
      mem_singleton, forall_eq_or_imp, forall_eq] at hQ ⊢
    exact hQ.1

/-! ### Product weights on prescriptions -/

section Product

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Product weight of a Boolean vector `τ` for marginals `w`. -/
def prodWeight (w : ι → 𝕂) (τ : ι → Bool) : 𝕂 :=
  ∏ i, (if τ i then w i else 1 - w i)

omit [DecidableEq ι] in
theorem prodWeight_nonneg {w : ι → 𝕂} (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (τ : ι → Bool) :
    0 ≤ prodWeight w τ :=
  prod_nonneg fun i _ => by split_ifs <;> linarith [hw i]

theorem sum_prodWeight (w : ι → 𝕂) : ∑ τ : ι → Bool, prodWeight w τ = 1 := by
  unfold prodWeight
  rw [← Fintype.prod_sum (fun i (b : Bool) => if b then w i else 1 - w i)]
  simp

theorem sum_prodWeight_marginal (w : ι → 𝕂) (i₀ : ι) :
    ∑ τ : ι → Bool, prodWeight w τ * (if τ i₀ then 1 else 0) = w i₀ := by
  let g : ∀ i : ι, Bool → 𝕂 := fun i b =>
    if i = i₀ then (if b then w i₀ else 0) else (if b then w i else 1 - w i)
  have hpt : ∀ τ : ι → Bool, prodWeight w τ * (if τ i₀ then 1 else 0) = ∏ i, g i (τ i) := by
    intro τ
    unfold prodWeight
    rw [Fintype.prod_eq_mul_prod_compl i₀, Fintype.prod_eq_mul_prod_compl i₀ (fun i => g i (τ i))]
    have hc : ∏ i ∈ {i₀}ᶜ, g i (τ i) = ∏ i ∈ {i₀}ᶜ, (if τ i then w i else 1 - w i) := by
      refine prod_congr rfl fun i hi => ?_
      have : i ≠ i₀ := by simpa using hi
      simp only [g, if_neg this]
    rw [hc]
    simp only [g, if_pos rfl]
    cases τ i₀ <;> simp
  rw [sum_congr rfl fun τ _ => hpt τ, ← Fintype.prod_sum g]
  have hg : ∀ i, ∑ b, g i b = if i = i₀ then w i₀ else 1 := by
    intro i
    by_cases hi : i = i₀ <;> simp [g, hi]
  rw [prod_congr rfl (fun i _ => hg i), prod_ite_eq' univ i₀ (fun _ => w i₀)]
  simp

end Product

/-! ### The optimal face -/

/-- The family of prescribed integral optima, indexed by `τ : E(H) → Bool`
(`true` = `K_5`, `false` = `K_4`), and their properties, under Theorem B. -/
theorem exists_prescribed_family (hn : 2 ≤ Fintype.card V)
    (hP : P.card = (Fintype.card V + 1) / 3) (hh : 63 * editDegree G P ≤ P.card) :
    ∃ F : ({e // e ∈ extEdges G P} → Bool) → Finset (Finset V), ∀ τ,
      IsCliquePartition G (F τ) ∧ (F τ).card = cp G ∧
      ∀ e ∈ extEdges G P, ∃ B ∈ F τ, (∀ v ∈ e, v ∈ B) ∧ B.card = prescription G P τ e ∧
        extSize P B = 2 := by
  have hσ : ∀ τ, ∀ e ∈ extEdges G P, prescription G P τ e = 4 ∨ prescription G P τ e = 5 := by
    intro τ e he
    unfold prescription
    rw [dif_pos he]
    split_ifs <;> simp
  have hB := fun τ => theoremB G P hn hP hh (prescription G P τ) (hσ τ)
  refine ⟨fun τ => Classical.choose (hB τ), fun τ => ?_⟩
  obtain ⟨h1, h2, -, -, h5, -⟩ := Classical.choose_spec (hB τ)
  exact ⟨h1, h2, h5⟩

/-- **Attainability.** Under the hypotheses of Theorem B, for every `w ∈ [0,1]^{E(H)}` there is
a fractional clique partition `x` of value `cp(G)` (hence optimal) with `z_e(x) = w_e` for every
exterior edge `e`. -/
theorem exists_frac_optimal_k5Weight (hn : 2 ≤ Fintype.card V)
    (hP : P.card = (Fintype.card V + 1) / 3) (hh : 63 * editDegree G P ≤ P.card)
    (w : {e // e ∈ extEdges G P} → 𝕂) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) :
    ∃ x : Finset V → 𝕂, IsFracPartition G x ∧ fracValue x = cp G ∧
      ∀ i : {e // e ∈ extEdges G P}, k5Weight P x i.1 = w i := by
  classical
  obtain ⟨F, hF⟩ := exists_prescribed_family G P hn hP hh
  let x : Finset V → 𝕂 := fun Q => ∑ τ, prodWeight w τ * (if Q ∈ F τ then 1 else 0)
  -- interchange of sums
  have hswap : ∀ (S : Finset (Finset V)), ∑ Q ∈ S, x Q =
      ∑ τ, prodWeight w τ * ((F τ).filter (fun Q => Q ∈ S)).card := by
    intro S
    simp only [x]
    rw [sum_comm]
    refine sum_congr rfl fun τ _ => ?_
    rw [← mul_sum]
    congr 1
    rw [sum_boole]
    norm_cast
    rw [filter_mem_eq_inter, filter_mem_eq_inter, inter_comm]
  refine ⟨x, ⟨fun Q => sum_nonneg fun τ _ => mul_nonneg (prodWeight_nonneg hw τ)
    (by split_ifs <;> norm_num), fun Q hQ => ?_, fun u v huv => ?_⟩, ?_, fun i => ?_⟩
  · -- support
    by_contra hcon
    apply hQ
    refine sum_eq_zero fun τ _ => ?_
    by_cases hQτ : Q ∈ F τ
    · exact absurd ⟨(hF τ).1.two_le Q hQτ, (hF τ).1.isClique Q hQτ⟩ hcon
    · simp [hQτ]
  · -- edge equations
    rw [hswap]
    have h1 : ∀ τ, ((F τ).filter (fun Q => Q ∈ univ.filter
        (fun Q : Finset V => u ∈ Q ∧ v ∈ Q))).card = 1 := by
      intro τ
      obtain ⟨B, ⟨hB, huB, hvB⟩, huniq⟩ := (hF τ).1.existsUnique u v huv
      rw [card_eq_one]
      refine ⟨B, ?_⟩
      ext Q
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · rintro ⟨hQ, huQ, hvQ⟩; exact huniq Q ⟨hQ, huQ, hvQ⟩
      · rintro rfl; exact ⟨hB, huB, hvB⟩
    simp only [h1, Nat.cast_one, mul_one]
    exact sum_prodWeight w
  · -- value
    unfold fracValue
    have := hswap univ
    simp only [mem_univ, filter_true] at this
    rw [this]
    simp only [(hF _).2.1]
    rw [← sum_mul, sum_prodWeight, one_mul]
  · -- projection
    unfold k5Weight
    rw [hswap]
    have h1 : ∀ τ, ((F τ).filter (fun Q => Q ∈ univ.filter (fun Q : Finset V =>
        (∀ v ∈ i.1.toFinset, v ∈ Q) ∧ coreSize P Q = 3 ∧ extSize P Q = 2))).card =
        if τ i then 1 else 0 := by
      intro τ
      obtain ⟨B, hB, heB, hcard, hext⟩ := (hF τ).2.2 i.1 i.2
      have hpre : prescription G P τ i.1 = if τ i then 5 else 4 := by
        unfold prescription; rw [dif_pos i.2]
      have hcB := card_eq_coreSize_add_extSize P B
      have hfil : (F τ).filter (fun Q => Q ∈ univ.filter (fun Q : Finset V =>
          (∀ v ∈ i.1.toFinset, v ∈ Q) ∧ coreSize P Q = 3 ∧ extSize P Q = 2)) =
          if τ i then {B} else ∅ := by
        ext Q
        simp only [mem_filter, mem_univ, true_and, Sym2.mem_toFinset]
        constructor
        · rintro ⟨hQ, heQ, hc3, he2⟩
          have := block_unique_of_edge G (hF τ).1 (extEdges_subset i.2) hB hQ heB heQ
          subst this
          have hQc := card_eq_coreSize_add_extSize P B
          cases hτ : τ i
          · rw [hτ] at hpre; simp only [Bool.false_eq_true, if_false] at hpre; omega
          · simp
        · intro hmem
          cases hτ : τ i
          · rw [hτ] at hmem; simp at hmem
          · rw [hτ] at hmem hpre
            simp only [if_true] at hpre
            obtain rfl : Q = B := by simpa using hmem
            exact ⟨hB, heB, by omega, hext⟩
      rw [hfil]
      split_ifs <;> simp
    simp only [h1, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact sum_prodWeight_marginal w i

/-- **The projection of the optimal fractional face is the cube.** Under the hypotheses of
Theorem B, the set of vectors `(z_e(x))_{e ∈ E(H)}`, as `x` ranges over the optimal fractional
clique partitions (value `cp(G)`, which is the fractional optimum), is exactly `[0,1]^{E(H)}`.
In particular this set has dimension `m`. -/
theorem frac_face_projection (hn : 2 ≤ Fintype.card V)
    (hP : P.card = (Fintype.card V + 1) / 3) (hh : 63 * editDegree G P ≤ P.card) :
    IsLeast {v : 𝕂 | ∃ x, IsFracPartition G x ∧ fracValue x = v} (cp G : 𝕂) ∧
    {w : {e // e ∈ extEdges G P} → 𝕂 | ∃ x, IsFracPartition G x ∧ fracValue x = cp G ∧
      ∀ i, k5Weight P x i.1 = w i} = {w | ∀ i, 0 ≤ w i ∧ w i ≤ 1} := by
  have hhA : 18 * editDegree G P + 1 ≤ P.card := by
    have := p_pos hn
    rw [← hP] at this
    omega
  refine ⟨(fractional_eq_cp G P hn hP hhA).1, ?_⟩
  ext w
  constructor
  · intro h
    obtain ⟨x, hx, -, hxw⟩ := h
    intro i
    rw [← hxw i]
    exact k5Weight_mem_Icc G P hx i.2
  · intro hw
    exact exists_frac_optimal_k5Weight G P hn hP hh w hw

end PaperVI
