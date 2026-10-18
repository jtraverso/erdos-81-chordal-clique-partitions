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
Paper VI — consequences of the slack identity at the optimum: the four optimal block types,
the `21t` bound of Appendix B, and the `2^m` distinct optimal partitions of Theorem B.
-/
module

public import PaperVI.TheoremB

@[expose] public section

namespace PaperVI

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Blockwise inequality of Appendix B: a block with positive slack has at most `21 ℓ` edges. -/
theorem choose_two_le_21_slack (a b : ℕ) (h : 0 < slack a b) :
    (((a + b).choose 2 : ℕ) : ℤ) ≤ 21 * slack a b := by
  have h2 := two_mul_slack a b
  have hc := two_mul_choose_two (a + b)
  push_cast at hc
  rcases le_or_gt (a + b) 7 with hk | hk
  · have : ((a + b : ℕ) : ℤ) ≤ 7 := by exact_mod_cast hk
    have h0 : (0 : ℤ) ≤ (a + b : ℕ) := by positivity
    push_cast at this h0
    nlinarith
  · have ha : (0 : ℤ) ≤ a := by positivity
    have hb : (0 : ℤ) ≤ b := by positivity
    have hk' : (8 : ℤ) ≤ a + b := by exact_mod_cast hk
    have : ((a : ℤ) + b) * ((a : ℤ) + b - 1) <
        21 * (((a : ℤ) - b) * ((a : ℤ) - b - 1) + ((b : ℤ) - 1) * ((b : ℤ) - 2)) := by
      nlinarith [sq_nonneg (10 * (b : ℤ) - 4 * ((a : ℤ) + b) - 1), sq_nonneg ((a : ℤ) - 3 * b),
        mul_nonneg ha hb]
    nlinarith

variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

/-- If `cp(G)` equals the lower bound `s - u - 2m`, then every optimal clique partition
uses only the zero-slack types `(1,1), (2,1), (2,2), (3,2)`; in particular every optimal
block has order at most five. -/
theorem optimal_types_of_cp_eq (hcp : (cp G : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P)
    {Bs : Finset (Finset V)} (hBs : IsCliquePartition G Bs) (hopt : Bs.card = cp G) :
    ∀ B ∈ Bs, ((coreSize P B = 1 ∧ extSize P B = 1) ∨ (coreSize P B = 2 ∧ extSize P B = 1) ∨
      (coreSize P B = 2 ∧ extSize P B = 2) ∨ (coreSize P B = 3 ∧ extSize P B = 2)) ∧
      B.card ≤ 5 := by
  have hid := slack_identity G P hBs
  have hsum : ∑ B ∈ Bs, slack (coreSize P B) (extSize P B) = 0 := by
    rw [← hid, hopt, hcp]; ring
  have hz := (sum_eq_zero_iff_of_nonneg (fun B _ => slack_nonneg _ _)).mp hsum
  intro B hB
  have ht := (slack_eq_zero_iff _ _).mp (hz B hB)
  refine ⟨ht, ?_⟩
  rw [card_eq_coreSize_add_extSize P B]
  rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- **Classification of optimal blocks (Section 7).** Under the hypothesis of Theorem A,
every optimal clique partition uses only the four types `(1,1), (2,1), (2,2), (3,2)`. -/
theorem optimal_types (hn : 2 ≤ Fintype.card V) (hP : P.card = (Fintype.card V + 1) / 3)
    (hh : 18 * editDegree G P + 1 ≤ P.card)
    {Bs : Finset (Finset V)} (hBs : IsCliquePartition G Bs) (hopt : Bs.card = cp G) :
    ∀ B ∈ Bs, ((coreSize P B = 1 ∧ extSize P B = 1) ∨ (coreSize P B = 2 ∧ extSize P B = 1) ∨
      (coreSize P B = 2 ∧ extSize P B = 2) ∨ (coreSize P B = 3 ∧ extSize P B = 2)) ∧
      B.card ≤ 5 :=
  optimal_types_of_cp_eq G P (theoremA G P hn hP hh).2.2.1 hBs hopt

/-- **Appendix B (edges in inefficient blocks).** Under the hypothesis of Theorem A, let `Π`
be a clique partition with `|Π| = cp(G) + t`. Then `t = Σ ℓ`, at most `t` blocks have
positive slack, and the union of the edge sets of these blocks has at most `21 t` edges. -/
theorem inefficient_edges_le (hn : 2 ≤ Fintype.card V) (hP : P.card = (Fintype.card V + 1) / 3)
    (hh : 18 * editDegree G P + 1 ≤ P.card)
    {Bs : Finset (Finset V)} (hBs : IsCliquePartition G Bs) (t : ℕ)
    (ht : Bs.card = cp G + t) :
    (t : ℤ) = ∑ B ∈ Bs, slack (coreSize P B) (extSize P B) ∧
    (Bs.filter (fun B => 0 < slack (coreSize P B) (extSize P B))).card ≤ t ∧
    ((Bs.filter (fun B => 0 < slack (coreSize P B) (extSize P B))).biUnion
      (innerEdges G)).card ≤ 21 * t := by
  have hcp := (theoremA G P hn hP hh).2.2.1
  have hid := slack_identity G P hBs
  have htsum : (t : ℤ) = ∑ B ∈ Bs, slack (coreSize P B) (extSize P B) := by
    rw [← hid, ht]; push_cast; rw [hcp]; ring
  set S := Bs.filter (fun B => 0 < slack (coreSize P B) (extSize P B))
  have hsplit : ∑ B ∈ S, slack (coreSize P B) (extSize P B) ≤ t := by
    rw [htsum]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun B _ _ => slack_nonneg _ _)
  refine ⟨htsum, ?_, ?_⟩
  · have : (S.card : ℤ) ≤ ∑ B ∈ S, slack (coreSize P B) (extSize P B) := by
      rw [card_eq_sum_ones, Nat.cast_sum]
      refine sum_le_sum fun B hB => ?_
      have := (mem_filter.mp hB).2
      push_cast; omega
    exact_mod_cast this.trans hsplit
  · have h1 := card_biUnion_le (s := S) (t := innerEdges G)
    have h2 : (∑ B ∈ S, (innerEdges G B).card : ℤ) ≤
        ∑ B ∈ S, 21 * slack (coreSize P B) (extSize P B) := by
      refine sum_le_sum fun B hB => ?_
      have hBm := mem_filter.mp hB
      rw [card_innerEdges_of_isClique G B (hBs.isClique B hBm.1),
        card_eq_coreSize_add_extSize P B]
      exact choose_two_le_21_slack _ _ hBm.2
    rw [← mul_sum] at h2
    have : ((S.biUnion (innerEdges G)).card : ℤ) ≤ 21 * t := by
      calc ((S.biUnion (innerEdges G)).card : ℤ) ≤ ∑ B ∈ S, ((innerEdges G B).card : ℤ) := by
            exact_mod_cast h1
        _ ≤ _ := h2
        _ ≤ 21 * t := by linarith
    exact_mod_cast this

/-- The prescription `σ` attached to a choice `τ` of `K_5` (true) or `K_4` (false) for each
exterior edge. -/
def prescription (τ : {e // e ∈ extEdges G P} → Bool) (e : Sym2 V) : ℕ :=
  if h : e ∈ extEdges G P then (if τ ⟨e, h⟩ then 5 else 4) else 4

/-- **At least `2^m` optimal partitions (Theorem B).** Under `p ≥ 63h`, distinct
prescriptions yield distinct optimal clique partitions: there is an injection from the `2^m`
prescriptions into the optimal clique partitions, and hence at least `2^m` of them. -/
theorem two_pow_m_optimal (hn : 2 ≤ Fintype.card V) (hP : P.card = (Fintype.card V + 1) / 3)
    (hh : 63 * editDegree G P ≤ P.card) :
    (∃ F : ({e // e ∈ extEdges G P} → Bool) → Finset (Finset V), Function.Injective F ∧
      ∀ τ, IsCliquePartition G (F τ) ∧ (F τ).card = cp G) ∧
    2 ^ mCount G P ≤ Nat.card {Bs : Finset (Finset V) // IsCliquePartition G Bs ∧
      Bs.card = cp G} := by
  have hσ : ∀ τ, ∀ e ∈ extEdges G P, prescription G P τ e = 4 ∨ prescription G P τ e = 5 := by
    intro τ e he
    unfold prescription
    rw [dif_pos he]
    split_ifs <;> simp
  have hB := fun τ => theoremB G P hn hP hh (prescription G P τ) (hσ τ)
  let F := fun τ => Classical.choose (hB τ)
  have hF : ∀ τ, IsCliquePartition G (F τ) ∧ (F τ).card = cp G ∧
      ∀ e ∈ extEdges G P, ∃ B ∈ F τ, (∀ v ∈ e, v ∈ B) ∧ B.card = prescription G P τ e ∧
        extSize P B = 2 := by
    intro τ
    obtain ⟨h1, h2, -, -, h5, -⟩ := Classical.choose_spec (hB τ)
    exact ⟨h1, h2, h5⟩
  have hinj : Function.Injective F := by
    intro τ τ' heq
    funext ⟨e, he⟩
    obtain ⟨B, hB1, heB, hcB, -⟩ := (hF τ).2.2 e he
    obtain ⟨B', hB1', heB', hcB', -⟩ := (hF τ').2.2 e he
    rw [← heq] at hB1'
    have := block_unique_of_edge G (hF τ).1 (extEdges_subset he) hB1 hB1' heB heB'
    rw [this, hcB'] at hcB
    unfold prescription at hcB
    rw [dif_pos he, dif_pos he] at hcB
    cases h1 : τ ⟨e, he⟩ <;> cases h2 : τ' ⟨e, he⟩ <;> simp_all
  refine ⟨⟨F, hinj, fun τ => ⟨(hF τ).1, (hF τ).2.1⟩⟩, ?_⟩
  let F' : ({e // e ∈ extEdges G P} → Bool) →
      {Bs : Finset (Finset V) // IsCliquePartition G Bs ∧ Bs.card = cp G} :=
    fun τ => ⟨F τ, (hF τ).1, (hF τ).2.1⟩
  have hF' : Function.Injective F' := fun τ τ' h => hinj (congrArg Subtype.val h)
  have hcard := Nat.card_le_card_of_injective F' hF'
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] at hcard
  exact hcard

end PaperVI
