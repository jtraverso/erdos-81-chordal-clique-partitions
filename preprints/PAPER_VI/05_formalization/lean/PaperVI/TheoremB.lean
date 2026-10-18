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
Paper VI — Theorem B (prescribed exterior blocks) and the `2^m` optimal partitions.
-/
module

public import PaperVI.TheoremA

@[expose] public section

namespace PaperVI

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The candidate estimate (19) for Theorem B, in untruncated form. -/
theorem arith_candidates_B {p q h k bx by_ dx dy sat nD m : ℕ} (hq1 : q ≤ 2 * p + 1)
    (hp : 63 * h ≤ p) (h1 : p ≤ k + bx + by_ + 3 * dx + 3 * dy + sat)
    (h2 : bx + dx + 1 ≤ h) (h3 : by_ + dy + 1 ≤ h) (h4 : 7 * h * sat ≤ 3 * nD)
    (h5 : nD + 1 ≤ m) (h6 : 2 * m ≤ q * h) : 30 * h + 3 ≤ k := by
  have hh : 1 ≤ h := by omega
  have hs : 14 * sat < 3 * q := by
    by_contra hc
    push_neg at hc
    have := Nat.mul_le_mul_right h hc
    nlinarith
  omega

variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

/-- The construction behind Theorem B, for a prescription `σ` of block orders `4` or `5`. -/
theorem exists_partition_B (hq1 : Pᶜ.card ≤ 2 * P.card + 1) (hq0 : 2 * P.card ≤ Pᶜ.card + 1)
    (hpq : P.card ≤ Pᶜ.card) (hh : 63 * editDegree G P ≤ P.card) (σ : Sym2 V → ℕ)
    (hσ : ∀ e ∈ extEdges G P, σ e = 4 ∨ σ e = 5) :
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ ∀ B ∈ Bs,
      (coreSize P B = 1 ∧ extSize P B = 1) ∨ (coreSize P B = 2 ∧ extSize P B = 1) ∨
      ∃ e ∈ extEdges G P, (∀ v ∈ e, v ∈ B) ∧ coreSize P B = σ e - 2 ∧ extSize P B = 2 :=
  exists_partition_of_lift G P (σ := fun e => σ e - 2) (c := 3)
    (r := 7 * editDegree G P) (need := 30 * editDegree G P + 3)
    (fun e he => by rcases hσ e he with h | h <;> omega)
    (fun e he => by rcases hσ e he with h | h <;> rw [h] <;> omega)
    (fun k bx by_ dx dy sat nD h1 h2 h3 h4 h5 h6 =>
      arith_candidates_B hq1 hh h1 h2 h3 h4 h5 h6)
    (by omega)

/-- Counting part of Theorem B: any clique partition whose blocks have the types produced by
the construction (crossing edges, triangles of type `(2,1)`, and a block of core size
`σ e - 2` with two exterior vertices around every exterior edge `e`) is optimal, and its block
numbers are as stated in Theorem B. -/
theorem theoremB_of_partition (hP : P.card = (Fintype.card V + 1) / 3) (σ : Sym2 V → ℕ)
    (hσ : ∀ e ∈ extEdges G P, σ e = 4 ∨ σ e = 5) {Bs : Finset (Finset V)}
    (hBs : IsCliquePartition G Bs)
    (htypes : ∀ B ∈ Bs, (coreSize P B = 1 ∧ extSize P B = 1) ∨
      (coreSize P B = 2 ∧ extSize P B = 1) ∨
      ∃ e ∈ extEdges G P, (∀ v ∈ e, v ∈ B) ∧ coreSize P B = σ e - 2 ∧ extSize P B = 2) :
    Bs.card = cp G ∧
      (cp G : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P ∧
      (cp G : ℤ) = Mval (Fintype.card V) + Cdef G P - Adef G P - 2 * mCount G P ∧
      (∀ e ∈ extEdges G P, ∃ B ∈ Bs, (∀ v ∈ e, v ∈ B) ∧ B.card = σ e ∧ extSize P B = 2) ∧
      (∀ B ∈ Bs, (coreSize P B = 2 ∧ extSize P B = 1) ∨ (coreSize P B = 1 ∧ extSize P B = 1) ∨
        ∃ e ∈ extEdges G P, (∀ v ∈ e, v ∈ B) ∧ B.card = σ e ∧ extSize P B = 2) ∧
      ((Bs.filter (fun B => B.card = 5)).card : ℤ) =
        ((extEdges G P).filter (fun e => σ e = 5)).card ∧
      ((Bs.filter (fun B => B.card = 4)).card : ℤ) =
        (mCount G P : ℤ) - ((extEdges G P).filter (fun e => σ e = 5)).card ∧
      ((Bs.filter (fun B => B.card = 3)).card : ℤ) =
        (uCount G P : ℤ) - mCount G P - 2 * ((extEdges G P).filter (fun e => σ e = 5)).card ∧
      ((Bs.filter (fun B => B.card = 2)).card : ℤ) =
        (sCount G P : ℤ) - 2 * uCount G P - 2 * mCount G P +
          2 * ((extEdges G P).filter (fun e => σ e = 5)).card := by
  -- block types and zero slack
  have htypes4 : ∀ B ∈ Bs, (coreSize P B = 1 ∧ extSize P B = 1) ∨
      (coreSize P B = 2 ∧ extSize P B = 1) ∨ (coreSize P B = 2 ∧ extSize P B = 2) ∨
      (coreSize P B = 3 ∧ extSize P B = 2) ∨ (coreSize P B = 1 ∧ extSize P B = 2) := by
    intro B hB
    rcases htypes B hB with h | h | ⟨e, he, -, hc, hb⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rcases hσ e he with h | h <;> rw [h] at hc
      · exact Or.inr (Or.inr (Or.inl ⟨hc, hb⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hc, hb⟩)))
  have htypesB : ∀ B ∈ Bs, (coreSize P B = 1 ∧ extSize P B = 1) ∨
      (coreSize P B = 2 ∧ extSize P B = 1) ∨ (coreSize P B = 2 ∧ extSize P B = 2) ∨
      (coreSize P B = 3 ∧ extSize P B = 2) := by
    intro B hB
    rcases htypes B hB with h | h | ⟨e, he, -, hc, hb⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rcases hσ e he with h | h <;> rw [h] at hc
      · exact Or.inr (Or.inr (Or.inl ⟨hc, hb⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hc, hb⟩))
  have hslack : ∀ B ∈ Bs, slack (coreSize P B) (extSize P B) = 0 := by
    intro B hB
    rw [slack_eq_zero_iff]
    rcases htypes B hB with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨e, he, -, hc, hb⟩
    · simp [h1, h2]
    · simp [h1, h2]
    · rcases hσ e he with h | h <;> rw [h] at hc <;> simp [hc, hb]
  have hid := slack_identity G P hBs
  rw [sum_eq_zero hslack] at hid
  have hlow := cp_ge G P
  have h1 := cp_le hBs
  have hcp : Bs.card = cp G := by omega
  have hcpZ : (cp G : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P := by omega
  -- counts
  obtain ⟨cu, cm, cs, -⟩ := type_counts G P hBs htypes4
  set k := ((extEdges G P).filter (fun e => σ e = 5)).card with hk
  have hN32 : typeCount P Bs 3 2 = k := by
    rw [typeCount_ext_eq G P hBs htypes 3, hk]
    congr 1
    apply filter_congr
    intro e he
    rcases hσ e he with h | h <;> rw [h] <;> simp
  have hN22 : typeCount P Bs 2 2 = ((extEdges G P).filter (fun e => ¬ σ e = 5)).card := by
    rw [typeCount_ext_eq G P hBs htypes 2]
    congr 1
    apply filter_congr
    intro e he
    rcases hσ e he with h | h <;> rw [h] <;> simp
  have hN12 : typeCount P Bs 1 2 = 0 := by
    rw [typeCount_ext_eq G P hBs htypes 1, card_eq_zero, filter_eq_empty_iff]
    intro e he
    rcases hσ e he with h | h <;> rw [h] <;> simp
  have hm : mCount G P = ((extEdges G P).filter (fun e => ¬ σ e = 5)).card + k := by
    rw [hk, mCount, add_comm]
    exact (card_filter_add_card_filter_not _).symm
  have hcardType : ∀ j a b, (∀ B ∈ Bs, B.card = j ↔ coreSize P B = a ∧ extSize P B = b) →
      (Bs.filter (fun B => B.card = j)).card = typeCount P Bs a b := by
    intro j a b hj
    unfold typeCount
    congr 1
    exact filter_congr hj
  have hc5 := hcardType 5 3 2 (fun B hB => by
    rw [card_eq_coreSize_add_extSize P B]
    rcases htypesB B hB with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega)
  have hc4 := hcardType 4 2 2 (fun B hB => by
    rw [card_eq_coreSize_add_extSize P B]
    rcases htypesB B hB with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega)
  have hc3 := hcardType 3 2 1 (fun B hB => by
    rw [card_eq_coreSize_add_extSize P B]
    rcases htypesB B hB with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega)
  have hc2 := hcardType 2 1 1 (fun B hB => by
    rw [card_eq_coreSize_add_extSize P B]
    rcases htypesB B hB with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega)
  refine ⟨hcp, hcpZ, ?_, ?_, ?_, by rw [hc5, hN32], by rw [hc4]; omega,
    by rw [hc3]; omega, by rw [hc2]; omega⟩
  · -- the formula with `M(n)`
    have hM := Mval_eq (Fintype.card V)
    rw [← hP] at hM
    have hpn : P.card ≤ Fintype.card V := card_le_univ P
    rw [hcpZ, hM]
    unfold Cdef Adef
    push_cast [hpn]
    ring
  · intro e he
    obtain ⟨B, hB, heB⟩ := exists_block_of_edge G hBs (extEdges_subset he)
    have ht := type_of_block_containing_ext G P htypes he hB heB
    refine ⟨B, hB, heB, ?_, ht.2⟩
    rw [card_eq_coreSize_add_extSize P B, ht.1, ht.2]
    rcases hσ e he with h | h <;> omega
  · intro B hB
    rcases htypes B hB with h | h | ⟨e, he, heB, hc, hb⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · refine Or.inr (Or.inr ⟨e, he, heB, ?_, hb⟩)
      rw [card_eq_coreSize_add_extSize P B, hc, hb]
      rcases hσ e he with h | h <;> omega


/-- **Theorem B (prescribed exterior blocks).** Let `n = |V| ≥ 2`, `p = ⌊(n+1)/3⌋ = |P|` and
`p ≥ 63h` (this includes `h = 0`). For every prescription `σ` of the orders `4` or `5` to the
exterior edges, there is an optimal clique partition of `G` (an exact partition of `E(G)`) in
which every exterior edge `xy` lies in a block `K_{σ(xy)}` with exactly two exterior vertices,
and every other block is a triangle of type `(2,1)` or a crossing single edge. With
`k = |σ⁻¹(5)|` its block counts are `N₅ = k`, `N₄ = m - k`, `N₃ = u - m - 2k`,
`N₂ = s - 2u - 2m + 2k`, and `cp(G) = s - u - 2m = M(n) + C - A - 2m`.

The manuscript hypothesis `n ≥ 2` (`hn`) is kept as stated; the formal proof does not
need it. -/
theorem theoremB (hn : 2 ≤ Fintype.card V) (hP : P.card = (Fintype.card V + 1) / 3)
    (hh : 63 * editDegree G P ≤ P.card) (σ : Sym2 V → ℕ)
    (hσ : ∀ e ∈ extEdges G P, σ e = 4 ∨ σ e = 5) :
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ Bs.card = cp G ∧
      (cp G : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P ∧
      (cp G : ℤ) = Mval (Fintype.card V) + Cdef G P - Adef G P - 2 * mCount G P ∧
      (∀ e ∈ extEdges G P, ∃ B ∈ Bs, (∀ v ∈ e, v ∈ B) ∧ B.card = σ e ∧ extSize P B = 2) ∧
      (∀ B ∈ Bs, (coreSize P B = 2 ∧ extSize P B = 1) ∨ (coreSize P B = 1 ∧ extSize P B = 1) ∨
        ∃ e ∈ extEdges G P, (∀ v ∈ e, v ∈ B) ∧ B.card = σ e ∧ extSize P B = 2) ∧
      ((Bs.filter (fun B => B.card = 5)).card : ℤ) =
        ((extEdges G P).filter (fun e => σ e = 5)).card ∧
      ((Bs.filter (fun B => B.card = 4)).card : ℤ) =
        (mCount G P : ℤ) - ((extEdges G P).filter (fun e => σ e = 5)).card ∧
      ((Bs.filter (fun B => B.card = 3)).card : ℤ) =
        (uCount G P : ℤ) - mCount G P - 2 * ((extEdges G P).filter (fun e => σ e = 5)).card ∧
      ((Bs.filter (fun B => B.card = 2)).card : ℤ) =
        (sCount G P : ℤ) - 2 * uCount G P - 2 * mCount G P +
          2 * ((extEdges G P).filter (fun e => σ e = 5)).card := by
  have hq : Pᶜ.card = Fintype.card V - P.card := card_compl P
  have hq1 : Pᶜ.card ≤ 2 * P.card + 1 := by
    rw [hq, hP]; exact q_le_two_p_add_one _
  have hq0 : 2 * P.card ≤ Pᶜ.card + 1 := by
    rw [hq, hP]; exact two_p_le_q_add_one _
  have hpq : P.card ≤ Pᶜ.card := by
    rw [hq, hP]; exact p_le_q _
  obtain ⟨Bs, hBs, htypes⟩ := exists_partition_B G P hq1 hq0 hpq hh σ hσ
  exact ⟨Bs, hBs, theoremB_of_partition G P hP σ hσ hBs htypes⟩

end PaperVI
