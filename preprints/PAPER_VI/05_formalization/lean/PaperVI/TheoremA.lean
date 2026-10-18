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
Paper VI — Theorem A (exact local formula), including the balanced variant `q = 2p`.
-/
module

public import PaperVI.Engine

@[expose] public section

namespace PaperVI

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The candidate estimate (15) for Theorem A, in untruncated form. -/
theorem arith_candidates_A {p q h k bx by_ dx dy sat nD m : ℕ} (hq1 : q ≤ 2 * p + 1)
    (hq2 : p + 18 * h ≤ q) (h1 : p ≤ k + bx + by_ + 2 * dx + 2 * dy + sat)
    (h2 : bx + dx + 1 ≤ h) (h3 : by_ + dy + 1 ≤ h) (h4 : 4 * h * sat ≤ 2 * nD)
    (h5 : nD + 1 ≤ m) (h6 : 2 * m ≤ q * h) : 5 * h + 2 ≤ k := by
  have hh : 1 ≤ h := by omega
  have hs : 4 * sat < q := by
    by_contra hc
    push_neg at hc
    have := Nat.mul_le_mul_right h hc
    nlinarith
  omega

/-- Membership in the zero-slack family used in Theorem A. -/
def IsTypeA (P B : Finset V) : Prop :=
  (coreSize P B = 2 ∧ extSize P B = 2) ∨ (coreSize P B = 2 ∧ extSize P B = 1) ∨
    (coreSize P B = 1 ∧ extSize P B = 1)

variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

/-- The construction behind Theorem A, under the general arithmetic condition
`q ≤ 2p + 1` and `p + 18h ≤ q`. -/
theorem exists_partition_A (hq1 : Pᶜ.card ≤ 2 * P.card + 1)
    (hq2 : P.card + 18 * editDegree G P ≤ Pᶜ.card) :
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ ∀ B ∈ Bs, IsTypeA P B := by
  obtain ⟨Bs, hBs, htypes⟩ := exists_partition_of_lift G P (σ := fun _ => 2) (c := 2)
    (r := 4 * editDegree G P) (need := 5 * editDegree G P + 2)
    (fun _ _ => le_rfl) (fun _ _ => by omega)
    (fun k bx by_ dx dy sat nD h1 h2 h3 h4 h5 h6 =>
      arith_candidates_A hq1 hq2 h1 h2 h3 (by simpa using h4) h5 (by simpa using h6))
    (by omega)
  refine ⟨Bs, hBs, fun B hB => ?_⟩
  rcases htypes B hB with h | h | ⟨e, -, -, hc, hb⟩
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)
  · exact Or.inl ⟨hc, hb⟩

/-- Conclusions of Theorem A from the existence of a type-A clique partition. -/
theorem theoremA_conclusions {Bs : Finset (Finset V)} (hBs : IsCliquePartition G Bs)
    (htypes : ∀ B ∈ Bs, IsTypeA P B) :
    (cp G : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P ∧
    cp G = cpLe 4 G ∧ Bs.card = cp G ∧ (∀ B ∈ Bs, B.card ≤ 4) ∧
    typeCount P Bs 2 2 = mCount G P ∧
    (typeCount P Bs 2 1 : ℤ) = (uCount G P : ℤ) - mCount G P ∧
    (typeCount P Bs 1 1 : ℤ) = (sCount G P : ℤ) - 2 * uCount G P - 2 * mCount G P := by
  have hslack : ∀ B ∈ Bs, slack (coreSize P B) (extSize P B) = 0 := by
    intro B hB
    rw [slack_eq_zero_iff]
    rcases htypes B hB with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  have hid := slack_identity G P hBs
  rw [sum_eq_zero hslack] at hid
  have hle4 : ∀ B ∈ Bs, B.card ≤ 4 := by
    intro B hB
    rw [card_eq_coreSize_add_extSize P B]
    rcases htypes B hB with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hlow := cp_ge G P
  have h1 := cp_le hBs
  have h2 := cpLe_le hBs hle4
  have h3 := cp_le_cpLe G (r := 4) (by norm_num)
  have hcp : Bs.card = cp G := by omega
  obtain ⟨cu, cm, cs, -⟩ := type_counts G P hBs (fun B hB => by
    rcases htypes B hB with h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inl h)
  have z32 : typeCount P Bs 3 2 = 0 := by
    unfold typeCount
    rw [card_eq_zero, filter_eq_empty_iff]
    intro B hB ⟨h1, h2⟩
    rcases htypes B hB with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ <;> omega
  have z12 : typeCount P Bs 1 2 = 0 := by
    unfold typeCount
    rw [card_eq_zero, filter_eq_empty_iff]
    intro B hB ⟨h1, h2⟩
    rcases htypes B hB with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ <;> omega
  refine ⟨by omega, by omega, hcp, hle4, by omega, by omega, by omega⟩

/-- **Theorem A (exact local formula).** Let `n = |V| ≥ 2`, `p = ⌊(n+1)/3⌋ = |P|`,
`h = Δ(G △ (K_P ∨ I_O))`. If `p ≥ 18h + 1`, then
`cp(G) = cp_{≤4}(G) = s - u - 2m = M(n) + C - A - 2m`, and there is an optimal clique
partition (an exact partition of `E(G)` into cliques) consisting of `m` blocks `K_4` of type
`(2,2)`, `u - m` triangles of type `(2,1)` and `s - 2u - 2m` crossing single edges.

The manuscript hypothesis `n ≥ 2` (`hn`) is kept as stated; the formal proof does not
need it. -/
theorem theoremA (hn : 2 ≤ Fintype.card V) (hP : P.card = (Fintype.card V + 1) / 3)
    (hh : 18 * editDegree G P + 1 ≤ P.card) :
    (cp G : ℤ) = Mval (Fintype.card V) + Cdef G P - Adef G P - 2 * mCount G P ∧
    cp G = cpLe 4 G ∧
    (cp G : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P ∧
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ Bs.card = cp G ∧
      (∀ B ∈ Bs, B.card ≤ 4) ∧ (∀ B ∈ Bs, IsTypeA P B) ∧
      typeCount P Bs 2 2 = mCount G P ∧
      (typeCount P Bs 2 1 : ℤ) = (uCount G P : ℤ) - mCount G P ∧
      (typeCount P Bs 1 1 : ℤ) = (sCount G P : ℤ) - 2 * uCount G P - 2 * mCount G P := by
  have hq : Pᶜ.card = Fintype.card V - P.card := card_compl P
  have hq1 : Pᶜ.card ≤ 2 * P.card + 1 := by
    rw [hq, hP]; exact q_le_two_p_add_one _
  have hq2 : P.card + 18 * editDegree G P ≤ Pᶜ.card := by
    have := two_p_le_q_add_one (Fintype.card V)
    rw [hq, hP] at *; omega
  obtain ⟨Bs, hBs, htypes⟩ := exists_partition_A G P hq1 hq2
  obtain ⟨hcp, h4, hcard, hle, c22, c21, c11⟩ := theoremA_conclusions G P hBs htypes
  refine ⟨?_, h4, hcp, Bs, hBs, hcard, hle, htypes, c22, c21, c11⟩
  have hM := Mval_eq (Fintype.card V)
  rw [← hP] at hM
  have hpn : P.card ≤ Fintype.card V := card_le_univ P
  rw [hcp, hM]
  unfold Cdef Adef
  push_cast [hpn]
  ring

/-- **Theorem A, balanced variant.** When `q = 2p`, the weaker condition `p ≥ 18h`
suffices. -/
theorem theoremA_balanced (hP : P.card = (Fintype.card V + 1) / 3)
    (hbal : Fintype.card V - P.card = 2 * P.card) (hh : 18 * editDegree G P ≤ P.card) :
    (cp G : ℤ) = Mval (Fintype.card V) + Cdef G P - Adef G P - 2 * mCount G P ∧
    cp G = cpLe 4 G ∧
    (cp G : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P ∧
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ Bs.card = cp G ∧
      (∀ B ∈ Bs, B.card ≤ 4) ∧ (∀ B ∈ Bs, IsTypeA P B) ∧
      typeCount P Bs 2 2 = mCount G P ∧
      (typeCount P Bs 2 1 : ℤ) = (uCount G P : ℤ) - mCount G P ∧
      (typeCount P Bs 1 1 : ℤ) = (sCount G P : ℤ) - 2 * uCount G P - 2 * mCount G P := by
  have hq : Pᶜ.card = Fintype.card V - P.card := card_compl P
  have hq1 : Pᶜ.card ≤ 2 * P.card + 1 := by omega
  have hq2 : P.card + 18 * editDegree G P ≤ Pᶜ.card := by omega
  obtain ⟨Bs, hBs, htypes⟩ := exists_partition_A G P hq1 hq2
  obtain ⟨hcp, h4, hcard, hle, c22, c21, c11⟩ := theoremA_conclusions G P hBs htypes
  refine ⟨?_, h4, hcp, Bs, hBs, hcard, hle, htypes, c22, c21, c11⟩
  have hM := Mval_eq (Fintype.card V)
  rw [← hP] at hM
  have hpn : P.card ≤ Fintype.card V := card_le_univ P
  rw [hcp, hM]
  unfold Cdef Adef
  push_cast [hpn]
  ring

end PaperVI
