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
Paper VI — Section 7, packing form: the maximum gain `Σ (binom(|Q|,2) - 1)` over
edge-disjoint clique packings, and over fractional clique packings with unit edge
capacities, is `2u + 3m`.
-/
module

public import PaperVI.TrianglePacking

@[expose] public section

namespace PaperVI

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An edge-disjoint packing of cliques of order at least two. -/
structure IsCliquePacking (G : SimpleGraph V) (Bs : Finset (Finset V)) : Prop where
  two_le : ∀ B ∈ Bs, 2 ≤ B.card
  isClique : ∀ B ∈ Bs, G.IsClique (B : Set V)
  edgeDisjoint : ∀ B ∈ Bs, ∀ B' ∈ Bs, B ≠ B' → (B ∩ B').card ≤ 1

/-- A fractional clique packing with unit edge capacities. -/
structure IsFracCliquePacking (G : SimpleGraph V) (y : Finset V → ℝ) : Prop where
  nonneg : ∀ Q, 0 ≤ y Q
  support : ∀ Q, y Q ≠ 0 → 2 ≤ Q.card ∧ G.IsClique (Q : Set V)
  edge : ∀ u v, G.Adj u v → ∑ Q ∈ univ.filter (fun Q : Finset V => u ∈ Q ∧ v ∈ Q), y Q ≤ 1

/-- The gain `Σ_Q (binom(|Q|,2) - 1)` of a family of blocks. -/
def gain (Bs : Finset (Finset V)) : ℤ := ∑ B ∈ Bs, (((B.card.choose 2 : ℕ) : ℤ) - 1)

/-- The gain `Σ_Q y_Q (binom(|Q|,2) - 1)` of a fractional packing. -/
def fracGain (y : Finset V → ℝ) : ℝ := ∑ Q, y Q * (((Q.card.choose 2 : ℕ) : ℝ) - 1)

variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

theorem frac_packing_count_le {y : Finset V → ℝ} (hy : IsFracCliquePacking G y)
    (K : Finset (Sym2 V)) (hK : K ⊆ G.edgeFinset) :
    ∑ Q, y Q * ((insideFilter K Q).card : ℝ) ≤ K.card := by
  rw [sum_mul_card_insideFilter]
  calc ∑ e ∈ K, ∑ Q, (if ∀ v ∈ e.toFinset, v ∈ Q then y Q else 0) ≤ ∑ _e ∈ K, (1 : ℝ) := by
        refine sum_le_sum fun e he => ?_
        induction e using Sym2.ind with
        | h u v =>
          have hadj : G.Adj u v := by simpa using hK he
          refine le_trans (le_of_eq ?_) (hy.edge u v hadj)
          rw [← sum_filter]
          apply sum_congr _ (fun _ _ => rfl)
          ext Q
          simp only [mem_filter, mem_univ, true_and, Sym2.mem_toFinset, Sym2.mem_iff]
          constructor
          · intro h; exact ⟨h u (Or.inl rfl), h v (Or.inr rfl)⟩
          · rintro ⟨hu, hv⟩ x (rfl | rfl) <;> assumption
    _ = K.card := by simp

/-- Every fractional clique packing has gain at most `2u + 3m`. -/
theorem fracGain_le {y : Finset V → ℝ} (hy : IsFracCliquePacking G y) :
    fracGain y ≤ 2 * (uCount G P : ℝ) + 3 * mCount G P := by
  have h1 := frac_packing_count_le G hy (coreEdges G P) (coreEdges_subset G P)
  have h2 := frac_packing_count_le G hy (extEdges G P) (extEdges_subset' G P)
  have hpt : ∀ Q, y Q * (((Q.card.choose 2 : ℕ) : ℝ) - 1) ≤
      2 * (y Q * ((insideFilter (coreEdges G P) Q).card : ℝ)) +
        3 * (y Q * ((insideFilter (extEdges G P) Q).card : ℝ)) := by
    intro Q
    by_cases hQ : y Q = 0
    · simp [hQ]
    · obtain ⟨-, hcl⟩ := hy.support Q hQ
      rw [card_insideFilter_core G P Q hcl, card_insideFilter_ext G P Q hcl,
        card_eq_coreSize_add_extSize P Q]
      have hs := slack_nonneg (coreSize P Q) (extSize P Q)
      have hc := choose_two_add (coreSize P Q) (extSize P Q)
      unfold slack at hs
      have hs' : ((((coreSize P Q + extSize P Q).choose 2 : ℕ) : ℝ) - 1) ≤
          2 * ((coreSize P Q).choose 2 : ℝ) + 3 * ((extSize P Q).choose 2 : ℝ) := by
        have : ((((coreSize P Q + extSize P Q).choose 2 : ℕ) : ℤ) - 1) ≤
            2 * ((coreSize P Q).choose 2 : ℤ) + 3 * ((extSize P Q).choose 2 : ℤ) := by
          linarith
        exact_mod_cast this
      nlinarith [hy.nonneg Q]
  unfold fracGain uCount mCount
  calc ∑ Q, y Q * (((Q.card.choose 2 : ℕ) : ℝ) - 1)
      ≤ ∑ Q, (2 * (y Q * ((insideFilter (coreEdges G P) Q).card : ℝ)) +
          3 * (y Q * ((insideFilter (extEdges G P) Q).card : ℝ))) := sum_le_sum fun Q _ => hpt Q
    _ = 2 * ∑ Q, y Q * ((insideFilter (coreEdges G P) Q).card : ℝ) +
          3 * ∑ Q, y Q * ((insideFilter (extEdges G P) Q).card : ℝ) := by
        rw [sum_add_distrib, mul_sum, mul_sum]
    _ ≤ _ := by linarith

omit [DecidableRel G.Adj] in
/-- The indicator of an integral clique packing is a fractional clique packing. -/
theorem isFracCliquePacking_indicator {Bs : Finset (Finset V)} (hBs : IsCliquePacking G Bs) :
    IsFracCliquePacking G (fun Q => if Q ∈ Bs then 1 else 0) ∧
      fracGain (fun Q => if Q ∈ Bs then (1 : ℝ) else 0) = gain Bs := by
  refine ⟨⟨fun Q => by split_ifs <;> norm_num, fun Q hQ => ?_, fun u v huv => ?_⟩, ?_⟩
  · have hQ' : Q ∈ Bs := by by_contra h; simp [h] at hQ
    exact ⟨hBs.two_le Q hQ', hBs.isClique Q hQ'⟩
  · rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    by_contra hgt
    push_neg at hgt
    have h2 : 1 < ((univ.filter (fun T : Finset V => u ∈ T ∧ v ∈ T)).filter
        (fun T => T ∈ Bs)).card := by exact_mod_cast hgt
    obtain ⟨T, hT, T', hT', hne⟩ := one_lt_card.mp h2
    simp only [mem_filter, mem_univ, true_and] at hT hT'
    have := hBs.edgeDisjoint T hT.2 T' hT'.2 hne
    have hsub : ({u, v} : Finset V) ⊆ T ∩ T' := by
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact mem_inter.mpr ⟨hT.1.1, hT'.1.1⟩
      · exact mem_inter.mpr ⟨hT.1.2, hT'.1.2⟩
    have := card_le_card hsub
    rw [card_pair huv.ne] at this
    omega
  · unfold fracGain gain
    simp only [ite_mul, one_mul, zero_mul]
    rw [← sum_filter]
    push_cast
    refine sum_congr (by ext; simp) fun B _ => by ring

/-- **Gain form of (22) (Section 7).** Under the hypothesis of Theorem A, the maximum gain
over edge-disjoint clique packings, and over fractional clique packings with unit edge
capacities, equals `2u + 3m`. -/
theorem gain_eq (hn : 2 ≤ Fintype.card V) (hP : P.card = (Fintype.card V + 1) / 3)
    (hh : 18 * editDegree G P + 1 ≤ P.card) :
    IsGreatest {g : ℤ | ∃ Bs, IsCliquePacking G Bs ∧ gain Bs = g}
      (2 * (uCount G P : ℤ) + 3 * mCount G P) ∧
    IsGreatest {g : ℝ | ∃ y, IsFracCliquePacking G y ∧ fracGain y = g}
      (2 * (uCount G P : ℝ) + 3 * mCount G P) := by
  obtain ⟨-, -, hcp, Bs, hBs, hcard, -, -⟩ := theoremA G P hn hP hh
  have hpack : IsCliquePacking G Bs :=
    ⟨hBs.two_le, hBs.isClique, fun B hB B' hB' hne =>
      inter_card_le_one_of_isCliquePartition G hBs hB hB' hne⟩
  obtain ⟨h1, h2, h3⟩ := partition_sums G P hBs
  have hgain : gain Bs = 2 * (uCount G P : ℤ) + 3 * mCount G P := by
    unfold gain
    have : ∀ B ∈ Bs, (((B.card.choose 2 : ℕ) : ℤ) - 1) = ((coreSize P B).choose 2 : ℤ) +
        ((extSize P B).choose 2 : ℤ) + ((coreSize P B * extSize P B : ℕ) : ℤ) - 1 := by
      intro B _
      rw [card_eq_coreSize_add_extSize P B, choose_two_add]
      push_cast; ring
    rw [sum_congr rfl this]
    simp only [sum_sub_distrib, sum_add_distrib, sum_const, nsmul_eq_mul, mul_one]
    rw [← Nat.cast_sum, ← Nat.cast_sum, ← Nat.cast_sum, h1, h2, h3, hcard]
    linarith
  obtain ⟨hind, hindg⟩ := isFracCliquePacking_indicator G hpack
  refine ⟨⟨⟨Bs, hpack, hgain⟩, ?_⟩, ⟨⟨_, hind, by rw [hindg, hgain]; push_cast; ring⟩, ?_⟩⟩
  · rintro g ⟨Bs', hBs', rfl⟩
    obtain ⟨hind', hindg'⟩ := isFracCliquePacking_indicator G hBs'
    have := fracGain_le G P hind'
    rw [hindg'] at this
    exact_mod_cast this
  · rintro g ⟨y, hy, rfl⟩
    exact fracGain_le G P hy

end PaperVI
