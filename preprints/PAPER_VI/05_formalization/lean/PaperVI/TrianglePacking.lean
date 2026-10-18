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
Paper VI — Section 4, formula (18): the integral and fractional triangle packing numbers
both equal `u + m`.
-/
module

public import PaperVI.TheoremC
public import PaperVI.Fractional

@[expose] public section

namespace PaperVI

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An edge-disjoint packing of triangles of `G`. -/
structure IsTrianglePacking (G : SimpleGraph V) (Ts : Finset (Finset V)) : Prop where
  card_eq : ∀ T ∈ Ts, T.card = 3
  isClique : ∀ T ∈ Ts, G.IsClique (T : Set V)
  edgeDisjoint : ∀ T ∈ Ts, ∀ T' ∈ Ts, T ≠ T' → (T ∩ T').card ≤ 1

/-- A fractional triangle packing: nonnegative weights on triangles of `G` with total weight
at most one on every edge. -/
structure IsFracTrianglePacking (G : SimpleGraph V) (w : Finset V → ℝ) : Prop where
  nonneg : ∀ T, 0 ≤ w T
  support : ∀ T, w T ≠ 0 → T.card = 3 ∧ G.IsClique (T : Set V)
  edge : ∀ u v, G.Adj u v → ∑ T ∈ univ.filter (fun T : Finset V => u ∈ T ∧ v ∈ T), w T ≤ 1

variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

/-- Exchanging the order of summation between edges and vertex sets. -/
theorem sum_mul_card_insideFilter (w : Finset V → ℝ) (K : Finset (Sym2 V)) :
    ∑ Q, w Q * ((insideFilter K Q).card : ℝ) =
      ∑ e ∈ K, ∑ Q, (if ∀ v ∈ e.toFinset, v ∈ Q then w Q else 0) := by
  calc ∑ Q, w Q * ((insideFilter K Q).card : ℝ)
      = ∑ Q, ∑ e ∈ K, (if ∀ v ∈ e.toFinset, v ∈ Q then w Q else 0) := by
        refine sum_congr rfl fun Q _ => ?_
        unfold insideFilter
        rw [card_filter, Nat.cast_sum, mul_sum]
        refine sum_congr rfl fun e _ => ?_
        split_ifs <;> simp
    _ = _ := sum_comm

/-- Every edge of `K ⊆ E(G)` carries weight at most one in a fractional triangle packing. -/
theorem frac_triangle_count_le {w : Finset V → ℝ} (hw : IsFracTrianglePacking G w)
    (K : Finset (Sym2 V)) (hK : K ⊆ G.edgeFinset) :
    ∑ Q, w Q * ((insideFilter K Q).card : ℝ) ≤ K.card := by
  rw [sum_mul_card_insideFilter]
  calc ∑ e ∈ K, ∑ Q, (if ∀ v ∈ e.toFinset, v ∈ Q then w Q else 0) ≤ ∑ _e ∈ K, (1 : ℝ) := by
        refine sum_le_sum fun e he => ?_
        induction e using Sym2.ind with
        | h u v =>
          have hadj : G.Adj u v := by simpa using hK he
          refine le_trans (le_of_eq ?_) (hw.edge u v hadj)
          rw [← sum_filter]
          apply sum_congr _ (fun _ _ => rfl)
          ext Q
          simp only [mem_filter, mem_univ, true_and, Sym2.mem_toFinset, Sym2.mem_iff]
          constructor
          · intro h; exact ⟨h u (Or.inl rfl), h v (Or.inr rfl)⟩
          · rintro ⟨hu, hv⟩ x (rfl | rfl) <;> assumption
    _ = K.card := by simp

/-- The internal-edge certificate: every fractional triangle packing has value at most
`u + m`. -/
theorem frac_triangle_le {w : Finset V → ℝ} (hw : IsFracTrianglePacking G w) :
    fracValue w ≤ (uCount G P : ℝ) + mCount G P := by
  have h1 := frac_triangle_count_le G hw (coreEdges G P) (coreEdges_subset G P)
  have h2 := frac_triangle_count_le G hw (extEdges G P) (extEdges_subset' G P)
  have hpt : ∀ Q, w Q ≤ w Q * ((insideFilter (coreEdges G P) Q).card : ℝ) +
      w Q * ((insideFilter (extEdges G P) Q).card : ℝ) := by
    intro Q
    by_cases hQ : w Q = 0
    · simp [hQ]
    · obtain ⟨h3, hcl⟩ := hw.support Q hQ
      rw [card_insideFilter_core G P Q hcl, card_insideFilter_ext G P Q hcl, ← mul_add]
      have hc := card_eq_coreSize_add_extSize P Q
      have : (1 : ℝ) ≤ ((coreSize P Q).choose 2 : ℕ) + ((extSize P Q).choose 2 : ℕ) := by
        have : 1 ≤ (coreSize P Q).choose 2 + (extSize P Q).choose 2 := by
          rcases (by omega : (coreSize P Q = 0 ∧ extSize P Q = 3) ∨
              (coreSize P Q = 1 ∧ extSize P Q = 2) ∨ (coreSize P Q = 2 ∧ extSize P Q = 1) ∨
              (coreSize P Q = 3 ∧ extSize P Q = 0)) with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
            rw [e1, e2] <;> decide
        exact_mod_cast this
      nlinarith [hw.nonneg Q]
  unfold fracValue uCount mCount
  calc ∑ Q, w Q ≤ ∑ Q, (w Q * ((insideFilter (coreEdges G P) Q).card : ℝ) +
        w Q * ((insideFilter (extEdges G P) Q).card : ℝ)) := sum_le_sum fun Q _ => hpt Q
    _ = _ := sum_add_distrib
    _ ≤ _ := add_le_add h1 h2

omit [Fintype V] [DecidableRel G.Adj] in
/-- Blocks of a clique partition are pairwise edge-disjoint. -/
theorem inter_card_le_one_of_isCliquePartition {Bs : Finset (Finset V)}
    (hBs : IsCliquePartition G Bs) {B B' : Finset V} (hB : B ∈ Bs) (hB' : B' ∈ Bs)
    (hne : B ≠ B') : (B ∩ B').card ≤ 1 := by
  by_contra h
  push_neg at h
  obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp h
  rw [mem_inter] at hu hv
  have hadj := hBs.isClique B hB hu.1 hv.1 huv
  obtain ⟨B0, -, h0⟩ := hBs.existsUnique u v hadj
  exact hne ((h0 B ⟨hB, hu.1, hv.1⟩).trans (h0 B' ⟨hB', hu.2, hv.2⟩).symm)

/-- **Formula (18).** Under the hypothesis of Theorem A, the maximum number of edge-disjoint
triangles and the maximum value of a fractional triangle packing both equal `u + m`. -/
theorem triangle_packing_eq (hn : 2 ≤ Fintype.card V) (hP : P.card = (Fintype.card V + 1) / 3)
    (hh : 18 * editDegree G P + 1 ≤ P.card) :
    IsGreatest {k : ℕ | ∃ Ts, IsTrianglePacking G Ts ∧ Ts.card = k} (uCount G P + mCount G P) ∧
    IsGreatest {v : ℝ | ∃ w, IsFracTrianglePacking G w ∧ fracValue w = v}
      ((uCount G P : ℝ) + mCount G P) := by
  obtain ⟨-, -, -, Bs, hBs, -, htypes, h12, h21⟩ := theoremC G P hn hP hh
  set Ts := Bs.filter (fun B => B.card = 3)
  have hTs : IsTrianglePacking G Ts := by
    refine ⟨fun T hT => (mem_filter.mp hT).2, fun T hT => hBs.isClique T (mem_filter.mp hT).1,
      fun T hT T' hT' hne => inter_card_le_one_of_isCliquePartition G hBs
        (mem_filter.mp hT).1 (mem_filter.mp hT').1 hne⟩
  have hTcard : Ts.card = uCount G P + mCount G P := by
    rw [← h12, ← h21]
    unfold typeCount
    rw [← card_union_of_disjoint]
    · congr 1
      ext B
      simp only [Ts, mem_filter, mem_union]
      constructor
      · rintro ⟨hB, h3⟩
        rw [card_eq_coreSize_add_extSize P B] at h3
        rcases htypes B hB with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · omega
        · exact Or.inl ⟨hB, h1, h2⟩
        · exact Or.inr ⟨hB, h1, h2⟩
      · rintro (⟨hB, h1, h2⟩ | ⟨hB, h1, h2⟩) <;>
          exact ⟨hB, by rw [card_eq_coreSize_add_extSize P B]; omega⟩
    · rw [disjoint_left]
      intro B h1 h2
      simp only [mem_filter] at h1 h2
      omega
  -- indicator of the packing
  have hind : IsFracTrianglePacking G (fun T => if T ∈ Ts then 1 else 0) := by
    refine ⟨fun T => by split_ifs <;> norm_num, fun T hT => ?_, fun u v huv => ?_⟩
    · have hT' : T ∈ Ts := by by_contra h; simp [h] at hT
      exact ⟨hTs.card_eq T hT', hTs.isClique T hT'⟩
    · rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
      obtain ⟨B, hB, hu⟩ := hBs.existsUnique u v huv
      have : (univ.filter (fun T : Finset V => u ∈ T ∧ v ∈ T)).filter (fun T => T ∈ Ts) ⊆ {B} := by
        intro T hT
        simp only [mem_filter, mem_univ, true_and] at hT
        rw [mem_singleton]
        exact hu T ⟨(mem_filter.mp hT.2).1, hT.1.1, hT.1.2⟩
      have := card_le_card this
      rw [card_singleton] at this
      exact_mod_cast this
  have hindv : fracValue (fun T => if T ∈ Ts then (1 : ℝ) else 0) = Ts.card := by
    unfold fracValue
    rw [← sum_filter, sum_const]
    simp
  refine ⟨⟨⟨Ts, hTs, hTcard⟩, ?_⟩, ⟨⟨_, hind, by rw [hindv, hTcard]; push_cast; ring⟩, ?_⟩⟩
  · rintro k ⟨Ts', hTs', rfl⟩
    have hind' : IsFracTrianglePacking G (fun T => if T ∈ Ts' then 1 else 0) := by
      refine ⟨fun T => by split_ifs <;> norm_num, fun T hT => ?_, fun u v huv => ?_⟩
      · have hT' : T ∈ Ts' := by by_contra h; simp [h] at hT
        exact ⟨hTs'.card_eq T hT', hTs'.isClique T hT'⟩
      · rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
        by_contra hgt
        push_neg at hgt
        have h2 : 1 < ((univ.filter (fun T : Finset V => u ∈ T ∧ v ∈ T)).filter
            (fun T => T ∈ Ts')).card := by exact_mod_cast hgt
        obtain ⟨T, hT, T', hT', hne⟩ := one_lt_card.mp h2
        simp only [mem_filter, mem_univ, true_and] at hT hT'
        have := hTs'.edgeDisjoint T hT.2 T' hT'.2 hne
        have hsub : ({u, v} : Finset V) ⊆ T ∩ T' := by
          intro z hz
          simp only [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact mem_inter.mpr ⟨hT.1.1, hT'.1.1⟩
          · exact mem_inter.mpr ⟨hT.1.2, hT'.1.2⟩
        have := card_le_card hsub
        rw [card_pair huv.ne] at this
        omega
    have hv := frac_triangle_le G P hind'
    have : fracValue (fun T => if T ∈ Ts' then (1 : ℝ) else 0) = Ts'.card := by
      unfold fracValue
      rw [← sum_filter, sum_const]
      simp
    rw [this] at hv
    exact_mod_cast hv
  · rintro v ⟨w, hw, rfl⟩
    exact frac_triangle_le G P hw

end PaperVI
