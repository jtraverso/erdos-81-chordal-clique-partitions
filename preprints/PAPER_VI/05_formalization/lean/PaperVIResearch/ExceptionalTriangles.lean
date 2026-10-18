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
Paper VI research round — Theorem E, part 4 (E2): triangle packings of the one-exceptional-
vertex graph, `ν₃(G) = ν₃*(G) = u + min(a,b)`.
-/
module

public import PaperVIResearch.ExceptionalTheorem

@[expose] public section

namespace PaperVI

namespace Research

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The indicator of an integral triangle packing is a fractional triangle packing. -/
theorem isFracTrianglePacking_indicator (G : SimpleGraph V) {Ts : Finset (Finset V)}
    (hTs : IsTrianglePacking G Ts) :
    IsFracTrianglePacking G (fun T => if T ∈ Ts then 1 else 0) ∧
      fracValue (fun T => if T ∈ Ts then (1 : ℝ) else 0) = Ts.card := by
  refine ⟨⟨fun T => by split_ifs <;> norm_num, fun T hT => ?_, fun u v huv => ?_⟩, ?_⟩
  · have hT' : T ∈ Ts := by by_contra h; simp [h] at hT
    exact ⟨hTs.card_eq T hT', hTs.isClique T hT'⟩
  · rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    by_contra hgt
    push_neg at hgt
    have h2 : 1 < ((univ.filter (fun T : Finset V => u ∈ T ∧ v ∈ T)).filter
        (fun T => T ∈ Ts)).card := by exact_mod_cast hgt
    obtain ⟨T, hT, T', hT', hne⟩ := one_lt_card.mp h2
    simp only [mem_filter, mem_univ, true_and] at hT hT'
    have := hTs.edgeDisjoint T hT.2 T' hT'.2 hne
    have hsub : ({u, v} : Finset V) ⊆ T ∩ T' := by
      intro w hw
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact mem_inter.mpr ⟨hT.1.1, hT'.1.1⟩
      · exact mem_inter.mpr ⟨hT.1.2, hT'.1.2⟩
    have := card_le_card hsub
    rw [card_pair huv.ne] at this
    omega
  · unfold fracValue
    rw [← sum_filter, sum_const]
    simp

/-- `|E(G)| = u + m + s`. -/
theorem card_edgeFinset_eq (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) :
    G.edgeFinset.card = uCount G P + mCount G P + sCount G P := by
  rw [← card_kinds P G.edgeFinset]; rfl

section E2

variable {G : SimpleGraph V} [DecidableRel G.Adj] {P R A B : Finset V} {z : V}
  (hS : ExSetup G P R A B z)
include hS

omit [Fintype V] [DecidableRel G.Adj] in
/-- Every triangle contains two core vertices, or `z` together with one core vertex and one
vertex of `R`. -/
theorem ExSetup.triangle_cases {Q : Finset V} (hQ : G.IsClique (Q : Set V)) (h3 : Q.card = 3) :
    (∃ u ∈ Q ∩ P, ∃ v ∈ Q ∩ P, u ≠ v) ∨ (z ∈ Q ∧ (∃ v, v ∈ Q ∩ P) ∧ ∃ x, x ∈ Q ∩ R) := by
  have hc := card_eq_coreSize_add_extSize P Q
  have he := hS.extSize_eq Q
  have hR := hS.card_inter_R_le hQ
  by_cases h2 : 2 ≤ (Q ∩ P).card
  · left
    obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp h2
    exact ⟨u, hu, v, hv, huv⟩
  · right
    unfold coreSize at hc
    by_cases hz : z ∈ Q
    · rw [if_pos hz] at he
      refine ⟨hz, ?_, ?_⟩
      · exact card_pos.mp (by omega)
      · exact card_pos.mp (by omega)
    · rw [if_neg hz] at he; omega

/-- **Upper bound of E2.** Every fractional triangle packing has value at most
`u + min(a,b)`: the core edges together with the smaller of the two stars at `z` meet every
triangle. -/
theorem ExSetup.frac_triangle_le {w : Finset V → ℝ} (hw : IsFracTrianglePacking G w) :
    fracValue w ≤ (uCount G P : ℝ) + min (A.card : ℝ) B.card := by
  set ZP := G.edgeFinset.filter (fun e => z ∈ e ∧ ∃ v ∈ e.toFinset, v ∈ P)
  set ZR := G.edgeFinset.filter (fun e => z ∈ e ∧ ∃ v ∈ e.toFinset, v ∈ R)
  have hZP : ZP.card = A.card := by rw [hS.card_zEdges P hS.zP, hS.filter_adj_P]
  have hZR : ZR.card = B.card := by rw [hS.card_zEdges R hS.zR, hS.filter_adj_R]
  set K := coreEdges G P ∪ (if A.card ≤ B.card then ZP else ZR) with hK
  have hKsub : K ⊆ G.edgeFinset := by
    refine union_subset (coreEdges_subset G P) ?_
    split_ifs <;> exact filter_subset _ _
  have hKcard : (K.card : ℝ) ≤ (uCount G P : ℝ) + min (A.card : ℝ) B.card := by
    have h1 := card_union_le (coreEdges G P) (if A.card ≤ B.card then ZP else ZR)
    have h2 : ((if A.card ≤ B.card then ZP else ZR).card : ℝ) = min (A.card : ℝ) B.card := by
      split_ifs with h
      · rw [hZP, min_eq_left (by exact_mod_cast h)]
      · rw [hZR, min_eq_right (by exact_mod_cast (le_of_lt (not_le.mp h)))]
    have h1' : (K.card : ℝ) ≤ (coreEdges G P).card +
        ((if A.card ≤ B.card then ZP else ZR).card : ℝ) := by exact_mod_cast h1
    rw [h2] at h1'
    exact h1'
  have hcount := frac_triangle_count_le G hw K hKsub
  have hpt : ∀ Q, w Q ≤ w Q * ((insideFilter K Q).card : ℝ) := by
    intro Q
    by_cases hQ : w Q = 0
    · simp [hQ]
    · obtain ⟨h3, hcl⟩ := hw.support Q hQ
      have hne : (insideFilter K Q).Nonempty := by
        rcases hS.triangle_cases hcl h3 with ⟨u, hu, v, hv, huv⟩ | ⟨hz, ⟨v, hv⟩, ⟨x, hx⟩⟩
        · rw [mem_inter] at hu hv
          refine ⟨s(u, v), ?_⟩
          simp only [insideFilter, mem_filter, Sym2.mem_toFinset, Sym2.mem_iff]
          refine ⟨mem_union_left _ ((mem_coreEdges G P).mpr ⟨hcl hu.1 hv.1 huv, hu.2, hv.2⟩), ?_⟩
          rintro c (rfl | rfl)
          · exact hu.1
          · exact hv.1
        · rw [mem_inter] at hv hx
          by_cases hab : A.card ≤ B.card
          · have hmemK : s(z, v) ∈ K := by
              rw [hK, if_pos hab]
              exact mem_union_right _ (mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr
                (hcl hz hv.1 (hS.ne_z_of_P hv.2).symm), Sym2.mem_mk_left z v, v,
                Sym2.mem_toFinset.mpr (Sym2.mem_mk_right z v), hv.2⟩)
            refine ⟨s(z, v), ?_⟩
            simp only [insideFilter, mem_filter]
            refine ⟨hmemK, ?_⟩
            intro c hc
            rw [Sym2.mem_toFinset, Sym2.mem_iff] at hc
            rcases hc with rfl | rfl
            · exact hz
            · exact hv.1
          · have hmemK : s(z, x) ∈ K := by
              rw [hK, if_neg hab]
              exact mem_union_right _ (mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr
                (hcl hz hx.1 (hS.ne_z_of_R hx.2).symm), Sym2.mem_mk_left z x, x,
                Sym2.mem_toFinset.mpr (Sym2.mem_mk_right z x), hx.2⟩)
            refine ⟨s(z, x), ?_⟩
            simp only [insideFilter, mem_filter]
            refine ⟨hmemK, ?_⟩
            intro c hc
            rw [Sym2.mem_toFinset, Sym2.mem_iff] at hc
            rcases hc with rfl | rfl
            · exact hz
            · exact hx.1
      have h1 : (1 : ℝ) ≤ (insideFilter K Q).card := by exact_mod_cast hne.card_pos
      nlinarith [hw.nonneg Q]
  unfold fracValue
  calc ∑ Q, w Q ≤ ∑ Q, w Q * ((insideFilter K Q).card : ℝ) := sum_le_sum fun Q _ => hpt Q
    _ ≤ K.card := hcount
    _ ≤ _ := hKcard

omit hS in
/-- In a clique partition into blocks of order two or three, `|E| = |Π| + 2 · #triangles`. -/
theorem card_edges_of_le_three {Bs : Finset (Finset V)} (hBs : IsCliquePartition G Bs)
    (h3 : ∀ Q ∈ Bs, Q.card ≤ 3) :
    G.edgeFinset.card = Bs.card + 2 * (Bs.filter (fun Q => Q.card = 3)).card := by
  have hsum : ∑ Q ∈ Bs, Q.card.choose 2 = G.edgeFinset.card := by
    rw [← sum_card_filter_inside hBs G.edgeFinset subset_rfl]
    refine sum_congr rfl fun Q hQ => ?_
    rw [← card_innerEdges_of_isClique G Q (hBs.isClique Q hQ)]
    congr 1
  have hpt : ∀ Q ∈ Bs, Q.card.choose 2 = 1 + 2 * (if Q.card = 3 then 1 else 0) := by
    intro Q hQ
    have h2 := hBs.two_le Q hQ
    have h3' := h3 Q hQ
    interval_cases hc : Q.card <;> simp
  rw [sum_congr rfl hpt, sum_add_distrib, ← mul_sum, sum_boole] at hsum
  simp at hsum
  omega

/-- **Theorem E2.** If `q ≥ p + 3`, the maximum number of edge-disjoint triangles and the
maximum value of a fractional triangle packing both equal `u + min(a,b)`, `u = binom(p,2)`. -/
theorem ExSetup.theoremE2 (hq : P.card + 2 ≤ R.card) :
    IsGreatest {k : ℕ | ∃ Ts, IsTrianglePacking G Ts ∧ Ts.card = k}
      (uCount G P + min A.card B.card) ∧
    IsGreatest {v : ℝ | ∃ w, IsFracTrianglePacking G w ∧ fracValue w = v}
      ((uCount G P : ℝ) + min (A.card : ℝ) B.card) := by
  obtain ⟨hcp3, Bs, hBs, hcard, hle3⟩ := hS.cpLe_three_eq hq
  set Ts := Bs.filter (fun Q => Q.card = 3)
  have hTs : IsTrianglePacking G Ts :=
    ⟨fun T hT => (mem_filter.mp hT).2, fun T hT => hBs.isClique T (mem_filter.mp hT).1,
      fun T hT T' hT' hne => inter_card_le_one_of_isCliquePartition G hBs
        (mem_filter.mp hT).1 (mem_filter.mp hT').1 hne⟩
  have hE := card_edges_of_le_three hBs hle3
  have hE' := card_edgeFinset_eq G P
  have hm := hS.mCount_eq
  have hTcard : Ts.card = uCount G P + min A.card B.card := by
    have h1 : (Ts.card : ℤ) * 2 = 2 * uCount G P + 2 * min (A.card : ℤ) B.card := by
      have e1 : ((G.edgeFinset.card : ℕ) : ℤ) = Bs.card + 2 * Ts.card := by exact_mod_cast hE
      have e2 : ((G.edgeFinset.card : ℕ) : ℤ) = uCount G P + mCount G P + sCount G P := by
        exact_mod_cast hE'
      rw [hcard, hcp3] at e1
      unfold Dthree at e1
      rw [hm] at e1 e2
      linarith
    have : (Ts.card : ℤ) = uCount G P + min (A.card : ℤ) B.card := by linarith
    have hmin : (min (A.card : ℤ) B.card) = ((min A.card B.card : ℕ) : ℤ) := by push_cast; rfl
    rw [hmin] at this
    exact_mod_cast this
  refine ⟨⟨⟨Ts, hTs, hTcard⟩, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro k ⟨Ts', hTs', rfl⟩
    obtain ⟨hind, hval⟩ := isFracTrianglePacking_indicator G hTs'
    have := hS.frac_triangle_le hind
    rw [hval] at this
    have h' : ((Ts'.card : ℕ) : ℝ) ≤ ((uCount G P + min A.card B.card : ℕ) : ℝ) := by
      push_cast
      exact this
    exact_mod_cast h'
  · obtain ⟨hind, hval⟩ := isFracTrianglePacking_indicator G hTs
    refine ⟨_, hind, ?_⟩
    rw [hval, hTcard]
    push_cast
    rfl
  · rintro v ⟨w, hw, rfl⟩
    exact hS.frac_triangle_le hw

end E2

end Research

end PaperVI
