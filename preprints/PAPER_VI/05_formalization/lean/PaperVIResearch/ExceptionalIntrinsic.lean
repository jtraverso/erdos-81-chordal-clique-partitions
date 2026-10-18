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
Paper VI research round — Theorem E, intrinsic maximum (E4) and the gap to `max_Q Φ_Q`.

For the one-exceptional-vertex graph with `q = 2p` (`|R| = 2p - 1`) and `p ≥ 19`,
`max_Q Φ_Q(G) = Φ + max(0, 3b - 2a)`. Hence `cp(G) - max_Q Φ_Q(G) = D(a,b) - max(0, 3b - 2a)`,
which equals `1` for `a = 3, b = 2` and `p/3` for `a = p, b = 2p/3`: no choice of core alone
restores a defect-free formula of the form `Φ_Q`.
-/
module

public import PaperVIResearch.ExceptionalTriangles
public import PaperVIResearch.Intrinsic

@[expose] public section

namespace PaperVI

namespace Research

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `Φ_Q(G) = e(G) - 2 e(Q) - 3 e(V \ Q)`. -/
theorem PhiQ_eq_edges (G : SimpleGraph V) [DecidableRel G.Adj] (Q : Finset V) :
    PhiQ G Q = (G.edgeFinset.card : ℤ) - 2 * (innerEdges G Q).card -
      3 * (innerEdges G Qᶜ).card := by
  have h := card_edgeFinset_eq G Q
  have h1 : uCount G Q = (innerEdges G Q).card := rfl
  have h2 : mCount G Q = (innerEdges G Qᶜ).card := by
    unfold mCount extEdges innerEdges
    congr 1
    ext e
    simp only [mem_filter, mem_compl]
  unfold PhiQ
  rw [h, ← h1, ← h2]
  push_cast
  ring

/-- The polynomial inequality behind (E4): for `p ≥ 19`, `x + x' = p`, `y + y' = 2p - 1`,
`2(binom(x,2) + x y) + 3(binom(x',2) + x' y') ≥ 2 binom(p,2) + 3x' + 3y`. -/
theorem e4_poly {p x x' y y' : ℕ} (hp : 19 ≤ p) (hx : x + x' = p) (hy : y + y' = 2 * p - 1) :
    2 * (p.choose 2 : ℤ) + 3 * x' + 3 * y ≤
      2 * ((x.choose 2 : ℤ) + x * y) + 3 * ((x'.choose 2 : ℤ) + x' * y') := by
  have c1 := choose_two_nat x
  have c2 := choose_two_nat x'
  have c3 := choose_two_nat p
  have hx' : (x : ℤ) = p - x' := by omega
  have hy' : (y' : ℤ) = 2 * p - 1 - y := by omega
  have hyr : (y : ℤ) ≤ 2 * p - 1 := by omega
  have c1' : 2 * (x.choose 2 : ℤ) = (x : ℤ) * x - x := by
    have : ((2 * x.choose 2 + x : ℕ) : ℤ) = ((x * x : ℕ) : ℤ) := by rw [c1]
    push_cast at this; linarith
  have c2' : 2 * (x'.choose 2 : ℤ) = (x' : ℤ) * x' - x' := by
    have : ((2 * x'.choose 2 + x' : ℕ) : ℤ) = ((x' * x' : ℕ) : ℤ) := by rw [c2]
    push_cast at this; linarith
  have c3' : 2 * (p.choose 2 : ℤ) = (p : ℤ) * p - p := by
    have : ((2 * p.choose 2 + p : ℕ) : ℤ) = ((p * p : ℕ) : ℤ) := by rw [c3]
    push_cast at this; linarith
  have hP : (19 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  set P' : ℤ := (p : ℤ)
  set X : ℤ := (x : ℤ)
  set X' : ℤ := (x' : ℤ)
  set Y : ℤ := (y : ℤ)
  have hX0 : 0 ≤ X := by positivity
  have hX'0 : 0 ≤ X' := by positivity
  have hY0 : 0 ≤ Y := by positivity
  -- `E = 5x'^2 + (8p-13)x' + (4p-6)y - 10x'y`, and `(2p-1) E` is a nonnegative combination
  have hF0 : 0 ≤ (2 * P' - 1 - Y) * (5 * X' ^ 2 + (8 * P' - 13) * X') := by
    apply mul_nonneg (by linarith)
    nlinarith
  have hF1 : 0 ≤ Y * (P' ^ 2 + 2 * P' * X + 5 * X ^ 2 - 19 * P' + 3 * X + 6) := by
    apply mul_nonneg hY0
    nlinarith
  have hE : 0 ≤ 5 * X' ^ 2 + (8 * P' - 13) * X' + (4 * P' - 6) * Y - 10 * X' * Y := by
    have key : (2 * P' - 1) * (5 * X' ^ 2 + (8 * P' - 13) * X' + (4 * P' - 6) * Y - 10 * X' * Y) =
        (2 * P' - 1 - Y) * (5 * X' ^ 2 + (8 * P' - 13) * X') +
          Y * (P' ^ 2 + 2 * P' * X + 5 * X ^ 2 - 19 * P' + 3 * X + 6) := by
      rw [hx']; ring
    have hpos : (0 : ℤ) < 2 * P' - 1 := by linarith
    by_contra hneg
    push_neg at hneg
    have : (2 * P' - 1) * (5 * X' ^ 2 + (8 * P' - 13) * X' + (4 * P' - 6) * Y - 10 * X' * Y) < 0 :=
      mul_neg_of_pos_of_neg hpos hneg
    linarith
  rw [hy']
  nlinarith

/-- `Q ∩ S` and `Qᶜ ∩ S` partition `S`. -/
theorem card_inter_add_card_compl_inter (Q S : Finset V) :
    (Q ∩ S).card + (Qᶜ ∩ S).card = S.card := by
  rw [← card_union_of_disjoint]
  · congr 1
    ext v
    simp only [mem_union, mem_inter, mem_compl]
    tauto
  · rw [disjoint_left]
    intro v h1 h2
    exact (mem_compl.mp (mem_inter.mp h2).1) (mem_inter.mp h1).1

section E4

variable {G : SimpleGraph V} [DecidableRel G.Adj] {P R A B : Finset V} {z : V}
  (hS : ExSetup G P R A B z)
include hS

/-- Lower bound on the edges inside any vertex set `X` of the exceptional graph:
`e(X) ≥ binom(|X∩P|,2) + |X∩P| |X∩R| + [z ∈ X] (|X∩A| + |X∩B|)`. -/
theorem ExSetup.inner_ge (X : Finset V) :
    (X ∩ P).card.choose 2 + (X ∩ P).card * (X ∩ R).card +
      (if z ∈ X then (X ∩ A).card + (X ∩ B).card else 0) ≤ (innerEdges G X).card := by
  set E1 := innerEdges G (X ∩ P)
  set E2 := ((X ∩ P) ×ˢ (X ∩ R)).image (fun ax => s(ax.1, ax.2))
  set E3 := if z ∈ X then ((X ∩ A) ∪ (X ∩ B)).image (fun v => s(z, v)) else ∅
  have hE1 : E1.card = (X ∩ P).card.choose 2 :=
    card_innerEdges_of_isClique G _ (fun u hu v hv huv =>
      hS.adjPP u (mem_inter.mp hu).2 v (mem_inter.mp hv).2 huv)
  have hE2 : E2.card = (X ∩ P).card * (X ∩ R).card := by
    rw [card_image_of_injOn, card_product]
    rintro ⟨a, x⟩ hax ⟨a', x'⟩ hax' h
    simp only [coe_product, Set.mem_prod, mem_coe, mem_inter] at hax hax'
    simp only [Sym2.eq_iff] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd hax'.2.2 (hS.notR_of_P hax.1.2)
  have hE3 : E3.card = if z ∈ X then (X ∩ A).card + (X ∩ B).card else 0 := by
    by_cases hz : z ∈ X
    · simp only [E3, if_pos hz]
      rw [card_image_of_injective _ (fun v w h => Sym2.congr_right.mp h),
        card_union_of_disjoint]
      rw [disjoint_left]
      intro v h1 h2
      exact hS.notR_of_P (hS.AsubP (mem_inter.mp h1).2) (hS.BsubR (mem_inter.mp h2).2)
    · simp only [E3, if_neg hz, card_empty]
  have hd12 : Disjoint E1 E2 := by
    rw [disjoint_left]
    intro e h1 h2
    obtain ⟨⟨a, x⟩, hax, rfl⟩ := mem_image.mp h2
    simp only [mem_product, mem_inter] at hax
    simp only [E1, innerEdges, mem_filter, Sym2.mem_toFinset, Sym2.mem_iff] at h1
    exact hS.notR_of_P (mem_inter.mp (h1.2 x (Or.inr rfl))).2 hax.2.2
  have hd3 : Disjoint (E1 ∪ E2) E3 := by
    rw [disjoint_left]
    intro e h12 h3
    by_cases hz : z ∈ X
    · simp only [E3, if_pos hz] at h3
      obtain ⟨v, -, rfl⟩ := mem_image.mp h3
      rcases mem_union.mp h12 with h1 | h2
      · simp only [E1, innerEdges, mem_filter, Sym2.mem_toFinset, Sym2.mem_iff] at h1
        exact hS.zP (mem_inter.mp (h1.2 z (Or.inl rfl))).2
      · obtain ⟨⟨a, x⟩, hax, hh⟩ := mem_image.mp h2
        simp only [mem_product, mem_inter] at hax
        have : z ∈ s(a, x) := by rw [hh]; exact Sym2.mem_mk_left _ _
        rcases Sym2.mem_iff.mp this with h | h
        · exact hS.zP (h ▸ hax.1.2)
        · exact hS.zR (h ▸ hax.2.2)
    · simp only [E3, if_neg hz] at h3
      exact absurd h3 (notMem_empty _)
  have hsub : E1 ∪ E2 ∪ E3 ⊆ innerEdges G X := by
    intro e he
    simp only [innerEdges, mem_filter, SimpleGraph.mem_edgeFinset]
    rcases mem_union.mp he with h12 | h3
    · rcases mem_union.mp h12 with h1 | h2
      · simp only [E1, innerEdges, mem_filter, SimpleGraph.mem_edgeFinset] at h1
        exact ⟨h1.1, fun v hv => (mem_inter.mp (h1.2 v hv)).1⟩
      · obtain ⟨⟨a, x⟩, hax, rfl⟩ := mem_image.mp h2
        simp only [mem_product, mem_inter] at hax
        refine ⟨hS.adjPR a hax.1.2 x hax.2.2, ?_⟩
        intro v hv
        rw [Sym2.mem_toFinset, Sym2.mem_iff] at hv
        rcases hv with rfl | rfl
        · exact hax.1.1
        · exact hax.2.1
    · by_cases hz : z ∈ X
      · simp only [E3, if_pos hz] at h3
        obtain ⟨v, hv, rfl⟩ := mem_image.mp h3
        have hvX : v ∈ X := by
          rcases mem_union.mp hv with h | h
          · exact (mem_inter.mp h).1
          · exact (mem_inter.mp h).1
        refine ⟨(hS.adjz v).mpr ?_, ?_⟩
        · rcases mem_union.mp hv with h | h
          · exact Or.inl (mem_inter.mp h).2
          · exact Or.inr (mem_inter.mp h).2
        · intro w hw
          rw [Sym2.mem_toFinset, Sym2.mem_iff] at hw
          rcases hw with rfl | rfl
          · exact hz
          · exact hvX
      · simp only [E3, if_neg hz] at h3
        exact absurd h3 (notMem_empty _)
  have := card_le_card hsub
  rw [card_union_of_disjoint hd3, card_union_of_disjoint hd12, hE1, hE2, hE3] at this
  exact this

/-- The edges inside `P ∪ {z}`: at most `binom(p,2) + a`. -/
theorem ExSetup.inner_insert_le :
    (innerEdges G (insert z P)).card ≤ P.card.choose 2 + A.card := by
  have hsub : innerEdges G (insert z P) ⊆ innerEdges G P ∪ A.image (fun v => s(z, v)) := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
    simp only [innerEdges, mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      Sym2.mem_toFinset, Sym2.mem_iff, forall_eq_or_imp, forall_eq, mem_insert] at he
    obtain ⟨hadj, hu, hv⟩ := he
    rcases hu with rfl | hu <;> rcases hv with rfl | hv
    · exact absurd hadj (G.loopless.irrefl _)
    · refine mem_union_right _ (mem_image.mpr ⟨v, ?_, rfl⟩)
      rcases (hS.adjz v).mp hadj with h | h
      · exact h
      · exact absurd (hS.BsubR h) (hS.notR_of_P hv)
    · refine mem_union_right _ (mem_image.mpr ⟨u, ?_, Sym2.eq_swap⟩)
      rcases (hS.adjz u).mp hadj.symm with h | h
      · exact h
      · exact absurd (hS.BsubR h) (hS.notR_of_P hu)
    · refine mem_union_left _ ?_
      simp only [innerEdges, mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        Sym2.mem_toFinset, Sym2.mem_iff, forall_eq_or_imp, forall_eq]
      exact ⟨hadj, hu, hv⟩
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  rw [card_innerEdges_of_isClique G P (fun u hu v hv huv => hS.adjPP u hu v hv huv)]
  exact Nat.add_le_add_left card_image_le _

/-- `R` is independent: no edges inside `R`. -/
theorem ExSetup.inner_R : innerEdges G R = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro e he
  induction e using Sym2.ind with
  | h u v =>
  simp only [innerEdges, mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
    Sym2.mem_toFinset, Sym2.mem_iff, forall_eq_or_imp, forall_eq] at he
  exact hS.indepR u he.2.1 v he.2.2 he.1

omit [DecidableRel G.Adj] in
/-- The complement of `P ∪ {z}` is `R`. -/
theorem ExSetup.compl_insert : (insert z P)ᶜ = R := by
  ext v
  simp only [mem_compl, mem_insert, not_or]
  constructor
  · rintro ⟨h1, h2⟩
    rcases hS.cover v with h | h | h
    · exact absurd h h2
    · exact h
    · exact absurd h h1
  · intro h
    exact ⟨hS.ne_z_of_R h, fun hP => hS.notR_of_P hP h⟩

/-- `Φ_P(G) = e(G) - 2 binom(p,2) - 3b`. -/
theorem ExSetup.PhiQ_P_eq :
    PhiQ G P = (G.edgeFinset.card : ℤ) - 2 * (P.card.choose 2 : ℤ) - 3 * B.card := by
  have hE := card_edgeFinset_eq G P
  unfold PhiQ
  rw [hE, hS.uCount_eq, hS.mCount_eq]
  push_cast
  ring

/-- `Φ_{P ∪ {z}} = Φ_P + 3b - 2a`. -/
theorem ExSetup.PhiQ_insert :
    PhiQ G (insert z P) = PhiQ G P + 3 * B.card - 2 * A.card := by
  have hlow := hS.inner_ge (insert z P)
  have hup := hS.inner_insert_le
  have hPz : insert z P ∩ P = P := by
    rw [insert_inter_of_notMem (fun h => hS.zP h), inter_self]
  have hRz : insert z P ∩ R = ∅ := by
    rw [insert_inter_of_notMem (fun h => hS.zR h)]
    exact disjoint_iff_inter_eq_empty.mp hS.disjPR
  have hAz : insert z P ∩ A = A := by
    rw [insert_inter_of_notMem (fun h => hS.zP (hS.AsubP h)), inter_eq_right.mpr hS.AsubP]
  have hBz : insert z P ∩ B = ∅ := by
    rw [insert_inter_of_notMem (fun h => hS.zR (hS.BsubR h)), eq_empty_iff_forall_notMem]
    intro v hv
    rw [mem_inter] at hv
    exact hS.notR_of_P hv.1 (hS.BsubR hv.2)
  rw [hPz, hRz, hAz, hBz, if_pos (mem_insert_self _ _)] at hlow
  simp only [card_empty, mul_zero, add_zero] at hlow
  have heq : (innerEdges G (insert z P)).card = P.card.choose 2 + A.card := le_antisymm hup hlow
  rw [PhiQ_eq_edges G (insert z P), hS.compl_insert, hS.inner_R, card_empty, heq,
    hS.PhiQ_P_eq]
  push_cast
  ring

/-- **(E4) Intrinsic maximum.** For `q = 2p` (i.e. `|R| = 2p - 1`) and `p ≥ 19`,
`max_Q Φ_Q(G) = Φ + max(0, 3b - 2a)`, attained at `P` or at `P ∪ {z}`. -/
theorem ExSetup.theoremE4 (hp : 19 ≤ P.card) (hq : R.card = 2 * P.card - 1) :
    IsGreatest (Set.range (PhiQ G)) (PhiQ G P + max 0 (3 * (B.card : ℤ) - 2 * A.card)) := by
  refine ⟨?_, ?_⟩
  · by_cases h : 3 * (B.card : ℤ) - 2 * A.card ≤ 0
    · exact ⟨P, by rw [max_eq_left h, add_zero]⟩
    · refine ⟨insert z P, ?_⟩
      rw [max_eq_right (by linarith), hS.PhiQ_insert]
      ring
  · rintro _ ⟨Q, rfl⟩
    rw [PhiQ_eq_edges G Q, hS.PhiQ_P_eq]
    have hQ := hS.inner_ge Q
    have hQc := hS.inner_ge Qᶜ
    have hxP := card_inter_add_card_compl_inter Q P
    have hxR := card_inter_add_card_compl_inter Q R
    have hxA := card_inter_add_card_compl_inter Q A
    have hxB := card_inter_add_card_compl_inter Q B
    have hAc : (Qᶜ ∩ A).card ≤ (Qᶜ ∩ P).card := card_le_card (inter_subset_inter_left hS.AsubP)
    have hBq : (Q ∩ B).card ≤ (Q ∩ R).card := card_le_card (inter_subset_inter_left hS.BsubR)
    have hpoly := e4_poly hp hxP (by rw [hxR, hq])
    by_cases hz : z ∈ Q
    · rw [if_pos hz] at hQ
      rw [if_neg (fun h => (mem_compl.mp h) hz)] at hQc
      have h1 : ((Q ∩ P).card.choose 2 + (Q ∩ P).card * (Q ∩ R).card + ((Q ∩ A).card +
          (Q ∩ B).card) : ℕ) ≤ ((innerEdges G Q).card : ℤ) := by exact_mod_cast hQ
      have h2 : ((Qᶜ ∩ P).card.choose 2 + (Qᶜ ∩ P).card * (Qᶜ ∩ R).card + 0 : ℕ) ≤
          ((innerEdges G Qᶜ).card : ℤ) := by exact_mod_cast hQc
      push_cast at h1 h2
      have : (A.card : ℤ) = (Q ∩ A).card + (Qᶜ ∩ A).card := by exact_mod_cast hxA.symm
      have : ((Qᶜ ∩ A).card : ℤ) ≤ (Qᶜ ∩ P).card := by exact_mod_cast hAc
      have hmax : 3 * (B.card : ℤ) - max 0 (3 * (B.card : ℤ) - 2 * A.card) ≤ 2 * A.card := by
        have := le_max_right 0 (3 * (B.card : ℤ) - 2 * A.card); linarith
      nlinarith
    · rw [if_neg hz] at hQ
      rw [if_pos (mem_compl.mpr hz)] at hQc
      have h1 : ((Q ∩ P).card.choose 2 + (Q ∩ P).card * (Q ∩ R).card + 0 : ℕ) ≤
          ((innerEdges G Q).card : ℤ) := by exact_mod_cast hQ
      have h2 : ((Qᶜ ∩ P).card.choose 2 + (Qᶜ ∩ P).card * (Qᶜ ∩ R).card +
          ((Qᶜ ∩ A).card + (Qᶜ ∩ B).card) : ℕ) ≤ ((innerEdges G Qᶜ).card : ℤ) := by
        exact_mod_cast hQc
      push_cast at h1 h2
      have : (B.card : ℤ) = (Q ∩ B).card + (Qᶜ ∩ B).card := by exact_mod_cast hxB.symm
      have : ((Q ∩ B).card : ℤ) ≤ (Q ∩ R).card := by exact_mod_cast hBq
      have hmax : 3 * (B.card : ℤ) - max 0 (3 * (B.card : ℤ) - 2 * A.card) ≤ 3 * B.card := by
        have := le_max_left 0 (3 * (B.card : ℤ) - 2 * A.card); linarith
      nlinarith

/-- **Gap to the intrinsic maximum.** Under the hypotheses of (E4),
`cp(G) - max_Q Φ_Q(G) = D(a,b) - max(0, 3b - 2a)`. -/
theorem ExSetup.gap_to_max_PhiQ (hp : 19 ≤ P.card) (hq : R.card = 2 * P.card - 1) :
    (cp G : ℤ) - (PhiQ G P + max 0 (3 * (B.card : ℤ) - 2 * A.card)) =
      Dval A.card B.card - max 0 (3 * (B.card : ℤ) - 2 * A.card) := by
  have hE1 := (hS.theoremE1 (by omega)).1
  unfold PhiQ
  rw [hE1]
  ring

/-- **Gap 1 example.** For `a = 3`, `b = 2` (and `q = 2p`, `p ≥ 19`):
`cp(G) - max_Q Φ_Q(G) = 1`. -/
theorem ExSetup.gap_example_three_two (hp : 19 ≤ P.card) (hq : R.card = 2 * P.card - 1)
    (ha : A.card = 3) (hb : B.card = 2) :
    (cp G : ℤ) - (PhiQ G P + max 0 (3 * (B.card : ℤ) - 2 * A.card)) = 1 := by
  rw [hS.gap_to_max_PhiQ hp hq, ha, hb]
  unfold Dval
  norm_num

/-- **Linear gap example (split graph).** For `a = p` and `3b = 2p` (and `q = 2p`, `p ≥ 19`):
`3 (cp(G) - max_Q Φ_Q(G)) = p`, i.e. the gap is `p/3`. -/
theorem ExSetup.gap_example_linear (hp : 19 ≤ P.card) (hq : R.card = 2 * P.card - 1)
    (ha : A.card = P.card) (hb : 3 * B.card = 2 * P.card) :
    3 * ((cp G : ℤ) - (PhiQ G P + max 0 (3 * (B.card : ℤ) - 2 * A.card))) = P.card := by
  rw [hS.gap_to_max_PhiQ hp hq, ha]
  unfold Dval
  have hb' : 3 * (B.card : ℤ) = 2 * P.card := by exact_mod_cast hb
  have e1 : 3 * (B.card : ℤ) - 2 * P.card = 0 := by linarith
  rw [e1, max_self]
  have e2 : max (2 * (B.card : ℤ) - P.card) 0 = 2 * (B.card : ℤ) - P.card := by
    apply max_eq_left; linarith
  rw [e2, max_eq_right (by linarith)]
  linarith

end E4

end Research

end PaperVI
