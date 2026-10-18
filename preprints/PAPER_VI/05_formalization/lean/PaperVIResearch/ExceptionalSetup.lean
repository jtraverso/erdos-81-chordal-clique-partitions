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
Paper VI research round — Theorem E, part 1: the one-exceptional-vertex graph, its edge
counts, and the three explicit signed edge duals (lower bounds).

The graph: a clique `P` (`p = |P|`), an independent set `R` (`|R| = q - 1`) completely joined
to `P`, and one extra vertex `z` adjacent exactly to `A ⊆ P` (`a = |A|`) and `B ⊆ R`
(`b = |B|`). The core is `P`; the exterior is `O = R ∪ {z}`, so `q = |O| = |R| + 1`.
-/
module

public import PaperVIResearch.Duals
public import PaperVI.TrianglePacking

@[expose] public section

namespace PaperVI

namespace Research

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The hypotheses of Theorem E: they determine `G` completely. -/
structure ExSetup (G : SimpleGraph V) (P R A B : Finset V) (z : V) : Prop where
  disjPR : Disjoint P R
  zP : z ∉ P
  zR : z ∉ R
  cover : ∀ v, v ∈ P ∨ v ∈ R ∨ v = z
  adjPP : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → G.Adj u v
  adjPR : ∀ u ∈ P, ∀ x ∈ R, G.Adj u x
  indepR : ∀ x ∈ R, ∀ y ∈ R, ¬ G.Adj x y
  AsubP : A ⊆ P
  BsubR : B ⊆ R
  adjz : ∀ v, G.Adj z v ↔ v ∈ A ∨ v ∈ B

/-- The defect `D(a,b) = max(0, 2b - a, 3b - 2a)` (untruncated integer arithmetic). -/
def Dval (a b : ℕ) : ℤ := max 0 (max (2 * (b : ℤ) - a) (3 * (b : ℤ) - 2 * a))

/-- The base weights of the slack certificate: `-1` on core edges, `-2` on exterior edges,
`1` on crossing edges. -/
def baseW (P : Finset V) (e : Sym2 V) : ℤ :=
  if ∀ v ∈ e.toFinset, v ∈ P then -1 else if ∀ v ∈ e.toFinset, v ∉ P then -2 else 1

/-- The signed edge dual of Theorem E: the base weights, corrected by `cP` on the edges from
`z` to `P` and by `cR` on the edges from `z` to `R`. -/
def exW (P R : Finset V) (z : V) (cP cR : ℤ) (e : Sym2 V) : ℤ :=
  baseW P e + (if z ∈ e ∧ ∃ v ∈ e.toFinset, v ∈ P then cP else 0) +
    (if z ∈ e ∧ ∃ v ∈ e.toFinset, v ∈ R then cR else 0)

theorem sum_baseW (P : Finset V) (S : Finset (Sym2 V)) :
    ∑ e ∈ S, baseW P e = -((S.filter (fun e => ∀ v ∈ e.toFinset, v ∈ P)).card : ℤ) -
      2 * (S.filter (fun e => ∀ v ∈ e.toFinset, v ∉ P)).card +
      (S.filter (fun e => (∃ v ∈ e.toFinset, v ∈ P) ∧ ∃ v ∈ e.toFinset, v ∉ P)).card := by
  unfold baseW
  rw [sum_ite, sum_ite, filter_filter, filter_filter, sum_const, sum_const, sum_const]
  have e1 : S.filter (fun e => (¬ ∀ v ∈ e.toFinset, v ∈ P) ∧ ∀ v ∈ e.toFinset, v ∉ P) =
      S.filter (fun e => ∀ v ∈ e.toFinset, v ∉ P) := by
    apply filter_congr
    intro e _
    induction e using Sym2.ind with
    | h a b =>
      simp only [Sym2.mem_toFinset, Sym2.mem_iff, forall_eq_or_imp, forall_eq, not_and]
      tauto
  have e2 : S.filter (fun e => (¬ ∀ v ∈ e.toFinset, v ∈ P) ∧ ¬ ∀ v ∈ e.toFinset, v ∉ P) =
      S.filter (fun e => (∃ v ∈ e.toFinset, v ∈ P) ∧ ∃ v ∈ e.toFinset, v ∉ P) := by
    apply filter_congr
    intro e _
    simp only [not_forall, not_not, exists_prop]
    tauto
  rw [e1, e2]
  simp only [nsmul_eq_mul]
  ring

section Setup

variable {G : SimpleGraph V} [DecidableRel G.Adj] {P R A B : Finset V} {z : V}
  (hS : ExSetup G P R A B z)
include hS

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem ExSetup.notR_of_P {v : V} (hv : v ∈ P) : v ∉ R :=
  fun h => disjoint_left.mp hS.disjPR hv h

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem ExSetup.ne_z_of_P {v : V} (hv : v ∈ P) : v ≠ z := fun h => hS.zP (h ▸ hv)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem ExSetup.ne_z_of_R {v : V} (hv : v ∈ R) : v ≠ z := fun h => hS.zR (h ▸ hv)

omit [Fintype V] [DecidableRel G.Adj] in
/-- Every clique has at most one vertex in `R`. -/
theorem ExSetup.card_inter_R_le {Q : Finset V} (hQ : G.IsClique (Q : Set V)) :
    (Q ∩ R).card ≤ 1 := by
  rw [card_le_one]
  intro x hx y hy
  by_contra hxy
  rw [mem_inter] at hx hy
  exact hS.indepR x hx.2 y hy.2 (hQ hx.1 hy.1 hxy)

omit [Fintype V] [DecidableRel G.Adj] in
/-- The exterior part of a vertex set is its `R`-part plus possibly `z`. -/
theorem ExSetup.extSize_eq (Q : Finset V) :
    extSize P Q = (Q ∩ R).card + if z ∈ Q then 1 else 0 := by
  unfold extSize
  split_ifs with hz
  · have : Q \ P = insert z (Q ∩ R) := by
      ext v
      simp only [mem_sdiff, mem_insert, mem_inter]
      constructor
      · rintro ⟨hv, hvP⟩
        rcases hS.cover v with h | h | h
        · exact absurd h hvP
        · exact Or.inr ⟨hv, h⟩
        · exact Or.inl h
      · rintro (rfl | ⟨hv, hvR⟩)
        · exact ⟨hz, hS.zP⟩
        · exact ⟨hv, hS.notR_of_P.mt (not_not.mpr hvR)⟩
    rw [this, card_insert_of_notMem (fun h => hS.zR (mem_inter.mp h).2)]
  · have : Q \ P = Q ∩ R := by
      ext v
      simp only [mem_sdiff, mem_inter]
      constructor
      · rintro ⟨hv, hvP⟩
        rcases hS.cover v with h | h | h
        · exact absurd h hvP
        · exact ⟨hv, h⟩
        · exact absurd (h ▸ hv) hz
      · rintro ⟨hv, hvR⟩
        exact ⟨hv, hS.notR_of_P.mt (not_not.mpr hvR)⟩
    rw [this, add_zero]

/-- Edges from `z` into a set `X` (with `z ∉ X`) inside a clique `Q`. -/
theorem ExSetup.card_zEdges_inner {Q : Finset V} (hQ : G.IsClique (Q : Set V)) (X : Finset V)
    (hzX : z ∉ X) :
    ((innerEdges G Q).filter (fun e => z ∈ e ∧ ∃ v ∈ e.toFinset, v ∈ X)).card =
      if z ∈ Q then (Q ∩ X).card else 0 := by
  split_ifs with hz
  · have : (innerEdges G Q).filter (fun e => z ∈ e ∧ ∃ v ∈ e.toFinset, v ∈ X) =
        (Q ∩ X).image (fun v => s(z, v)) := by
      ext e
      induction e using Sym2.ind with
      | h u w =>
        simp only [innerEdges, mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          Sym2.mem_toFinset, Sym2.mem_iff, mem_image, mem_inter]
        constructor
        · rintro ⟨⟨hadj, hin⟩, hzuw, v, hv, hvX⟩
          refine ⟨v, ⟨hin v hv, hvX⟩, ?_⟩
          rcases hzuw with rfl | rfl <;> rcases hv with rfl | rfl
          · exact absurd hvX hzX
          · rfl
          · exact Sym2.eq_swap
          · exact absurd hvX hzX
        · rintro ⟨v, ⟨hvQ, hvX⟩, hv⟩
          rw [Sym2.eq_iff] at hv
          have hzv : z ≠ v := fun h => hzX (h ▸ hvX)
          rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · refine ⟨⟨hQ hz hvQ hzv, ?_⟩, Or.inl rfl, _, Or.inr rfl, hvX⟩
            rintro c (rfl | rfl) <;> assumption
          · refine ⟨⟨hQ hvQ hz hzv.symm, ?_⟩, Or.inr rfl, _, Or.inl rfl, hvX⟩
            rintro c (rfl | rfl) <;> assumption
    rw [this, card_image_of_injective _ (fun v w h => Sym2.congr_right.mp h)]
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro e he ⟨hze, -⟩
    simp only [innerEdges, mem_filter] at he
    exact hz (he.2 z (Sym2.mem_toFinset.mpr hze))

/-- Edges from `z` into a set `X` (with `z ∉ X`) in the whole graph. -/
theorem ExSetup.card_zEdges (X : Finset V) (hzX : z ∉ X) :
    (G.edgeFinset.filter (fun e => z ∈ e ∧ ∃ v ∈ e.toFinset, v ∈ X)).card =
      (X.filter (G.Adj z)).card := by
  have : G.edgeFinset.filter (fun e => z ∈ e ∧ ∃ v ∈ e.toFinset, v ∈ X) =
      (X.filter (G.Adj z)).image (fun v => s(z, v)) := by
    ext e
    induction e using Sym2.ind with
    | h u w =>
      simp only [mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        Sym2.mem_toFinset, Sym2.mem_iff, mem_image]
      constructor
      · rintro ⟨hadj, hzuw, v, hv, hvX⟩
        refine ⟨v, ?_, ?_⟩
        · rcases hzuw with rfl | rfl <;> rcases hv with rfl | rfl
          · exact absurd hvX hzX
          · exact ⟨hvX, hadj⟩
          · exact ⟨hvX, hadj.symm⟩
          · exact absurd hvX hzX
        · rcases hzuw with rfl | rfl <;> rcases hv with rfl | rfl
          · exact absurd hvX hzX
          · rfl
          · exact Sym2.eq_swap
          · exact absurd hvX hzX
      · rintro ⟨v, ⟨hvX, hadj⟩, hv⟩
        rw [Sym2.eq_iff] at hv
        rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨hadj, Or.inl rfl, _, Or.inr rfl, hvX⟩
        · exact ⟨hadj.symm, Or.inr rfl, _, Or.inl rfl, hvX⟩
  rw [this, card_image_of_injective _ (fun v w h => Sym2.congr_right.mp h)]

omit [Fintype V] [DecidableEq V] in
theorem ExSetup.filter_adj_P : P.filter (G.Adj z) = A := by
  ext v
  simp only [mem_filter, hS.adjz]
  constructor
  · rintro ⟨hv, h | h⟩
    · exact h
    · exact absurd (hS.BsubR h) (hS.notR_of_P hv)
  · intro h; exact ⟨hS.AsubP h, Or.inl h⟩

omit [Fintype V] [DecidableEq V] in
theorem ExSetup.filter_adj_R : R.filter (G.Adj z) = B := by
  ext v
  simp only [mem_filter, hS.adjz]
  constructor
  · rintro ⟨hv, h | h⟩
    · exact absurd hv (hS.notR_of_P (hS.AsubP h))
    · exact h
  · intro h; exact ⟨hS.BsubR h, Or.inr h⟩

/-- The weight of a clique under the dual `exW cP cR`. -/
theorem ExSetup.setWeight_exW {Q : Finset V} (hQ : G.IsClique (Q : Set V)) (cP cR : ℤ) :
    setWeight G (exW P R z cP cR) Q =
      (coreSize P Q : ℤ) * extSize P Q - ((coreSize P Q).choose 2 : ℤ) -
        2 * ((extSize P Q).choose 2 : ℤ) +
        (if z ∈ Q then cP * (coreSize P Q) + cR * (Q ∩ R).card else 0) := by
  unfold setWeight exW
  rw [sum_add_distrib, sum_add_distrib, sum_baseW, ← sum_filter, ← sum_filter, sum_const,
    sum_const, hS.card_zEdges_inner hQ P hS.zP, hS.card_zEdges_inner hQ R hS.zR]
  have h1 : ((innerEdges G Q).filter (fun e => ∀ v ∈ e.toFinset, v ∈ P)).card =
      (coreSize P Q).choose 2 := by
    rw [← card_insideFilter_core G P Q hQ]
    unfold innerEdges insideFilter coreEdges
    rw [filter_filter, filter_filter]
    congr 1; ext e; simp only [mem_filter]; tauto
  have h2 : ((innerEdges G Q).filter (fun e => ∀ v ∈ e.toFinset, v ∉ P)).card =
      (extSize P Q).choose 2 := by
    rw [← card_insideFilter_ext G P Q hQ]
    unfold innerEdges insideFilter extEdges
    rw [filter_filter, filter_filter]
    congr 1; ext e; simp only [mem_filter]; tauto
  have h3 : ((innerEdges G Q).filter
      (fun e => (∃ v ∈ e.toFinset, v ∈ P) ∧ ∃ v ∈ e.toFinset, v ∉ P)).card =
      coreSize P Q * extSize P Q := by
    rw [← card_insideFilter_cross G P Q hQ]
    unfold innerEdges insideFilter crossEdges
    rw [filter_filter, filter_filter]
    congr 1; ext e; simp only [mem_filter]; tauto
  rw [h1, h2, h3]
  split_ifs with hz
  · simp only [coreSize]; push_cast; ring
  · simp only [zero_smul, add_zero, Nat.cast_mul]; ring

/-- The total weight of `E(G)` under the dual `exW cP cR` is `Φ + cP a + cR b`. -/
theorem ExSetup.sum_exW (cP cR : ℤ) :
    ∑ e ∈ G.edgeFinset, exW P R z cP cR e =
      (sCount G P : ℤ) - uCount G P - 2 * mCount G P + cP * A.card + cR * B.card := by
  unfold exW
  rw [sum_add_distrib, sum_add_distrib, sum_baseW, ← sum_filter, ← sum_filter, sum_const,
    sum_const, hS.card_zEdges P hS.zP, hS.card_zEdges R hS.zR, hS.filter_adj_P,
    hS.filter_adj_R]
  have hu : (G.edgeFinset.filter (fun e => ∀ v ∈ e.toFinset, v ∈ P)).card = uCount G P := by
    unfold uCount coreEdges; congr 1; ext e; simp only [mem_filter, SimpleGraph.mem_edgeFinset]
  have hm : (G.edgeFinset.filter (fun e => ∀ v ∈ e.toFinset, v ∉ P)).card = mCount G P := by
    unfold mCount extEdges; congr 1; ext e; simp only [mem_filter, SimpleGraph.mem_edgeFinset]
  have hs : (G.edgeFinset.filter
      (fun e => (∃ v ∈ e.toFinset, v ∈ P) ∧ ∃ v ∈ e.toFinset, v ∉ P)).card = sCount G P := by
    unfold sCount crossEdges; congr 1
  rw [hu, hm, hs]
  ring

omit [Fintype V] [DecidableRel G.Adj] in
/-- Arithmetic core of the dual feasibility checks. -/
theorem ExSetup.clique_weight_cases {Q : Finset V} (hQ : G.IsClique (Q : Set V)) :
    ((Q ∩ R).card = 0 ∨ (Q ∩ R).card = 1) ∧
      extSize P Q = (Q ∩ R).card + if z ∈ Q then 1 else 0 := by
  have := hS.card_inter_R_le hQ
  exact ⟨by omega, hS.extSize_eq Q⟩

/-- Feasibility of a dual `(cP, cR)` from per-case arithmetic conditions. -/
theorem ExSetup.setWeight_le_one {Q : Finset V} (hQ : G.IsClique (Q : Set V)) {cP cR : ℤ}
    (hcase : ∀ k : ℕ, ∀ j zq : ℕ, j ≤ 1 → zq ≤ 1 → (Q.card = k + j + zq) →
      (k : ℤ) * (j + zq) - (k.choose 2 : ℤ) - 2 * ((j + zq).choose 2 : ℤ) +
        (if zq = 1 then cP * k + cR * j else 0) ≤ 1) :
    setWeight G (exW P R z cP cR) Q ≤ 1 := by
  rw [hS.setWeight_exW hQ]
  obtain ⟨hj, hext⟩ := hS.clique_weight_cases hQ
  have hcard := card_eq_coreSize_add_extSize P Q
  rw [hext]
  by_cases hz : z ∈ Q
  · have := hcase (coreSize P Q) (Q ∩ R).card 1 (by omega) le_rfl
      (by rw [hcard, hext, if_pos hz]; ring)
    rw [if_pos rfl] at this
    rw [if_pos hz, if_pos hz]
    push_cast at this ⊢
    linarith
  · have := hcase (coreSize P Q) (Q ∩ R).card 0 (by omega) (by omega)
      (by rw [hcard, hext, if_neg hz]; ring)
    rw [if_neg (by decide : (0:ℕ) ≠ 1)] at this
    rw [if_neg hz, if_neg hz]
    push_cast at this ⊢
    linarith

end Setup

/-- Two choose-two facts used in the arithmetic. -/
theorem choose_two_cast (k : ℕ) : 2 * (k.choose 2 : ℤ) = (k : ℤ) * ((k : ℤ) - 1) :=
  two_mul_choose_two k

/-- Arithmetic of the three duals of Theorem E: `(0,0)`, `(-1,2)`, `(-2,3)`. -/
theorem dual_arith (k j zq : ℕ) (hj : j ≤ 1) (hz : zq ≤ 1) (cP cR : ℤ)
    (hc : (cP = 0 ∧ cR = 0) ∨ (cP = -1 ∧ cR = 2) ∨ (cP = -2 ∧ cR = 3)) :
    (k : ℤ) * (j + zq) - (k.choose 2 : ℤ) - 2 * ((j + zq).choose 2 : ℤ) +
      (if zq = 1 then cP * k + cR * j else 0) ≤ 1 := by
  have hk := choose_two_cast k
  have h1 := int_mul_pred_nonneg ((k : ℤ) - 1)
  have h2 := int_mul_pred_nonneg ((k : ℤ) - 2)
  have hk0 : (0 : ℤ) ≤ k := by positivity
  interval_cases j <;> interval_cases zq <;>
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> (try simp) <;> nlinarith

/-- Arithmetic of the dual `(0,1)` restricted to blocks of order at most three. -/
theorem dual_arith_le_three (k j zq : ℕ) (hj : j ≤ 1) (hz : zq ≤ 1) (h3 : k + j + zq ≤ 3) :
    (k : ℤ) * (j + zq) - (k.choose 2 : ℤ) - 2 * ((j + zq).choose 2 : ℤ) +
      (if zq = 1 then (0 : ℤ) * k + 1 * j else 0) ≤ 1 := by
  have hk := choose_two_cast k
  have h1 := int_mul_pred_nonneg ((k : ℤ) - 1)
  have h2 := int_mul_pred_nonneg ((k : ℤ) - 2)
  have hk0 : (0 : ℤ) ≤ k := by positivity
  interval_cases j <;> interval_cases zq <;> (try simp) <;> nlinarith

end Research

end PaperVI
