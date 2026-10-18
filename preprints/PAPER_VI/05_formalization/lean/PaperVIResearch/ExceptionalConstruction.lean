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
Paper VI research round — Theorem E, part 2: the physical construction.

The `b` exterior edges `zx` (`x ∈ B`) receive pairwise disjoint core sets `T x ⊆ A` of size at
most two (a single edge, a triangle `zvx`, or a `K₄` `zvv'x`). This is a legal lifting with
load at most one; the residual core is completed by the Häggkvist–Janssen theorem with colours
from `R` (so `z` is never used as a completion colour), and the remaining crossing edges are
single blocks. The exact block count is `Φ + Σ_{x ∈ B} ℓ(|T x|, 2)`.
-/
module

public import PaperVIResearch.ExceptionalSetup
public import PaperVI.Engine

@[expose] public section

namespace PaperVI

namespace Research

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The slack of a block of type `(k, 2)`, `k ≤ 2`: `3, 1, 0`. -/
theorem slack_zero_two : slack 0 2 = 3 := by decide
theorem slack_one_two : slack 1 2 = 1 := by decide
theorem slack_two_two : slack 2 2 = 0 := by decide

omit [Fintype V] in
/-- **Greedy star assignment (general form).** Given a target function `tgt` with a one-step
recurrence, the vertices of `Bf` receive pairwise disjoint subsets of `A` of size at most `c`
with total slack `Σ ℓ(|T x|, 2) ≤ tgt |A| |Bf|`. -/
theorem exists_star_assign_gen (c : ℕ) (tgt : ℕ → ℕ → ℤ) (h0 : ∀ a, 0 ≤ tgt a 0)
    (hstep : ∀ a b, ∃ n, n ≤ a ∧ n ≤ c ∧ slack n 2 + tgt (a - n) b ≤ tgt a (b + 1))
    (Bf : Finset V) : ∀ A : Finset V, ∃ T : V → Finset V,
      (∀ x ∈ Bf, T x ⊆ A ∧ (T x).card ≤ c) ∧
      (∀ x ∈ Bf, ∀ y ∈ Bf, x ≠ y → Disjoint (T x) (T y)) ∧
      ∑ x ∈ Bf, slack (T x).card 2 ≤ tgt A.card Bf.card := by
  induction Bf using Finset.induction_on with
  | empty => intro A; exact ⟨fun _ => ∅, by simp, by simp, by simpa using h0 A.card⟩
  | insert x Bf hx ih =>
    intro A
    obtain ⟨n, hna, hnc, hval⟩ := hstep A.card Bf.card
    obtain ⟨S, hSA, hScard⟩ := exists_subset_card_eq hna
    obtain ⟨T, h1, h2, h3⟩ := ih (A \ S)
    have hT : ∀ y ∈ Bf, Function.update T x S y = T y := fun y hy =>
      Function.update_of_ne (fun h => hx (by rw [← h]; exact hy)) _ _
    refine ⟨Function.update T x S, ?_, ?_, ?_⟩
    · intro y hy
      rw [mem_insert] at hy
      rcases hy with rfl | hy
      · rw [Function.update_self]; exact ⟨hSA, by omega⟩
      · rw [hT y hy]; exact ⟨(h1 y hy).1.trans sdiff_subset, (h1 y hy).2⟩
    · intro y hy y' hy' hyy'
      rw [mem_insert] at hy hy'
      rcases hy with rfl | hy <;> rcases hy' with rfl | hy'
      · exact absurd rfl hyy'
      · rw [Function.update_self, hT y' hy']
        exact disjoint_of_subset_right (h1 y' hy').1 disjoint_sdiff
      · rw [Function.update_self, hT y hy]
        exact disjoint_of_subset_left (h1 y hy).1 sdiff_disjoint
      · rw [hT y hy, hT y' hy']; exact h2 y hy y' hy' hyy'
    · rw [sum_insert hx, Function.update_self, hScard, card_insert_of_notMem hx,
        sum_congr rfl (fun y hy => by rw [hT y hy])]
      have hc : (A \ S).card = A.card - n := by rw [card_sdiff_of_subset hSA, hScard]
      rw [hc] at h3
      linarith

/-- The recurrence for the defect `D(a,b)` (blocks of size at most four). -/
theorem Dval_step (a b : ℕ) :
    ∃ n, n ≤ a ∧ n ≤ 2 ∧ slack n 2 + Dval (a - n) b ≤ Dval a (b + 1) := by
  unfold Dval
  by_cases ha : a = 0
  · refine ⟨0, by omega, by omega, ?_⟩
    rw [slack_zero_two]; subst ha; push_cast; omega
  · by_cases hab : a ≤ b + 1
    · refine ⟨1, by omega, by omega, ?_⟩
      rw [slack_one_two]; push_cast [show 1 ≤ a by omega]; omega
    · refine ⟨2, by omega, le_rfl, ?_⟩
      rw [slack_two_two]; push_cast [show 2 ≤ a by omega]; omega

/-- The target `3b - 2 min(a,b)` for blocks of size at most three. -/
def Dthree (a b : ℕ) : ℤ := 3 * (b : ℤ) - 2 * min (a : ℤ) b

theorem Dthree_step (a b : ℕ) :
    ∃ n, n ≤ a ∧ n ≤ 1 ∧ slack n 2 + Dthree (a - n) b ≤ Dthree a (b + 1) := by
  unfold Dthree
  by_cases ha : a = 0
  · refine ⟨0, by omega, by omega, ?_⟩
    rw [slack_zero_two]; subst ha; push_cast; omega
  · refine ⟨1, by omega, le_rfl, ?_⟩
    rw [slack_one_two]; push_cast [show 1 ≤ a by omega]; omega

section Construction

variable {G : SimpleGraph V} [DecidableRel G.Adj] {P R A B : Finset V} {z : V}
  (hS : ExSetup G P R A B z)
include hS

/-- The exterior edges are exactly the edges `zx`, `x ∈ B`. -/
theorem ExSetup.extEdges_eq : extEdges G P = B.image (fun x => s(z, x)) := by
  ext e
  induction e using Sym2.ind with
  | h u w =>
    rw [mem_extEdges, mem_image]
    constructor
    · rintro ⟨hadj, hu, hw⟩
      rcases hS.cover u with h1 | h1 | rfl
      · exact absurd h1 hu
      · rcases hS.cover w with h2 | h2 | rfl
        · exact absurd h2 hw
        · exact absurd hadj (hS.indepR u h1 w h2)
        · refine ⟨u, ?_, Sym2.eq_swap⟩
          rcases (hS.adjz u).mp hadj.symm with h | h
          · exact absurd (hS.AsubP h) hu
          · exact h
      · refine ⟨w, ?_, rfl⟩
        rcases (hS.adjz w).mp hadj with h | h
        · exact absurd (hS.AsubP h) hw
        · exact h
    · rintro ⟨x, hx, hxe⟩
      rw [Sym2.eq_iff] at hxe
      have hxR := hS.BsubR hx
      have hxP : x ∉ P := fun h => hS.notR_of_P h hxR
      have hzx : G.Adj z x := (hS.adjz x).mpr (Or.inr hx)
      rcases hxe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hzx, hS.zP, hxP⟩
      · exact ⟨hzx.symm, hxP, hS.zP⟩

variable {T : V → Finset V} (hTA : ∀ x ∈ B, T x ⊆ A)
  (hTd : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → Disjoint (T x) (T y))

/-- The lifting attached to a star assignment. -/
def starLift (B : Finset V) (z : V) (T : V → Finset V) (e : Sym2 V) : Finset V :=
  (B.filter (fun x => e = s(z, x))).biUnion T

omit hS [Fintype V] in
theorem starLift_apply {x : V} (hx : x ∈ B) : starLift B z T s(z, x) = T x := by
  unfold starLift
  have : B.filter (fun y => s(z, x) = s(z, y)) = {x} := by
    ext y
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨-, h⟩; exact (Sym2.congr_right.mp h).symm
    · rintro rfl; exact ⟨hx, rfl⟩
  rw [this, singleton_biUnion]

include hTA hTd in
/-- The star assignment is a legal lifting with load at most one. -/
theorem ExSetup.starLift_inv :
    LiftInv G P (fun e => (starLift B z T e).card) 1 (extEdges G P) (starLift B z T) := by
  rw [hS.extEdges_eq]
  have hmem : ∀ e ∈ B.image (fun x => s(z, x)), ∃ x ∈ B, e = s(z, x) ∧
      starLift B z T e = T x := by
    intro e he
    obtain ⟨x, hx, rfl⟩ := mem_image.mp he
    exact ⟨x, hx, rfl, starLift_apply hx⟩
  refine ⟨?_, fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨x, hx, -, h⟩ := hmem e he
    rw [h]; exact (hTA x hx).trans hS.AsubP
  · intro e he a ha b hb hab
    obtain ⟨x, hx, -, h⟩ := hmem e he
    rw [h] at ha hb
    exact hS.adjPP a (hS.AsubP (hTA x hx ha)) b (hS.AsubP (hTA x hx hb)) hab
  · intro e he a ha y hy
    obtain ⟨x, hx, rfl, h⟩ := hmem e he
    rw [h] at ha
    have haA := hTA x hx ha
    rw [Sym2.mem_iff] at hy
    rcases hy with rfl | rfl
    · exact ((hS.adjz a).mpr (Or.inl haA)).symm
    · exact hS.adjPR a (hS.AsubP haA) _ (hS.BsubR hx)
  · intro e he e' he' hee' a ha b _ _ hae'
    obtain ⟨x, hx, rfl, h⟩ := hmem e he
    obtain ⟨x', hx', rfl, h'⟩ := hmem e' he'
    rw [h] at ha; rw [h'] at hae'
    have hxx : x ≠ x' := fun h => hee' (h ▸ rfl)
    exact absurd hae' (disjoint_left.mp (hTd x hx x' hx' hxx) ha)
  · intro e he e' he' hee' _ _ _ a ha
    obtain ⟨x, hx, rfl, h⟩ := hmem e he
    obtain ⟨x', hx', rfl, h'⟩ := hmem e' he'
    rw [h] at ha; rw [h']
    have hxx : x ≠ x' := fun h => hee' (h ▸ rfl)
    exact disjoint_left.mp (hTd x hx x' hx' hxx) ha
  · intro a
    rw [card_le_one]
    intro e he e' he'
    rw [mem_filter] at he he'
    obtain ⟨x, hx, rfl, h⟩ := hmem e he.1
    obtain ⟨x', hx', rfl, h'⟩ := hmem e' he'.1
    have h1 := he.2; have h2 := he'.2
    rw [h] at h1; rw [h'] at h2
    by_contra hne
    have hxx : x ≠ x' := fun h => hne (h ▸ rfl)
    exact disjoint_left.mp (hTd x hx x' hx' hxx) h1 h2

include hTd in
/-- At most one exterior colour (in `R`) is unavailable at a core vertex. -/
theorem ExSetup.card_unavail_R_le {a : V} (ha : a ∈ P) :
    (R.filter (fun x => ¬ availPair G P (starLift B z T) a x)).card ≤ 1 := by
  have key : ∀ x ∈ R.filter (fun x => ¬ availPair G P (starLift B z T) a x),
      x ∈ B ∧ a ∈ T x := by
    intro x hx
    rw [mem_filter] at hx
    obtain ⟨hxR, hna⟩ := hx
    unfold availPair at hna
    push_neg at hna
    obtain ⟨e, he, hae, hxe⟩ := hna (hS.adjPR a ha x hxR)
    rw [hS.extEdges_eq] at he
    obtain ⟨y, hy, rfl⟩ := mem_image.mp he
    rw [starLift_apply hy] at hae
    rw [Sym2.mem_iff] at hxe
    rcases hxe with rfl | rfl
    · exact absurd hxR hS.zR
    · exact ⟨hy, hae⟩
  rw [card_le_one]
  intro x hx y hy
  obtain ⟨hxB, hax⟩ := key x hx
  obtain ⟨hyB, hay⟩ := key y hy
  by_contra hxy
  exact disjoint_left.mp (hTd x hxB y hyB hxy) hax hay

omit [Fintype V] [DecidableRel G.Adj] hTd in
include hTA in
theorem ExSetup.starBlock_inter_P {x : V} (hx : x ∈ B) :
    insert z (insert x (T x)) ∩ P = T x := by
  ext v
  simp only [mem_inter, mem_insert]
  constructor
  · rintro ⟨h | h | h, hv⟩
    · exact absurd (h ▸ hv) hS.zP
    · exact absurd (h ▸ hv) (fun hP => hS.notR_of_P hP (hS.BsubR hx))
    · exact h
  · intro h
    exact ⟨Or.inr (Or.inr h), hS.AsubP (hTA x hx h)⟩

omit [Fintype V] [DecidableRel G.Adj] hTd in
include hTA in
theorem ExSetup.starBlock_sdiff_P {x : V} (hx : x ∈ B) :
    insert z (insert x (T x)) \ P = {z, x} := by
  ext v
  simp only [mem_sdiff, mem_insert, mem_singleton]
  constructor
  · rintro ⟨h | h | h, hv⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (hS.AsubP (hTA x hx h)) hv
  · rintro (rfl | rfl)
    · exact ⟨Or.inl rfl, hS.zP⟩
    · exact ⟨Or.inr (Or.inl rfl), fun hP => hS.notR_of_P hP (hS.BsubR hx)⟩

omit [Fintype V] [DecidableRel G.Adj] hTd in
include hTA in
theorem ExSetup.slack_starBlock {x : V} (hx : x ∈ B) :
    slack (coreSize P (insert z (insert x (T x)))) (extSize P (insert z (insert x (T x)))) =
      slack (T x).card 2 := by
  unfold coreSize extSize
  rw [hS.starBlock_inter_P hTA hx, hS.starBlock_sdiff_P hTA hx,
    card_pair (hS.ne_z_of_R (hS.BsubR hx)).symm]

include hTA hTd in
/-- **The physical construction of Theorem E.** For every star assignment (pairwise disjoint
`T x ⊆ A`, `x ∈ B`), if `p + 2 ≤ |R|` (i.e. `q ≥ p + 3`) there is an exact clique partition of
`G` containing every star block `{z, x} ∪ T x`, whose other blocks are crossing edges or
triangles of type `(2,1)`, and whose number of blocks is `Φ + Σ_{x ∈ B} ℓ(|T x|, 2)`. -/
theorem ExSetup.exists_partition_star (hq : P.card + 2 ≤ R.card) :
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧
      (∀ x ∈ B, insert z (insert x (T x)) ∈ Bs) ∧
      (∀ Q ∈ Bs, (∃ x ∈ B, Q = insert z (insert x (T x))) ∨
        (extSize P Q = 1 ∧ (coreSize P Q = 1 ∨ coreSize P Q = 2))) ∧
      (Bs.card : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P +
        ∑ x ∈ B, slack (T x).card 2 := by
  have hT := hS.starLift_inv hTA hTd
  have hRc : R ⊆ Pᶜ := fun x hx => mem_compl.mpr (fun h => hS.notR_of_P h hx)
  obtain ⟨f, hf1, hf2, hf3⟩ := exists_completion_coloring_in P R hRc
    (availPair G P (starLift B z T)) 1 (fun a ha => hS.card_unavail_R_le hTd ha) hq
  have hf1' := fun a ha b hb hab (_ : residPair G P (starLift B z T) a b) => hf1 a ha b hb hab
  have hf2' := fun a ha b hb hab (_ : residPair G P (starLift B z T) a b) =>
    (hf2 a ha b hb hab).2
  have hf3' := fun a ha b hb b' hb' hab hab' hbb' (_ : residPair G P (starLift B z T) a b)
    (_ : residPair G P (starLift B z T) a b') => hf3 a ha b hb b' hb' hab hab' hbb'
  have hBs := allBlocks_isCliquePartition hT hf1' hf2' hf3'
  set Bs := allBlocks G P (starLift B z T) f with hBsdef
  have hstar : ∀ x ∈ B, insert z (insert x (T x)) ∈ Bs := by
    intro x hx
    refine mem_allBlocks.mpr (Or.inl (mem_liftBlocks.mpr ⟨s(z, x), ?_, ?_⟩))
    · rw [hS.extEdges_eq]; exact mem_image_of_mem _ hx
    · rw [starLift_apply hx]
      ext v; simp only [mem_union, Sym2.mem_toFinset, Sym2.mem_iff, mem_insert]; tauto
  have hclass : ∀ Q ∈ Bs, (∃ x ∈ B, Q = insert z (insert x (T x))) ∨
      (extSize P Q = 1 ∧ (coreSize P Q = 1 ∨ coreSize P Q = 2)) := by
    intro Q hQ
    rcases allBlocks_types hT hf2' hQ with h | h | ⟨e, he, heQ, -, -⟩
    · exact Or.inr ⟨h.2, Or.inl h.1⟩
    · exact Or.inr ⟨h.2, Or.inr h.1⟩
    · left
      rw [hS.extEdges_eq] at he
      obtain ⟨x, hx, rfl⟩ := mem_image.mp he
      refine ⟨x, hx, block_unique_of_edge G hBs (e := s(z, x)) ?_ hQ (hstar x hx) heQ ?_⟩
      · exact SimpleGraph.mem_edgeFinset.mpr ((hS.adjz x).mpr (Or.inr hx))
      · intro v hv
        rcases Sym2.mem_iff.mp hv with rfl | rfl <;> simp
  refine ⟨Bs, hBs, hstar, hclass, ?_⟩
  have hid := slack_identity G P hBs
  have hsum : ∑ Q ∈ Bs, slack (coreSize P Q) (extSize P Q) = ∑ x ∈ B, slack (T x).card 2 := by
    have hL : B.image (fun x => insert z (insert x (T x))) ⊆ Bs := by
      intro Q hQ
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hQ
      exact hstar x hx
    rw [← sum_subset hL]
    · rw [sum_image]
      · exact sum_congr rfl fun x hx => hS.slack_starBlock hTA hx
      · intro x hx y hy hxy
        have hxm : x ∈ insert z (insert y (T y)) := by
          have hxy' : insert z (insert x (T x)) = insert z (insert y (T y)) := hxy
          rw [← hxy']; simp
        simp only [mem_coe, mem_insert] at hxm hx hy
        rcases hxm with h | h | h
        · exact absurd h (hS.ne_z_of_R (hS.BsubR hx))
        · exact h
        · exact absurd (hS.AsubP (hTA y hy h)) (fun hP => hS.notR_of_P hP (hS.BsubR hx))
    · intro Q hQ hQL
      rcases hclass Q hQ with ⟨x, hx, rfl⟩ | ⟨h1, h2 | h2⟩
      · exact absurd (mem_image_of_mem _ hx) hQL
      · rw [h1, h2]; decide
      · rw [h1, h2]; decide
  rw [hsum] at hid
  linarith

end Construction

end Research

end PaperVI
