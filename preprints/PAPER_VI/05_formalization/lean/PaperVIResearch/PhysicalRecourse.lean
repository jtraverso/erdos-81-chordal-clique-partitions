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
Paper VI research round — Priority 3 (continued): optimal partitions containing preassigned
physical blocks, and bounded recourse in the EXTERIOR LIFTING LAYER.

* `exists_partition_extending`: the general construction started from a legal partial lifting.
* `theoremB_extending`: under the hypothesis of Theorem B, every legal partial `K₄/K₅` lifting
  with load at most `7h` (prescribed orders `σ e ∈ {4,5}` on the edges it covers) is contained
  in an OPTIMAL clique partition realising the prescription `σ` on all exterior edges.
* `recourse_lift` / `theoremB_recourse`: in a complete legal lifting with load at most `r`, a
  new legal block may be imposed on one exterior edge while changing at most 13 core sets of
  the lifting (the edge's own block included). This bounds recourse in the exterior lifting
  layer only; the final triangle completion may change globally.
-/
module

public import PaperVIResearch.PhysicalExtension

@[expose] public section

namespace PaperVI

namespace Research

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

/-- **General construction from a preassigned partial lifting.** Under the hypotheses of the
general construction, there is an exact clique partition of `G` containing every preassigned
block `T₀ e ∪ e` (`e ∈ D₀`), all of whose blocks have the types of the construction. -/
theorem exists_partition_extending {σ : Sym2 V → ℕ} {c r need : ℕ}
    (hσc : ∀ e ∈ extEdges G P, σ e ≤ c)
    (hneed : ∀ e ∈ extEdges G P, σ e * (editDegree G P + (c - 1) * r + 1) ≤
      need + (editDegree G P + (c - 1) * r))
    (hcand : ∀ k bx by_ dx dy sat nD : ℕ, P.card ≤ k + bx + by_ + c * dx + c * dy + sat →
      bx + dx + 1 ≤ editDegree G P → by_ + dy + 1 ≤ editDegree G P → r * sat ≤ c * nD →
      nD + 1 ≤ mCount G P → 2 * mCount G P ≤ Pᶜ.card * editDegree G P → need ≤ k)
    (hlist : P.card + 2 * (editDegree G P + 2 * r) ≤ Pᶜ.card)
    {D₀ : Finset (Sym2 V)} {T₀ : Sym2 V → Finset V} (hinv : LiftInv G P σ r D₀ T₀)
    (hD₀ : D₀ ⊆ extEdges G P) :
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧
      (∀ e ∈ D₀, T₀ e ∪ e.toFinset ∈ Bs) ∧ ∀ B ∈ Bs,
      (coreSize P B = 1 ∧ extSize P B = 1) ∨ (coreSize P B = 2 ∧ extSize P B = 1) ∨
      ∃ e ∈ extEdges G P, (∀ v ∈ e, v ∈ B) ∧ coreSize P B = σ e ∧ extSize P B = 2 := by
  obtain ⟨T, hT, hagree⟩ := extend_lift G P hσc hneed hcand hinv hD₀
  obtain ⟨f, hf1, hf2, hf3⟩ := exists_completion_coloring P (availPair G P T)
    (editDegree G P + 2 * r) (card_unavail_le G P hT) hlist
  have hf1' := fun a ha b hb hab (_ : residPair G P T a b) => hf1 a ha b hb hab
  have hf2' := fun a ha b hb hab (_ : residPair G P T a b) => hf2 a ha b hb hab
  have hf3' := fun a ha b hb b' hb' hab hab' hbb' (_ : residPair G P T a b)
    (_ : residPair G P T a b') => hf3 a ha b hb b' hb' hab hab' hbb'
  refine ⟨allBlocks G P T f, allBlocks_isCliquePartition hT hf1' hf2' hf3', fun e he => ?_,
    fun B hB => allBlocks_types hT hf2' hB⟩
  rw [← hagree e he]
  exact mem_allBlocks.mpr (Or.inl (mem_liftBlocks.mpr ⟨e, hD₀ he, rfl⟩))

/-- **Theorem B with preassigned physical blocks.** Under the hypothesis of Theorem B
(`p = ⌊(n+1)/3⌋`, `p ≥ 63h`) and a prescription `σ e ∈ {4,5}` of block orders on the exterior
edges, let `T₀` be ANY legal partial lifting on `D₀ ⊆ E(H)` with core sets of size
`σ e - 2` and load at most `7h` (invariant `LiftInv`). Then some OPTIMAL clique partition
contains every preassigned block `T₀ e ∪ e`, `e ∈ D₀`, and realises `σ` on every exterior
edge. -/
theorem theoremB_extending (hP : P.card = (Fintype.card V + 1) / 3)
    (hh : 63 * editDegree G P ≤ P.card) (σ : Sym2 V → ℕ)
    (hσ : ∀ e ∈ extEdges G P, σ e = 4 ∨ σ e = 5)
    {D₀ : Finset (Sym2 V)} {T₀ : Sym2 V → Finset V}
    (hinv : LiftInv G P (fun e => σ e - 2) (7 * editDegree G P) D₀ T₀)
    (hD₀ : D₀ ⊆ extEdges G P) :
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ Bs.card = cp G ∧
      (cp G : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P ∧
      (∀ e ∈ D₀, T₀ e ∪ e.toFinset ∈ Bs) ∧
      (∀ e ∈ extEdges G P, ∃ B ∈ Bs, (∀ v ∈ e, v ∈ B) ∧ B.card = σ e ∧ extSize P B = 2) := by
  have hq : Pᶜ.card = Fintype.card V - P.card := card_compl P
  have hq1 : Pᶜ.card ≤ 2 * P.card + 1 := by
    rw [hq, hP]; exact q_le_two_p_add_one _
  have hq0 : 2 * P.card ≤ Pᶜ.card + 1 := by
    rw [hq, hP]; exact two_p_le_q_add_one _
  obtain ⟨Bs, hBs, hpre, htypes⟩ := exists_partition_extending G P (σ := fun e => σ e - 2)
    (c := 3) (r := 7 * editDegree G P) (need := 30 * editDegree G P + 3)
    (fun e he => by rcases hσ e he with h | h <;> omega)
    (fun e he => by rcases hσ e he with h | h <;> rw [h] <;> omega)
    (fun k bx by_ dx dy sat nD h1 h2 h3 h4 h5 h6 =>
      arith_candidates_B hq1 hh h1 h2 h3 h4 h5 h6)
    (by omega) hinv hD₀
  obtain ⟨hc, hcp, -, hreal, -⟩ := theoremB_of_partition G P hP σ hσ hBs htypes
  exact ⟨Bs, hBs, hc, hcp, hpre, hreal⟩

/-! ### Bounded recourse in the exterior lifting layer -/

omit [Fintype V] [DecidableRel G.Adj] in
/-- Edges of `D` whose core set contains a given pair. -/
theorem card_pair_owner_le {σ : Sym2 V → ℕ} {r : ℕ} {D : Finset (Sym2 V)}
    {T : Sym2 V → Finset V} (hT : LiftInv G P σ r D T) {a b : V} (hab : a ≠ b) :
    (D.filter (fun e => a ∈ T e ∧ b ∈ T e)).card ≤ 1 := by
  rw [card_le_one]
  intro e he e' he'
  rw [mem_filter] at he he'
  by_contra hne
  exact hT.pairDisj e he.1 e' he'.1 hne a he.2.1 b he.2.2 hab he'.2.1 he'.2.2

omit [Fintype V] [DecidableRel G.Adj] in
/-- Edges of `D` through an exterior vertex `x` whose core set contains `a`. -/
theorem card_inc_owner_le {σ : Sym2 V → ℕ} {r : ℕ} {D : Finset (Sym2 V)}
    {T : Sym2 V → Finset V} (hT : LiftInv G P σ r D T) (x a : V) :
    (D.filter (fun e => x ∈ e ∧ a ∈ T e)).card ≤ 1 := by
  rw [card_le_one]
  intro e he e' he'
  rw [mem_filter] at he he'
  by_contra hne
  exact hT.incDisj e he.1 e' he'.1 hne x he.2.1 he'.2.1 a he.2.2 he'.2.2

/-- A new block on `e₀`: a legal core set `N` (inside `P`, a clique, joined to both ends of
`e₀`). -/
structure LegalNewBlock (e₀ : Sym2 V) (N : Finset V) : Prop where
  sub : N ⊆ P
  coreAdj : ∀ a ∈ N, ∀ b ∈ N, a ≠ b → G.Adj a b
  crossAdj : ∀ a ∈ N, ∀ x ∈ e₀, G.Adj a x

/-- **Bounded recourse (abstract form).** Let `T` be a complete legal lifting (load at most
`r`, `r ≥ 1`) and let `N` (of size at most three) be a legal new core set for the exterior edge
`e₀`. Under the counting hypotheses of the lifting lemma for the updated size prescription,
there is a complete legal lifting `T'` with load at most `r` such that `T' e₀ = N` and
`T' e = T e` for all but at most `13` exterior edges `e` (the edge `e₀` included). -/
theorem recourse_lift {σ : Sym2 V → ℕ} {c r need : ℕ} (hr : 1 ≤ r)
    {T : Sym2 V → Finset V} (hT : LiftInv G P σ r (extEdges G P) T)
    {e₀ : Sym2 V} (he₀ : e₀ ∈ extEdges G P) {N : Finset V} (hN : LegalNewBlock G P e₀ N)
    (hN3 : N.card ≤ 3)
    (hσc : ∀ e ∈ extEdges G P, Function.update σ e₀ N.card e ≤ c)
    (hneed : ∀ e ∈ extEdges G P, Function.update σ e₀ N.card e *
      (editDegree G P + (c - 1) * r + 1) ≤ need + (editDegree G P + (c - 1) * r))
    (hcand : ∀ k bx by_ dx dy sat nD : ℕ, P.card ≤ k + bx + by_ + c * dx + c * dy + sat →
      bx + dx + 1 ≤ editDegree G P → by_ + dy + 1 ≤ editDegree G P → r * sat ≤ c * nD →
      nD + 1 ≤ mCount G P → 2 * mCount G P ≤ Pᶜ.card * editDegree G P → need ≤ k) :
    ∃ T' : Sym2 V → Finset V,
      LiftInv G P (Function.update σ e₀ N.card) r (extEdges G P) T' ∧ T' e₀ = N ∧
      ((extEdges G P).filter (fun e => T' e ≠ T e)).card ≤ 13 := by
  set E := extEdges G P with hE
  -- pair conflicts
  set W1 := (N.sym2.filter (fun s => ¬ s.IsDiag)).biUnion
    (fun s => E.filter (fun e => ∀ a ∈ s.toFinset, a ∈ T e)) with hW1
  -- incidence conflicts
  set W2 := (e₀.toFinset ×ˢ N).biUnion
    (fun xa => E.filter (fun e => xa.1 ∈ e ∧ xa.2 ∈ T e)) with hW2
  set W012 := insert e₀ (W1 ∪ W2) with hW012
  have hW1card : W1.card ≤ 3 := by
    refine card_biUnion_le.trans ?_
    have hle : ∀ s ∈ N.sym2.filter (fun s => ¬ s.IsDiag),
        (E.filter (fun e => ∀ a ∈ s.toFinset, a ∈ T e)).card ≤ 1 := by
      intro s hs
      induction s using Sym2.ind with
      | h a b =>
        rw [mem_filter, Sym2.mk_isDiag_iff] at hs
        refine le_trans (card_le_card ?_) (card_pair_owner_le G P hT hs.2)
        intro e he
        simp only [mem_filter, Sym2.mem_toFinset, Sym2.mem_iff] at he ⊢
        exact ⟨he.1, he.2 a (Or.inl rfl), he.2 b (Or.inr rfl)⟩
    calc ∑ s ∈ N.sym2.filter (fun s => ¬ s.IsDiag),
          (E.filter (fun e => ∀ a ∈ s.toFinset, a ∈ T e)).card
        ≤ ∑ _s ∈ N.sym2.filter (fun s => ¬ s.IsDiag), 1 := sum_le_sum hle
      _ = (N.sym2.filter (fun s => ¬ s.IsDiag)).card := by simp
      _ = N.card.choose 2 := card_sym2_filter_not_isDiag N
      _ ≤ 3 := by interval_cases h : N.card <;> simp_all
  have hW2card : W2.card ≤ 6 := by
    refine card_biUnion_le.trans ?_
    calc ∑ xa ∈ e₀.toFinset ×ˢ N, (E.filter (fun e => xa.1 ∈ e ∧ xa.2 ∈ T e)).card
        ≤ ∑ _xa ∈ e₀.toFinset ×ˢ N, 1 :=
          sum_le_sum fun xa _ => card_inc_owner_le G P hT xa.1 xa.2
      _ = e₀.toFinset.card * N.card := by simp
      _ ≤ 2 * 3 := by
          apply Nat.mul_le_mul _ hN3
          rw [Sym2.card_toFinset]; split_ifs <;> omega
  -- load relief
  set L : V → Finset (Sym2 V) := fun a => (E \ W012).filter (fun e => a ∈ T e) with hL
  have hpick : ∀ a ∈ N, r ≤ (L a).card → ∃ e, e ∈ L a := by
    intro a _ h
    exact card_pos.mp (by omega)
  haveI : Nonempty (Sym2 V) := ⟨e₀⟩
  choose! g hg using hpick
  set W3 := (N.filter (fun a => r ≤ (L a).card)).image g with hW3
  have hW3card : W3.card ≤ 3 := (card_image_le).trans ((card_filter_le _ _).trans hN3)
  set W := W012 ∪ W3 with hW
  have hWcard : W.card ≤ 13 := by
    rw [hW]
    have h1 := card_union_le W012 W3
    have h2 : W012.card ≤ (W1 ∪ W2).card + 1 := by rw [hW012]; exact card_insert_le _ _
    have h3 := card_union_le W1 W2
    omega
  -- the new partial lifting
  set D₀ := insert e₀ (E \ W) with hD₀
  set T₀ := Function.update T e₀ N with hT₀
  have hT₀e : T₀ e₀ = N := by simp [hT₀]
  have hT₀o : ∀ e, e ≠ e₀ → T₀ e = T e := fun e he => by simp [hT₀, he]
  have hnotW : ∀ e ∈ E \ W, e ≠ e₀ ∧ e ∉ W1 ∧ e ∉ W2 ∧ e ∉ W3 := by
    intro e he
    rw [mem_sdiff, hW, mem_union, hW012, mem_insert, mem_union] at he
    push_neg at he
    exact ⟨he.2.1.1, he.2.1.2.1, he.2.1.2.2, he.2.2⟩
  have hE_of : ∀ e ∈ E \ W, e ∈ E := fun e he => (mem_sdiff.mp he).1
  -- no pair conflicts with `N`
  have hpairN : ∀ e ∈ E \ W, ∀ a ∈ N, ∀ b ∈ N, a ≠ b → a ∈ T e → b ∉ T e := by
    intro e he a ha b hb hab hae hbe
    refine (hnotW e he).2.1 (mem_biUnion.mpr ⟨s(a, b), ?_, ?_⟩)
    · rw [mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff]; exact ⟨⟨ha, hb⟩, hab⟩
    · rw [mem_filter]; refine ⟨hE_of e he, ?_⟩
      intro c hc
      rw [Sym2.mem_toFinset, Sym2.mem_iff] at hc
      rcases hc with rfl | rfl <;> assumption
  -- no incidence conflicts with `N`
  have hincN : ∀ e ∈ E \ W, ∀ x ∈ e₀, x ∈ e → ∀ a ∈ N, a ∉ T e := by
    intro e he x hx hxe a ha hae
    refine (hnotW e he).2.2.1 (mem_biUnion.mpr ⟨(x, a), ?_, ?_⟩)
    · rw [mem_product, Sym2.mem_toFinset]; exact ⟨hx, ha⟩
    · rw [mem_filter]; exact ⟨hE_of e he, hxe, hae⟩
  -- load strictly below `r` for vertices of `N`
  have hloadN : ∀ a ∈ N, ((E \ W).filter (fun e => a ∈ T e)).card < r := by
    intro a ha
    have hsubL : (E \ W).filter (fun e => a ∈ T e) ⊆ L a := by
      intro e he
      simp only [hL, mem_filter, mem_sdiff, hW, mem_union, not_or] at he ⊢
      exact ⟨⟨he.1.1, he.1.2.1⟩, he.2⟩
    have hLle : (L a).card ≤ r := by
      refine le_trans (card_le_card ?_) (hT.load a)
      intro e he
      simp only [hL, mem_filter, mem_sdiff] at he ⊢
      exact ⟨he.1.1, he.2⟩
    by_cases hfull : r ≤ (L a).card
    · have hgW : g a ∈ W3 := mem_image_of_mem g (mem_filter.mpr ⟨ha, hfull⟩)
      have hga := hg a ha hfull
      have hsub2 : (E \ W).filter (fun e => a ∈ T e) ⊆ (L a).erase (g a) := by
        intro e he
        refine mem_erase.mpr ⟨?_, hsubL he⟩
        rintro rfl
        exact (hnotW _ (mem_filter.mp he).1).2.2.2 hgW
      have := card_le_card hsub2
      rw [card_erase_of_mem hga] at this
      omega
    · exact lt_of_le_of_lt (card_le_card hsubL) (by omega)
  have he₀D : e₀ ∉ E \ W := fun h => (hnotW e₀ h).1 rfl
  have hinv₀ : LiftInv G P (Function.update σ e₀ N.card) r D₀ T₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e he
      rcases mem_insert.mp he with rfl | he
      · rw [hT₀e]; exact hN.sub
      · rw [hT₀o e (hnotW e he).1]; exact hT.sub e (hE_of e he)
    · intro e he
      rcases mem_insert.mp he with rfl | he
      · rw [hT₀e, Function.update_self]
      · rw [hT₀o e (hnotW e he).1, Function.update_of_ne (hnotW e he).1]
        exact hT.card e (hE_of e he)
    · intro e he a ha b hb hab
      rcases mem_insert.mp he with rfl | he
      · rw [hT₀e] at ha hb; exact hN.coreAdj a ha b hb hab
      · rw [hT₀o e (hnotW e he).1] at ha hb; exact hT.coreAdj e (hE_of e he) a ha b hb hab
    · intro e he a ha x hx
      rcases mem_insert.mp he with rfl | he
      · rw [hT₀e] at ha; exact hN.crossAdj a ha x hx
      · rw [hT₀o e (hnotW e he).1] at ha; exact hT.crossAdj e (hE_of e he) a ha x hx
    · intro e he e' he' hee' a ha b hb hab hae'
      rcases mem_insert.mp he with rfl | he <;> rcases mem_insert.mp he' with rfl | he'
      · exact absurd rfl hee'
      · rw [hT₀e] at ha hb; rw [hT₀o e' (hnotW e' he').1] at hae' ⊢
        exact hpairN e' he' a ha b hb hab hae'
      · rw [hT₀o e (hnotW e he).1] at ha hb; rw [hT₀e] at hae' ⊢
        intro hbN
        exact hpairN e he a hae' b hbN hab ha hb
      · rw [hT₀o e (hnotW e he).1] at ha hb; rw [hT₀o e' (hnotW e' he').1] at hae' ⊢
        exact hT.pairDisj e (hE_of e he) e' (hE_of e' he') hee' a ha b hb hab hae'
    · intro e he e' he' hee' x hx hx' a ha
      rcases mem_insert.mp he with rfl | he <;> rcases mem_insert.mp he' with rfl | he'
      · exact absurd rfl hee'
      · rw [hT₀e] at ha; rw [hT₀o e' (hnotW e' he').1]
        exact hincN e' he' x hx hx' a ha
      · rw [hT₀o e (hnotW e he).1] at ha; rw [hT₀e]
        intro haN
        exact hincN e he x hx' hx a haN ha
      · rw [hT₀o e (hnotW e he).1] at ha; rw [hT₀o e' (hnotW e' he').1]
        exact hT.incDisj e (hE_of e he) e' (hE_of e' he') hee' x hx hx' a ha
    · intro a
      have hfD : (E \ W).filter (fun e => a ∈ T₀ e) = (E \ W).filter (fun e => a ∈ T e) :=
        filter_congr fun e he => by rw [hT₀o e (hnotW e he).1]
      rw [hD₀, filter_insert, hT₀e]
      split_ifs with haN
      · rw [card_insert_of_notMem (fun h => he₀D (mem_filter.mp h).1), hfD]
        have := hloadN a haN
        omega
      · rw [hfD]
        exact le_trans (card_le_card (filter_subset_filter _ sdiff_subset)) (hT.load a)
  have hD₀sub : D₀ ⊆ E := insert_subset he₀ sdiff_subset
  obtain ⟨T', hT', hagree⟩ := extend_lift G P hσc hneed hcand hinv₀ hD₀sub
  refine ⟨T', hT', by rw [hagree e₀ (mem_insert_self _ _), hT₀e], ?_⟩
  refine le_trans (card_le_card ?_) hWcard
  intro e he
  rw [mem_filter] at he
  by_contra heW
  have heD : e ∈ E \ W := mem_sdiff.mpr ⟨he.1, heW⟩
  apply he.2
  rw [hagree e (mem_insert_of_mem heD), hT₀o e (hnotW e heD).1]

/-- **Bounded recourse under Theorem B.** Under the hypothesis of Theorem B, let `T` be a
complete legal lifting realising a prescription `σ e ∈ {4,5}` with load at most `7h`, and let
`N` be a legal new core set of size two or three for an exterior edge `e₀` (a legal `K₄` or
`K₅` on `e₀`). Then there is a complete legal lifting with load at most `7h`, realising the
prescription `σ` updated only at `e₀` (to `|N| + 2`), that contains the new block on `e₀` and
differs from `T` on at most `13` exterior edges (the edge `e₀` included). Only the exterior
lifting layer is controlled; the triangle completion may change globally. -/
theorem theoremB_recourse (hP : P.card = (Fintype.card V + 1) / 3)
    (hh : 63 * editDegree G P ≤ P.card) (σ : Sym2 V → ℕ)
    (hσ : ∀ e ∈ extEdges G P, σ e = 4 ∨ σ e = 5)
    {T : Sym2 V → Finset V}
    (hT : LiftInv G P (fun e => σ e - 2) (7 * editDegree G P) (extEdges G P) T)
    {e₀ : Sym2 V} (he₀ : e₀ ∈ extEdges G P) {N : Finset V} (hN : LegalNewBlock G P e₀ N)
    (hN23 : N.card = 2 ∨ N.card = 3) :
    ∃ T' : Sym2 V → Finset V,
      LiftInv G P (Function.update (fun e => σ e - 2) e₀ N.card) (7 * editDegree G P)
        (extEdges G P) T' ∧ T' e₀ = N ∧
      ((extEdges G P).filter (fun e => T' e ≠ T e)).card ≤ 13 := by
  have hq : Pᶜ.card = Fintype.card V - P.card := card_compl P
  have hq1 : Pᶜ.card ≤ 2 * P.card + 1 := by
    rw [hq, hP]; exact q_le_two_p_add_one _
  have hh1 : 1 ≤ editDegree G P := by
    induction e₀ using Sym2.ind with
    | h x y =>
      rw [mem_extEdges] at he₀
      have := ext_local_bound G P x he₀.2.1
      have hy : y ∈ Pᶜ.filter (fun w => G.Adj x w) := mem_filter.mpr ⟨mem_compl.mpr he₀.2.2, he₀.1⟩
      have := card_pos.mpr ⟨y, hy⟩
      omega
  have hσ' : ∀ e ∈ extEdges G P, Function.update (fun e => σ e - 2) e₀ N.card e ≤ 3 := by
    intro e he
    by_cases h : e = e₀
    · subst h; rw [Function.update_self]; omega
    · rw [Function.update_of_ne h]; rcases hσ e he with h' | h' <;> simp [h']
  exact recourse_lift G P (c := 3) (need := 30 * editDegree G P + 3) (by omega) hT he₀ hN
    (by omega) hσ'
    (fun e he => by
      have := hσ' e he
      calc Function.update (fun e => σ e - 2) e₀ N.card e *
            (editDegree G P + (3 - 1) * (7 * editDegree G P) + 1)
          ≤ 3 * (editDegree G P + (3 - 1) * (7 * editDegree G P) + 1) :=
            Nat.mul_le_mul_right _ this
        _ ≤ _ := by omega)
    (fun k bx by_ dx dy sat nD h1 h2 h3 h4 h5 h6 =>
      arith_candidates_B hq1 hh h1 h2 h3 h4 h5 h6)

end Research

end PaperVI
