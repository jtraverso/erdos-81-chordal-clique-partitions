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
/- Protected target alignment in the actual bounded-load exterior lifting.
Adapted from Research.recourse_lift; load relief is chosen outside protected Q. -/
module
public import PaperVIResearch.PhysicalRecourse
public import PaperVIRecourse.ProtectedOwners
@[expose] public section
namespace PaperVIRecourse
open Finset PaperVI PaperVI.Research
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

theorem protected_recourse_lift {σ : Sym2 V → ℕ} {c r need : ℕ} (hr : 1 ≤ r)
    {T Tstar : Sym2 V → Finset V}
    (hT : LiftInv G P σ r (extEdges G P) T)
    (hTstar : LiftInv G P σ r (extEdges G P) Tstar)
    {Q : Finset (Sym2 V)} (hQsub : Q ⊆ extEdges G P)
    (hprotect : ∀ e ∈ Q, T e = Tstar e)
    {e₀ : Sym2 V} (he₀ : e₀ ∈ extEdges G P) (he₀Q : e₀ ∉ Q)
    (hNcard_le : (Tstar e₀).card ≤ 3)
    (hσc : ∀ e ∈ extEdges G P, σ e ≤ c)
    (hneed : ∀ e ∈ extEdges G P, σ e *
      (editDegree G P + (c-1)*r+1) ≤ need+(editDegree G P+(c-1)*r))
    (hcand : ∀ k bx by_ dx dy sat nD : ℕ,
      P.card ≤ k+bx+by_+c*dx+c*dy+sat →
      bx+dx+1 ≤ editDegree G P → by_+dy+1 ≤ editDegree G P → r*sat ≤ c*nD →
      nD+1 ≤ mCount G P → 2*mCount G P ≤ Pᶜ.card*editDegree G P → need ≤ k) :
    ∃ T', LiftInv G P σ r (extEdges G P) T' ∧ T' e₀ = Tstar e₀ ∧
      (∀ e ∈ Q, T' e = Tstar e) ∧
      ((extEdges G P).filter (fun e => T' e ≠ T e)).card ≤ 13 := by
  classical
  let N := Tstar e₀
  have hN3 : N.card ≤ 3 := hNcard_le
  have hNcard : N.card = σ e₀ := hTstar.card e₀ he₀
  have hN : LegalNewBlock G P e₀ N :=
    ⟨hTstar.sub e₀ he₀,hTstar.coreAdj e₀ he₀,hTstar.crossAdj e₀ he₀⟩
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
      _ ≤ 3 := by interval_cases h : N.card <;> norm_num [h]
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
  have hpick : ∀ a ∈ N, r ≤ (L a).card → ∃ e, e ∈ L a ∧ e ∉ Q := by
    intro a ha hsat
    apply exists_unprotected_owner G P hTstar he₀ he₀Q ha
      (D := L a) (T := T) (Q := Q)
    · intro e he
      exact (mem_sdiff.mp (mem_filter.mp he).1).1
    · intro e he
      exact (mem_filter.mp he).2
    · exact hprotect
    · exact hsat
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
  have hprotected_not_W : ∀ e ∈ Q, e ∉ W := by
    intro e heQ
    have hne : e₀ ≠ e := fun h => he₀Q (h ▸ heQ)
    have hn0 : e ≠ e₀ := hne.symm
    have hn1 : e ∉ W1 := by
      intro heW
      obtain ⟨s, hs, heS⟩ := mem_biUnion.mp heW
      induction s using Sym2.ind with
      | h a b =>
        rw [mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff] at hs
        have heS' := mem_filter.mp heS
        have hae : a ∈ Tstar e := by
          rw [← hprotect e heQ]
          exact heS'.2 a (by simp)
        have hbe : b ∈ Tstar e := by
          rw [← hprotect e heQ]
          exact heS'.2 b (by simp)
        exact hTstar.pairDisj e₀ he₀ e (hQsub heQ) hne a hs.1.1 b hs.1.2 hs.2 hae hbe
    have hn2 : e ∉ W2 := by
      intro heW
      obtain ⟨⟨x,a⟩,hxa,heS⟩ := mem_biUnion.mp heW
      rw [mem_product, Sym2.mem_toFinset] at hxa
      have heS' := mem_filter.mp heS
      have hae : a ∈ Tstar e := by rw [← hprotect e heQ]; exact heS'.2.2
      exact hTstar.incDisj e₀ he₀ e (hQsub heQ) hne x hxa.1 heS'.2.1 a hxa.2 hae
    have hn3 : e ∉ W3 := by
      intro heW
      obtain ⟨a,ha,hga⟩ := mem_image.mp heW
      have ha' := mem_filter.mp ha
      exact (hg a ha'.1 ha'.2).2 (hga.symm ▸ heQ)
    simp only [hW,hW012,mem_union,mem_insert]
    tauto
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
      rw [card_erase_of_mem hga.1] at this
      omega
    · exact lt_of_le_of_lt (card_le_card hsubL) (by omega)
  have he₀D : e₀ ∉ E \ W := fun h => (hnotW e₀ h).1 rfl
  have hinv₀ : LiftInv G P (σ) r D₀ T₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e he
      rcases mem_insert.mp he with rfl | he
      · rw [hT₀e]; exact hN.sub
      · rw [hT₀o e (hnotW e he).1]; exact hT.sub e (hE_of e he)
    · intro e he
      rcases mem_insert.mp he with rfl | he
      · rw [hT₀e]; exact hNcard
      · rw [hT₀o e (hnotW e he).1]
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
  refine ⟨T', hT', by rw [hagree e₀ (mem_insert_self _ _), hT₀e], ?_, ?_⟩
  · intro e heQ
    have heD : e ∈ E \ W := mem_sdiff.mpr ⟨hQsub heQ,hprotected_not_W e heQ⟩
    rw [hagree e (mem_insert_of_mem heD),hT₀o e (hnotW e heD).1,hprotect e heQ]
  · refine le_trans (card_le_card ?_) hWcard
    intro e he
    rw [mem_filter] at he
    by_contra heW
    have heD : e ∈ E \ W := mem_sdiff.mpr ⟨he.1, heW⟩
    apply he.2
    rw [hagree e (mem_insert_of_mem heD), hT₀o e (hnotW e heD).1]

end PaperVIRecourse
