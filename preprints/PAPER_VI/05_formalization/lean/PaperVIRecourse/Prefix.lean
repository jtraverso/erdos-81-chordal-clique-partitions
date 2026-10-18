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
/- Universal prefix-preserving greedy terminal completion. Original one-step counting
argument adapted from PaperVI.JoinVariant.exists_greedy_coloring; the retained-domain
induction is new and does not assume an extension exists. -/
module
public import PaperVI.JoinVariant
@[expose] public section
namespace PaperVIRecourse
open Finset PaperVI
variable {V : Type*} [DecidableEq V]

/-- A physical edge-coloring prefix on a specified domain of unordered core pairs. -/
def PartialColoring (P R : Finset V) (J U : V → V → Prop)
    (D : Finset (Sym2 V)) (g : Sym2 V → V) : Prop :=
  ∀ a ∈ P, ∀ b ∈ P, J a b → s(a,b) ∈ D →
    g s(a,b) ∈ R ∧ ¬ U a (g s(a,b)) ∧ ¬ U b (g s(a,b)) ∧
    ∀ b' ∈ P, b' ≠ b → J a b' → s(a,b') ∈ D → g s(a,b) ≠ g s(a,b')

def requestEdges (P : Finset V) (J : V → V → Prop) [DecidableRel J] : Finset (Sym2 V) :=
  ((P ×ˢ P).filter (fun ab => J ab.1 ab.2)).image (fun ab => s(ab.1, ab.2))

theorem greedy_step (P R : Finset V) (J : V → V → Prop) [DecidableRel J]
    (hJsymm : ∀ a b, J a b → J b a) (U : V → V → Prop) [DecidableRel U] (c : ℕ)
    (hbound : ∀ a ∈ P, (R.filter (U a)).card + (P.filter (J a)).card ≤ c)
    (hR : 2*c ≤ R.card+1) {E : Finset (Sym2 V)} {g : Sym2 V → V}
    (hg : PartialColoring P R J U E g) {e0 : Sym2 V}
    (he0 : e0 ∈ requestEdges P J) (he0E : e0 ∉ E) :
    ∃ g', PartialColoring P R J U (insert e0 E) g' ∧ ∀ e ∈ E, g' e = g e := by
  classical
  change e0 ∈ ((P ×ˢ P).filter (fun ab => J ab.1 ab.2)).image (fun ab => s(ab.1,ab.2)) at he0
  obtain ⟨⟨a0, b0⟩, hmem0, rfl⟩ := mem_image.mp he0
  simp only [mem_filter, mem_product] at hmem0
  obtain ⟨⟨ha0, hb0⟩, hab0J⟩ := hmem0
  dsimp only at ha0 hb0 hab0J he0E ⊢
  set F := R.filter (U a0) ∪ R.filter (U b0) ∪
    ((P.filter (J a0)).erase b0).image (fun b' => g s(a0, b')) ∪
    ((P.filter (J b0)).erase a0).image (fun a' => g s(b0, a')) with hF
  have hFcard : F.card < R.card := by
    have h1 := card_union_le (R.filter (U a0) ∪ R.filter (U b0) ∪
      ((P.filter (J a0)).erase b0).image (fun b' => g s(a0, b')))
      (((P.filter (J b0)).erase a0).image (fun a' => g s(b0, a')))
    have h2 := card_union_le (R.filter (U a0) ∪ R.filter (U b0))
      (((P.filter (J a0)).erase b0).image (fun b' => g s(a0, b')))
    have h3 := card_union_le (R.filter (U a0)) (R.filter (U b0))
    have h4 := card_image_le (s := (P.filter (J a0)).erase b0) (f := fun b' => g s(a0, b'))
    have h5 := card_image_le (s := (P.filter (J b0)).erase a0) (f := fun a' => g s(b0, a'))
    have h6 := card_erase_of_mem (s := P.filter (J a0)) (a := b0) (mem_filter.mpr ⟨hb0, hab0J⟩)
    have h7 := card_erase_of_mem (s := P.filter (J b0)) (a := a0)
      (mem_filter.mpr ⟨ha0, hJsymm _ _ hab0J⟩)
    have h8 := hbound a0 ha0
    have h9 := hbound b0 hb0
    have h10 : 1 ≤ (P.filter (J a0)).card := card_pos.mpr ⟨b0, mem_filter.mpr ⟨hb0, hab0J⟩⟩
    have h11 : 1 ≤ (P.filter (J b0)).card :=
      card_pos.mpr ⟨a0, mem_filter.mpr ⟨ha0, hJsymm _ _ hab0J⟩⟩
    rw [hF]
    omega
  obtain ⟨x, hxR, hxF⟩ := exists_mem_notMem_of_card_lt_card hFcard
  have hxU : ∀ v, (v = a0 ∨ v = b0) → ¬ U v x := by
    rintro v (rfl | rfl) hU
    · exact hxF (by rw [hF]; simp [hxR, hU])
    · exact hxF (by rw [hF]; simp [hxR, hU])
  have hxa0 : ∀ b' ∈ P, J a0 b' → b' ≠ b0 → x ≠ g s(a0, b') := by
    intro b' hb' hJ hne hx
    exact hxF (by rw [hF]; simp only [mem_union, mem_image, mem_erase, mem_filter]
                  exact Or.inl (Or.inr ⟨b', ⟨hne, hb', hJ⟩, hx.symm⟩))
  have hxb0 : ∀ a' ∈ P, J b0 a' → a' ≠ a0 → x ≠ g s(b0, a') := by
    intro a' ha' hJ hne hx
    exact hxF (by rw [hF]; simp only [mem_union, mem_image, mem_erase, mem_filter]
                  exact Or.inr ⟨a', ⟨hne, ha', hJ⟩, hx.symm⟩)
  refine ⟨fun e => if e = s(a0, b0) then x else g e, ?_, ?_⟩
  · intro a ha b hb hab hmemab
    by_cases habe : s(a, b) = s(a0, b0)
    · simp only [habe, ite_true]
      have hcases := Sym2.eq_iff.mp habe
      refine ⟨hxR, hxU a (by tauto), hxU b (by tauto), ?_⟩
      intro b' hb' hbb' hab' _
      have hne : s(a, b') ≠ s(a0, b0) := by
        rw [← habe]; intro h; exact hbb' (Sym2.congr_right.mp h)
      simp only [hne, ite_false]
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hxa0 b' hb' hab' hbb'
      · exact hxb0 b' hb' hab' hbb'
    · simp only [habe, ite_false]
      have hE : s(a, b) ∈ E := (mem_insert.mp hmemab).resolve_left habe
      obtain ⟨h1, h2, h3, h4⟩ := hg a ha b hb hab hE
      refine ⟨h1, h2, h3, ?_⟩
      intro b' hb' hbb' hab' hmem'
      by_cases hab'e : s(a, b') = s(a0, b0)
      · simp only [hab'e, ite_true]
        rcases Sym2.eq_iff.mp hab'e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact (hxa0 b hb hab hbb'.symm).symm
        · exact (hxb0 b hb hab hbb'.symm).symm
      · simp only [hab'e, ite_false]
        exact h4 b' hb' hbb' hab' ((mem_insert.mp hmem').resolve_left hab'e)
  · intro e he
    have hne : e ≠ s(a0, b0) := fun h => he0E (h ▸ he)
    simp only [hne, ite_false]

/-- Every legal prefix extends; the construction retains each prescribed color. -/
theorem exists_greedy_coloring_extending (P R : Finset V)
    (J : V → V → Prop) [DecidableRel J]
    (hJsymm : ∀ a b, J a b → J b a) (U : V → V → Prop) [DecidableRel U] (c : ℕ)
    (hbound : ∀ a ∈ P, (R.filter (U a)).card + (P.filter (J a)).card ≤ c)
    (hR : 2*c ≤ R.card+1) {D₀ : Finset (Sym2 V)} {g₀ : Sym2 V → V}
    (hD₀ : D₀ ⊆ requestEdges P J) (h₀ : PartialColoring P R J U D₀ g₀) :
    ∃ g, PartialColoring P R J U (requestEdges P J) g ∧ ∀ e ∈ D₀, g e = g₀ e := by
  classical
  have key : ∃ g, PartialColoring P R J U (D₀ ∪ (requestEdges P J \ D₀)) g ∧
      ∀ e ∈ D₀, g e = g₀ e := by
    refine Finset.induction_on' (motive := fun E =>
      ∃ g, PartialColoring P R J U (D₀ ∪ E) g ∧ ∀ e ∈ D₀, g e = g₀ e)
      (requestEdges P J \ D₀) ⟨g₀, by simpa using h₀, fun _ _ => rfl⟩ ?_
    intro e0 E he0 _ he0E ih
    obtain ⟨g, hg, hagree⟩ := ih
    have hnot : e0 ∉ D₀ ∪ E := by
      rw [mem_union, not_or]
      exact ⟨(mem_sdiff.mp he0).2, he0E⟩
    obtain ⟨g', hg', hret⟩ := greedy_step P R J hJsymm U c hbound hR hg
      (mem_sdiff.mp he0).1 hnot
    refine ⟨g', ?_, fun e he => (hret e (mem_union_left _ he)).trans (hagree e he)⟩
    have : D₀ ∪ insert e0 E = insert e0 (D₀ ∪ E) := by
      ext; simp only [mem_union, mem_insert]; tauto
    rw [this]
    exact hg'
  obtain ⟨g, hg, hagree⟩ := key
  rw [union_sdiff_of_subset hD₀] at hg
  exact ⟨g, hg, hagree⟩

end PaperVIRecourse
