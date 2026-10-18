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
/- Any physical all-K5 lifting in a complete join admits completion preserving
an arbitrary legal terminal prefix. No load bound or balanced core size is needed. -/
module
public import PaperVIRecourse.Prefix
@[expose] public section
namespace PaperVIRecourse
open Finset PaperVI
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

/-- An arbitrary legal terminal prefix extends to an actual optimal clique partition.
The old physical triangles and every prescribed exterior K5 are retained. -/
theorem exists_optimal_partition_extending_prefix
    (hjoin : ∀ a ∈ P, ∀ v, a ≠ v → G.Adj a v)
    (hq : 2 * P.card ≤ Pᶜ.card + 1)
    {r : ℕ} {T : Sym2 V → Finset V}
    (hT : LiftInv G P (fun _ => 3) r (extEdges G P) T)
    {D₀ : Finset (Sym2 V)} {g₀ : Sym2 V → V}
    (hD₀ : D₀ ⊆ requestEdges P (residPair G P T))
    (h₀ : PartialColoring P Pᶜ (residPair G P T) (usedPair G P T) D₀ g₀) :
    ∃ (g : Sym2 V → V) (Bs : Finset (Finset V)),
      IsCliquePartition G Bs ∧ Bs.card = cp G ∧
      Bs = allBlocks G P T (fun a b => g s(a,b)) ∧
      (∀ e ∈ D₀, g e = g₀ e) ∧
      (∀ e ∈ extEdges G P, T e ∪ e.toFinset ∈ Bs) ∧
      (∀ a ∈ P, ∀ b ∈ P, a ≠ b → residPair G P T a b → s(a,b) ∈ D₀ →
        ({a,b,g₀ s(a,b)} : Finset V) ∈ Bs) ∧
      PartialColoring P Pᶜ (residPair G P T) (usedPair G P T)
        (requestEdges P (residPair G P T)) g ∧
      (cp G : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P := by
  classical
  obtain ⟨g, hg, hagree⟩ := exists_greedy_coloring_extending P Pᶜ
    (residPair G P T) (fun _ _ h => residPair_symm h) (usedPair G P T)
    (P.card - 1) (fun a ha => used_add_resid_le G P hjoin hT ha)
    (by omega) hD₀ h₀
  have hmem : ∀ a ∈ P, ∀ b ∈ P, residPair G P T a b →
      s(a,b) ∈ requestEdges P (residPair G P T) := by
    intro a ha b hb hab
    exact mem_image.mpr ⟨(a,b), mem_filter.mpr ⟨mem_product.mpr ⟨ha,hb⟩,hab⟩, rfl⟩
  let f : V → V → V := fun a b => g s(a,b)
  have hf1 : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → residPair G P T a b → f a b = f b a :=
    fun a _ b _ _ _ => by simp only [f, Sym2.eq_swap]
  have hf2 : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → residPair G P T a b →
      f a b ∉ P ∧ availPair G P T a (f a b) ∧ availPair G P T b (f a b) := by
    intro a ha b hb _ hres
    obtain ⟨h1,h2,h3,-⟩ := hg a ha b hb hres (hmem a ha b hb hres)
    have hx : f a b ∉ P := by simpa using h1
    exact ⟨hx, ⟨hjoin a ha _ (fun h => hx (h ▸ ha)),h2⟩,
      ⟨hjoin b hb _ (fun h => hx (h ▸ hb)),h3⟩⟩
  have hf3 : ∀ a ∈ P, ∀ b ∈ P, ∀ b' ∈ P, a ≠ b → a ≠ b' → b ≠ b' →
      residPair G P T a b → residPair G P T a b' → f a b ≠ f a b' := by
    intro a ha b hb b' hb' _ _ hbb' hres hres'
    exact (hg a ha b hb hres (hmem a ha b hb hres)).2.2.2 b' hb' hbb'.symm
      hres' (hmem a ha b' hb' hres')
  let Bs := allBlocks G P T f
  have hBs : IsCliquePartition G Bs := allBlocks_isCliquePartition hT hf1 hf2 hf3
  have hzero : ∀ B ∈ Bs, slack (coreSize P B) (extSize P B) = 0 := by
    intro B hB
    rw [slack_eq_zero_iff]
    rcases allBlocks_types hT hf2 hB with h | h | ⟨e,he,-,hc,hb⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr ⟨hc,hb⟩))
  have hid := slack_identity G P hBs
  rw [sum_eq_zero hzero] at hid
  have hlo := cp_ge G P
  have hhi := cp_le hBs
  have hopt : Bs.card = cp G := by omega
  refine ⟨g,Bs,hBs,hopt,rfl,hagree,?_,?_,hg,?_⟩
  · intro e he
    exact mem_allBlocks.mpr (Or.inl (mem_liftBlocks.mpr ⟨e,he,rfl⟩))
  · intro a ha b hb hab hres he
    have hc : f a b = g₀ s(a,b) := hagree _ he
    rw [← hc]
    exact mem_allBlocks.mpr (Or.inr (Or.inl
      (mem_triBlocks.mpr ⟨a,b,ha,hb,hab,hres,rfl⟩)))
  · omega

/-- A complete legal all-K5 lifting suffices to attain the EFO lower bound,
without any balanced core-size or vertex-load hypothesis. -/
theorem cp_eq_lower_of_complete_allK5_lift
    (hjoin : ∀ a ∈ P, ∀ v, a ≠ v → G.Adj a v)
    (hq : 2 * P.card ≤ Pᶜ.card + 1)
    {r : ℕ} {T : Sym2 V → Finset V}
    (hT : LiftInv G P (fun _ => 3) r (extEdges G P) T) :
    (cp G : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P := by
  classical
  let g₀ : Sym2 V → V := fun e => (Quot.out e).1
  have hD₀ : (∅ : Finset (Sym2 V)) ⊆ requestEdges P (residPair G P T) := empty_subset _
  have h₀ : PartialColoring P Pᶜ (residPair G P T) (usedPair G P T) ∅ g₀ := by
    intro a _ b _ _ he
    simp at he
  obtain ⟨_,_,_,_,_,_,_,_,_,hcp⟩ :=
    exists_optimal_partition_extending_prefix G P hjoin hq hT hD₀ h₀
  exact hcp

end PaperVIRecourse
