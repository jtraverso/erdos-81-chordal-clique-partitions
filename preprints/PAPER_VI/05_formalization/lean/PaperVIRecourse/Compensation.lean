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
/- Exact local compensation for physical all-K5 liftings in complete joins. -/
module
public import PaperVI.JoinVariant
@[expose] public section
namespace PaperVIRecourse
open Finset PaperVI
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

/-- Every K5 participation consumes two crossing edges and two incident core edges.
This proves the literal equality, stronger than the old sufficient budget inequality. -/
theorem used_add_resid_eq
    (hjoin : ∀ a ∈ P, ∀ v, a ≠ v → G.Adj a v)
    {T : Sym2 V → Finset V} {r : ℕ}
    (hT : LiftInv G P (fun _ => 3) r (extEdges G P) T) {a : V} (ha : a ∈ P) :
    (Pᶜ.filter (usedPair G P T a)).card + (P.filter (residPair G P T a)).card =
      P.card - 1 := by
  classical
  let E := (extEdges G P).filter (fun e => a ∈ T e)
  have hUset : Pᶜ.filter (usedPair G P T a) = E.biUnion Sym2.toFinset := by
    ext x
    simp only [mem_filter, mem_compl, usedPair, mem_biUnion, E, Sym2.mem_toFinset]
    constructor
    · rintro ⟨-,e,he,hae,hxe⟩
      exact ⟨e,⟨he,hae⟩,hxe⟩
    · rintro ⟨e,⟨he,hae⟩,hxe⟩
      exact ⟨not_mem_of_mem_extEdges he hxe,e,he,hae,hxe⟩
  have hUdisj : (E : Set (Sym2 V)).PairwiseDisjoint Sym2.toFinset := by
    intro e he e' he' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx hx'
    have he1 := mem_filter.mp (mem_coe.mp he)
    have he2 := mem_filter.mp (mem_coe.mp he')
    exact hT.incDisj e he1.1 e' he2.1 hne x (Sym2.mem_toFinset.mp hx)
      (Sym2.mem_toFinset.mp hx') a he1.2 he2.2
  have hU : (Pᶜ.filter (usedPair G P T a)).card = 2 * E.card := by
    rw [hUset, card_biUnion hUdisj]
    have hc : ∀ e ∈ E, e.toFinset.card = 2 := by
      intro e he
      have hed := (mem_filter.mp he).1
      have hgraph : e ∈ G.edgeFinset := extEdges_subset hed
      exact Sym2.card_toFinset_of_not_isDiag _ (G.not_isDiag_of_mem_edgeSet
        (SimpleGraph.mem_edgeFinset.mp hgraph))
    rw [sum_congr rfl hc, sum_const, smul_eq_mul, mul_comm]
  have hCset : P.filter (fun b => b ≠ a ∧ coveredPair G P T a b) =
      E.biUnion (fun e => (T e).erase a) := by
    ext b
    constructor
    · intro hb
      obtain ⟨_,hba,e,he,hae,hbe⟩ := mem_filter.mp hb
      exact mem_biUnion.mpr ⟨e,mem_filter.mpr ⟨he,hae⟩,mem_erase.mpr ⟨hba,hbe⟩⟩
    · intro hb
      obtain ⟨e,he,hb⟩ := mem_biUnion.mp hb
      have he1 := mem_filter.mp he
      have hb1 := mem_erase.mp hb
      exact mem_filter.mpr ⟨hT.sub e he1.1 hb1.2,hb1.1,e,he1.1,he1.2,hb1.2⟩
  have hCdisj : (E : Set (Sym2 V)).PairwiseDisjoint (fun e => (T e).erase a) := by
    intro e he e' he' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro b hb hb'
    rw [mem_erase] at hb hb'
    have he1 := mem_filter.mp (mem_coe.mp he)
    have he2 := mem_filter.mp (mem_coe.mp he')
    exact hT.pairDisj e he1.1 e' he2.1 hne a he1.2 b hb.2 hb.1.symm he2.2 hb'.2
  have hC : (P.filter (fun b => b ≠ a ∧ coveredPair G P T a b)).card = 2 * E.card := by
    rw [hCset, card_biUnion hCdisj]
    have hc : ∀ e ∈ E, ((T e).erase a).card = 2 := by
      intro e he
      have he1 := mem_filter.mp he
      rw [card_erase_of_mem he1.2,hT.card e he1.1]
    rw [sum_congr rfl hc, sum_const, smul_eq_mul, mul_comm]
  have hpart : (P.filter (residPair G P T a)).card +
      (P.filter (fun b => b ≠ a ∧ coveredPair G P T a b)).card = P.card - 1 := by
    rw [← card_erase_of_mem ha,
      ← card_filter_add_card_filter_not (s := P.erase a) (residPair G P T a)]
    congr 2
    · ext b
      simp only [mem_filter, mem_erase]
      constructor
      · rintro ⟨hb,hres⟩; exact ⟨⟨hres.1.ne.symm,hb⟩,hres⟩
      · rintro ⟨⟨-,hb⟩,hres⟩; exact ⟨hb,hres⟩
    · ext b
      simp only [mem_filter, mem_erase, residPair, not_and, not_not]
      constructor
      · rintro ⟨hb,hba,hcov⟩; exact ⟨⟨hba,hb⟩,fun _ => hcov⟩
      · rintro ⟨⟨hba,hb⟩,hcov⟩
        exact ⟨hb,hba,hcov (hjoin a ha b hba.symm)⟩
  omega

end PaperVIRecourse
