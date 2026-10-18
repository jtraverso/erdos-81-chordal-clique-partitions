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
/- Exact block counts for arbitrary optimal partitions extending all-K5 lifts. -/
module
public import PaperVIRecourse.OptimalAdapter
public import PaperVI.Engine
@[expose] public section
namespace PaperVIRecourse
open Finset PaperVI
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

theorem allK5_lift_type
    {r : ℕ} {T : Sym2 V → Finset V}
    (hT : LiftInv G P (fun _ => 3) r (extEdges G P) T)
    {B : Finset V} (hB : B ∈ liftBlocks G P T) :
    coreSize P B = 3 ∧ extSize P B = 2 := by
  classical
  obtain ⟨e, he, rfl⟩ := mem_liftBlocks.mp hB
  constructor
  · unfold coreSize
    have heq : (T e ∪ e.toFinset) ∩ P = T e := by
      ext v
      rw [mem_inter]
      constructor
      · rintro ⟨h1, h2⟩
        exact (mem_lift_core he h2).mp h1
      · intro h
        exact ⟨mem_union_left _ h, hT.sub e he h⟩
    rw [heq, hT.card e he]
  · unfold extSize
    have heq : (T e ∪ e.toFinset) \ P = e.toFinset := by
      ext v
      rw [mem_sdiff]
      constructor
      · rintro ⟨h1, h2⟩
        exact Sym2.mem_toFinset.mpr ((mem_lift_ext hT he h2).mp h1)
      · intro h
        exact ⟨mem_union_right _ h, not_mem_of_mem_extEdges he (Sym2.mem_toFinset.mp h)⟩
    rw [heq]
    exact Sym2.card_toFinset_of_not_isDiag e
      (G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (extEdges_subset he)))

/-- These counts hold for any actual optimum containing the prescribed lifts,
without assuming that the optimum was produced by the assembly algorithm. -/
theorem optimal_allK5_counts
    (hjoin : ∀ a ∈ P, ∀ v, a ≠ v → G.Adj a v)
    (hq : 2 * P.card ≤ Pᶜ.card + 1)
    {r : ℕ} {T : Sym2 V → Finset V}
    (hT : LiftInv G P (fun _ => 3) r (extEdges G P) T)
    {Bs : Finset (Finset V)} (hBs : IsCliquePartition G Bs) (hopt : Bs.card = cp G)
    (hlift : ∀ e ∈ extEdges G P, T e ∪ e.toFinset ∈ Bs) :
    typeCount P Bs 2 1 + 3 * mCount G P = uCount G P ∧
      typeCount P Bs 1 1 + 2 * uCount G P = sCount G P ∧
      typeCount P Bs 3 2 = mCount G P := by
  classical
  have htypes : ∀ B ∈ Bs, (coreSize P B = 3 ∧ extSize P B = 2) ∨
      (coreSize P B = 2 ∧ extSize P B = 1) ∨
      (coreSize P B = 1 ∧ extSize P B = 1) := by
    intro B hB
    rcases optimal_blocks_of_allK5_lift G P hjoin hq hT hBs hopt hlift B hB with h | h | h
    · exact Or.inl (allK5_lift_type G P hT h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hzero : ∀ j, j = 1 ∨ j = 2 → typeCount P Bs j 2 = 0 := by
    intro j hj
    unfold typeCount
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro B hB
    obtain ⟨hB, hc, he⟩ := mem_filter.mp hB
    rcases htypes B hB with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
  have hwide : ∀ B ∈ Bs, (coreSize P B = 1 ∧ extSize P B = 1) ∨
      (coreSize P B = 2 ∧ extSize P B = 1) ∨ (coreSize P B = 2 ∧ extSize P B = 2) ∨
      (coreSize P B = 3 ∧ extSize P B = 2) ∨ (coreSize P B = 1 ∧ extSize P B = 2) := by
    intro B hB
    rcases htypes B hB with h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
  obtain ⟨hu, hm, hs, _⟩ := type_counts G P hBs hwide
  have h12 := hzero 1 (Or.inl rfl)
  have h22 := hzero 2 (Or.inr rfl)
  omega

end PaperVIRecourse

#print axioms PaperVIRecourse.optimal_allK5_counts
