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
/- Physical extraction facts for arbitrary optimal partitions extending an all-K5
lifting. The partition is not assumed to come from the assembly function. -/
module
public import PaperVIRecourse.JoinPrefix
public import PaperVI.Optimal
@[expose] public section
namespace PaperVIRecourse
open Finset PaperVI
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

/-- Every block of an arbitrary optimum extending a complete all-K5 lifting is
one of those lifting blocks, a terminal triangle, or a crossing K2. -/
theorem optimal_blocks_of_allK5_lift
    (hjoin : ∀ a ∈ P, ∀ v, a ≠ v → G.Adj a v)
    (hq : 2 * P.card ≤ Pᶜ.card + 1)
    {r : ℕ} {T : Sym2 V → Finset V}
    (hT : LiftInv G P (fun _ => 3) r (extEdges G P) T)
    {Bs : Finset (Finset V)} (hBs : IsCliquePartition G Bs) (hopt : Bs.card = cp G)
    (hlift : ∀ e ∈ extEdges G P, T e ∪ e.toFinset ∈ Bs) :
    ∀ B ∈ Bs, B ∈ liftBlocks G P T ∨
      (coreSize P B = 2 ∧ extSize P B = 1) ∨
      (coreSize P B = 1 ∧ extSize P B = 1) := by
  classical
  have hcp := cp_eq_lower_of_complete_allK5_lift G P hjoin hq hT
  have htypes := optimal_types_of_cp_eq G P hcp hBs hopt
  have hlarge : ∀ B ∈ Bs, extSize P B = 2 → B ∈ liftBlocks G P T := by
    intro B hB hsize
    have hc : 1 < (B \ P).card := by change 1 < extSize P B; omega
    obtain ⟨x,hx,y,hy,hxy⟩ := one_lt_card.mp hc
    have hx1 := mem_sdiff.mp hx
    have hy1 := mem_sdiff.mp hy
    have hadj := hBs.isClique B hB hx1.1 hy1.1 hxy
    have he : s(x,y) ∈ extEdges G P := (mem_extEdges G P).mpr ⟨hadj,hx1.2,hy1.2⟩
    obtain ⟨D,_,hunique⟩ := hBs.existsUnique x y hadj
    have hBD : B = D := hunique B ⟨hB,hx1.1,hy1.1⟩
    have hLD : T s(x,y) ∪ s(x,y).toFinset = D :=
      hunique _ ⟨hlift _ he,mem_union_right _ (by simp),mem_union_right _ (by simp)⟩
    exact mem_liftBlocks.mpr ⟨s(x,y),he,hLD.trans hBD.symm⟩
  intro B hB
  rcases (htypes B hB).1 with h | h | h | h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)
  · exact Or.inl (hlarge B hB h.2)
  · exact Or.inl (hlarge B hB h.2)

/-- Exact physical decomposition of any such optimum, with no assembly premise. -/
theorem optimal_partition_decomposition
    (hjoin : ∀ a ∈ P, ∀ v, a ≠ v → G.Adj a v)
    (hq : 2 * P.card ≤ Pᶜ.card + 1)
    {r : ℕ} {T : Sym2 V → Finset V}
    (hT : LiftInv G P (fun _ => 3) r (extEdges G P) T)
    {Bs : Finset (Finset V)} (hBs : IsCliquePartition G Bs) (hopt : Bs.card = cp G)
    (hlift : ∀ e ∈ extEdges G P, T e ∪ e.toFinset ∈ Bs) :
    Bs = liftBlocks G P T ∪
      Bs.filter (fun B => coreSize P B = 2 ∧ extSize P B = 1) ∪
      Bs.filter (fun B => coreSize P B = 1 ∧ extSize P B = 1) := by
  classical
  have ht := optimal_blocks_of_allK5_lift G P hjoin hq hT hBs hopt hlift
  ext B
  constructor
  · intro hB
    rcases ht B hB with h | h | h
    · exact mem_union_left _ (mem_union_left _ h)
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hB,h⟩))
    · exact mem_union_right _ (mem_filter.mpr ⟨hB,h⟩)
  · intro hB
    rcases mem_union.mp hB with hB | hB
    · rcases mem_union.mp hB with hB | hB
      · obtain ⟨e,he,rfl⟩ := mem_liftBlocks.mp hB
        exact hlift e he
      · exact (mem_filter.mp hB).1
    · exact (mem_filter.mp hB).1

end PaperVIRecourse
