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
/- Charge lost crossing K2 blocks to changed lifting and new terminal edges. -/
module
public import PaperVIRecourse.RetainedConstruction
@[expose] public section
namespace PaperVIRecourse
open Finset PaperVI
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

def crossingBlocks (Bs : Finset (Finset V)) : Finset (Finset V) :=
  Bs.filter (fun B => coreSize P B = 1 ∧ extSize P B = 1)

def crossingRepairEdges (T₀ T₁ : Sym2 V → Finset V)
    (N : Finset (Finset V)) : Finset (Sym2 V) :=
  (changedBlocks G P T₀ T₁).biUnion (insideFilter (crossEdges G P)) ∪
    N.biUnion (insideFilter (crossEdges G P))

theorem crossingRepairEdges_card_le
    {r : ℕ} {T₀ T₁ : Sym2 V → Finset V}
    (hT₁ : LiftInv G P (fun _ => 3) r (extEdges G P) T₁)
    {N : Finset (Finset V)}
    (hNclique : ∀ B ∈ N, G.IsClique (B : Set V))
    (hNtype : ∀ B ∈ N, coreSize P B = 2 ∧ extSize P B = 1) :
    (crossingRepairEdges G P T₀ T₁ N).card ≤
      6 * (changedAssignments G P T₀ T₁).card + 2 * N.card := by
  classical
  have hW : ((changedBlocks G P T₀ T₁).biUnion
      (insideFilter (crossEdges G P))).card ≤ 6 * (changedAssignments G P T₀ T₁).card := by
    calc
      _ ≤ ∑ B ∈ changedBlocks G P T₀ T₁, (insideFilter (crossEdges G P) B).card := card_biUnion_le
      _ = ∑ _B ∈ changedBlocks G P T₀ T₁, 6 := by
        apply sum_congr rfl
        intro B hB
        obtain ⟨e, he, rfl⟩ := mem_image.mp hB
        have ht := allK5_lift_type G P hT₁ (mem_liftBlocks.mpr ⟨e,(mem_filter.mp he).1,rfl⟩)
        rw [card_insideFilter_cross G P _ (lifting_block_isClique G P hT₁ (mem_filter.mp he).1), ht.1, ht.2]
      _ = 6 * (changedBlocks G P T₀ T₁).card := by simp [mul_comm]
      _ ≤ _ := Nat.mul_le_mul_left 6 card_image_le
  have hN : (N.biUnion (insideFilter (crossEdges G P))).card ≤ 2 * N.card := by
    calc
      _ ≤ ∑ B ∈ N, (insideFilter (crossEdges G P) B).card := card_biUnion_le
      _ = ∑ _B ∈ N, 2 := by
        apply sum_congr rfl
        intro B hB
        rw [card_insideFilter_cross G P B (hNclique B hB), (hNtype B hB).1, (hNtype B hB).2]
      _ = _ := by simp [mul_comm]
  exact (card_union_le _ _).trans (Nat.add_le_add hW hN)

theorem two_blocks_eq_of_shared_edge
    {B C : Finset V} (hB : B.card = 2) (hC : C.card = 2)
    {e : Sym2 V} (he : e ∈ G.edgeFinset)
    (heB : ∀ v ∈ e.toFinset, v ∈ B) (heC : ∀ v ∈ e.toFinset, v ∈ C) : B = C := by
  have hc : e.toFinset.card = 2 := Sym2.card_toFinset_of_not_isDiag e
    (G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp he))
  have h1 : e.toFinset = B := eq_of_subset_of_card_le heB (by omega)
  have h2 : e.toFinset = C := eq_of_subset_of_card_le heC (by omega)
  exact h1.symm.trans h2

/-- Any lost old crossing edge is covered by a changed new K5 or a new triangle.
The bound counts actual old blocks through unique ownership of physical edges. -/
theorem crossing_loss_le
    (hjoin : ∀ a ∈ P, ∀ v, a ≠ v → G.Adj a v)
    (hq : 2 * P.card ≤ Pᶜ.card + 1)
    {r : ℕ} {T₀ T₁ : Sym2 V → Finset V}
    (hT₁ : LiftInv G P (fun _ => 3) r (extEdges G P) T₁)
    {Bs₀ Bs₁ A : Finset (Finset V)}
    (hBs₀ : IsCliquePartition G Bs₀) (hBs₁ : IsCliquePartition G Bs₁)
    (hopt₁ : Bs₁.card = cp G)
    (hlift₀ : ∀ e ∈ extEdges G P, T₀ e ∪ e.toFinset ∈ Bs₀)
    (hlift₁ : ∀ e ∈ extEdges G P, T₁ e ∪ e.toFinset ∈ Bs₁)
    (hAold : A ⊆ Bs₀) :
    (crossingBlocks P Bs₀ \ Bs₁).card ≤
      6 * (changedAssignments G P T₀ T₁).card +
        2 * (terminalBlocks P Bs₁ \ A).card := by
  classical
  let N := terminalBlocks P Bs₁ \ A
  let U := crossingRepairEdges G P T₀ T₁ N
  have hhit : crossingBlocks P Bs₀ \ Bs₁ ⊆
      Bs₀.filter (fun B => ¬ Disjoint (innerEdges G B) U) := by
    intro B hB
    obtain ⟨hB0,hBnot⟩ := mem_sdiff.mp hB
    obtain ⟨hBold,hBt⟩ := mem_filter.mp hB0
    have hBcard : B.card = 2 := by
      rw [card_eq_coreSize_add_extSize P B,hBt.1,hBt.2]
    have hcross : (insideFilter (crossEdges G P) B).card = 1 := by
      rw [card_insideFilter_cross G P B (hBs₀.isClique B hBold),hBt.1,hBt.2]
    obtain ⟨e,he⟩ := card_pos.mp (by omega : 0 < (insideFilter (crossEdges G P) B).card)
    simp only [insideFilter,mem_filter] at he
    obtain ⟨hecross,heB⟩ := he
    have heG := crossEdges_subset G P hecross
    obtain ⟨C,hC,heC⟩ := exists_block_of_edge G hBs₁ heG
    have hCnot : C ∉ Bs₀ := by
      intro hC0
      have hBC : B = C := block_unique_of_edge G hBs₀ heG hBold hC0
        (fun v hv => heB v (Sym2.mem_toFinset.mpr hv)) heC
      exact hBnot (hBC.symm ▸ hC)
    have heC' : ∀ v ∈ e.toFinset, v ∈ C := fun v hv => heC v (Sym2.mem_toFinset.mp hv)
    have heU : e ∈ U := by
      rcases optimal_blocks_of_allK5_lift G P hjoin hq hT₁ hBs₁ hopt₁ hlift₁ C hC with hL | hT | hE
      · obtain ⟨f,hf,hCf⟩ := mem_liftBlocks.mp hL
        have hchange : T₀ f ≠ T₁ f := by
          intro heq
          apply hCnot
          rw [← hCf, ← heq]
          exact hlift₀ f hf
        apply mem_union_left
        apply mem_biUnion.mpr
        exact ⟨C,mem_image.mpr ⟨f,mem_filter.mpr ⟨hf,hchange⟩,hCf⟩,
          by simpa only [insideFilter,mem_filter] using And.intro hecross heC'⟩
      · apply mem_union_right
        apply mem_biUnion.mpr
        exact ⟨C,mem_sdiff.mpr ⟨mem_filter.mpr ⟨hC,hT⟩,fun hCA => hCnot (hAold hCA)⟩,
          by simpa only [insideFilter,mem_filter] using And.intro hecross heC'⟩
      · have hCcard : C.card = 2 := by
          rw [card_eq_coreSize_add_extSize P C,hE.1,hE.2]
        have hBC := two_blocks_eq_of_shared_edge G hBcard hCcard heG heB heC'
        exact False.elim (hBnot (hBC.symm ▸ hC))
    exact mem_filter.mpr ⟨hBold,Finset.not_disjoint_iff.mpr
      ⟨e,by simpa only [innerEdges,mem_filter] using And.intro heG heB,heU⟩⟩
  have hbound := crossingRepairEdges_card_le G P (T₀ := T₀) hT₁
    (N := N) (fun B hB => hBs₁.isClique B (mem_filter.mp (mem_sdiff.mp hB).1).1)
    (fun B hB => (mem_filter.mp (mem_sdiff.mp hB).1).2)
  exact (card_le_card hhit).trans ((card_hit_partition_le G hBs₀ U).trans hbound)

end PaperVIRecourse

#print axioms PaperVIRecourse.crossing_loss_le
