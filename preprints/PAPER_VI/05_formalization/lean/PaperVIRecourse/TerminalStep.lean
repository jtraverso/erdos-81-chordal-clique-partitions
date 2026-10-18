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
/- Insert a target terminal triangle while protecting all already matched triangles. -/
module
public import PaperVIRecourse.CompatiblePrefix
public import PaperVIRecourse.PhysicalRecourse
@[expose] public section
namespace PaperVIRecourse
open Finset PaperVI
open scoped symmDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

theorem terminal_avoids_lift
    {r : ℕ} {T : Sym2 V → Finset V}
    (hT : LiftInv G P (fun _ => 3) r (extEdges G P) T)
    {Bs : Finset (Finset V)} (hBs : IsCliquePartition G Bs)
    (hlift : ∀ e ∈ extEdges G P, T e ∪ e.toFinset ∈ Bs)
    {B : Finset V} (hB : B ∈ terminalBlocks P Bs) :
    ∀ e ∈ extEdges G P, Disjoint (innerEdges G B) (innerEdges G (T e ∪ e.toFinset)) := by
  intro e he
  have ht := allK5_lift_type G P hT (mem_liftBlocks.mpr ⟨e,he,rfl⟩)
  apply partition_innerEdges_disjoint G hBs (mem_filter.mp hB).1 (hlift e he)
  intro heq
  have hc := (mem_filter.mp hB).2.1
  rw [heq] at hc
  omega

/-- With a fixed legal all-K5 lifting, any target terminal triangle can be
inserted at distance at most eighteen, retaining every already matched triangle. -/
theorem exists_terminal_step
    (hjoin : ∀ a ∈ P, ∀ v, a ≠ v → G.Adj a v)
    (hq : 2 * P.card ≤ Pᶜ.card + 1)
    {r : ℕ} {T : Sym2 V → Finset V}
    (hT : LiftInv G P (fun _ => 3) r (extEdges G P) T)
    {Bs₀ BsTarget : Finset (Finset V)}
    (hBs₀ : IsCliquePartition G Bs₀) (hopt₀ : Bs₀.card = cp G)
    (hlift₀ : ∀ e ∈ extEdges G P, T e ∪ e.toFinset ∈ Bs₀)
    (hTarget : IsCliquePartition G BsTarget)
    (hliftTarget : ∀ e ∈ extEdges G P, T e ∪ e.toFinset ∈ BsTarget)
    {Q : Finset V} (hQ : Q ∈ terminalBlocks P BsTarget) :
    ∃ Bs₁, IsCliquePartition G Bs₁ ∧ Bs₁.card = cp G ∧
      (∀ e ∈ extEdges G P, T e ∪ e.toFinset ∈ Bs₁) ∧ Q ∈ Bs₁ ∧
      (∀ B ∈ terminalBlocks P Bs₀, B ∈ terminalBlocks P BsTarget → B ∈ Bs₁) ∧
      (Bs₀ ∆ Bs₁).card ≤ 18 := by
  classical
  let K := (terminalBlocks P Bs₀).filter (fun B => Disjoint (innerEdges G B) (innerEdges G Q))
  let A := insert Q K
  have hKold : K ⊆ terminalBlocks P Bs₀ := filter_subset _ _
  have hAclique : ∀ B ∈ A, G.IsClique (B : Set V) := by
    intro B hB
    rcases mem_insert.mp hB with rfl | hB
    · exact hTarget.isClique _ (mem_filter.mp hQ).1
    · exact hBs₀.isClique B (mem_filter.mp (hKold hB)).1
  have hAtype : ∀ B ∈ A, coreSize P B = 2 ∧ extSize P B = 1 := by
    intro B hB
    rcases mem_insert.mp hB with rfl | hB
    · exact (mem_filter.mp hQ).2
    · exact (mem_filter.mp (hKold hB)).2
  have hAdisj : ∀ B ∈ A, ∀ C ∈ A, B ≠ C → Disjoint (innerEdges G B) (innerEdges G C) := by
    intro B hB C hC hne
    rcases mem_insert.mp hB with rfl | hB <;> rcases mem_insert.mp hC with rfl | hC
    · exact False.elim (hne rfl)
    · exact (mem_filter.mp hC).2.symm
    · exact (mem_filter.mp hB).2
    · exact partition_innerEdges_disjoint G hBs₀ (mem_filter.mp (hKold hB)).1
        (mem_filter.mp (hKold hC)).1 hne
  have hAavoid : ∀ B ∈ A, ∀ e ∈ extEdges G P,
      Disjoint (innerEdges G B) (innerEdges G (T e ∪ e.toFinset)) := by
    intro B hB
    rcases mem_insert.mp hB with rfl | hB
    · exact terminal_avoids_lift G P hT hTarget hliftTarget hQ
    · exact terminal_avoids_lift G P hT hBs₀ hlift₀ (hKold hB)
  obtain ⟨Bs₁,hBs₁,hopt₁,hAkeep,hlift₁⟩ :=
    exists_optimal_partition_of_compatible_triangles G P hjoin hq hT hAclique hAdisj hAtype hAavoid
  have hKkeep : K ⊆ Bs₁ := fun B hB => hAkeep (mem_insert_of_mem hB)
  have hR : (terminalBlocks P Bs₀ \ K).card ≤ 3 := by
    have hsub : terminalBlocks P Bs₀ \ K ⊆
        Bs₀.filter (fun B => ¬ Disjoint (innerEdges G B) (innerEdges G Q)) := by
      intro B hB
      obtain ⟨hB0,hnot⟩ := mem_sdiff.mp hB
      exact mem_filter.mpr ⟨(mem_filter.mp hB0).1,fun hd => hnot (mem_filter.mpr ⟨hB0,hd⟩)⟩
    have hQcard : Q.card = 3 := by
      rw [card_eq_coreSize_add_extSize P Q,(mem_filter.mp hQ).2.1,(mem_filter.mp hQ).2.2]
    have hedge : (innerEdges G Q).card = 3 := by
      rw [card_innerEdges_of_isClique G Q (hTarget.isClique Q (mem_filter.mp hQ).1),hQcard]
      decide
    exact (card_le_card hsub).trans ((card_hit_partition_le G hBs₀ _).trans_eq hedge)
  have hN := new_terminal_count_eq_removed G P hjoin hq hT hT hBs₀ hopt₀ hlift₀
    hBs₁ hopt₁ hlift₁ hKold hKkeep
  have hcross := crossing_loss_le G P hjoin hq hT hBs₀ hBs₁ hopt₁ hlift₀ hlift₁
    (hKold.trans (filter_subset _ _))
  rw [hN] at hcross
  have hchange : (changedAssignments G P T T).card = 0 := by simp [changedAssignments]
  rw [hchange] at hcross
  have hLloss : (liftBlocks G P T \ Bs₁).card = 0 := by
    apply card_eq_zero.mpr
    apply sdiff_eq_empty_iff_subset.mpr
    intro B hB
    obtain ⟨e,he,rfl⟩ := mem_liftBlocks.mp hB
    exact hlift₁ e he
  have hTloss : (terminalBlocks P Bs₀ \ Bs₁).card ≤ (terminalBlocks P Bs₀ \ K).card := by
    apply card_le_card
    intro B hB
    exact mem_sdiff.mpr ⟨(mem_sdiff.mp hB).1,fun hBK => (mem_sdiff.mp hB).2 (hKkeep hBK)⟩
  have hdec := optimal_partition_decomposition G P hjoin hq hT hBs₀ hopt₀ hlift₀
  change Bs₀ = liftBlocks G P T ∪ terminalBlocks P Bs₀ ∪ crossingBlocks P Bs₀ at hdec
  have hsum := loss_union_three_le (liftBlocks G P T) (terminalBlocks P Bs₀)
    (crossingBlocks P Bs₀) Bs₁ Bs₁ Bs₁
  simp only [union_self] at hsum
  rw [← hdec] at hsum
  have hloss : (Bs₀ \ Bs₁).card ≤ 9 := by omega
  have hdist := card_symmDiff_eq_twice_loss Bs₀ Bs₁ (hopt₀.trans hopt₁.symm)
  refine ⟨Bs₁,hBs₁,hopt₁,hlift₁,hAkeep (mem_insert_self _ _),?_,by omega⟩
  intro B hB0 hBT
  by_cases heq : B = Q
  · subst B
    exact hAkeep (mem_insert_self _ _)
  · apply hKkeep
    exact mem_filter.mpr ⟨hB0,partition_innerEdges_disjoint G hTarget
      (mem_filter.mp hBT).1 (mem_filter.mp hQ).1 heq⟩

end PaperVIRecourse

#print axioms PaperVIRecourse.exists_terminal_step
