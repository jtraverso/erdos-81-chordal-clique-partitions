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
/- Physical accounting and full recourse for arbitrary optimal old partitions. -/
module
public import PaperVIRecourse.RetainedConstruction
public import PaperVIRecourse.BlockDistance
public import PaperVIRecourse.CrossCharges
@[expose] public section
namespace PaperVIRecourse
open Finset PaperVI
open scoped symmDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

theorem terminal_card_eq
    (hjoin : ∀ a ∈ P, ∀ v, a ≠ v → G.Adj a v)
    (hq : 2 * P.card ≤ Pᶜ.card + 1)
    {r₀ r₁ : ℕ} {T₀ T₁ : Sym2 V → Finset V}
    (hT₀ : LiftInv G P (fun _ => 3) r₀ (extEdges G P) T₀)
    (hT₁ : LiftInv G P (fun _ => 3) r₁ (extEdges G P) T₁)
    {Bs₀ Bs₁ : Finset (Finset V)}
    (hBs₀ : IsCliquePartition G Bs₀) (hopt₀ : Bs₀.card = cp G)
    (hlift₀ : ∀ e ∈ extEdges G P, T₀ e ∪ e.toFinset ∈ Bs₀)
    (hBs₁ : IsCliquePartition G Bs₁) (hopt₁ : Bs₁.card = cp G)
    (hlift₁ : ∀ e ∈ extEdges G P, T₁ e ∪ e.toFinset ∈ Bs₁) :
    (terminalBlocks P Bs₀).card = (terminalBlocks P Bs₁).card := by
  have h₀ := (optimal_allK5_counts G P hjoin hq hT₀ hBs₀ hopt₀ hlift₀).1
  have h₁ := (optimal_allK5_counts G P hjoin hq hT₁ hBs₁ hopt₁ hlift₁).1
  change (terminalBlocks P Bs₀).card + 3 * mCount G P = uCount G P at h₀
  change (terminalBlocks P Bs₁).card + 3 * mCount G P = uCount G P at h₁
  omega

/-- The number of new terminal triangles is exactly the number of removed old
ones, once the common retained physical prefix is fixed. -/
theorem new_terminal_count_eq_removed
    (hjoin : ∀ a ∈ P, ∀ v, a ≠ v → G.Adj a v)
    (hq : 2 * P.card ≤ Pᶜ.card + 1)
    {r₀ r₁ : ℕ} {T₀ T₁ : Sym2 V → Finset V}
    (hT₀ : LiftInv G P (fun _ => 3) r₀ (extEdges G P) T₀)
    (hT₁ : LiftInv G P (fun _ => 3) r₁ (extEdges G P) T₁)
    {Bs₀ Bs₁ A : Finset (Finset V)}
    (hBs₀ : IsCliquePartition G Bs₀) (hopt₀ : Bs₀.card = cp G)
    (hlift₀ : ∀ e ∈ extEdges G P, T₀ e ∪ e.toFinset ∈ Bs₀)
    (hBs₁ : IsCliquePartition G Bs₁) (hopt₁ : Bs₁.card = cp G)
    (hlift₁ : ∀ e ∈ extEdges G P, T₁ e ∪ e.toFinset ∈ Bs₁)
    (hA₀ : A ⊆ terminalBlocks P Bs₀) (hA₁ : A ⊆ Bs₁) :
    (terminalBlocks P Bs₁ \ A).card = (terminalBlocks P Bs₀ \ A).card := by
  classical
  have hA₁T : A ⊆ terminalBlocks P Bs₁ := by
    intro B hB
    exact mem_filter.mpr ⟨hA₁ hB,(mem_filter.mp (hA₀ hB)).2⟩
  rw [card_sdiff_of_subset hA₁T,card_sdiff_of_subset hA₀,
    terminal_card_eq G P hjoin hq hT₀ hT₁ hBs₀ hopt₀ hlift₀ hBs₁ hopt₁ hlift₁]

/-- Old lifting blocks not retained in the new lifting are charged to changed
exterior assignments. -/
theorem lift_block_loss_le (T₀ T₁ : Sym2 V → Finset V) :
    (liftBlocks G P T₀ \ liftBlocks G P T₁).card ≤
      (changedAssignments G P T₀ T₁).card := by
  classical
  have hs : liftBlocks G P T₀ \ liftBlocks G P T₁ ⊆
      (changedAssignments G P T₀ T₁).image (fun e => T₀ e ∪ e.toFinset) := by
    intro B hB
    obtain ⟨hB,hnB⟩ := mem_sdiff.mp hB
    obtain ⟨e,he,rfl⟩ := mem_liftBlocks.mp hB
    have hne : T₀ e ≠ T₁ e := by
      intro heq
      exact hnB (mem_liftBlocks.mpr ⟨e,he,by rw [heq]⟩)
    exact mem_image.mpr ⟨e,mem_filter.mpr ⟨he,hne⟩,rfl⟩
  exact (card_le_card hs).trans card_image_le

theorem terminal_loss_le_removed {Bs₀ Bs₁ A : Finset (Finset V)}
    (hA : A ⊆ terminalBlocks P Bs₁) :
    (terminalBlocks P Bs₀ \ terminalBlocks P Bs₁).card ≤
      (terminalBlocks P Bs₀ \ A).card := by
  apply card_le_card
  intro B hB
  exact mem_sdiff.mpr ⟨(mem_sdiff.mp hB).1,
    fun hBA => (mem_sdiff.mp hB).2 (hA hBA)⟩

/-- Full physical recourse: any old optimum extending a complete all-K5 lifting
has an optimum extending the new legal lifting, losing at most 34k old blocks
and at block symmetric difference at most 68k. The construction retains the
unaffected physical terminal prefix; no representation of the old optimum is assumed. -/
theorem exists_full_allK5_recourse
    (hjoin : ∀ a ∈ P, ∀ v, a ≠ v → G.Adj a v)
    (hq : 2 * P.card ≤ Pᶜ.card + 1)
    {r₀ r₁ : ℕ} {T₀ T₁ : Sym2 V → Finset V}
    (hT₀ : LiftInv G P (fun _ => 3) r₀ (extEdges G P) T₀)
    (hT₁ : LiftInv G P (fun _ => 3) r₁ (extEdges G P) T₁)
    {Bs₀ : Finset (Finset V)} (hBs₀ : IsCliquePartition G Bs₀)
    (hopt₀ : Bs₀.card = cp G)
    (hlift₀ : ∀ e ∈ extEdges G P, T₀ e ∪ e.toFinset ∈ Bs₀) :
    ∃ Bs₁, IsCliquePartition G Bs₁ ∧ Bs₁.card = cp G ∧
      (∀ e ∈ extEdges G P, T₁ e ∪ e.toFinset ∈ Bs₁) ∧
      (Bs₀ \ Bs₁).card ≤ 34 * (changedAssignments G P T₀ T₁).card ∧
      (Bs₀ ∆ Bs₁).card ≤ 68 * (changedAssignments G P T₀ T₁).card ∧
      retainedTriangles G P T₀ T₁ Bs₀ ⊆ Bs₁ := by
  classical
  obtain ⟨Bs₁,hBs₁,hopt₁,hkeep,hlift₁⟩ :=
    exists_optimal_partition_retaining_changed_safe G P hjoin hq hT₁ hBs₀ hlift₀
  let A := retainedTriangles G P T₀ T₁ Bs₀
  have hA₀ : A ⊆ terminalBlocks P Bs₀ := filter_subset _ _
  have hAold : A ⊆ Bs₀ := hA₀.trans (filter_subset _ _)
  have hR := removed_terminal_count_le G P (T₀ := T₀) hT₁ hBs₀
  have hN := new_terminal_count_eq_removed G P hjoin hq hT₀ hT₁
    hBs₀ hopt₀ hlift₀ hBs₁ hopt₁ hlift₁ hA₀ hkeep
  have hQloss := crossing_loss_le G P hjoin hq hT₁ hBs₀ hBs₁ hopt₁ hlift₀ hlift₁ hAold
  rw [hN] at hQloss
  have hLsub : liftBlocks G P T₁ ⊆ Bs₁ := by
    intro B hB
    obtain ⟨e,he,rfl⟩ := mem_liftBlocks.mp hB
    exact hlift₁ e he
  have hLloss : (liftBlocks G P T₀ \ Bs₁).card ≤
      (changedAssignments G P T₀ T₁).card := by
    apply le_trans (card_le_card (t := liftBlocks G P T₀ \ liftBlocks G P T₁) ?_)
      (lift_block_loss_le G P T₀ T₁)
    intro B hB
    exact mem_sdiff.mpr ⟨(mem_sdiff.mp hB).1,fun hBL => (mem_sdiff.mp hB).2 (hLsub hBL)⟩
  have hTloss : (terminalBlocks P Bs₀ \ Bs₁).card ≤
      (terminalBlocks P Bs₀ \ A).card := by
    apply card_le_card
    intro B hB
    exact mem_sdiff.mpr ⟨(mem_sdiff.mp hB).1,fun hBA => (mem_sdiff.mp hB).2 (hkeep hBA)⟩
  have hdec := optimal_partition_decomposition G P hjoin hq hT₀ hBs₀ hopt₀ hlift₀
  change Bs₀ = liftBlocks G P T₀ ∪ terminalBlocks P Bs₀ ∪ crossingBlocks P Bs₀ at hdec
  have hsum := loss_union_three_le (liftBlocks G P T₀) (terminalBlocks P Bs₀)
    (crossingBlocks P Bs₀) Bs₁ Bs₁ Bs₁
  simp only [union_self] at hsum
  rw [← hdec] at hsum
  have hloss : (Bs₀ \ Bs₁).card ≤ (changedAssignments G P T₀ T₁).card +
      (terminalBlocks P Bs₀ \ A).card +
      (6 * (changedAssignments G P T₀ T₁).card + 2 * (terminalBlocks P Bs₀ \ A).card) := by
    omega
  have hcard : Bs₀.card = Bs₁.card := hopt₀.trans hopt₁.symm
  have hd := allK5_distance_of_loss_account Bs₀ Bs₁ hcard hR hloss
  exact ⟨Bs₁,hBs₁,hopt₁,hlift₁,hd.1,hd.2,hkeep⟩

end PaperVIRecourse
