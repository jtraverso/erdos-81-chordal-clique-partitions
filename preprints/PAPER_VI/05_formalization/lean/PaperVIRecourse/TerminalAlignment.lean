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
/- Align terminal triangles while keeping the complete all-K5 lifting fixed. -/
module
public import PaperVIRecourse.TerminalStep
public import PaperVIRecourse.PartitionIdentity
public import PaperVIRecourse.Paths
@[expose] public section
namespace PaperVIRecourse
open Finset PaperVI
open scoped symmDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

/-- Each step inserts a missing target triangle and preserves the triangles
already shared with the target. The number of steps is at most the initial
number of missing target triangles. -/
theorem terminal_alignment_missing_bound
    (hjoin : ∀ a ∈ P, ∀ v, a ≠ v → G.Adj a v)
    (hq : 2 * P.card ≤ Pᶜ.card + 1)
    {r : ℕ} {T : Sym2 V → Finset V}
    (hT : LiftInv G P (fun _ => 3) r (extEdges G P) T)
    {Bs₀ BsTarget : Finset (Finset V)}
    (hBs₀ : IsCliquePartition G Bs₀) (hopt₀ : Bs₀.card = cp G)
    (hlift₀ : ∀ e ∈ extEdges G P, T e ∪ e.toFinset ∈ Bs₀)
    (hTarget : IsCliquePartition G BsTarget) (hoptTarget : BsTarget.card = cp G)
    (hliftTarget : ∀ e ∈ extEdges G P, T e ∪ e.toFinset ∈ BsTarget) :
    ∃ n, n ≤ (terminalBlocks P BsTarget \ terminalBlocks P Bs₀).card ∧
      BlockPath (BoundedAllK5Opt G P r) 18 n Bs₀ BsTarget := by
  classical
  have aux : ∀ k : ℕ, ∀ Bs : Finset (Finset V),
      IsCliquePartition G Bs → Bs.card = cp G →
      (∀ e ∈ extEdges G P, T e ∪ e.toFinset ∈ Bs) →
      (terminalBlocks P BsTarget \ terminalBlocks P Bs).card = k →
      ∃ n, n ≤ k ∧ BlockPath (BoundedAllK5Opt G P r) 18 n Bs BsTarget := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro Bs hBs hopt hlift hcard
      have hgood : BoundedAllK5Opt G P r Bs := ⟨hBs,hopt,T,hT,hlift⟩
      by_cases hz : k = 0
      · have hsub : terminalBlocks P BsTarget ⊆ terminalBlocks P Bs := by
          intro Q hQ
          by_contra hnot
          have hmem : Q ∈ terminalBlocks P BsTarget \ terminalBlocks P Bs :=
            mem_sdiff.mpr ⟨hQ,hnot⟩
          have hpos := card_pos.mpr ⟨Q,hmem⟩
          omega
        have heq := optimal_partition_eq_of_terminal_subset G P hjoin hq hT
          hTarget hoptTarget hliftTarget hBs hopt hlift hsub
        subst Bs
        exact ⟨0, Nat.zero_le _, BlockPath.refl hgood⟩
      · have hpos : 0 < (terminalBlocks P BsTarget \ terminalBlocks P Bs).card := by omega
        obtain ⟨Q,hQ⟩ := card_pos.mp hpos
        obtain ⟨hQtarget,hQnot⟩ := mem_sdiff.mp hQ
        obtain ⟨Bs₁,hBs₁,hopt₁,hlift₁,hQnew,hretain,hdist⟩ :=
          exists_terminal_step G P hjoin hq hT hBs hopt hlift hTarget hliftTarget hQtarget
        have hQnewterm : Q ∈ terminalBlocks P Bs₁ :=
          mem_filter.mpr ⟨hQnew,(mem_filter.mp hQtarget).2⟩
        have hsub : terminalBlocks P BsTarget \ terminalBlocks P Bs₁ ⊆
            terminalBlocks P BsTarget \ terminalBlocks P Bs := by
          intro B hB
          obtain ⟨hBt,hBn⟩ := mem_sdiff.mp hB
          apply mem_sdiff.mpr ⟨hBt,?_⟩
          intro hBo
          exact hBn (mem_filter.mpr ⟨hretain B hBo hBt,(mem_filter.mp hBt).2⟩)
        have hneq : terminalBlocks P BsTarget \ terminalBlocks P Bs₁ ≠
            terminalBlocks P BsTarget \ terminalBlocks P Bs := by
          intro heq
          have hmem := heq.symm ▸ hQ
          exact (mem_sdiff.mp hmem).2 hQnewterm
        have hlt : (terminalBlocks P BsTarget \ terminalBlocks P Bs₁).card < k := by
          rw [← hcard]
          exact card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,hneq⟩)
        obtain ⟨n,hn,hpath⟩ := ih _ hlt Bs₁ hBs₁ hopt₁ hlift₁ rfl
        exact ⟨n+1,by omega,BlockPath.step hgood hdist hpath⟩
  exact aux _ Bs₀ hBs₀ hopt₀ hlift₀ rfl

/-- Any two optimal partitions with the same bounded complete lifting are
connected by eighteen-block steps, using at most the target's terminal count. -/
theorem terminal_alignment
    (hjoin : ∀ a ∈ P, ∀ v, a ≠ v → G.Adj a v)
    (hq : 2 * P.card ≤ Pᶜ.card + 1)
    {r : ℕ} {T : Sym2 V → Finset V}
    (hT : LiftInv G P (fun _ => 3) r (extEdges G P) T)
    {Bs₀ BsTarget : Finset (Finset V)}
    (hBs₀ : IsCliquePartition G Bs₀) (hopt₀ : Bs₀.card = cp G)
    (hlift₀ : ∀ e ∈ extEdges G P, T e ∪ e.toFinset ∈ Bs₀)
    (hTarget : IsCliquePartition G BsTarget) (hoptTarget : BsTarget.card = cp G)
    (hliftTarget : ∀ e ∈ extEdges G P, T e ∪ e.toFinset ∈ BsTarget) :
    ∃ n, n ≤ (terminalBlocks P BsTarget).card ∧
      BlockPath (BoundedAllK5Opt G P r) 18 n Bs₀ BsTarget := by
  obtain ⟨n,hn,hpath⟩ := terminal_alignment_missing_bound G P hjoin hq hT
    hBs₀ hopt₀ hlift₀ hTarget hoptTarget hliftTarget
  exact ⟨n,hn.trans (card_le_card sdiff_subset),hpath⟩

end PaperVIRecourse

#print axioms PaperVIRecourse.terminal_alignment_missing_bound
#print axioms PaperVIRecourse.terminal_alignment
