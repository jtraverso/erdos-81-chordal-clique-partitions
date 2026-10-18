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
/- Recover the whole physical partition from its non-edge blocks. -/
module
public import PaperVIRecourse.PhysicalRecourse
@[expose] public section
namespace PaperVIRecourse
open Finset PaperVI
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem partition_subset_of_same_large_blocks
    {Bs₀ Bs₁ : Finset (Finset V)}
    (hBs₀ : IsCliquePartition G Bs₀) (hBs₁ : IsCliquePartition G Bs₁)
    (hlarge₀ : ∀ B ∈ Bs₀, 2 < B.card → B ∈ Bs₁)
    (hlarge₁ : ∀ B ∈ Bs₁, 2 < B.card → B ∈ Bs₀) : Bs₀ ⊆ Bs₁ := by
  intro B hB
  by_cases hbig : 2 < B.card
  · exact hlarge₀ B hB hbig
  have hBcard : B.card = 2 := by have := hBs₀.two_le B hB; omega
  obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp (by omega : 1 < B.card)
  have hadj := hBs₀.isClique B hB ha hb hab
  obtain ⟨C,⟨hC,haC,hbC⟩,_⟩ := hBs₁.existsUnique a b hadj
  by_cases hCbig : 2 < C.card
  · have hBC := block_unique_of_edge G hBs₀
      (e := s(a,b)) (SimpleGraph.mem_edgeFinset.mpr hadj) hB (hlarge₁ C hC hCbig)
      (fun v hv => by rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption)
      (fun v hv => by rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption)
    exact hBC.symm ▸ hC
  · have hCcard : C.card = 2 := by have := hBs₁.two_le C hC; omega
    have hBC := two_blocks_eq_of_shared_edge G hBcard hCcard
      (e := s(a,b)) (SimpleGraph.mem_edgeFinset.mpr hadj)
      (fun v hv => by rcases Sym2.mem_iff.mp (Sym2.mem_toFinset.mp hv) with rfl | rfl <;> assumption)
      (fun v hv => by rcases Sym2.mem_iff.mp (Sym2.mem_toFinset.mp hv) with rfl | rfl <;> assumption)
    exact hBC.symm ▸ hC

theorem partition_eq_of_same_large_blocks
    {Bs₀ Bs₁ : Finset (Finset V)}
    (hBs₀ : IsCliquePartition G Bs₀) (hBs₁ : IsCliquePartition G Bs₁)
    (hlarge₀ : ∀ B ∈ Bs₀, 2 < B.card → B ∈ Bs₁)
    (hlarge₁ : ∀ B ∈ Bs₁, 2 < B.card → B ∈ Bs₀) : Bs₀ = Bs₁ :=
  Subset.antisymm (partition_subset_of_same_large_blocks G hBs₀ hBs₁ hlarge₀ hlarge₁)
    (partition_subset_of_same_large_blocks G hBs₁ hBs₀ hlarge₁ hlarge₀)

variable (P : Finset V)

theorem optimal_partition_eq_of_terminal_subset
    (hjoin : ∀ a ∈ P, ∀ v, a ≠ v → G.Adj a v)
    (hq : 2 * P.card ≤ Pᶜ.card + 1)
    {r : ℕ} {T : Sym2 V → Finset V}
    (hT : LiftInv G P (fun _ => 3) r (extEdges G P) T)
    {Bs₀ Bs₁ : Finset (Finset V)}
    (hBs₀ : IsCliquePartition G Bs₀) (hopt₀ : Bs₀.card = cp G)
    (hlift₀ : ∀ e ∈ extEdges G P, T e ∪ e.toFinset ∈ Bs₀)
    (hBs₁ : IsCliquePartition G Bs₁) (hopt₁ : Bs₁.card = cp G)
    (hlift₁ : ∀ e ∈ extEdges G P, T e ∪ e.toFinset ∈ Bs₁)
    (hsub : terminalBlocks P Bs₀ ⊆ terminalBlocks P Bs₁) : Bs₀ = Bs₁ := by
  classical
  have hc := terminal_card_eq G P hjoin hq hT hT hBs₀ hopt₀ hlift₀ hBs₁ hopt₁ hlift₁
  have heq := eq_of_subset_of_card_le hsub hc.ge
  have hlarge : ∀ {X Y : Finset (Finset V)}, IsCliquePartition G X → X.card = cp G →
      (∀ e ∈ extEdges G P, T e ∪ e.toFinset ∈ X) →
      (∀ e ∈ extEdges G P, T e ∪ e.toFinset ∈ Y) →
      terminalBlocks P X ⊆ terminalBlocks P Y → ∀ B ∈ X, 2 < B.card → B ∈ Y := by
    intro X Y hX hopt hLX hLY hTS B hB hbig
    rcases optimal_blocks_of_allK5_lift G P hjoin hq hT hX hopt hLX B hB with hL | htri | hedge
    · obtain ⟨e,he,rfl⟩ := mem_liftBlocks.mp hL
      exact hLY e he
    · exact (mem_filter.mp (hTS (mem_filter.mpr ⟨hB,htri⟩))).1
    · have hcB := card_eq_coreSize_add_extSize P B
      rw [hedge.1,hedge.2] at hcB
      omega
  exact partition_eq_of_same_large_blocks G hBs₀ hBs₁
    (hlarge hBs₀ hopt₀ hlift₀ hlift₁ hsub)
    (hlarge hBs₁ hopt₁ hlift₁ hlift₀ heq.ge)

end PaperVIRecourse

#print axioms PaperVIRecourse.optimal_partition_eq_of_terminal_subset
