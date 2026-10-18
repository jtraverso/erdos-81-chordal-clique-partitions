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
/- Construct an optimal new partition retaining all old terminal triangles
unaffected by the changed physical lifting resources. -/
module
public import PaperVIRecourse.PhysicalPrefix
public import PaperVIRecourse.Counts
@[expose] public section
namespace PaperVIRecourse
open Finset PaperVI
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

def terminalBlocks (Bs : Finset (Finset V)) : Finset (Finset V) :=
  Bs.filter (fun B => coreSize P B = 2 ∧ extSize P B = 1)

def changedAssignments (T₀ T₁ : Sym2 V → Finset V) : Finset (Sym2 V) :=
  (extEdges G P).filter (fun e => T₀ e ≠ T₁ e)

def changedBlocks (T₀ T₁ : Sym2 V → Finset V) : Finset (Finset V) :=
  (changedAssignments G P T₀ T₁).image (fun e => T₁ e ∪ e.toFinset)

def repairEdges (T₀ T₁ : Sym2 V → Finset V) : Finset (Sym2 V) :=
  (changedBlocks G P T₀ T₁).biUnion (fun B => innerEdges G B \ extEdges G P)

def retainedTriangles (T₀ T₁ : Sym2 V → Finset V) (Bs : Finset (Finset V)) :
    Finset (Finset V) :=
  (terminalBlocks P Bs).filter (fun B => Disjoint (innerEdges G B) (repairEdges G P T₀ T₁))

theorem ext_edge_mem_inner_lift (T : Sym2 V → Finset V) {e : Sym2 V}
    (he : e ∈ extEdges G P) : e ∈ innerEdges G (T e ∪ e.toFinset) := by
  classical
  simp only [innerEdges,mem_filter]
  exact ⟨extEdges_subset he,fun v hv => mem_union_right _ hv⟩

theorem type21_disjoint_exterior (B : Finset V) (hext : extSize P B = 1) :
    Disjoint (innerEdges G B) (extEdges G P) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e heB heE
  induction e using Sym2.ind with
  | h a b =>
    obtain ⟨hadj,ha,hb⟩ := (innerEdges_pair_iff G B a b).mp heB
    obtain ⟨_,haP,hbP⟩ := (mem_extEdges G P).mp heE
    have hsub : ({a,b} : Finset V) ⊆ B \ P := by
      intro v hv
      rcases mem_insert.mp hv with rfl | hv
      · exact mem_sdiff.mpr ⟨ha,haP⟩
      · have : v = b := mem_singleton.mp hv
        subst v
        exact mem_sdiff.mpr ⟨hb,hbP⟩
    have hc := card_le_card hsub
    rw [card_pair hadj.ne] at hc
    change (B \ P).card = 1 at hext
    omega

theorem lifting_block_isClique
    {r : ℕ} {T : Sym2 V → Finset V}
    (hT : LiftInv G P (fun _ => 3) r (extEdges G P) T)
    {e : Sym2 V} (he : e ∈ extEdges G P) :
    G.IsClique ((T e ∪ e.toFinset : Finset V) : Set V) := by
  intro a ha b hb hab
  rcases mem_union.mp ha with ha | ha <;> rcases mem_union.mp hb with hb | hb
  · exact hT.coreAdj e he a ha b hb hab
  · exact hT.crossAdj e he a ha b (Sym2.mem_toFinset.mp hb)
  · exact (hT.crossAdj e he b hb a (Sym2.mem_toFinset.mp ha)).symm
  · exact adj_of_mem_extEdges he (Sym2.mem_toFinset.mp ha) (Sym2.mem_toFinset.mp hb) hab

/-- At most nine old terminal triangles are discarded per changed lifting
assignment. This is a physical edge-ownership bound, not an assumed loss account. -/
theorem removed_terminal_count_le
    {r : ℕ} {T₀ T₁ : Sym2 V → Finset V}
    (hT₁ : LiftInv G P (fun _ => 3) r (extEdges G P) T₁)
    {Bs₀ : Finset (Finset V)} (hBs₀ : IsCliquePartition G Bs₀) :
    (terminalBlocks P Bs₀ \ retainedTriangles G P T₀ T₁ Bs₀).card ≤
      9 * (changedAssignments G P T₀ T₁).card := by
  classical
  have hsub : terminalBlocks P Bs₀ \ retainedTriangles G P T₀ T₁ Bs₀ ⊆
      Bs₀.filter (fun B => ¬ Disjoint (innerEdges G B) (repairEdges G P T₀ T₁)) := by
    intro B hB
    obtain ⟨hBT,hnret⟩ := mem_sdiff.mp hB
    exact mem_filter.mpr ⟨(mem_filter.mp hBT).1,fun hd =>
      hnret (mem_filter.mpr ⟨hBT,hd⟩)⟩
  have hclique : ∀ B ∈ changedBlocks G P T₀ T₁, G.IsClique (B : Set V) := by
    intro B hB
    obtain ⟨e,he,rfl⟩ := mem_image.mp hB
    exact lifting_block_isClique G P hT₁ (mem_filter.mp he).1
  have htype : ∀ B ∈ changedBlocks G P T₀ T₁,
      coreSize P B = 3 ∧ extSize P B = 2 := by
    intro B hB
    obtain ⟨e,he,rfl⟩ := mem_image.mp hB
    exact allK5_lift_type G P hT₁ (mem_liftBlocks.mpr ⟨e,(mem_filter.mp he).1,rfl⟩)
  have h9 := card_hit_partition_type32_le G hBs₀ P (changedBlocks G P T₀ T₁) hclique htype
  have hW : (changedBlocks G P T₀ T₁).card ≤ (changedAssignments G P T₀ T₁).card :=
    card_image_le
  exact (card_le_card hsub).trans (h9.trans (Nat.mul_le_mul_left 9 hW))

/-- The retained old triangles avoid every new physical lifting block, including
unchanged assignments. -/
theorem retainedTriangles_avoid
    {T₀ T₁ : Sym2 V → Finset V} {Bs₀ : Finset (Finset V)}
    (hBs₀ : IsCliquePartition G Bs₀)
    (hlift₀ : ∀ e ∈ extEdges G P, T₀ e ∪ e.toFinset ∈ Bs₀) :
    ∀ B ∈ retainedTriangles G P T₀ T₁ Bs₀, ∀ e ∈ extEdges G P,
      Disjoint (innerEdges G B) (innerEdges G (T₁ e ∪ e.toFinset)) := by
  classical
  intro B hB e he
  obtain ⟨hBT,hdisj⟩ := mem_filter.mp hB
  obtain ⟨hBold,ht⟩ := mem_filter.mp hBT
  have hnoext := type21_disjoint_exterior G P B ht.2
  by_cases hchange : T₀ e ≠ T₁ e
  · apply Finset.disjoint_left.mpr
    intro z hzB hzL
    have hzext : z ∉ extEdges G P := fun hz => Finset.disjoint_left.mp hnoext hzB hz
    have hnew : T₁ e ∪ e.toFinset ∈ changedBlocks G P T₀ T₁ :=
      mem_image.mpr ⟨e,mem_filter.mpr ⟨he,hchange⟩,rfl⟩
    exact Finset.disjoint_left.mp hdisj hzB
      (mem_biUnion.mpr ⟨_,hnew,mem_sdiff.mpr ⟨hzL,hzext⟩⟩)
  · have heq : T₀ e = T₁ e := not_ne_iff.mp hchange
    have hne : B ≠ T₀ e ∪ e.toFinset := by
      intro hBL
      have hedge := ext_edge_mem_inner_lift G P T₀ he
      rw [← hBL] at hedge
      exact Finset.disjoint_left.mp hnoext hedge he
    rw [← heq]
    exact partition_innerEdges_disjoint G hBs₀ hBold (hlift₀ e he) hne

/-- The new optimal physical partition exists, keeping the selected old triangles.
No coloring/assembly hypothesis is imposed on the old partition. -/
theorem exists_optimal_partition_retaining_changed_safe
    (hjoin : ∀ a ∈ P, ∀ v, a ≠ v → G.Adj a v)
    (hq : 2 * P.card ≤ Pᶜ.card + 1)
    {r : ℕ} {T₀ T₁ : Sym2 V → Finset V}
    (hT₁ : LiftInv G P (fun _ => 3) r (extEdges G P) T₁)
    {Bs₀ : Finset (Finset V)} (hBs₀ : IsCliquePartition G Bs₀)
    (hlift₀ : ∀ e ∈ extEdges G P, T₀ e ∪ e.toFinset ∈ Bs₀) :
    ∃ Bs₁, IsCliquePartition G Bs₁ ∧ Bs₁.card = cp G ∧
      retainedTriangles G P T₀ T₁ Bs₀ ⊆ Bs₁ ∧
      ∀ e ∈ extEdges G P, T₁ e ∪ e.toFinset ∈ Bs₁ := by
  classical
  apply exists_optimal_partition_retaining_physical_triangles G P hjoin hq hT₁ hBs₀
  · exact (filter_subset _ _).trans (filter_subset _ _)
  · intro B hB
    exact (mem_filter.mp (mem_filter.mp hB).1).2
  · exact retainedTriangles_avoid G P hBs₀ hlift₀

end PaperVIRecourse
