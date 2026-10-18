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
/- Complete an arbitrary compatible physical terminal prefix, including new triangles. -/
module
public import PaperVIRecourse.PhysicalPrefix
@[expose] public section
namespace PaperVIRecourse
open Finset PaperVI
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem compatible_family_unique {A : Finset (Finset V)}
    (hAdisj : ∀ B ∈ A, ∀ C ∈ A, B ≠ C → Disjoint (innerEdges G B) (innerEdges G C))
    {B C : Finset V} (hB : B ∈ A) (hC : C ∈ A)
    {a b : V} (hadj : G.Adj a b) (haB : a ∈ B) (hbB : b ∈ B)
    (haC : a ∈ C) (hbC : b ∈ C) : B = C := by
  by_contra hne
  exact Finset.disjoint_left.mp (hAdisj B hB C hC hne)
    ((innerEdges_pair_iff G B a b).mpr ⟨hadj,haB,hbB⟩)
    ((innerEdges_pair_iff G C a b).mpr ⟨hadj,haC,hbC⟩)

variable (P : Finset V)

/-- A family of compatible actual triangles extends while preserving every
triangle and all prescribed K5 blocks. It need not be contained in an old partition. -/
theorem exists_optimal_partition_of_compatible_triangles
    (hjoin : ∀ a ∈ P, ∀ v, a ≠ v → G.Adj a v)
    (hq : 2 * P.card ≤ Pᶜ.card + 1)
    {r : ℕ} {T : Sym2 V → Finset V}
    (hT : LiftInv G P (fun _ => 3) r (extEdges G P) T)
    {A : Finset (Finset V)}
    (hAclique : ∀ B ∈ A, G.IsClique (B : Set V))
    (hAdisj : ∀ B ∈ A, ∀ C ∈ A, B ≠ C → Disjoint (innerEdges G B) (innerEdges G C)) (ht : ∀ B ∈ A, coreSize P B = 2 ∧ extSize P B = 1)
    (havoid : ∀ B ∈ A, ∀ e ∈ extEdges G P,
      Disjoint (innerEdges G B) (innerEdges G (T e ∪ e.toFinset))) :
    ∃ Bs, IsCliquePartition G Bs ∧ Bs.card = cp G ∧ A ⊆ Bs ∧
      ∀ e ∈ extEdges G P, T e ∪ e.toFinset ∈ Bs := by
  classical
  let D := prefixCoreEdges G P A
  have hex : ∀ e ∈ D, ∃ x, x ∉ P ∧ ∀ a b, e = s(a,b) →
      ({a,b,x} : Finset V) ∈ A := fun _ he => prefix_edge_has_triangle G P ht he
  let g₀ : Sym2 V → V := fun e =>
    if he : e ∈ D then Classical.choose (hex e he) else (Quot.out e).1
  have hg₀ : ∀ e ∈ D, g₀ e ∉ P ∧ ∀ a b, e = s(a,b) →
      ({a,b,g₀ e} : Finset V) ∈ A := by
    intro e he
    simpa only [g₀,dif_pos he] using Classical.choose_spec (hex e he)
  have hres : ∀ a b, s(a,b) ∈ D → residPair G P T a b := by
    intro a b he
    obtain ⟨B,hB,heB⟩ := mem_biUnion.mp he
    obtain ⟨hadj,haB,hbB⟩ := (innerEdges_pair_iff G _ a b).mp heB
    refine ⟨hadj,?_⟩
    rintro ⟨e,hee,hae,hbe⟩
    exact Finset.disjoint_left.mp (havoid B hB e hee)
      ((innerEdges_pair_iff G B a b).mpr ⟨hadj,(mem_inter.mp haB).1,(mem_inter.mp hbB).1⟩)
      ((innerEdges_pair_iff G _ a b).mpr
        ⟨hadj,mem_union_left _ hae,mem_union_left _ hbe⟩)
  have hD : D ⊆ requestEdges P (residPair G P T) := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      obtain ⟨B,hB,heB⟩ := mem_biUnion.mp he
      obtain ⟨_,haB,hbB⟩ := (innerEdges_pair_iff G _ a b).mp heB
      exact mem_image.mpr ⟨(a,b),mem_filter.mpr
        ⟨mem_product.mpr ⟨(mem_inter.mp haB).2,(mem_inter.mp hbB).2⟩,hres a b he⟩,rfl⟩
  have hpartial : PartialColoring P Pᶜ (residPair G P T) (usedPair G P T) D g₀ := by
    intro a ha b hb hab he
    let x := g₀ s(a,b)
    have hx : x ∉ P := (hg₀ _ he).1
    have htri : ({a,b,x} : Finset V) ∈ A := (hg₀ _ he).2 a b rfl
    have hclique := hAclique _ htri
    have hax : a ≠ x := fun h => hx (h ▸ ha)
    have hbx : b ≠ x := fun h => hx (h ▸ hb)
    have hadjax : G.Adj a x := hclique (by simp) (by simp) hax
    have hadjbx : G.Adj b x := hclique (by simp) (by simp) hbx
    have hunused : ∀ v, v = a ∨ v = b → ¬ usedPair G P T v x := by
      intro v hv
      rintro ⟨e,hee,hve,hxe⟩
      have hvtri : v ∈ ({a,b,x} : Finset V) := by rcases hv with rfl | rfl <;> simp
      have hvx : v ≠ x := by rcases hv with rfl | rfl; exact hax; exact hbx
      have hvadj := hclique hvtri (by simp) hvx
      exact Finset.disjoint_left.mp (havoid _ htri e hee)
        ((innerEdges_pair_iff G _ v x).mpr ⟨hvadj,hvtri,by simp⟩)
        ((innerEdges_pair_iff G _ v x).mpr
          ⟨hvadj,mem_union_left _ hve,mem_union_right _ (Sym2.mem_toFinset.mpr hxe)⟩)
    refine ⟨mem_compl.mpr hx,hunused a (Or.inl rfl),hunused b (Or.inr rfl),?_⟩
    intro b' hb' hbb' _ he' heq
    have htri' : ({a,b',x} : Finset V) ∈ A := by
      change ({a,b',g₀ s(a,b)} : Finset V) ∈ A
      rw [heq]
      exact (hg₀ _ he').2 a b' rfl
    have heqB := compatible_family_unique G hAdisj htri htri' hadjax
      (by simp) (by simp) (by simp) (by simp)
    have hbe : b ∈ ({a,b',x} : Finset V) := heqB ▸ (by simp)
    have hba : b ≠ a := hab.1.ne.symm
    simpa [hba,hbb'.symm,hbx] using hbe
  obtain ⟨g,Bs,hBs,hopt,_,_,hlift,hprefix,_,_⟩ :=
    exists_optimal_partition_extending_prefix G P hjoin hq hT hD hpartial
  refine ⟨Bs,hBs,hopt,?_,hlift⟩
  intro B hB
  have hc : 1 < (B ∩ P).card := by change 1 < coreSize P B; rw [(ht B hB).1]; decide
  obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp hc
  have ha₁ := mem_inter.mp ha
  have hb₁ := mem_inter.mp hb
  have hadj := hAclique B hB ha₁.1 hb₁.1 hab
  have he : s(a,b) ∈ D := mem_biUnion.mpr
    ⟨B,hB,(innerEdges_pair_iff G _ a b).mpr ⟨hadj,ha,hb⟩⟩
  have hnew := hprefix a ha₁.2 b hb₁.2 hab (hres a b he) he
  have hold := (hg₀ _ he).2 a b rfl
  have heqB := compatible_family_unique G hAdisj hold hB hadj
    (by simp) (by simp) ha₁.1 hb₁.1
  exact heqB ▸ hnew

end PaperVIRecourse

#print axioms PaperVIRecourse.exists_optimal_partition_of_compatible_triangles
