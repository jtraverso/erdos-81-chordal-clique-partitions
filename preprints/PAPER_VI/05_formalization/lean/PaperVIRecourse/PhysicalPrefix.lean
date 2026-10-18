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
/- Extracting a terminal coloring from physical old triangles, not from an
assumed assembly representation. -/
module
public import PaperVIRecourse.OptimalAdapter
public import PaperVIRecourse.ResourceHits
@[expose] public section
namespace PaperVIRecourse
open Finset PaperVI
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem type21_eq_triangle (P B : Finset V)
    (ht : coreSize P B = 2 ∧ extSize P B = 1)
    {a b : V} (ha : a ∈ P) (hb : b ∈ P) (hab : a ≠ b)
    (haB : a ∈ B) (hbB : b ∈ B) :
    ∃ x, x ∉ P ∧ ({a,b,x} : Finset V) = B := by
  classical
  have hc : 0 < (B \ P).card := by change 0 < extSize P B; omega
  obtain ⟨x,hx⟩ := card_pos.mp hc
  have hx1 := mem_sdiff.mp hx
  have hax : a ≠ x := fun h => hx1.2 (h ▸ ha)
  have hbx : b ≠ x := fun h => hx1.2 (h ▸ hb)
  have hcard : B.card = 3 := by
    rw [PaperVI.card_eq_coreSize_add_extSize P B,ht.1,ht.2]
  have hsub : ({a,b,x} : Finset V) ⊆ B := by
    intro v hv
    simp only [mem_insert,mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact haB
    · exact hbB
    · exact hx1.1
  refine ⟨x,hx1.2,eq_of_subset_of_card_le hsub ?_⟩
  rw [hcard]
  simp [hab,hax,hbx]

variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

def prefixCoreEdges (A : Finset (Finset V)) : Finset (Sym2 V) :=
  A.biUnion (fun B => innerEdges G (B ∩ P))

/-- Every edge in the physical terminal prefix has an actual old triangle and
an exterior color. The same triangle is used for either orientation of the edge. -/
theorem prefix_edge_has_triangle {A : Finset (Finset V)}
    (ht : ∀ B ∈ A, coreSize P B = 2 ∧ extSize P B = 1)
    {e : Sym2 V} (he : e ∈ prefixCoreEdges G P A) :
    ∃ x, x ∉ P ∧ ∀ a b, e = s(a,b) →
      ({a,b,x} : Finset V) ∈ A := by
  classical
  obtain ⟨B,hB,heB⟩ := mem_biUnion.mp he
  induction e using Sym2.ind with
  | h a b =>
    simp only [innerEdges,mem_filter,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] at heB
    have hab : G.Adj a b := heB.1
    have ha := mem_inter.mp (heB.2 a (by simp))
    have hb := mem_inter.mp (heB.2 b (by simp))
    obtain ⟨x,hx,htri⟩ := type21_eq_triangle P B (ht B hB) ha.2 hb.2 hab.ne ha.1 hb.1
    have hbase : ({a,b,x} : Finset V) ∈ A := by rw [htri]; exact hB
    refine ⟨x,hx,?_⟩
    intro c d heq
    rcases Sym2.eq_iff.mp heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hbase
    · simpa only [Finset.insert_comm] using hbase

theorem innerEdges_pair_iff (B : Finset V) (a b : V) :
    s(a,b) ∈ innerEdges G B ↔ G.Adj a b ∧ a ∈ B ∧ b ∈ B := by
  simp only [innerEdges,mem_filter,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,
    Sym2.mem_toFinset,Sym2.mem_iff,forall_eq_or_imp,forall_eq]

/-- Every physical edge-disjoint family of old terminal triangles that avoids
the new lifting extends to an actual optimal partition containing those triangles.
The old partition can be arbitrary; it need not have been assembled by this code. -/
theorem exists_optimal_partition_retaining_physical_triangles
    (hjoin : ∀ a ∈ P, ∀ v, a ≠ v → G.Adj a v)
    (hq : 2 * P.card ≤ Pᶜ.card + 1)
    {r : ℕ} {T : Sym2 V → Finset V}
    (hT : LiftInv G P (fun _ => 3) r (extEdges G P) T)
    {Bs₀ A : Finset (Finset V)} (hBs₀ : IsCliquePartition G Bs₀)
    (hA : A ⊆ Bs₀) (ht : ∀ B ∈ A, coreSize P B = 2 ∧ extSize P B = 1)
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
    have hclique := hBs₀.isClique _ (hA htri)
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
    obtain ⟨B,_,hunique⟩ := hBs₀.existsUnique a x hadjax
    have h₁ := hunique ({a,b,x} : Finset V) ⟨hA htri,by simp,by simp⟩
    have h₂ := hunique ({a,b',x} : Finset V) ⟨hA htri',by simp,by simp⟩
    have hbe : b ∈ ({a,b',x} : Finset V) := (h₁.trans h₂.symm) ▸ (by simp)
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
  have hadj := hBs₀.isClique B (hA hB) ha₁.1 hb₁.1 hab
  have he : s(a,b) ∈ D := mem_biUnion.mpr
    ⟨B,hB,(innerEdges_pair_iff G _ a b).mpr ⟨hadj,ha,hb⟩⟩
  have hnew := hprefix a ha₁.2 b hb₁.2 hab (hres a b he) he
  have hold := hA ((hg₀ _ he).2 a b rfl)
  obtain ⟨C,_,hunique⟩ := hBs₀.existsUnique a b hadj
  have h₁ := hunique ({a,b,g₀ s(a,b)} : Finset V) ⟨hold,by simp,by simp⟩
  have h₂ := hunique B ⟨hA hB,ha₁.1,hb₁.1⟩
  exact (h₁.trans h₂.symm) ▸ hnew

end PaperVIRecourse
