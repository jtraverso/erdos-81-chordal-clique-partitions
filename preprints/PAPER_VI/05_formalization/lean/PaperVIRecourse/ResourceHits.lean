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
/- A physical edge can hit at most one block of an edge clique partition. -/
module
public import PaperVI.Counting
@[expose] public section
namespace PaperVIRecourse
open Finset PaperVI

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- For pairwise resource-disjoint objects, every hit can be charged to a different
resource. No matching or reconstruction assumption is used. -/
theorem card_hit_objects_le (A : Finset α) (res : α → Finset β) (U : Finset β)
    (hdisj : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → Disjoint (res a) (res b)) :
    (A.filter (fun a => ¬ Disjoint (res a) U)).card ≤ U.card := by
  classical
  let S := A.filter (fun a => ¬ Disjoint (res a) U)
  have hex : ∀ a ∈ S, ∃ b, b ∈ res a ∧ b ∈ U := by
    intro a ha
    exact Finset.not_disjoint_iff.mp (mem_filter.mp ha).2
  choose f hf using fun a : S => hex a.val a.property
  apply Finset.card_le_card_of_injective (f := fun a : S => (⟨f a,(hf a).2⟩ : U))
  intro a b heq
  apply Subtype.ext
  by_contra hne
  have hd := hdisj a.val (mem_filter.mp a.property).1 b.val
    (mem_filter.mp b.property).1 hne
  have heq' : f a = f b := congrArg Subtype.val heq
  exact Finset.disjoint_left.mp hd (hf a).1 (heq'.symm ▸ (hf b).1)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Distinct blocks in a clique partition share no physical edge. -/
theorem partition_innerEdges_disjoint {Bs : Finset (Finset V)}
    (hBs : IsCliquePartition G Bs) {B C : Finset V} (hB : B ∈ Bs) (hC : C ∈ Bs)
    (hne : B ≠ C) : Disjoint (innerEdges G B) (innerEdges G C) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e heB heC
  induction e using Sym2.ind with
  | h a b =>
    simp only [innerEdges,Finset.mem_filter] at heB heC
    have hb := heB
    have hc := heC
    have hab : G.Adj a b := SimpleGraph.mem_edgeFinset.mp hb.1
    obtain ⟨D,_,hunique⟩ := hBs.existsUnique a b hab
    have hBD : B = D := hunique B ⟨hB,hb.2 a (by simp),hb.2 b (by simp)⟩
    have hCD : C = D := hunique C ⟨hC,hc.2 a (by simp),hc.2 b (by simp)⟩
    exact hne (hBD.trans hCD.symm)

/-- A finite family of edge changes can spoil no more old blocks than its size. -/
theorem card_hit_partition_le {Bs : Finset (Finset V)}
    (hBs : IsCliquePartition G Bs) (U : Finset (Sym2 V)) :
    (Bs.filter (fun B => ¬ Disjoint (innerEdges G B) U)).card ≤ U.card :=
  card_hit_objects_le Bs (innerEdges G) U
    (fun _ hB _ hC hne => partition_innerEdges_disjoint G hBs hB hC hne)

/-- A physical K5 of type (3,2) has nine edges other than its exterior edge.
These are exactly the edges that can hit old terminal triangles. -/
theorem card_nonExterior_edges_of_type32 (P B : Finset V)
    (hB : G.IsClique (B : Set V)) (hcore : coreSize P B = 3) (hext : extSize P B = 2) :
    (innerEdges G B \ extEdges G P).card = 9 := by
  classical
  have heq : extEdges G P ∩ innerEdges G B = innerEdges G (B \ P) := by
    ext e
    simp only [mem_inter,innerEdges,extEdges,mem_filter]
    constructor
    · rintro ⟨⟨hadj,hP⟩,⟨_,hmem⟩⟩
      exact ⟨hadj,fun v hv => mem_sdiff.mpr ⟨hmem v hv,hP v hv⟩⟩
    · rintro ⟨hadj,hmem⟩
      exact ⟨⟨hadj,fun v hv => (mem_sdiff.mp (hmem v hv)).2⟩,
        hadj,fun v hv => (mem_sdiff.mp (hmem v hv)).1⟩
  have hcard : B.card = 5 := by
    have hc := card_sdiff_add_card_inter B P
    change (B ∩ P).card = 3 at hcore
    change (B \ P).card = 2 at hext
    omega
  have hsub : G.IsClique ((B \ P : Finset V) : Set V) :=
    hB.subset (fun _ hx => (mem_sdiff.mp hx).1)
  rw [card_sdiff,heq,card_innerEdges_of_isClique G B hB,
    card_innerEdges_of_isClique G (B \ P) hsub,hcard]
  change 10 - (extSize P B).choose 2 = 9
  rw [hext]
  decide

/-- Changed type-(3,2) blocks provide at most nine relevant edge resources each. -/
theorem card_hit_partition_type32_le {Bs : Finset (Finset V)}
    (hBs : IsCliquePartition G Bs) (P : Finset V) (Ws : Finset (Finset V))
    (hclique : ∀ B ∈ Ws, G.IsClique (B : Set V))
    (htype : ∀ B ∈ Ws, coreSize P B = 3 ∧ extSize P B = 2) :
    (Bs.filter (fun B => ¬ Disjoint (innerEdges G B)
      (Ws.biUnion (fun W => innerEdges G W \ extEdges G P)))).card ≤ 9 * Ws.card := by
  classical
  have hc : (Ws.biUnion (fun W => innerEdges G W \ extEdges G P)).card ≤ 9 * Ws.card := by
    calc
      _ ≤ ∑ W ∈ Ws, (innerEdges G W \ extEdges G P).card := card_biUnion_le
      _ = ∑ _W ∈ Ws, 9 := sum_congr rfl (fun W hW =>
        card_nonExterior_edges_of_type32 G P W (hclique W hW)
          (htype W hW).1 (htype W hW).2)
      _ = _ := by simp [mul_comm]
  exact (card_hit_partition_le G hBs _).trans hc

end PaperVIRecourse
