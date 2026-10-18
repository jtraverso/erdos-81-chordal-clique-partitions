/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Original mathematical attributions and third-party notices are retained below.
-/

/-
Paper V formalization and integration.
Authors: Juan Pablo Traverso Gianini

Original mathematical attributions and existing source/port provenance are
retained below; this author credit does not reattribute those prior results.
-/

/-
Paper IV — Brooks B, (a2) structural half: cut vertex ⇒ partition with connected pieces.

`cut_partition_of_unreachable`: given a cut vertex `x` witnessed by two `G−x`-unreachable
vertices `d,e`, produces the partition `V∖{x}=A₀⊔B₀` (both nonempty, no cross edge, both
`G[{x}∪A₀]`,`G[{x}∪B₀]` connected) required by `colorable_of_cut_partition`. Uses the hand-proved
linchpin `exists_adj_in_class` (from BrooksHub) for the piece-connectivity. Proof produced by
Aristotle (project a8d4024c) from a scaffold with that linchpin supplied; verified here against
Mathlib v4.28.0, free of placeholder proofs, axiom-clean.
-/
module

public import PaperV.BrooksHub

import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Lift

@[expose] public section

open SimpleGraph Finset

namespace PaperV.Brooks

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma connected_induce_insert_of_component_neighbors (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V) (A : Finset V)
    (P : (G.induce ({x}ᶜ : Set V)).ConnectedComponent → Prop)
    (hmem : ∀ v, v ∈ A ↔ ∃ hv : v ≠ x,
      P ((G.induce ({x}ᶜ : Set V)).connectedComponentMk ⟨v, hv⟩))
    (hneigh : ∀ C, P C → ∃ z, G.Adj x z ∧ ∃ hz : z ≠ x,
      (G.induce ({x}ᶜ : Set V)).connectedComponentMk ⟨z, hz⟩ = C) :
    (G.induce ((insert x A : Finset V) : Set V)).Connected := by
  rw [connected_iff]
  constructor
  · intro u v
    -- First establish that x can reach any vertex in A
    have hx_reach : ∀ (v : V) (hv : v ∈ A), SimpleGraph.Reachable (G.induce (↑(insert x A))) ⟨x, by simp⟩ ⟨v, by simp [hv]⟩ := by
      intro v hvA
      -- v ≠ x and P holds for v's component
      rw [hmem] at hvA
      obtain ⟨hvx, hPC⟩ := hvA
      -- get neighbor z of x in the same component
      obtain ⟨z, hzx, hzx_ne, hz_comp⟩ := hneigh _ hPC
      -- z is in A by hmem (z ≠ x and P(component(z)) since component(z) = component(v) and P(component(v)))
      have hzA : z ∈ A := by
        rw [hmem]
        exact ⟨hzx_ne, hz_comp ▸ hPC⟩
      -- z and v are in the same connected component of G.induce ({x}ᶜ), so reachable
      have hz_reach_v : SimpleGraph.Reachable (G.induce ({x}ᶜ : Set V)) ⟨z, hzx_ne⟩ ⟨v, hvx⟩ := by
        rw [ConnectedComponent.eq] at hz_comp
        exact hz_comp
      -- Compose: x → z → v
      have hx_reach_z : SimpleGraph.Reachable (G.induce (↑(insert x A))) ⟨x, by simp⟩ ⟨z, by simp [hzA]⟩ := by
        have hadj : SimpleGraph.Adj (G.induce (↑(insert x A))) ⟨x, by simp⟩ ⟨z, by simp [hzA]⟩ := by simpa using hzx
        exact hadj.reachable
      -- All vertices in the same component as v are in A
      have hcomp_subset_A : ∀ w : {v : V // v ∈ ({x}ᶜ : Set V)},
        SimpleGraph.Reachable (G.induce ({x}ᶜ : Set V)) ⟨v, hvx⟩ w → w.1 ∈ A := by
        intro w hw
        rw [hmem]
        refine ⟨w.2, ?_⟩
        have heq : (G.induce ({x}ᶜ : Set V)).connectedComponentMk w = (G.induce ({x}ᶜ : Set V)).connectedComponentMk ⟨v, hvx⟩ := by
          exact ConnectedComponent.eq.mpr hw.symm
        rw [heq]
        exact hPC
      have hine : ∀ w : {v : V // v ∈ ({x}ᶜ : Set V)}, SimpleGraph.Reachable (G.induce ({x}ᶜ : Set V)) ⟨z, hzx_ne⟩ w → w.1 ∈ A := by
        intro w hw
        exact hcomp_subset_A w (hz_reach_v.symm.trans hw)
      -- Get the walk
      obtain ⟨w'⟩ := hz_reach_v
      -- emb maps vertices in {x}ᶜ to insert x A
      let emb : {v : V // v ∈ ({x}ᶜ : Set V)} → {v : V // v ∈ (↑(insert x A) : Set V)} := fun p =>
        if h : p.val ∈ A then ⟨p.val, by simp [h]⟩ else ⟨z, by simp [hzA]⟩
      -- emb preserves adjacency when both endpoints are in A
      have emb_preserves : ∀ a b : {v : V // v ∈ ({x}ᶜ : Set V)},
          (G.induce ({x}ᶜ : Set V)).Adj a b → a.val ∈ A → b.val ∈ A →
          (G.induce (↑(insert x A))).Adj (emb a) (emb b) := by
        intro a b hadj ha hb
        simp [emb, ha, hb]
        exact hadj
      -- All vertices on w' are in A since they're reachable from z
      have walk_mem_A : ∀ w'' : {v : V // v ∈ ({x}ᶜ : Set V)},
          SimpleGraph.Reachable (G.induce ({x}ᶜ : Set V)) ⟨z, hzx_ne⟩ w'' → w''.val ∈ A := hine
      -- Key lemma: given a walk, we can lift it
      have liftWalk : ∀ {u w : {v : V // v ∈ ({x}ᶜ : Set V)}}
          (p : (G.induce ({x}ᶜ : Set V)).Walk u w),
          (G.induce ({x}ᶜ : Set V)).Reachable ⟨z, hzx_ne⟩ u → u.val ∈ A → w.val ∈ A →
          (G.induce (↑(insert x A))).Reachable (emb u) (emb w) := by
        intro u w p hu_reach_u hu hw
        induction p with
        | nil => simp [emb, hu]
        | @cons u' v' w' hadj rest ih =>
          have hu_reach_v : (G.induce ({x}ᶜ : Set V)).Reachable u' v' := hadj.reachable
          have hv_reach_from_z : (G.induce ({x}ᶜ : Set V)).Reachable ⟨z, hzx_ne⟩ v' := hu_reach_u.trans hu_reach_v
          have hv_mem : v'.val ∈ A := walk_mem_A v' hv_reach_from_z
          exact (emb_preserves u' v' hadj hu hv_mem).reachable.trans (ih hv_reach_from_z hv_mem hw)
      have hz_reach_v_lift : SimpleGraph.Reachable (G.induce (↑(insert x A))) ⟨z, by simp [hzA]⟩ ⟨v, by simp [hvA]⟩ := by
        convert liftWalk w' (SimpleGraph.Reachable.refl _) hzA hvA using 1 <;> simp [emb, hzA, hvA]
      exact hx_reach_z.trans hz_reach_v_lift
    -- Now prove Reachable u v by going via x
    obtain ⟨hu, hu'⟩ := u
    obtain ⟨hv, hv'⟩ := v
    simp only [Finset.mem_insert, Finset.mem_coe] at hu' hv'
    -- u is either x or in A, v is either x or in A
    rcases hu' with rfl | huA <;> rcases hv' with rfl | hvA
    · exact SimpleGraph.Reachable.refl _
    · exact hx_reach hv hvA
    · exact (hx_reach hu huA).symm
    · exact ((hx_reach hu huA).symm).trans (hx_reach hv hvA)
  exact ⟨⟨x, by simp⟩⟩

-- TARGET (prove this) ----------------------------------------------------------------------
theorem cut_partition_of_unreachable (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (x d e : V) (hd : d ≠ x) (he : e ≠ x)
    (hsep : ¬ (G.induce ({x}ᶜ : Set V)).Reachable ⟨d, hd⟩ ⟨e, he⟩) :
    ∃ (A₀ B₀ : Finset V), A₀.Nonempty ∧ B₀.Nonempty ∧ x ∉ A₀ ∧ x ∉ B₀ ∧
      Disjoint A₀ B₀ ∧ insert x (A₀ ∪ B₀) = Finset.univ ∧
      (∀ a ∈ A₀, ∀ b ∈ B₀, ¬ G.Adj a b) ∧
      (G.induce ((insert x A₀ : Finset V) : Set V)).Connected ∧
      (G.induce ((insert x B₀ : Finset V) : Set V)).Connected := by
  -- Define B₀ as vertices reachable from e in G.induce ({x}ᶜ), A₀ as everything else
  classical
  let preB₀ : Finset {v : V // v ≠ x} := Finset.univ.filter (fun v : {v : V // v ≠ x} => (G.induce ({x}ᶜ : Set V)).Reachable ⟨e, he⟩ v)
  let B₀ : Finset V := preB₀.map ⟨Subtype.val, Subtype.val_injective⟩
  let A₀ : Finset V := (Finset.univ \ {x}) \ B₀
  have hB₀_mem : ∀ v, v ∈ B₀ ↔ ∃ (w : {v : V // v ≠ x}), w ∈ preB₀ ∧ w.val = v := fun v => Finset.mem_map
  have hA₀_mem : ∀ v, v ∈ A₀ ↔ v ≠ x ∧ v ∉ B₀ := fun v => by simp [A₀]
  refine ⟨A₀, B₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- A₀.Nonempty: d ∈ A₀
  · use d
    simp only [hA₀_mem]
    refine ⟨hd, ?_⟩
    simp only [hB₀_mem]
    intro ⟨w, hw_mem, hw_eq⟩
    simp [preB₀] at hw_mem
    have hw_eq' : w = ⟨d, hd⟩ := Subtype.ext hw_eq
    rw [hw_eq'] at hw_mem
    exact hsep hw_mem.symm
  -- B₀.Nonempty: e ∈ B₀
  · use e
    simp only [hB₀_mem]
    use ⟨e, he⟩
    simp [preB₀]
    exact SimpleGraph.Reachable.refl _
  -- x ∉ A₀
  · rw [hA₀_mem]
    simp
  -- x ∉ B₀
  · rw [hB₀_mem]
    intro ⟨w, _, hw_eq⟩
    have : w.val = x := hw_eq
    exact w.property this
  -- Disjoint A₀ B₀
  · rw [Finset.disjoint_left]
    intro a haA haB
    rw [hA₀_mem] at haA
    exact haA.2 haB
  -- insert x (A₀ ∪ B₀) = univ
  · ext v
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases hvx : v = x
    case pos => left; exact hvx
    case neg =>
      by_cases hvB₀ : v ∈ B₀
      · right; exact Or.inr hvB₀
      · right
        rw [hA₀_mem]
        exact Or.inl ⟨hvx, hvB₀⟩
  -- ∀ a ∈ A₀, ∀ b ∈ B₀, ¬G.Adj a b
  · intro a haA b hbB hab
    rw [hA₀_mem] at haA
    rw [hB₀_mem] at hbB
    obtain ⟨⟨vb, hvb⟩, hve_mem, hvb_eq⟩ := hbB
    simp [preB₀] at hve_mem
    have h_a_in_B₀ : a ∈ B₀ := by
      rw [hB₀_mem]
      use ⟨a, haA.1⟩
      simp [preB₀]
      have hb_eq : b = vb := hvb_eq.symm
      have hab' : (G.induce ({x}ᶜ : Set V)).Adj ⟨a, haA.1⟩ ⟨vb, hvb⟩ := by
        rw [hb_eq] at hab
        simp [SimpleGraph.induce]
        exact hab
      -- hve_mem : Reachable ⟨e, he⟩ ⟨vb, hvb⟩
      -- hab'.reachable : Reachable ⟨a, haA.1⟩ ⟨vb, hvb⟩
      -- We need Reachable ⟨e, he⟩ ⟨a, haA.1⟩
      exact SimpleGraph.Reachable.trans hve_mem hab'.reachable.symm
    exact haA.2 h_a_in_B₀
  -- Connected (insert x A₀)
  · apply connected_induce_insert_of_component_neighbors G x A₀ (fun C => C ≠ (G.induce ({x}ᶜ : Set V)).connectedComponentMk (⟨e, he⟩ : {v : V // v ≠ x}))
    · intro v
      rw [hA₀_mem]
      apply Iff.intro
      · intro ⟨hvx, hvB₀⟩
        refine ⟨hvx, ?_⟩
        intro h
        apply hvB₀
        exact hB₀_mem v |>.mpr ⟨⟨v, hvx⟩, by simp only [preB₀, Finset.mem_filter, Finset.mem_univ, true_and]; exact ConnectedComponent.eq.mp h.symm, rfl⟩
      · intro ⟨hvx, hPC⟩
        refine ⟨hvx, ?_⟩
        intro hvB₀
        rw [hB₀_mem] at hvB₀
        obtain ⟨w, hw_mem, hw_eq⟩ := hvB₀
        simp only [preB₀, Finset.mem_filter, Finset.mem_univ, true_and] at hw_mem
        have h_mk_eq : (G.induce ({x}ᶜ : Set V)).connectedComponentMk (⟨e, he⟩ : {v : V // v ≠ x}) = (G.induce ({x}ᶜ : Set V)).connectedComponentMk w := ConnectedComponent.eq.mpr hw_mem
        have hw_eq' : w = (⟨v, hvx⟩ : {v : V // v ≠ x}) := Subtype.ext hw_eq
        rw [hw_eq'] at h_mk_eq
        exact hPC h_mk_eq.symm
    · intro C hC
      -- Need to find some v ≠ x in component C
      obtain ⟨⟨v, hv⟩, hv_rep⟩ := C.exists_rep
      have hvx : v ≠ x := hv
      have hC_eq : C = (G.induce ({x}ᶜ : Set V)).connectedComponentMk (⟨v, hvx⟩ : {v : V // v ≠ x}) := by
        rw [← hv_rep]
        rfl
      obtain ⟨z, hzx, hzx_ne, hz_comp⟩ := exists_adj_in_class G hconn hvx
      refine ⟨z, hzx, hzx_ne, ?_⟩
      exact Eq.trans hz_comp.symm hC_eq.symm
  -- Connected (insert x B₀)
  · apply connected_induce_insert_of_component_neighbors G x B₀ (fun C => C = (G.induce ({x}ᶜ : Set V)).connectedComponentMk (⟨e, he⟩ : {v : V // v ≠ x}))
    · intro v
      rw [hB₀_mem]
      constructor
      · rintro ⟨⟨w, hw⟩, hw_mem, hw_eq⟩
        simp [preB₀] at hw_mem
        have hw_ne : v ≠ x := hw_eq ▸ hw
        refine ⟨hw_ne, ?_⟩
        simp only [← hw_eq]
        exact (ConnectedComponent.eq.mpr hw_mem.symm)
      · rintro ⟨hvx, hPC⟩
        use ⟨v, hvx⟩
        simp [preB₀]
        exact (ConnectedComponent.eq.mp hPC).symm
    · intro C hCeq
      rw [hCeq]
      obtain ⟨z, hzx, hzx_ne, hz_comp⟩ := exists_adj_in_class G hconn he
      exact ⟨z, hzx, hzx_ne, hz_comp.symm⟩

end PaperV.Brooks
