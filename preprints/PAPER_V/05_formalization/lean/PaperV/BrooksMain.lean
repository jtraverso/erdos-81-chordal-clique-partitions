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
Brooks' theorem, cubic case (top assembly, B9): Δ ≤ 3 and no K₄ ⟹ 3-colourable.
Reduces to connected components + case split into the non-regular case (B3, proved) and the
3-regular case (B8 = `connected_colorable_three_of_degree_eq_three` from `BrooksReg`).
-/
module

public import PaperV.BrooksNonRegular
public import PaperV.BrooksB4
public import PaperV.BrooksReg

@[expose] public section

open SimpleGraph Finset

namespace PaperV.Brooks

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Brooks' theorem, cubic case (B9).** A finite simple graph with maximum degree `≤ 3` and no
4-clique is 3-colourable. -/
theorem brooks_cubic (G : SimpleGraph V) [DecidableRel G.Adj]
    (hΔ : G.maxDegree ≤ 3) (hK4 : G.CliqueFree 4) : G.Colorable 3 := by
  rw [G.colorable_iff_forall_connectedComponents]
  intro c
  letI : Fintype c := Fintype.ofFinite c
  let H := c.toSimpleGraph
  letI : DecidableRel H.Adj := Classical.decRel _
  have hconn : H.Connected := c.connected_toSimpleGraph
  have hemb : H ↪g G := SimpleGraph.Embedding.induce c.supp
  have hdeg : ∀ v, H.degree v ≤ 3 := by
    intro v
    have hinj : Function.Injective (fun x : c => x.val) := Subtype.val_injective
    have himg : Finset.card (H.neighborFinset v) =
        Finset.card ((H.neighborFinset v).map ⟨(fun x : c => x.val), hinj⟩) := by simp
    rw [SimpleGraph.degree, himg]
    apply (Finset.card_le_card ?_).trans ((G.degree_le_maxDegree v.val).trans hΔ)
    intro x hx
    simp only [Finset.mem_map] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    apply (G.mem_neighborFinset v.val y.val).mpr
    exact (c.toSimpleGraph_adj v.property y.property).mp ((H.mem_neighborFinset v y).mp hy)
  have hfree : H.CliqueFree 4 := SimpleGraph.CliqueFree.comap hemb.isContained hK4
  by_cases hlow : ∃ v, H.degree v < 3
  · exact connected_colorable_three_of_exists_degree_lt H hconn hdeg hlow
  · apply connected_colorable_three_of_degree_eq_three H hconn _ hfree
    intro v
    exact Nat.le_antisymm (hdeg v) (not_lt.mp (not_exists.mp hlow v))

end PaperV.Brooks

