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
/-
Paper VI research round — Priority 4, step 2: extracting a sparse but dense subgraph with
Vizing's theorem.

Vizing colours the edges of `J` properly with `Δ(J) + 1` colours. Grouping the colours into
windows of `d` consecutive colours, the union `K` of the colour classes in a most popular window
has maximum degree at most `d` (the colours at a vertex are distinct) and carries at least a
`1 / (Δ(J)/d + 1)` fraction of the edges of `J`. No sparsity of `J` is assumed.
-/
module

public import PaperV.Vizing.Main
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace PaperVI

namespace Research

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Sparse dense subgraph from Vizing's theorem.** For every finite simple graph `J` and every
`d ≥ 1` there is a set `K` of edges of `J` such that every vertex lies on at most `d` edges of
`K` and `|E(J)| ≤ (⌊Δ(J)/d⌋ + 1) · |K|`. -/
theorem exists_sparse_dense_subgraph (J : SimpleGraph V) [DecidableRel J.Adj] (d : ℕ)
    (hd : 1 ≤ d) :
    ∃ K ⊆ J.edgeFinset, (∀ v, (K.filter (fun e => v ∈ e)).card ≤ d) ∧
      J.edgeFinset.card ≤ (J.maxDegree / d + 1) * K.card := by
  classical
  obtain ⟨col⟩ := Vizing.lineGraph_colorable J
  let cc : Sym2 V → ℕ := fun e => if h : e ∈ J.edgeSet then ((col ⟨e, h⟩ : Fin _) : ℕ) else 0
  have hcc : ∀ e (h : e ∈ J.edgeSet), cc e = ((col ⟨e, h⟩ : Fin _) : ℕ) := fun e h => by
    simp only [cc, dif_pos h]
  let t := range (J.maxDegree / d + 1)
  have hmaps : ∀ e ∈ J.edgeFinset, cc e / d ∈ t := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    rw [mem_range, Nat.lt_succ_iff]
    apply Nat.div_le_div_right
    rw [hcc e he]
    exact Nat.lt_succ_iff.mp (col ⟨e, he⟩).2
  obtain ⟨w, -, hmax⟩ := t.exists_max_image
    (fun w => (J.edgeFinset.filter (fun e => cc e / d = w)).card) ⟨0, by simp [t]⟩
  refine ⟨J.edgeFinset.filter (fun e => cc e / d = w), filter_subset _ _, ?_, ?_⟩
  · intro v
    have hle : ((J.edgeFinset.filter (fun e => cc e / d = w)).filter (fun e => v ∈ e)).card ≤
        (Ico (w * d) (w * d + d)).card := by
      apply card_le_card_of_injOn cc
      · intro e he
        simp only [coe_filter, Set.mem_setOf_eq, mem_filter] at he
        rw [coe_Ico, Set.mem_Ico, ← he.1.2]
        exact ⟨Nat.div_mul_le_self _ _, Nat.lt_div_mul_add (by omega)⟩
      · intro e he e' he' hee
        simp only [coe_filter, Set.mem_setOf_eq, mem_filter, SimpleGraph.mem_edgeFinset] at he he'
        by_contra hne
        have hadj : J.lineGraph.Adj ⟨e, he.1.1⟩ ⟨e', he'.1.1⟩ := by
          rw [SimpleGraph.lineGraph_adj_iff_exists]
          exact ⟨fun h => hne (congrArg Subtype.val h), v, he.2, he'.2⟩
        apply col.valid hadj
        apply Fin.ext
        rw [← hcc e he.1.1, ← hcc e' he'.1.1]
        exact hee
    simpa using hle
  · rw [card_eq_sum_card_fiberwise (f := fun e => cc e / d) (t := t) (fun e he => hmaps e he)]
    calc ∑ y ∈ t, (J.edgeFinset.filter (fun e => cc e / d = y)).card
        ≤ ∑ _y ∈ t, (J.edgeFinset.filter (fun e => cc e / d = w)).card :=
          sum_le_sum fun y hy => hmax y hy
      _ = _ := by rw [sum_const, smul_eq_mul, card_range]

end Research

end PaperVI
