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

/- Brooks submodule B4: a degree-3 vertex in a K4-free graph has two non-adjacent neighbours. -/
module

import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Set
public import Mathlib.Combinatorics.SimpleGraph.Coloring
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section
open SimpleGraph
namespace PaperV.Brooks
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- If `v` has degree 3 and `G` has no 4-clique, then two of `v`'s neighbours are non-adjacent. -/
theorem exists_nonadj_neighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (hdeg : G.degree v = 3) (hK4 : G.CliqueFree 4) :
    ∃ a b, a ∈ G.neighborFinset v ∧ b ∈ G.neighborFinset v ∧ a ≠ b ∧ ¬ G.Adj a b := by
  by_contra! h
  -- All pairs of neighbors are adjacent
  -- The neighbor finset has 3 elements
  have hcard : (G.neighborFinset v).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact hdeg
  -- Combine v with its neighbors to form a 4-element set
  have hvnotin : v ∉ G.neighborFinset v := by simp [SimpleGraph.mem_neighborFinset]
  have hsize : ({v} ∪ G.neighborFinset v).card = 4 := by
    rw [Finset.card_union_of_disjoint]
    · simp [hcard]
    · rw [Finset.disjoint_singleton_left]
      exact hvnotin
  -- Show it's a clique
  have hclique : IsClique G ({v} ∪ G.neighborFinset v) := by
    intro x hx y hy hxy
    by_cases hxv : x = v <;> by_cases hyv : y = v
    · simp_all
    · subst hxv; simp at hy; cases hy <;> simp_all
    · subst hyv; simp at hx; cases hx <;> simp_all [SimpleGraph.Adj.symm]
    · simp at hx hy
      have hax : x ∈ G.neighborFinset v := by rw [SimpleGraph.mem_neighborFinset]; simpa using hx.resolve_left hxv
      have hby : y ∈ G.neighborFinset v := by rw [SimpleGraph.mem_neighborFinset]; simpa using hy.resolve_left hyv
      exact (h x y hax hby hxy)
  have hclique' : G.IsClique ↑({v} ∪ G.neighborFinset v) := by convert hclique using 1; simp
  have hnc : G.IsNClique 4 ({v} ∪ G.neighborFinset v) := ⟨hclique', hsize⟩
  exact hK4 ({v} ∪ G.neighborFinset v) hnc

end PaperV.Brooks
