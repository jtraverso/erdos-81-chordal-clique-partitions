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
Paper IV — Brooks B, connectivity linchpin for the cut-vertex reduction.

Two general, reusable facts feeding the (a2) "cut ⇒ partition" half of the residual Lovász step:

* `mem_of_walk_closed` — a `G`-walk starting inside a set closed under `G`-adjacency stays inside it.
* `exists_adj_in_class` — in a connected `G`, every `d ≠ x` has `x` adjacent to some vertex in the
  same `G−x`-component as `d`. (Otherwise that component is closed under all `G`-adjacency, hence
  unreachable from `x`, contradicting connectedness.)

This is exactly what proves BOTH induced pieces `G[{x}∪A₀]`, `G[{x}∪B₀]` connected once a cut vertex
`x` is available (each component of `G−x` hangs off `x`). Kept as an independent Mathlib-only leaf.
-/
module

import Mathlib.Tactic.Push
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

open SimpleGraph Finset

namespace PaperV.Brooks

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- If `W` is closed under `G`-adjacency, a walk starting in `W` stays in `W`. -/
theorem mem_of_walk_closed (G : SimpleGraph V) (W : Set V)
    (hW : ∀ w ∈ W, ∀ y, G.Adj w y → y ∈ W) {u v : V} (p : G.Walk u v) :
    u ∈ W → v ∈ W := by
  induction p with
  | nil => exact id
  | @cons a b c hadj q ih => exact fun ha => ih (hW a ha b hadj)

/-- **Linchpin.** In a connected `G`, for any `d ≠ x`, `x` is adjacent to some vertex `z` in the
same `G−x`-component as `d`. -/
theorem exists_adj_in_class (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    {x d : V} (hd : d ≠ x) :
    ∃ z, G.Adj x z ∧ ∃ hz : z ≠ x,
      (G.induce ({x}ᶜ : Set V)).connectedComponentMk ⟨d, hd⟩ =
      (G.induce ({x}ᶜ : Set V)).connectedComponentMk ⟨z, hz⟩ := by
  classical
  by_contra hcon
  push_neg at hcon
  set D := (G.induce ({x}ᶜ : Set V)).connectedComponentMk ⟨d, hd⟩ with hD
  set W : Set V := {v | ∃ hv : v ≠ x,
      (G.induce ({x}ᶜ : Set V)).connectedComponentMk ⟨v, hv⟩ = D} with hWdef
  have hdW : d ∈ W := ⟨hd, rfl⟩
  have hxW : x ∉ W := by rintro ⟨hx, _⟩; exact hx rfl
  have hclosed : ∀ w ∈ W, ∀ y, G.Adj w y → y ∈ W := by
    rintro w ⟨hwx, hwD⟩ y hadj
    by_cases hyx : y = x
    · subst hyx
      exact absurd (hwD ▸ rfl) (hcon w hadj.symm hwx)
    · refine ⟨hyx, ?_⟩
      have hadj' : (G.induce ({x}ᶜ : Set V)).Adj ⟨w, hwx⟩ ⟨y, hyx⟩ := by
        simpa [SimpleGraph.induce, SimpleGraph.comap] using hadj
      rw [← hwD]
      exact (ConnectedComponent.eq.mpr hadj'.reachable).symm
  obtain ⟨p⟩ := hconn.preconnected d x
  exact hxW (mem_of_walk_closed G W hclosed p hdW)

end PaperV.Brooks
