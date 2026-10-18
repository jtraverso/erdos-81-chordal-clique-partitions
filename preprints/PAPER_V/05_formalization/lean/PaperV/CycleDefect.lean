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
Paper IV — Extremal `oct` values for cycles (v0.9.15 candidate).

Complements the complete-graph extremal witness (`oct(K_n)=n−2`) with the cycle family — tightness at
the sparse end: even cycles are bipartite (`oct=0`), odd cycles need exactly one vertex deleted
(`oct=1`). The three underlying `cycleGraph` colouring facts are Mathlib-level (Aristotle-assisted:
project 22a7a984, audited: no placeholder proofs, axiom-clean); the `oct` values wire them through `oct_eq_zero_iff`.
-/
module

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
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
public import PaperV.DqBasic

import Mathlib.Tactic.Ext

@[expose] public section
open SimpleGraph Finset

theorem cycleGraph_even_colorable (n : ℕ) : (cycleGraph (2 * n + 2)).Colorable 2 := by
  simpa using (cycleGraph.bicoloring_of_even (2 * n + 2) (by refine ⟨n + 1, ?_⟩; omega)).colorable

theorem cycleGraph_odd_not_colorable (n : ℕ) : ¬ (cycleGraph (2 * n + 3)).Colorable 2 := by
  intro h
  have hle : (cycleGraph (2 * n + 3)).chromaticNumber ≤ 2 := h.chromaticNumber_le
  have heq : (cycleGraph (2 * n + 3)).chromaticNumber = 3 :=
    chromaticNumber_cycleGraph_of_odd (2 * n + 3) (by omega) (by refine ⟨n + 1, ?_⟩; omega)
  rw [heq] at hle; norm_num at hle

lemma cycleGraph_delete_zero_parity_ne (n : ℕ)
    (u v : (({0}ᶜ) : Set (Fin (2 * n + 3))))
    (h : ((cycleGraph (2 * n + 3)).induce (({0}ᶜ) : Set (Fin (2 * n + 3)))).Adj u v) :
    u.val.val % 2 ≠ v.val.val % 2 := by
  rw [SimpleGraph.induce_adj] at h
  simp only [SimpleGraph.cycleGraph_adj] at h
  have hu : (u : Fin (2 * n + 3)).val ≠ 0 := fun h => u.2 (Fin.ext h)
  have hv : (v : Fin (2 * n + 3)).val ≠ 0 := fun h => v.2 (Fin.ext h)
  rcases h with h | h
  · have heq : (u : Fin (2 * n + 3)) = (v : Fin (2 * n + 3)) + 1 := by rw [← h]; simp
    have hv_lt : (v : Fin (2 * n + 3)).val < 2 * n + 2 := by
      by_contra hc; push_neg at hc
      have : (v : Fin (2 * n + 3)).val = 2 * n + 2 := by omega
      have : (u : Fin (2 * n + 3)).val = 0 := by rw [heq]; simp [Fin.val_add, this]
      exact hu this
    have : (u : Fin (2 * n + 3)).val = (v : Fin (2 * n + 3)).val + 1 := by
      rw [heq, Fin.val_add]; simp [Nat.mod_eq_of_lt (by omega : (v : Fin (2 * n + 3)).val + 1 < 2 * n + 3)]
    omega
  · have heq : (v : Fin (2 * n + 3)) = (u : Fin (2 * n + 3)) + 1 := by rw [← h]; simp
    have hu_lt : (u : Fin (2 * n + 3)).val < 2 * n + 2 := by
      by_contra hc; push_neg at hc
      have : (u : Fin (2 * n + 3)).val = 2 * n + 2 := by omega
      have : (v : Fin (2 * n + 3)).val = 0 := by rw [heq]; simp [Fin.val_add, this]
      exact hv this
    have : (v : Fin (2 * n + 3)).val = (u : Fin (2 * n + 3)).val + 1 := by
      rw [heq, Fin.val_add]; simp [Nat.mod_eq_of_lt (by omega : (u : Fin (2 * n + 3)).val + 1 < 2 * n + 3)]
    omega

theorem cycleGraph_odd_delete_colorable (n : ℕ) :
    ((cycleGraph (2 * n + 3)).induce (({0}ᶜ) : Set (Fin (2 * n + 3)))).Colorable 2 := by
  refine ⟨Coloring.mk (fun u ↦ ⟨u.val.val % 2, Nat.mod_lt _ (by omega)⟩) ?_⟩
  intro u v h
  exact Fin.ne_of_val_ne (cycleGraph_delete_zero_parity_ne n u v h)

namespace PaperV
/-- Even cycle: `oct = 0` (bipartite). -/
theorem oct_cycleGraph_even (n : ℕ) : oct (cycleGraph (2 * n + 2)) = 0 := by
  classical
  rw [oct_eq_zero_iff _]
  exact cycleGraph_even_colorable n

/-- Odd cycle: `oct = 1` (one vertex must be deleted to make it bipartite). -/
theorem oct_cycleGraph_odd (n : ℕ) : oct (cycleGraph (2 * n + 3)) = 1 := by
  classical
  apply le_antisymm
  · -- oct ≤ 1 : delete vertex 0
    apply Nat.sInf_le
    refine ⟨{0}, ?_, Finset.card_singleton _⟩
    rw [IsDefectSet, Finset.coe_singleton]
    exact cycleGraph_odd_delete_colorable n
  · -- oct ≥ 1 : not bipartite
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [oct_eq_zero_iff _] at h0
    exact cycleGraph_odd_not_colorable n h0
end PaperV
