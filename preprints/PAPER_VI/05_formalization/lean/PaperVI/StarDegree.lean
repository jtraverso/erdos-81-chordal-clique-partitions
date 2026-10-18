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
module

public import PaperVI.Defs
import Mathlib.Tactic.Tauto
import Lean.Elab.Tactic.Omega

@[expose] public section
namespace PaperVI
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Enlarging the core by one exterior vertex modifies precisely its exterior star. -/
theorem star_edit_adj (P : Finset V) {w : V} (hw : w ∉ P) (a b : V) :
    (editGraph (refGraph (insert w P)) P).Adj a b ↔
      a ≠ b ∧ a ∉ P ∧ b ∉ P ∧ (a = w ∨ b = w) := by
  by_cases ha : a = w
  · subst a
    simp [editGraph, symmDiff_def, refGraph, hw]
    tauto
  · by_cases hb : b = w
    · subst b
      simp [editGraph, symmDiff_def, refGraph, hw]
      tauto
    · simp [editGraph, symmDiff_def, refGraph, ha, hb]
      tauto

/-- Exact modification degree at the star centre, including a singleton exterior. -/
theorem star_edit_center_degree (P : Finset V) {w : V} (hw : w ∉ P) :
    (editGraph (refGraph (insert w P)) P).degree w = Pᶜ.card - 1 := by
  classical
  have he : (editGraph (refGraph (insert w P)) P).neighborFinset w = Pᶜ.erase w := by
    ext v
    simp [SimpleGraph.mem_neighborFinset, star_edit_adj P hw, hw, ne_comm]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, he,
    Finset.card_erase_of_mem (Finset.mem_compl.mpr hw)]

/-- The maximum modification degree is the degree of the exterior star centre. -/
theorem star_edit_degree (P : Finset V) {w : V} (hw : w ∉ P) :
    editDegree (refGraph (insert w P)) P = Pᶜ.card - 1 := by
  classical
  unfold editDegree
  apply le_antisymm
  · apply SimpleGraph.maxDegree_le_of_forall_degree_le
    intro a
    by_cases ha : a ∈ P
    · have he : (editGraph (refGraph (insert w P)) P).neighborFinset a = ∅ := by
        ext b
        simp [SimpleGraph.mem_neighborFinset, star_edit_adj P hw, ha]
      simp [← SimpleGraph.card_neighborFinset_eq_degree, he]
    · have hs : (editGraph (refGraph (insert w P)) P).neighborFinset a ⊆ Pᶜ.erase a := by
        intro b hb
        have h := (star_edit_adj P hw a b).mp ((SimpleGraph.mem_neighborFinset _ a b).mp hb)
        exact Finset.mem_erase.mpr ⟨h.1.symm, Finset.mem_compl.mpr h.2.2.1⟩
      have h := Finset.card_le_card hs
      rw [SimpleGraph.card_neighborFinset_eq_degree,
        Finset.card_erase_of_mem (Finset.mem_compl.mpr ha)] at h
      exact h
  · rw [← star_edit_center_degree P hw]
    exact SimpleGraph.degree_le_maxDegree _ w

theorem balanced_star_edit_degree (p : ℕ) (hn : Fintype.card V = 3 * p)
    (P : Finset V) (hP : P.card = p) {w : V} (hw : w ∉ P) :
    editDegree (refGraph (insert w P)) P = 2 * p - 1 := by
  rw [star_edit_degree P hw, Finset.card_compl, hn, hP]
  omega

/-- The concentrated counterexample lies outside Theorem A's local edit region. -/
theorem balanced_star_outside_local_range (p : ℕ) (hp : 1 ≤ p)
    (hn : Fintype.card V = 3 * p) (P : Finset V) (hP : P.card = p)
    {w : V} (hw : w ∉ P) :
    ¬ (18 * editDegree (refGraph (insert w P)) P + 1 ≤ P.card) := by
  rw [balanced_star_edit_degree p hn P hP hw, hP]
  omega

end PaperVI
