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
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.SymmDiff
import Lean.Elab.Tactic.Omega

/-! Finite-set accounting for physical block partitions. These lemmas convert
already established loss estimates into distance estimates. They do not assert
the existence of a legal graph reconstruction. -/

@[expose] public section

namespace PaperVIRecourse

open Finset
open scoped symmDiff

variable {α : Type*} [DecidableEq α]

/-- Equal-size block collections lose and gain the same number of blocks. -/
theorem card_symmDiff_eq_twice_loss (A B : Finset α) (hcard : A.card = B.card) :
    (A ∆ B).card = 2 * (A \ B).card := by
  have hd : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  have heq := Finset.card_sdiff_comm hcard
  rw [symmDiff, Finset.sup_eq_union, Finset.card_union_of_disjoint hd]
  omega

theorem card_symmDiff_le_twice_loss (A B : Finset α) (hcard : A.card = B.card)
    {L : ℕ} (hloss : (A \ B).card ≤ L) :
    (A ∆ B).card ≤ 2 * L := by
  rw [card_symmDiff_eq_twice_loss A B hcard]
  omega

/-- The three layers of a partition can be charged separately. -/
theorem loss_union_three_le (A₀ B₀ C₀ A₁ B₁ C₁ : Finset α) :
    ((A₀ ∪ B₀ ∪ C₀) \ (A₁ ∪ B₁ ∪ C₁)).card ≤
      (A₀ \ A₁).card + (B₀ \ B₁).card + (C₀ \ C₁).card := by
  have hs : (A₀ ∪ B₀ ∪ C₀) \ (A₁ ∪ B₁ ∪ C₁) ⊆
      (A₀ \ A₁) ∪ (B₀ \ B₁) ∪ (C₀ \ C₁) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_union] at hx ⊢
    rcases hx.1 with (ha | hb) | hc
    · exact Or.inl (Or.inl ⟨ha, fun h => hx.2 (Or.inl (Or.inl h))⟩)
    · exact Or.inl (Or.inr ⟨hb, fun h => hx.2 (Or.inl (Or.inr h))⟩)
    · exact Or.inr ⟨hc, fun h => hx.2 (Or.inr h)⟩
  exact (Finset.card_le_card hs).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))

/-- Numerical closure of the physical 9k triangle-removal accounting. -/
theorem allK5_distance_of_loss_account (A B : Finset α)
    (hcard : A.card = B.card) {k R : ℕ} (hR : R ≤ 9 * k)
    (hloss : (A \ B).card ≤ k + R + (6 * k + 2 * R)) :
    (A \ B).card ≤ 34 * k ∧ (A ∆ B).card ≤ 68 * k := by
  have h34 : (A \ B).card ≤ 34 * k := by omega
  refine ⟨h34, ?_⟩
  have hd := card_symmDiff_le_twice_loss A B hcard h34
  omega

/-- A fixed-lifting terminal repair removes at most three old requests. -/
theorem terminal_distance_of_loss_account (A B : Finset α)
    (hcard : A.card = B.card) {R : ℕ} (hR : R ≤ 3)
    (hloss : (A \ B).card ≤ 3 * R) :
    (A ∆ B).card ≤ 18 := by
  have hd := card_symmDiff_le_twice_loss A B hcard hloss
  omega

theorem allK5_distance_of_thirteen_changes (A B : Finset α)
    {k : ℕ} (hk : k ≤ 13) (hd : (A ∆ B).card ≤ 68 * k) :
    (A ∆ B).card ≤ 884 := by
  omega

end PaperVIRecourse
