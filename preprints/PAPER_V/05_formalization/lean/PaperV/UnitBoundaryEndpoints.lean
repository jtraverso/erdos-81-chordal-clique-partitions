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

module
public import PaperV.UnitBoundaryCompletion

@[expose] public section
namespace PaperV.UnitBoundary
open Finset
variable {α R : Type*} [DecidableEq α] [DecidableEq R]

/-- The exact unit-boundary formula without a total representative-function input.
The empty object universe is included. -/
theorem completion_optimal_unconditional (res : α → Finset R)
    (Q D : Finset α) (SR : Finset R) (cfg : Config res Q D SR) :
    packOpt res (Q ∪ D) = (Z res Q SR).card + (B res Q SR).card +
      nuAvoid res D (B res Q SR) := by
  classical
  by_cases h : Nonempty α
  · letI := h
    letI : Inhabited α := Classical.inhabited_of_nonempty h
    obtain ⟨reps⟩ := exists_reps res Q SR
    exact unitBoundary_completion_optimal cfg reps
  · have hempty : ∀ S : Finset α, S = ∅ := by
      intro S
      apply Finset.eq_empty_of_forall_notMem
      intro a ha
      exact h ⟨a⟩
    simp [hempty Q, hempty D, packOpt, Z, B, nuAvoid, ResFeasible]

/-- Endpoint transport as an actual feasible packing, also for an empty object
universe. `R1` is the chosen outer representative family. -/
theorem exists_endpoint_repacking (res : α → Finset R)
    (Q0 Q1 D : Finset α) (SR : Finset R)
    (cfg0 : Config res Q0 D SR) (cfg1 : Config res Q1 D SR)
    (C0 : Finset α) (hC0 : C0 ⊆ D) (hf : ResFeasible res C0)
    (hav : ∀ d ∈ C0, Disjoint (res d) (B res Q0 SR)) :
    ∃ R1 P1 : Finset α,
      R1 ⊆ Q1 \ Z res Q1 SR ∧
      P1 = Z res Q1 SR ∪ R1 ∪ keptCentral res C0 (B res Q1 SR) ∧
      ResFeasible res P1 ∧ P1 ⊆ Q1 ∪ D ∧
      (∃ h ≤ (B res Q1 SR \ B res Q0 SR).card,
        P1.card + h = (Z res Q1 SR).card + (B res Q1 SR).card + C0.card) ∧
      (Z res Q0 SR).card + (B res Q0 SR).card + C0.card + (Z res Q1 SR).card ≤
        P1.card + (Z res Q0 SR).card + (B res Q0 SR \ B res Q1 SR).card := by
  classical
  by_cases h : Nonempty α
  · letI := h
    letI : Inhabited α := Classical.inhabited_of_nonempty h
    obtain ⟨reps0⟩ := exists_reps res Q0 SR
    obtain ⟨reps1⟩ := exists_reps res Q1 SR
    obtain ⟨hfeas, hsub, hcard, hbound⟩ :=
      endpoint_repacking_card_bound cfg0 cfg1 reps0 reps1 hC0 hf hav
    rw [card_normPack cfg0 reps0 hC0] at hbound
    exact ⟨repSet reps1, normPack reps1 (keptCentral res C0 (B res Q1 SR)),
      repSet_subset reps1, rfl, hfeas, hsub, hcard, hbound⟩
  · have hempty : ∀ S : Finset α, S = ∅ := by
      intro S
      apply Finset.eq_empty_of_forall_notMem
      intro a ha
      exact h ⟨a⟩
    refine ⟨∅, ∅, ?_⟩
    simp [hempty Q0, hempty Q1, hempty D, hempty C0, Z, B, keptCentral,
      ResFeasible]
end PaperV.UnitBoundary
