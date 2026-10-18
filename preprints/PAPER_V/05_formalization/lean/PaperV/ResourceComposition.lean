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

/- Paper V, F2: portfolios and genuinely resource-compatible unions. -/
module

public import PaperV.TwoErrorCertificate
import Mathlib.Tactic.FieldSimp

import Lean.Elab.Tactic.NormCast
import Mathlib.Tactic.Linarith

@[expose] public section

open Finset

namespace PaperV.ResourceCertificate

variable {I E : Type*} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]

namespace System

variable (R : System I E)

/-- Nonempty resources prevent an object from occurring on both sides. -/
theorem disjoint_of_cross_resources {P Q : Finset I}
    (hcross : ∀ a ∈ P, ∀ b ∈ Q, Disjoint (R.resources a) (R.resources b)) :
    Disjoint P Q := by
  rw [Finset.disjoint_left]
  intro o hoP hoQ
  obtain ⟨e, he⟩ := R.nonempty o
  exact Finset.disjoint_left.mp (hcross o hoP o hoQ) he he

/-- The feasibility of the union is proved from the physical cross-resource condition. -/
theorem packing_union {P Q : Finset I} (hP : R.Packing P) (hQ : R.Packing Q)
    (hcross : ∀ a ∈ P, ∀ b ∈ Q, Disjoint (R.resources a) (R.resources b)) :
    R.Packing (P ∪ Q) := by
  intro a ha b hb hab
  rcases Finset.mem_union.mp ha with ha | ha <;>
    rcases Finset.mem_union.mp hb with hb | hb
  · exact hP ha hb hab
  · exact hcross a ha b hb
  · exact (hcross b hb a ha).symm
  · exact hQ ha hb hab

theorem gain_union (w : I → ℚ) {P Q : Finset I}
    (hcross : ∀ a ∈ P, ∀ b ∈ Q, Disjoint (R.resources a) (R.resources b)) :
    R.gain w (P ∪ Q) = R.gain w P + R.gain w Q := by
  exact Finset.sum_union (R.disjoint_of_cross_resources hcross)

theorem packing_biUnion {J : Type*} [DecidableEq J] (js : Finset J)
    (out : J → Finset I) (hpack : ∀ j ∈ js, R.Packing (out j))
    (hcross : ∀ i ∈ js, ∀ j ∈ js, i ≠ j →
      ∀ a ∈ out i, ∀ b ∈ out j, Disjoint (R.resources a) (R.resources b)) :
    R.Packing (js.biUnion out) := by
  intro a ha b hb hab
  obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨j, hj, hbj⟩ := Finset.mem_biUnion.mp hb
  by_cases hij : i = j
  · subst j
    exact hpack i hi hai hbj hab
  · exact hcross i hi j hj hij a hai b hbj

theorem gain_biUnion {J : Type*} [DecidableEq J] (js : Finset J)
    (out : J → Finset I) (w : I → ℚ)
    (hcross : ∀ i ∈ js, ∀ j ∈ js, i ≠ j →
      ∀ a ∈ out i, ∀ b ∈ out j, Disjoint (R.resources a) (R.resources b)) :
    R.gain w (js.biUnion out) = ∑ j ∈ js, R.gain w (out j) := by
  unfold gain
  apply Finset.sum_biUnion
  intro i hi j hj hij
  exact R.disjoint_of_cross_resources (hcross i hi j hj hij)

/-- Additive losses for a finite family of physical realizers. -/
theorem compatible_realization_union {J : Type*} [DecidableEq J] (js : Finset J)
    (out : J → Finset I) (w : I → ℚ) (mass loss : J → ℚ)
    (hpack : ∀ j ∈ js, R.Packing (out j))
    (hcross : ∀ i ∈ js, ∀ j ∈ js, i ≠ j →
      ∀ a ∈ out i, ∀ b ∈ out j, Disjoint (R.resources a) (R.resources b))
    (hreal : ∀ j ∈ js, mass j ≤ R.gain w (out j) + loss j) :
    R.Packing (js.biUnion out) ∧
      ∑ j ∈ js, mass j ≤ R.gain w (js.biUnion out) + ∑ j ∈ js, loss j := by
  refine ⟨R.packing_biUnion js out hpack hcross, ?_⟩
  rw [R.gain_biUnion js out w hcross]
  simpa only [Finset.sum_add_distrib] using Finset.sum_le_sum hreal

end System

open System
variable {R : System I E}

/-- RCT stated directly for a rational multiplicity realization certificate. -/
theorem Realization.exists_heavy_out {w : I → ℚ} {X : I → ℕ} {q : ℕ}
    (c : Realization R w X q) (hq : 0 < q) :
    ∃ i : Fin q, R.mass w X ≤ c.cost + (q : ℚ) * R.gain w (c.out i) := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin q))
    (fun i => R.gain w (c.out i)) ⟨⟨0, hq⟩, Finset.mem_univ _⟩
  refine ⟨i, ?_⟩
  rw [c.mass_split]
  have hb := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin q))) => c.bound j)
  have hm : (∑ j : Fin q, R.gain w (c.out j)) ≤ (q : ℚ) * R.gain w (c.out i) := by
    calc
      _ ≤ ∑ _j : Fin q, R.gain w (c.out i) :=
        Finset.sum_le_sum (fun j _ => hi j (Finset.mem_univ _))
      _ = _ := by simp
  rw [Finset.sum_add_distrib] at hb
  unfold Realization.cost
  linarith

/-- Select the minimum-cost certificate over a nonempty finite portfolio,
then an actual physical output of that certificate. The target and weights stay fixed. -/
theorem portfolio_selection {J : Type*} [Fintype J] [Nonempty J]
    {w : I → ℚ} {X : I → ℕ} {q : ℕ} (hq : 0 < q)
    (cert : J → Realization R w X q) :
    ∃ j : J, (∀ k, (cert j).cost ≤ (cert k).cost) ∧
      ∃ i : Fin q, R.Packing ((cert j).out i) ∧
        R.mass w X / q - (cert j).cost / q ≤ R.gain w ((cert j).out i) := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image (Finset.univ : Finset J)
    (fun j => (cert j).cost) Finset.univ_nonempty
  obtain ⟨i, hi⟩ := (cert j).exists_heavy_out hq
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  refine ⟨j, fun k => hj k (Finset.mem_univ _), i, (cert j).feasible i, ?_⟩
  have hdiv := (div_le_div_of_nonneg_right hi hqQ.le)
  have hcancel : (q : ℚ) * R.gain w ((cert j).out i) / q = R.gain w ((cert j).out i) := by
    field_simp [hqQ.ne']
  rw [add_div, hcancel] at hdiv
  linarith

end PaperV.ResourceCertificate
