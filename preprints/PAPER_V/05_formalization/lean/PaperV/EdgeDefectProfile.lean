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
Paper IV — The edge-colouring defect profile `q ↦ D_q(L(G))` is determined by the Class 1/2 bit.

Combining `Dq_lineGraph_eq_zero_iff_edgeChromatic` (D_q(L(G)) = 0 ↔ χ'(G) ≤ q) with the Vizing
dichotomy `edgeChromaticNumber_eq_maxDegree_or` (χ' = Δ ∨ χ' = Δ+1):

  D_q(L(G)) = 0  ↔  Δ+1 ≤ q  ∨  (q = Δ ∧ G is Class 1),
  D_q(L(G)) > 0  ↔  q < Δ    ∨  (q = Δ ∧ G is Class 2).

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.Vizing

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

@[expose] public section

open SimpleGraph

namespace PaperV

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `G` is **Class 1** when `χ'(G) = Δ(G)`. -/
def IsClassOne (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  edgeChromaticNumber G = (G.maxDegree : ℕ∞)

/-- `G` is **Class 2** when `χ'(G) = Δ(G) + 1`. -/
def IsClassTwo (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  edgeChromaticNumber G = (G.maxDegree : ℕ∞) + 1

theorem isClassOne_or_isClassTwo (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] :
    IsClassOne G ∨ IsClassTwo G :=
  edgeChromaticNumber_eq_maxDegree_or G

omit [DecidableEq V] in
theorem not_isClassOne_and_isClassTwo (G : SimpleGraph V) [DecidableRel G.Adj] :
    ¬ (IsClassOne G ∧ IsClassTwo G) := by
  rintro ⟨h1, h2⟩
  unfold IsClassOne at h1
  unfold IsClassTwo at h2
  rw [h1] at h2
  have h3 : ((G.maxDegree : ℕ) : ℕ∞) = ((G.maxDegree + 1 : ℕ) : ℕ∞) := by
    rw [Nat.cast_add, Nat.cast_one]; exact h2
  have h4 : G.maxDegree = G.maxDegree + 1 := ENat.coe_inj.mp h3
  omega

/-- **Edge-defect profile.** `D_q(L(G)) = 0 ↔ Δ(G)+1 ≤ q ∨ (q = Δ(G) ∧ G Class 1)`. -/
theorem Dq_lineGraph_eq_zero_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (G.lineGraph).Adj] [Nonempty V] {q : ℕ} (hq : 1 ≤ q) :
    Dq (G.lineGraph) q = 0 ↔ (G.maxDegree + 1 ≤ q ∨ (q = G.maxDegree ∧ IsClassOne G)) := by
  rw [Dq_lineGraph_eq_zero_iff_edgeChromatic G hq]
  unfold IsClassOne
  rcases edgeChromaticNumber_eq_maxDegree_or G with h | h
  · rw [h]
    constructor
    · intro hle
      have hle' : G.maxDegree ≤ q := by exact_mod_cast hle
      rcases Nat.lt_or_ge G.maxDegree q with hlt | hge
      · exact Or.inl hlt
      · exact Or.inr ⟨by omega, rfl⟩
    · rintro (hlt | ⟨hEq, _⟩)
      · exact_mod_cast (by omega : G.maxDegree ≤ q)
      · exact_mod_cast (by omega : G.maxDegree ≤ q)
  · rw [h]
    have hcast : (G.maxDegree : ℕ∞) + 1 = ((G.maxDegree + 1 : ℕ) : ℕ∞) := by push_cast; ring
    rw [hcast]
    constructor
    · intro hle
      exact Or.inl (by exact_mod_cast hle)
    · rintro (hle | ⟨hEq, hcls⟩)
      · exact_mod_cast hle
      · exfalso
        have h3 : ((G.maxDegree + 1 : ℕ) : ℕ∞) = ((G.maxDegree : ℕ) : ℕ∞) := hcls
        have h4 : G.maxDegree + 1 = G.maxDegree := ENat.coe_inj.mp h3
        omega

/-- `D_q(L(G)) > 0 ↔ q < Δ(G) ∨ (q = Δ(G) ∧ G Class 2)`: the whole profile is pinned by the single
Class 1 / Class 2 bit at `q = Δ`. -/
theorem Dq_lineGraph_pos_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (G.lineGraph).Adj] [Nonempty V] {q : ℕ} (hq : 1 ≤ q) :
    0 < Dq (G.lineGraph) q ↔ (q < G.maxDegree ∨ (q = G.maxDegree ∧ IsClassTwo G)) := by
  rw [Nat.pos_iff_ne_zero, Ne, Dq_lineGraph_eq_zero_iff G hq]
  rcases isClassOne_or_isClassTwo G with h1 | h2
  · have hn2 : ¬ IsClassTwo G := fun h2 => not_isClassOne_and_isClassTwo G ⟨h1, h2⟩
    constructor
    · intro hn
      push_neg at hn
      rcases Nat.lt_or_ge q G.maxDegree with hlt | hge
      · exact Or.inl hlt
      · exact absurd h1 (hn.2 (by omega))
    · rintro (hlt | ⟨_, h2⟩)
      · push_neg; exact ⟨by omega, fun h => absurd h (by omega)⟩
      · exact absurd h2 hn2
  · have hn1 : ¬ IsClassOne G := fun h1 => not_isClassOne_and_isClassTwo G ⟨h1, h2⟩
    constructor
    · intro hn
      push_neg at hn
      rcases Nat.lt_or_ge q G.maxDegree with hlt | hge
      · exact Or.inl hlt
      · exact Or.inr ⟨by omega, h2⟩
    · rintro (hlt | ⟨hEq, _⟩)
      · push_neg; exact ⟨by omega, fun _ => hn1⟩
      · push_neg; exact ⟨by omega, fun _ => hn1⟩

end PaperV
