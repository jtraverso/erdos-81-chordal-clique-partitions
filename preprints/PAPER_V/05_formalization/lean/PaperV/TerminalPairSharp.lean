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
Paper V — Sharper constant in the coarse form of P4-133.

`p4_133_existence` gives `⌊a·|Pall|/m⌋ ≤ |S'| + 4 + 10·|X|`. The recorded coarse (division-free) form
`p4_133_existence_coarse` weakens this to `a·|Pall| ≤ m·|S'| + m·(4 + 17·|X|)`, absorbing the floor into the
coefficient of `|X|` (using `|X| ≥ 1`). Clearing the floor exactly instead gives the strict bound

  `a·|Pall| < m·(|S'| + 5 + 10·|X|)`,   hence   `a·|Pall| ≤ m·|S'| + m·(5 + 10·|X|)`,

which is sharper than the coarse form whenever `|X| ≥ 1` (`5 + 10|X| ≤ 4 + 17|X|`) and does not need `Pall ≠ ∅`.
The coefficient `10` of `|X|` and the additive `4` come from the rounding layer (Beck–Fiala with four roles) and are
not touched here.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.TerminalPairAssembly

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith

@[expose] public section

open Finset SimpleGraph

namespace PaperV.TerminalPair

variable {ι B : Type*} [Fintype ι] [DecidableEq ι] [Fintype B] [DecidableEq B]

/-- **P4-133, sharp division-free form:** `a·|Pall| < m·(|S'| + 5 + 10·|X|)`. -/
theorem p4_133_existence_sharp
    (emap : ι → Fin 2 → Sym2 B) (Pall : Finset ι)
    (hinj : Set.InjOn (fun p : ι × Fin 2 => emap p.1 p.2) {p | p.1 ∈ Pall})
    (hloop : ∀ P ∈ Pall, ∀ i, ¬ (emap P i).IsDiag)
    (a m : ℕ) (ha1 : 1 ≤ a) (ham : a ≤ m) (X : Finset B)
    (hcover : ∀ P ∈ Pall, ∀ i, ∃ w ∈ X, w ∈ emap P i)
    (hbaseDeg : (termGraph emap Pall).maxDegree ≤ m) :
    ∃ S' : Finset ι, S' ⊆ Pall ∧
      ((termGraph emap S').lineGraph).Colorable a ∧
      a * Pall.card < m * (S'.card + 5 + 10 * X.card) := by
  obtain ⟨S', hS'sub, hcolor, hcount⟩ :=
    p4_133_existence emap Pall hinj hloop a m ha1 ham X hcover hbaseDeg
  refine ⟨S', hS'sub, hcolor, ?_⟩
  have hm : 0 < m := lt_of_lt_of_le ha1 ham
  have hfloor : a * Pall.card < m * ((a * Pall.card) / m + 1) := Nat.lt_mul_div_succ _ hm
  have hmono : m * ((a * Pall.card) / m + 1) ≤ m * (S'.card + 5 + 10 * X.card) :=
    Nat.mul_le_mul_left m (by omega)
  exact lt_of_lt_of_le hfloor hmono

/-- The sharp form implies the recorded coarse form (`5 + 10|X| ≤ 4 + 17|X|` once `|X| ≥ 1`, and `X ≠ ∅` when
`Pall ≠ ∅` by `hcover`); with `Pall = ∅` both sides vanish. -/
theorem p4_133_sharp_le_coarse (m S' X : ℕ) (hX : 1 ≤ X) :
    m * (S' + 5 + 10 * X) ≤ m * S' + m * (4 + 17 * X) := by
  nlinarith

end PaperV.TerminalPair
