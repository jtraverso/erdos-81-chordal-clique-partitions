/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Author: Juan Pablo Traverso Gianini
This attribution identifies the author of this series formalization.
Existing mathematical, tool-assistance and third-party credits are retained below.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ChordalStabilityNote

/-- The split baseline as a rational expression. -/
def baseline (n p : ℚ) : ℚ := p * (n - p) - p * (p - 1) / 2

/-- Scalar entry budget from the physical near ledger. No existence input is hidden here. -/
theorem entry_budget {n p M d c L m A : ℚ}
    (hc : c = M - d) (hcL : c ≤ L)
    (hledger : L ≤ baseline n p - m / 20 - A / 2)
    (hbase : baseline n p ≤ M) (hm : 0 ≤ m) (hA : 0 ≤ A) :
    M - d ≤ baseline n p ∧ m + A ≤ 20 * d := by
  constructor <;> linarith

/-- The completed-square identity, independent of floors or graph conventions. -/
theorem square_identity (n p : ℚ) :
    (6 * p - 2 * n - 1)^2 = (2 * n + 1)^2 - 24 * baseline n p := by
  unfold baseline
  ring

/-- Near-optimality forces the root size into the coarse interval needed by VI. -/
theorem root_window {n p M d : ℚ} (hn : 100 ≤ n) (hd : d ≤ n / 2000)
    (hfloor : n * (n + 1) / 6 - 1 ≤ M)
    (hbase : M - d ≤ baseline n p) :
    (6 * p - 2 * n - 1)^2 ≤ 24 * d + 25 ∧
    3 * n / 10 ≤ p ∧ p ≤ 2 * n / 5 := by
  have hs : (6 * p - 2 * n - 1)^2 ≤ 24 * d + 25 := by
    rw [square_identity]
    nlinarith
  have hsmall : (6 * p - 2 * n - 1)^2 ≤ n^2 / 100 := by
    have hnprod : 0 ≤ (n - 100) * n := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hlo : -n / 10 ≤ 6 * p - 2 * n - 1 := by
    by_contra h
    push_neg at h
    nlinarith [sq_nonneg (6 * p - 2 * n - 1 + n / 10)]
  have hhi : 6 * p - 2 * n - 1 ≤ n / 10 := by
    by_contra h
    push_neg at h
    nlinarith [sq_nonneg (6 * p - 2 * n - 1 - n / 10)]
  exact ⟨hs, by linarith, by linarith⟩

/-- The linear deficit budget activates the t=4 local capacity window. -/
theorem local_capacity_window {n p h d : ℚ}
    (hd : d ≤ n / 2000) (hh : h ≤ 20 * d)
    (hp0 : 3 * n / 10 ≤ p) (hp1 : p ≤ 2 * n / 5) (hn : 0 ≤ n) :
    p + 18 * h ≤ n - p ∧ n - p + 36 * h ≤ 4 * p := by
  constructor <;> linarith

/-- After exact local attainment, the entry factor twenty disappears. -/
theorem exact_deficit_edit {M B c d A m : ℚ}
    (hc : c = B - A - 2 * m) (hd : d = M - c)
    (hB : B ≤ M) (hm : 0 ≤ m) :
    d = (M - B) + A + 2 * m ∧ A + m ≤ d := by
  constructor <;> linarith

end ChordalStabilityNote

#print axioms ChordalStabilityNote.entry_budget
#print axioms ChordalStabilityNote.root_window
#print axioms ChordalStabilityNote.local_capacity_window
#print axioms ChordalStabilityNote.exact_deficit_edit
