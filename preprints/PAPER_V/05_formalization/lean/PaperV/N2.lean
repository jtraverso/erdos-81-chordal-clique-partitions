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
Improvement N2: a-priori integrality-gap bound for the host-clique master matching LP.
Under a half-integral optimum, ν ≥ (2/3)·μ*_mat, equivalently μ*_mat − ν ≤ μ*_mat/3.

NOTE. In the pure-profile specialization Proposition 4.3 already establishes the *exact* identity
`μ*_mat = ν` (`prop43_muMat`, `prop43_nu`), so the ⅓-gap is trivially satisfied (the gap is 0) and
the half-integrality/optimality hypotheses are unused. The theorem is retained as the requested N2
statement, but here it carries no content beyond Prop 4.3 — a genuine ⅓-gap would require a model
with `μ*_mat > ν`, which the pure-profile host-clique model does not exhibit. This makes N2
unconditional and Brooks-independent (no triangle-free/subcubic colouring route is needed).
-/
module

public import PaperV.PureProfile

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Set

@[expose] public section

open Finset

namespace PaperV.PureProfile

variable (m s : ℕ)

/-- A half-integral point: every coordinate is `0`, `1/2`, or `1`. -/
def IsHalfIntegral (x : Obj m s → ℝ) : Prop := ∀ o, x o = 0 ∨ x o = 1 / 2 ∨ x o = 1

/-- **Zero integrality gap in the pure-profile master LP** (the real content).  With the odd-set
(blossom) inequalities present in `MasterFeasible`, Proposition 4.3 forces `μ*_mat = ν` exactly:
the host-clique master matching LP is integral, so its integrality gap vanishes. -/
theorem hostClique_gap_zero : muMat m s = (nu m s : ℝ) := by
  rw [prop43_muMat, prop43_nu]

/-- **N2 (a-priori host-clique ⅓-gap), as a COROLLARY of `hostClique_gap_zero`.**  If the master
matching LP has a half-integral optimum, then `μ*_mat − ν ≤ μ*_mat / 3` (i.e. `ν ≥ (2/3) μ*_mat`).

In the pure-profile model this is *vacuous*: by `hostClique_gap_zero` the gap `μ*_mat − ν` is
already `0`, so `0 ≤ μ*_mat/3` holds for free and the half-integrality/optimality hypotheses are
unused.  A genuine (tight) ⅓-gap requires dropping the odd-set constraints — see `N2Gap.lean`,
where the triangle instance realises `μ*_deg − ν = μ*_deg/3` with `μ*_deg > ν`. -/
theorem hostClique_gap_le_third (x : Obj m s → ℝ)
    (hmf : MasterFeasible m s x) (hhalf : IsHalfIntegral m s x)
    (hopt : (∑ o, x o) = muMat m s) :
    muMat m s - (nu m s : ℝ) ≤ muMat m s / 3 := by
  rw [hostClique_gap_zero]
  have hn : (0 : ℝ) ≤ (nu m s : ℝ) := by positivity
  linarith

end PaperV.PureProfile
