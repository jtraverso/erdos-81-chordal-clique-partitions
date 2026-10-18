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
Paper V — LP → multiset bridge (wave 2a′, item 3; "Theorem D-lite").

The transfer engine is stated for multisets `X : O → ℕ`. Downstream papers start from a fractional
optimum `x : O → K` (`K` an ordered field). If `x` is `q`-integral, `q · x(o) = X(o) ∈ ℕ`, then

  `Σ_o w(o) x(o) = |X|_w / q`,      `x ≤ 1 ⇒ X is a q-multiset`,

and every transfer statement for `X` reads, for `x`:

  `Σ w x ≤ ν_w(C) + D_q^w(H[X])/q`          (weighted transfer),
  `Σ w x ≤ ν_{w_P}(P) + cost/q`             (RCT, any realizability certificate),
  `Σ w x ≤ ν_{w_P}(P) + D_{q,ℛ}^w/q`        (RDT).

This is the bridge `μ* − ν ≤ D/q` of the design note in `ConflictGraph.lean`, made explicit.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.RealizabilityDefect

import Lean.Elab.Tactic.NormCast
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

public import Mathlib.Algebra.Order.Field.Basic

@[expose] public section

open Finset

namespace PaperV

variable {C P : ConflictSystem} {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- `x` is `q`-integral with integer multiset `X`: `q · x(o) = X(o)` for every object. -/
def IsQIntegral (q : ℕ) (x : C.O → K) (X : C.O → ℕ) : Prop := ∀ o, (q : K) * x o = (X o : K)

/-- The `q`-integral rounding of a fractional point: `X(o) = q · x(o)` (when integral). -/
theorem lp_value_eq {q : ℕ} (hq : 0 < q) {x : C.O → K} {X : C.O → ℕ} (hx : IsQIntegral q x X)
    (w : C.O → ℕ) : ∑ o, (w o : K) * x o = (wMultSize C w X : K) / q := by
  have hqK : (q : K) ≠ 0 := by exact_mod_cast hq.ne'
  rw [eq_div_iff hqK]
  unfold wMultSize
  push_cast
  rw [Finset.sum_mul]
  congr 1; ext o
  rw [← hx o]; ring

/-- Resource domination (`x ≤ 1`) makes `X` a `q`-multiset. -/
theorem isQMultiset_of_le_one {q : ℕ} {x : C.O → K} {X : C.O → ℕ} (hx : IsQIntegral q x X)
    (hle : ∀ o, x o ≤ 1) : IsQMultiset C X q := by
  intro o
  have h := hx o
  have hq0 : (0 : K) ≤ q := by exact_mod_cast Nat.zero_le q
  have : (X o : K) ≤ q := by
    rw [← h]
    calc (q : K) * x o ≤ (q : K) * 1 := mul_le_mul_of_nonneg_left (hle o) hq0
      _ = q := mul_one _
  exact_mod_cast this

/-- Nonnegativity of `x` follows from integrality. -/
theorem nonneg_of_isQIntegral {q : ℕ} (hq : 0 < q) {x : C.O → K} {X : C.O → ℕ}
    (hx : IsQIntegral q x X) (o : C.O) : 0 ≤ x o := by
  have hqK : (0 : K) < q := by exact_mod_cast hq
  have h := hx o
  have : (0 : K) ≤ (q : K) * x o := by rw [h]; exact_mod_cast Nat.zero_le _
  exact (mul_nonneg_iff_of_pos_left hqK).mp this

/-- **LP form of the weighted transfer.** `Σ w x ≤ ν_w(C) + D_q^w(H[X])/q`. -/
theorem lp_transfer {q : ℕ} (hq : 1 ≤ q) {x : C.O → K} {X : C.O → ℕ} (hx : IsQIntegral q x X)
    (w : C.O → ℕ) :
    ∑ o, (w o : K) * x o ≤ (wNu C w : K) + (wDq C w X q : K) / q := by
  have hq0 : 0 < q := hq
  have hqK : (0 : K) < q := by exact_mod_cast hq0
  rw [lp_value_eq hq0 hx w]
  have h := transfer_q_weighted C w X q hq
  have h' : (wMultSize C w X : K) ≤ (q : K) * (wNu C w : K) + (wDq C w X q : K) := by
    exact_mod_cast h
  rw [div_le_iff₀ hqK]
  calc (wMultSize C w X : K) ≤ (q : K) * (wNu C w : K) + (wDq C w X q : K) := h'
    _ = ((wNu C w : K) + (wDq C w X q : K) / q) * q := by field_simp

/-- **LP form of RCT.** For any realizability certificate: `Σ w x ≤ ν_{w_P}(P) + cost/q`. -/
theorem lp_realizable_transfer {q : ℕ} (hq : 1 ≤ q) {x : C.O → K} {X : C.O → ℕ}
    (hx : IsQIntegral q x X) {w : C.O → ℕ} {wP : P.O → ℕ} (cert : RealCert C P w wP X q) :
    ∑ o, (w o : K) * x o ≤ (wNu P wP : K) + (cert.cost : K) / q := by
  have hq0 : 0 < q := hq
  have hqK : (0 : K) < q := by exact_mod_cast hq0
  rw [lp_value_eq hq0 hx w]
  have h := realizable_transfer_cert hq cert
  have h' : (wMultSize C w X : K) ≤ (q : K) * (wNu P wP : K) + (cert.cost : K) := by
    exact_mod_cast h
  rw [div_le_iff₀ hqK]
  calc (wMultSize C w X : K) ≤ (q : K) * (wNu P wP : K) + (cert.cost : K) := h'
    _ = ((wNu P wP : K) + (cert.cost : K) / q) * q := by field_simp

/-- **LP form of RDT.** `Σ w x ≤ ν_{w_P}(P) + D_{q,ℛ}^w/q` whenever an admissible certificate exists. -/
theorem lp_realizability_defect_transfer {q : ℕ} (hq : 1 ≤ q) {x : C.O → K} {X : C.O → ℕ}
    (hx : IsQIntegral q x X) {w : C.O → ℕ} {wP : P.O → ℕ} (R : RealizerClass C P w wP X)
    (hne : ∃ cert : RealCert C P w wP X q, cert.Admissible R) :
    ∑ o, (w o : K) * x o ≤ (wNu P wP : K) + (wRDq R q : K) / q := by
  have hq0 : 0 < q := hq
  have hqK : (0 : K) < q := by exact_mod_cast hq0
  rw [lp_value_eq hq0 hx w]
  have h := realizability_defect_transfer hq R hne
  have h' : (wMultSize C w X : K) ≤ (q : K) * (wNu P wP : K) + (wRDq R q : K) := by
    exact_mod_cast h
  rw [div_le_iff₀ hqK]
  calc (wMultSize C w X : K) ≤ (q : K) * (wNu P wP : K) + (wRDq R q : K) := h'
    _ = ((wNu P wP : K) + (wRDq R q : K) / q) * q := by field_simp

end PaperV
