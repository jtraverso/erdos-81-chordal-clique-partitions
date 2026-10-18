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

public import PaperV.Vizing.Main
public import PaperV.ChromaticIndex

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Lift
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set

@[expose] public section

/-!
# Vizing's theorem (upper bound), homed into Paper IV

`χ'(G) ≤ Δ(G)+1` for finite simple graphs, phrased via the line graph. Not in Mathlib;
proved from first principles (fan + Kempe) in `PaperV.Vizing.*`. Closes the §3.6 gap:
the upper Vizing bound the manuscript previously declared unavailable.
-/

open SimpleGraph

namespace PaperV

theorem vizing_lineGraph_chromaticNumber_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.lineGraph).chromaticNumber ≤ (G.maxDegree : ℕ∞) + 1 := by
  have h : (G.lineGraph).Colorable (G.maxDegree + 1) := Vizing.lineGraph_colorable G
  have := h.chromaticNumber_le
  rwa [Nat.cast_add, Nat.cast_one] at this

/-- Vizing's upper bound in terms of the paper's `edgeChromaticNumber` (§3.6). -/
theorem edgeChromaticNumber_le_maxDegree_add_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeChromaticNumber G ≤ (G.maxDegree : ℕ∞) + 1 :=
  vizing_lineGraph_chromaticNumber_le G


/-- **Vizing sandwich**: `Δ(G) ≤ χ'(G) ≤ Δ(G)+1`. -/
theorem edgeChromaticNumber_bounds {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.maxDegree : ℕ∞) ≤ edgeChromaticNumber G ∧
      edgeChromaticNumber G ≤ (G.maxDegree : ℕ∞) + 1 :=
  ⟨maxDegree_le_edgeChromaticNumber G, edgeChromaticNumber_le_maxDegree_add_one G⟩

/-- **Class 1 / Class 2 dichotomy** (Vizing): `χ'(G) = Δ(G)` or `χ'(G) = Δ(G)+1`. -/
theorem edgeChromaticNumber_eq_maxDegree_or {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeChromaticNumber G = (G.maxDegree : ℕ∞) ∨
      edgeChromaticNumber G = (G.maxDegree : ℕ∞) + 1 := by
  obtain ⟨hlo, hhi⟩ := edgeChromaticNumber_bounds G
  set d := G.maxDegree with hd
  set c := edgeChromaticNumber G with hc
  have hcast : (d : ℕ∞) + 1 = ((d + 1 : ℕ) : ℕ∞) := by push_cast; ring
  rw [hcast] at hhi
  have hfin : c ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) hhi
  lift c to ℕ using hfin with cn
  have h1 : d ≤ cn := by exact_mod_cast hlo
  have h2 : cn ≤ d + 1 := by exact_mod_cast hhi
  rcases (show cn = d ∨ cn = d + 1 by omega) with h | h
  · left; rw [h]
  · right; rw [h]; push_cast; ring


end PaperV
