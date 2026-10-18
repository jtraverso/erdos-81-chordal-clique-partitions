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
Paper V, F8. The actual copy image multiset and a physical RealCert supply the
integral part of the gap budget. Fractional slack is retained explicitly.
-/
module

public import PaperV.MixedCopyFrac
public import PaperV.Realizer

import Lean.Elab.Tactic.NormCast
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section

open Finset SimpleGraph

namespace PaperV.MixedBudget

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def gap (G : SimpleGraph V) [DecidableRel G.Adj] (gain : ℕ → ℕ) : ℝ :=
  Mixed.Wstar G gain - (wNu (mixedCS G) (mixedWeight G gain) : ℝ)

noncomputable def fractionalSlack (G : SimpleGraph V) [DecidableRel G.Adj]
    (v u : V) (gain : ℕ → ℕ) : ℝ :=
  Mixed.Wstar G gain -
    (Mixed.Wstar (copyGraph G v u) gain + Mixed.Wstar (copyGraph G u v) gain) / 2

theorem fractionalSlack_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (v u : V) (huv : ¬ G.Adj u v) (gain : ℕ → ℕ) :
    0 ≤ fractionalSlack G v u gain := by
  have h := Mixed.mixed_copy_fractional G v u huv gain
  unfold fractionalSlack
  linarith

/-- F8 for any nonnegative integer gains depending on clique size, hence for
the physical mixed K3/K4 gains 2 and 5. The two input sets really are optimal
physical packings, and the certificate is over their actual mapped occurrences. -/
theorem mixed_copy_gap_budget (G : SimpleGraph V) [DecidableRel G.Adj]
    (v u : V) (huv : ¬ G.Adj u v) (gain : ℕ → ℕ)
    (P₁ : Finset (mixedCS (copyGraph G v u)).O)
    (P₂ : Finset (mixedCS (copyGraph G u v)).O)
    (_hP₁ : CSFeasible (mixedCS (copyGraph G v u)) P₁)
    (_hP₂ : CSFeasible (mixedCS (copyGraph G u v)) P₂)
    (hopt₁ : packGain (copyGraph G v u) gain P₁ =
      wNu (mixedCS (copyGraph G v u)) (mixedWeight (copyGraph G v u) gain))
    (hopt₂ : packGain (copyGraph G u v) gain P₂ =
      wNu (mixedCS (copyGraph G u v)) (mixedWeight (copyGraph G u v) gain))
    (cert : RealCert (mixedCS G) (mixedCS G) (mixedWeight G gain) (mixedWeight G gain)
      (imageMultiset G v u huv (fun h => huv h.symm) P₁ P₂) 2) :
    0 ≤ fractionalSlack G v u gain ∧
      gap G gain ≤
        (gap (copyGraph G v u) gain + gap (copyGraph G u v) gain) / 2 +
          fractionalSlack G v u gain + (cert.cost : ℝ) / 2 := by
  have hN := realizable_transfer_cert (by norm_num : 1 ≤ 2) cert
  rw [wMultSize_imageMultiset, hopt₁, hopt₂] at hN
  have hR :
      (wNu (mixedCS (copyGraph G v u)) (mixedWeight (copyGraph G v u) gain) : ℝ) +
      (wNu (mixedCS (copyGraph G u v)) (mixedWeight (copyGraph G u v) gain) : ℝ) ≤
      2 * (wNu (mixedCS G) (mixedWeight G gain) : ℝ) + (cert.cost : ℝ) := by
    exact_mod_cast hN
  refine ⟨fractionalSlack_nonneg G v u huv gain, ?_⟩
  unfold gap fractionalSlack
  linarith

/-- A finite labeled binary copy tree. At every branch the children have half
of their parent's weight; its recursive sums encode 2^(-depth). -/
inductive CopyTree (α : Type*) where
  | leaf : α → CopyTree α
  | node : α → CopyTree α → CopyTree α → CopyTree α

namespace CopyTree

variable {α : Type*}

def root : CopyTree α → α
  | .leaf a => a
  | .node a _ _ => a

def leaves (f : α → ℝ) : CopyTree α → ℝ
  | .leaf a => f a
  | .node _ l r => (leaves f l + leaves f r) / 2

def internal (f : α → ℝ) : CopyTree α → ℝ
  | .leaf _ => 0
  | .node a l r => f a + (internal f l + internal f r) / 2

def valid (Γ δ C : α → ℝ) : CopyTree α → Prop
  | .leaf _ => True
  | .node a l r =>
      Γ a ≤ (Γ l.root + Γ r.root) / 2 + δ a + C a / 2 ∧
      valid Γ δ C l ∧ valid Γ δ C r

/-- F8a: summing the certified one-step inequalities with the exact depth
weights. No bound on the accumulated slack or cost is assumed or concluded. -/
theorem gap_budget (Γ δ C : α → ℝ) (t : CopyTree α) (h : t.valid Γ δ C) :
    Γ t.root ≤ t.leaves Γ + t.internal δ + t.internal C / 2 := by
  induction t with
  | leaf a => simp [root, leaves, internal]
  | node a l r hl hr =>
    have hb := h.1
    have hL := hl h.2.1
    have hR := hr h.2.2
    simp only [root, leaves, internal]
    linarith

/-- Sum of the actual one-step fractional deficits on the finite copy tree. -/
def slack (F : α → ℝ) : CopyTree α → ℝ
  | .leaf _ => 0
  | .node a l r => F a - (F l.root + F r.root) / 2 + (slack F l + slack F r) / 2

/-- Exact telescoping identity for fractional slack; no asymptotic estimate is hidden. -/
theorem slack_telescopes (F : α → ℝ) (t : CopyTree α) :
    t.slack F = F t.root - t.leaves F := by
  induction t with
  | leaf a => simp [slack, root, leaves]
  | node a l r hl hr =>
    simp only [slack, root, leaves, hl, hr]
    ring

end CopyTree

end PaperV.MixedBudget
