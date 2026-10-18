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
/- A local corollary covering the second complete-split extremal size at n = 3k+1. -/
module
public import PaperVIOpt.Parametric

@[expose] public section
namespace PaperVI.Research
open Finset

/-- Both complete-split core sizes k and k+1 have baseline M(3k+1). -/
theorem second_split_baseline (k : ℕ) :
    ((k+1 : ℕ) : ℤ)*(2*k) - ((k+1).choose 2 : ℤ) = (Mval (3*k+1) : ℤ) := by
  have hM := Mval_eq (3*k+1)
  have hp : (3*k+1+1)/3=k := by omega
  have hq : 3*k+1-k=2*k+1 := by omega
  rw [hp,hq] at hM
  have hc := two_mul_choose_two k
  have hc' := two_mul_choose_two (k+1)
  push_cast at hM hc' ⊢
  nlinarith

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact local formula around the second extremal core, omitted by p=floor((n+1)/3).
The threshold p≥18h+2 pays for q=2p-2 in the same parametric construction. -/
theorem second_core_formula (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) (k : ℕ) (hn : Fintype.card V=3*k+1) (hP : P.card=k+1)
    (hh : 18*editDegree G P+2 ≤ P.card) :
    (cp G : ℤ) = (Mval (Fintype.card V) : ℤ)+Cdef G P-Adef G P-2*mCount G P := by
  have hq : Pᶜ.card=2*k := by rw [card_compl,hn,hP]; omega
  have hlow : P.card+(4*4+2)*editDegree G P ≤ Pᶜ.card := by omega
  have hup : Pᶜ.card+4*(4+5)*editDegree G P ≤ 4*P.card := by omega
  obtain ⟨_,hformula⟩ := cp_window_K4_simple G P 4 (by norm_num) hlow hup
  have hbase : (P.card : ℤ)*((Fintype.card V : ℤ)-P.card)-(P.card.choose 2 : ℤ) =
      (Mval (Fintype.card V) : ℤ) := by
    rw [hn,hP]
    have hb := second_split_baseline k
    push_cast at hb ⊢
    nlinarith
  linarith

end PaperVI.Research
