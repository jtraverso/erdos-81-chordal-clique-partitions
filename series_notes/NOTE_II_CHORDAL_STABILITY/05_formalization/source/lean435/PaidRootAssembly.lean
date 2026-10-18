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

import PartitionAdapter
import WindowArithmetic
import GraphWindow
import PaperIV.SplitBaselineTarget
import PaperVIOpt.Parametric

namespace ChordalStabilityNote

open Finset PaperVI

def baselineInt (n p : ℕ) : ℤ := (p : ℤ) * ((n : ℤ) - p) - (p.choose 2 : ℤ)

theorem baselineInt_cast (n p : ℕ) :
    (baselineInt n p : ℚ) = baseline (n : ℚ) (p : ℚ) := by
  have h : 2 * (p.choose 2 : ℚ) = (p : ℚ) * ((p : ℚ) - 1) := by
    exact_mod_cast PaperVI.two_mul_choose_two p
  unfold baselineInt baseline
  push_cast
  nlinarith

theorem baselineInt_le_M (n p : ℕ) : baselineInt n p ≤ (Mval n : ℤ) := by
  have h := PaperIV.SplitBaselineTarget.splitBaseline_le_targetSize
    (show (baselineInt n p : ℚ) = PaperIV.splitBaseline n p from baselineInt_cast n p)
  exact h

theorem M_floor_lower (n : ℕ) :
    (n : ℚ) * ((n : ℚ) + 1) / 6 - 1 ≤ (Mval n : ℚ) := by
  have hr := Nat.mod_lt (n * (n + 1)) (by norm_num : 0 < 6)
  have hd := Nat.div_add_mod (n * (n + 1)) 6
  have hb : n * (n + 1) ≤ 6 * Mval n + 5 := by unfold Mval; omega
  have hbQ : (n : ℚ) * ((n : ℚ) + 1) ≤ 6 * (Mval n : ℚ) + 5 := by exact_mod_cast hb
  linarith

/-- The exact conclusions after entering the local window. This is a result
record, not an input assumption. -/
structure RootStability {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Finset (Fin n)) : Prop where
  isClique : G.IsClique (P : Set (Fin n))
  exactFormula : (cp G : ℤ) = baselineInt n P.card - Adef G P - 2 * mCount G P
  four : cp G = cpLe 4 G
  deficitFormula : (Mval n : ℤ) - cp G =
    ((Mval n : ℤ) - baselineInt n P.card) + Adef G P + 2 * mCount G P
  editIdentity : (editDistance G P : ℤ) = Adef G P + mCount G P
  editBound : (editDistance G P : ℤ) ≤ (Mval n : ℤ) - cp G
  square : (6 * (P.card : ℚ) - 2 * n - 1)^2 ≤
    24 * ((Mval n : ℚ) - cp G) + 25
  canonical : P = univ.filter (fun v => n < 2 * G.degree v)

/-- A genuine physical partition and its paid ledger activate the exact local
theorem. This intermediate theorem does not assert existence of its inputs. -/
theorem stability_of_paid_root {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P : Finset (Fin n)) (hP : G.IsClique (P : Set (Fin n)))
    (Bs : Finset (Finset (Fin n))) (hBs : PaperIV.Model.IsExactPartition G Bs)
    (hn : 100 ≤ n)
    (hdeficit : (Mval n : ℚ) - cp G ≤ (n : ℚ) / 2000)
    (hpaid : (Bs.card : ℚ) ≤ baseline n P.card - (mCount G P : ℚ) / 20 -
      (Adef G P : ℚ) / 2) : RootStability G P := by
  classical
  have hC := Cdef_eq_zero_of_clique P hP
  have hBz := baselineInt_le_M n P.card
  have hB : baseline (n : ℚ) (P.card : ℚ) ≤ (Mval n : ℚ) := by
    rw [← baselineInt_cast]
    exact_mod_cast hBz
  have hA : (0 : ℚ) ≤ (Adef G P : ℚ) := by
    have h := missingSpoke_card_eq_Adef (G := G) P
    have h0 : (0 : ℤ) ≤ Adef G P := by rw [← h]; positivity
    exact_mod_cast h0
  have hm : (0 : ℚ) ≤ mCount G P := Nat.cast_nonneg _
  have hcL : (cp G : ℚ) ≤ (Bs.card : ℚ) := by
    exact_mod_cast cp_le_physical_partition hBs
  have he := entry_budget (n := (n : ℚ)) (p := (P.card : ℚ))
    (M := (Mval n : ℚ)) (d := (Mval n : ℚ) - cp G)
    (c := (cp G : ℚ)) (L := (Bs.card : ℚ)) (m := (mCount G P : ℚ))
    (A := (Adef G P : ℚ)) (by ring) hcL hpaid hB hm hA
  have hr := root_window (n := (n : ℚ)) (p := (P.card : ℚ))
    (M := (Mval n : ℚ)) (d := (Mval n : ℚ) - cp G)
    (by exact_mod_cast hn) hdeficit (M_floor_lower n) he.1
  have hEditZ := editDistance_eq G P
  rw [hC, zero_add] at hEditZ
  have hEditQ : (editDistance G P : ℚ) = (Adef G P : ℚ) + mCount G P := by
    exact_mod_cast hEditZ
  have hdegree : (editDegree G P : ℚ) ≤ 20 * ((Mval n : ℚ) - cp G) := by
    have hg : (editDegree G P : ℚ) ≤ editDistance G P := by
      exact_mod_cast editDegree_le_editDistance G P
    rw [hEditQ] at hg
    linarith [he.2]
  have hw := local_capacity_window hdeficit hdegree hr.2.1 hr.2.2 (Nat.cast_nonneg n)
  have hpN : P.card ≤ n := by simpa using card_le_univ P
  have hq : (Pᶜ.card : ℚ) = (n : ℚ) - P.card := by
    rw [card_compl]
    simp only [Fintype.card_fin]
    exact Nat.cast_sub hpN
  have hlow : P.card + (4 * 4 + 2) * editDegree G P ≤ Pᶜ.card := by
    have hqL : (P.card : ℚ) + 18 * editDegree G P ≤ (Pᶜ.card : ℚ) := by
      rw [hq]; exact hw.1
    norm_num
    exact_mod_cast hqL
  have hupZ : (Pᶜ.card : ℤ) + 36 * editDegree G P ≤ 4 * P.card := by
    have hqU : (Pᶜ.card : ℚ) + 36 * editDegree G P ≤ 4 * P.card := by
      rw [hq]; exact hw.2
    exact_mod_cast hqU
  obtain ⟨_, hf, hfour, _⟩ := cp_window_K4 G P 4 (by norm_num) hlow (by
    have hh0 : (0 : ℤ) ≤ editDegree G P := by positivity
    norm_num
    nlinarith)
  have hf' : (cp G : ℤ) = baselineInt n P.card - Adef G P - 2 * mCount G P := by
    simpa [baselineInt, hC] using hf
  have hpRec : 5 * P.card ≤ 2 * Fintype.card (Fin n) := by
    have hpQ : 5 * (P.card : ℚ) ≤ 2 * (n : ℚ) := by linarith [hr.2.2]
    simpa using (show 5 * P.card ≤ 2 * n by exact_mod_cast hpQ)
  have hhRec : 100 * editDegree G P ≤ Fintype.card (Fin n) := by
    have hhQ : 100 * (editDegree G P : ℚ) ≤ (n : ℚ) := by linarith
    simpa using (show 100 * editDegree G P ≤ n by exact_mod_cast hhQ)
  refine ⟨hP, hf', hfour, ?_, hEditZ, ?_, hr.1, ?_⟩
  · linarith
  · have hmZ : (0 : ℤ) ≤ mCount G P := by positivity
    omega
  · simpa using core_eq_highDegree_window G P (by simpa using hn) hpRec hhRec

end ChordalStabilityNote

#print axioms ChordalStabilityNote.stability_of_paid_root
