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

/- A fresh assembly of the Erdős 81 bound through Paper V's physical transfer.
Structural and rounding inputs are explicitly attributed to Paper IV.
The final all-chordal theorem of IV is not an input. -/
import Erdos81Note.PhysicalTransfer
import PaperIV.NearH1Localization
import PaperIV.RC01FarAssembly
import PaperIV.CertifiedOptimumExistence
import PaperIV.SplitBaselineTarget
import PaperIV.FarRoundingToPhysical
import Mathlib.Data.Nat.Choose.Bounds
import Lean.Util.CollectAxioms

namespace Erdos81Note
open PaperIV.FarRounding

/-- A paid physical completion supplies a one-class certificate with reference e(G).
This interface retains the cost of realization rather than assuming a transfer gap. -/
theorem partition_of_paid_packing {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : ℕ) (P : Packing G)
    (hpaid : G.edgeFinset.card - P.gain ≤ T) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ T := by
  have hg := P.gain_le_card_edgeFinset
  apply partition_of_reference_gain G G.edgeFinset.card T P hg
  omega

/-- The far branch: quadratic slack pays IV's rounding loss; V then gives the partition. -/
theorem far_certificate {η : ℚ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ∀ w : ℚ, CertifiedFractionalOptimum G w →
        (G.edgeFinset.card : ℚ)-w < (n : ℚ)^2/6-η*(n : ℚ)^2 →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize n := by
  obtain ⟨N,hN⟩ := PaperIV.RC01FarAssembly.uniformTransferAt (η/2) (by positivity)
  refine ⟨N,?_⟩
  intro n hn G _ w hw hfar
  obtain ⟨P,hP⟩ := hN n hn G w hw
  have hg := P.gain_le_card_edgeFinset
  have hdiff : ((G.edgeFinset.card-P.gain : ℕ) : ℚ) =
      (G.edgeFinset.card : ℚ)-(P.gain : ℚ) := by exact Nat.cast_sub hg
  have hsmall : ((G.edgeFinset.card-P.gain : ℕ) : ℚ) < (n : ℚ)^2/6 := by
    rw [hdiff]
    have : 0 ≤ η*(n : ℚ)^2/2 := by positivity
    linarith
  have h6 : 6*(G.edgeFinset.card-P.gain) ≤ n*(n+1) := by
    have hq : ((6*(G.edgeFinset.card-P.gain) : ℕ) : ℚ) ≤
        ((n*(n+1) : ℕ) : ℚ) := by
      push_cast
      have hn0 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
      nlinarith
    exact_mod_cast hq
  apply partition_of_paid_packing G (targetSize n) P
  rw [targetSize, Nat.le_div_iff_mul_le (by norm_num)]
  omega

/-- The near branch uses localization by descent and the physical ledger of IV.
No partition is transported backwards along the descent. -/
theorem near_certificate {n : ℕ} (hn : 4*10^12 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : PaperIV.IsChordal G) {w : ℚ} (hw : CertifiedFractionalOptimum G w)
    (hnear : ¬ ((G.edgeFinset.card : ℚ)-w < (n : ℚ)^2/6-
      PaperIV.NearH1Calibration.eta*(n : ℚ)^2)) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize n := by
  classical
  obtain ⟨W⟩ := PaperIV.NearH1Localization.exists_nearStructureWitness_of_nearRegime
    hn G hG hw hnear
  let P := PaperIV.FarRoundingToPhysical.ofPhysicalPacking W.isPacking
  have hbaseQ : ((W.accounts.baseCount : ℤ) : ℚ) =
      PaperIV.splitBaseline (n : ℚ) W.accounts.split := by
    simpa [W.accounts_order] using W.accounts.base_eq
  have hbase := PaperIV.SplitBaselineTarget.splitBaseline_le_targetSize hbaseQ
  have hbase' : W.accounts.baseCount ≤ targetSize n := by
    have hb : W.accounts.baseCount ≤ PaperIV.targetSize n := by exact_mod_cast hbase
    simpa [PaperIV.targetSize, targetSize] using hb
  have hpaidQ := W.accounts.count_le_paid
  have hcountQ : ((PaperIV.PhysicalCompletion.completion G W.packing).card : ℚ) ≤
      (W.accounts.baseCount : ℚ) := by
    rw [← W.accounts.base_eq] at hpaidQ
    have hm : (0 : ℚ) ≤ W.accounts.missingEdges.card := Nat.cast_nonneg _
    have hA : (0 : ℚ) ≤ W.accounts.rootLossEdges.card := Nat.cast_nonneg _
    linarith
  have hcount : (PaperIV.PhysicalCompletion.completion G W.packing).card ≤ targetSize n := by
    have hc : (PaperIV.PhysicalCompletion.completion G W.packing).card ≤
        W.accounts.baseCount := by exact_mod_cast hcountQ
    omega
  have hsum := PaperIV.FarRoundingToPhysical.completion_count_add_gain P
  have hsum' : (PaperIV.PhysicalCompletion.completion G W.packing).card + P.gain =
      G.edgeFinset.card := by
    simpa only [P, PaperIV.FarRoundingToPhysical.ofPhysicalPacking,
      PaperIV.Model.graphEdges] using hsum
  apply partition_of_paid_packing G (targetSize n) P
  omega

/-- Eventual sharp Erdős 81 bound, assembled here through the physical transfer of V. -/
theorem erdos81_eventual :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.IsChordal G →
      ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize n := by
  have hη : 0 < PaperIV.NearH1Calibration.eta := by
    norm_num [PaperIV.NearH1Calibration.eta]
  obtain ⟨N,hN⟩ := far_certificate hη
  refine ⟨max N (4*10^12),?_⟩
  intro n hn G _ hG
  obtain ⟨w,hw⟩ := PaperIV.CertifiedOptimumExistence.exists_certifiedFractionalOptimum G
  by_cases hfar : (G.edgeFinset.card : ℚ)-w < (n : ℚ)^2/6-
      PaperIV.NearH1Calibration.eta*(n : ℚ)^2
  · exact hN n (le_trans (Nat.le_max_left _ _) hn) G w hw hfar
  · exact near_certificate (le_trans (Nat.le_max_right _ _) hn) G hG hw hfar

/-- An absolute additive constant handles all orders, including the empty graph. -/
theorem erdos81_all_orders :
    ∃ b : ℕ, ∀ n : ℕ, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.IsChordal G →
      ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize n+b := by
  obtain ⟨N,hN⟩ := erdos81_eventual
  refine ⟨N^2,?_⟩
  intro n G _ hG
  by_cases hn : N ≤ n
  · obtain ⟨Q,hQ,hsize⟩ := hN n hn G hG
    exact ⟨Q,hQ,by omega⟩
  · let P : Packing G := Packing.empty
    obtain ⟨Q,hQ,hsize⟩ := exists_cliquePartition_of_packing P
    have hgain : P.gain=0 := by simp [P, Packing.empty, Packing.gain]
    have he : G.edgeFinset.card ≤ n^2 := by
      have hc : G.edgeFinset.card ≤ n.choose 2 := by
        simpa using G.card_edgeFinset_le_card_choose_two
      exact hc.trans (Nat.choose_le_pow n 2)
    have hnN : n ≤ N := by omega
    have hn2 : n^2 ≤ N^2 := Nat.pow_le_pow_left hnN 2
    exact ⟨Q,hQ,by omega⟩

end Erdos81Note

-- Axiom gates are intentionally evaluated in this fresh assembly check.
#print axioms Erdos81Note.partition_of_certificate
#print axioms Erdos81Note.erdos81_eventual
#print axioms Erdos81Note.erdos81_all_orders
