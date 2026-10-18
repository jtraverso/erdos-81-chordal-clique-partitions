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

import PaidRootAssembly
import PaperIV.NearH1Calibration

namespace ChordalStabilityNote

open PaperVI PaperIV.FarRounding

theorem numerical_far_margin {n : ℚ} (hn : 2 * 10^13 ≤ n) :
    n / 2000 + 1 < PaperIV.NearH1Calibration.eta * n^2 / 2 := by
  have hn0 : 0 ≤ n := by linarith
  have hp : 0 ≤ (n - 2 * 10^13) * n := mul_nonneg (sub_nonneg.mpr hn) hn0
  norm_num [PaperIV.NearH1Calibration.eta] at *
  nlinarith

/-- A physical rounded packing rules out the far regime for a graph whose
actual clique-partition optimum is within the specified linear window. -/
theorem not_far_of_rounded_packing {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hn : 2 * 10^13 ≤ n)
    (hdeficit : (Mval n : ℚ) - cp G ≤ (n : ℚ) / 2000)
    {w : ℚ} (P : Packing G)
    (hround : w - (P.gain : ℚ) ≤ (PaperIV.NearH1Calibration.eta / 2) * (n : ℚ)^2) :
    ¬ ((G.edgeFinset.card : ℚ) - w <
      (n : ℚ)^2 / 6 - PaperIV.NearH1Calibration.eta * (n : ℚ)^2) := by
  intro hfar
  obtain ⟨Q, _, hsize⟩ := exists_cliquePartition_of_packing P
  have hsizeQ : (Q.size : ℚ) + P.gain = (G.edgeFinset.card : ℚ) := by exact_mod_cast hsize
  have hcp : (cp G : ℚ) ≤ Q.size := by exact_mod_cast cp_le_far_partition Q
  have hsmall : (Q.size : ℚ) < (n : ℚ)^2 / 6 -
      PaperIV.NearH1Calibration.eta * (n : ℚ)^2 / 2 := by linarith
  have hmargin := numerical_far_margin (n := (n : ℚ)) (by exact_mod_cast hn)
  have hM := M_floor_lower n
  have hn0 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  nlinarith

end ChordalStabilityNote

#print axioms ChordalStabilityNote.not_far_of_rounded_packing
