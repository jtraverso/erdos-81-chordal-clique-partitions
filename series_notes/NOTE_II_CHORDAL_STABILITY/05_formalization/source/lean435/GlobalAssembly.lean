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

import NearAssembly
import FarGap
import PaperIV.NearH1Localization
import PaperIV.RC01FarAssembly
import PaperIV.CertifiedOptimumExistence

namespace ChordalStabilityNote

open Finset PaperVI PaperIV.FarRounding

/-- Exact chordal stability in a linear deficit window. The only graph
hypotheses are chordality and the actual optimum's deficit. The near witness,
local capacity and local equality are conclusions of the proved IV–VI chain. -/
theorem eventual_root_stability :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.IsChordal G → cp G ≤ Mval n →
      2000 * (Mval n - cp G) ≤ n →
      RootStability G (univ.filter (fun v => n < 2 * G.degree v)) := by
  classical
  have hη : 0 < PaperIV.NearH1Calibration.eta / 2 := by
    norm_num [PaperIV.NearH1Calibration.eta]
  obtain ⟨N, hN⟩ := PaperIV.RC01FarAssembly.uniformTransferAt
    (PaperIV.NearH1Calibration.eta / 2) hη
  refine ⟨max N (2 * 10^13), ?_⟩
  intro n hn G _ hchordal hcp hdeficit
  have hnRound : N ≤ n := le_trans (le_max_left _ _) hn
  have hnBig : 2 * 10^13 ≤ n := le_trans (le_max_right _ _) hn
  have hdQ : (Mval n : ℚ) - cp G ≤ (n : ℚ) / 2000 := by
    have hd : (2000 : ℚ) * ((Mval n - cp G : ℕ) : ℚ) ≤ n := by exact_mod_cast hdeficit
    rw [Nat.cast_sub hcp] at hd
    linarith
  obtain ⟨w, hw⟩ := PaperIV.CertifiedOptimumExistence.exists_certifiedFractionalOptimum G
  obtain ⟨P, hP⟩ := hN n hnRound G w hw
  have hnear := not_far_of_rounded_packing G hnBig hdQ P hP
  obtain ⟨W⟩ := PaperIV.NearH1Localization.exists_nearStructureWitness_of_nearRegime
    (by omega : 4 * 10^12 ≤ n) G hchordal hw hnear
  have hs := stability_of_nearStructureWitness G W (by omega) hdQ
  rw [← hs.canonical]
  exact hs

end ChordalStabilityNote

#print axioms ChordalStabilityNote.eventual_root_stability
