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
import PaperIV.NearH1StructureWitness

namespace ChordalStabilityNote

open PaperVI

/-- The actual structural witness produced by IV activates VI's exact local
construction. The global final theorem must obtain W from IV localization;
this helper is intentionally not advertised as that unconditional endpoint. -/
theorem stability_of_nearStructureWitness {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (W : PaperIV.NearH1StructureWitness.NearStructureWitness G)
    (hn : 100 ≤ n)
    (hdeficit : (Mval n : ℚ) - cp G ≤ (n : ℚ) / 2000) :
    RootStability G W.regularized.root := by
  classical
  have hm : (W.accounts.missingEdges.card : ℚ) =
      (mCount G W.regularized.root : ℚ) := by
    rw [W.accounts_missing, outsideEdges_eq_extEdges]
    rfl
  have hA : (W.accounts.rootLossEdges.card : ℚ) =
      (Adef G W.regularized.root : ℚ) := by
    rw [W.accounts_rootLoss]
    exact_mod_cast missingSpoke_card_eq_Adef (G := G) W.regularized.root
  have hb : PaperIV.splitBaseline W.accounts.order W.accounts.split =
      baseline (n : ℚ) (W.regularized.root.card : ℚ) := by
    rw [W.accounts_order, W.accounts_split]
    simp [PaperIV.splitBaseline, baseline]
  have hp := W.accounts.count_le_paid
  rw [hm, hA, hb] at hp
  exact stability_of_paid_root G W.regularized.root W.regularized.isClique
    (PaperIV.PhysicalCompletion.completion G W.packing)
    (PaperIV.PhysicalCompletion.isExactPartition_completion W.isPacking.toIsPacking)
    hn hdeficit hp

end ChordalStabilityNote

#print axioms ChordalStabilityNote.stability_of_nearStructureWitness
