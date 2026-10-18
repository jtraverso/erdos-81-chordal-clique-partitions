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

import PaperVIResearch.Intrinsic
import PaperVI.Rigidity
import Lean.Util.CollectAxioms

/-! Graph interfaces for the near-extremal note. These apply to an arbitrary
finite graph and core; no balanced-core-size assumption is introduced. -/

namespace ChordalStabilityNote

open Finset PaperVI

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

/-- The maximum local number of edits never exceeds the total edit count. -/
theorem editDegree_le_editDistance : editDegree G P ≤ editDistance G P := by
  classical
  unfold editDegree editDistance
  convert (editGraph G P).maxDegree_le_of_forall_degree_le _
    (fun v => (editGraph G P).degree_le_card_edgeFinset (v := v))

/-- Degree recognition in the coarse window supplied by Paper IV. The reference
core need not have the maximizing cardinality used in VI's balanced theorem. -/
theorem core_eq_highDegree_window (hn : 100 ≤ Fintype.card V)
    (hp : 5 * P.card ≤ 2 * Fintype.card V)
    (hh : 100 * editDegree G P ≤ Fintype.card V) :
    P = univ.filter (fun v => Fintype.card V < 2 * G.degree v) := by
  ext v
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro hv
    have := PaperVI.Research.degree_core_ge G P hv
    omega
  · intro hv
    by_contra hvP
    have := PaperVI.Research.degree_ext_le G P hvP
    omega

end ChordalStabilityNote

#print axioms ChordalStabilityNote.editDegree_le_editDistance
#print axioms ChordalStabilityNote.core_eq_highDegree_window
