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
/-
Paper VI research round — failure of automatic exceptional-set cleanup.

In the one-exceptional-vertex graph, every modified edge (relative to the complete split graph
on the core `P`) is incident with `z`, so every vertex other than `z` has modification degree at
most one. Nevertheless, for `a = p`, `3b = 2p`, `q = 2p`, `p ≥ 19` the graph is split (hence
chordal) and `cp(G)` exceeds the intrinsic maximum `max_Q Φ_Q(G)` by exactly `p/3`.
-/
module

public import PaperVIResearch.ExceptionalIntrinsic
public import PaperVIResearch.ExceptionalExamples

@[expose] public section

namespace PaperVI

namespace Research

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {P R A B : Finset V} {z : V}
  (hS : ExSetup G P R A B z)
include hS

omit [Fintype V] [DecidableRel G.Adj] in
/-- Every modified edge is incident with `z`: outside `X = {z}` each vertex has modification
degree at most one. -/
theorem ExSetup.edit_only_at_z {v w : V} (hv : v ≠ z) (hvw : (editGraph G P).Adj v w) :
    w = z := by
  rcases (hS.editAdj_iff v w).mp hvw with ⟨h, -⟩ | ⟨h, -⟩
  · exact absurd h hv
  · exact h

/-- **Counterexample to automatic cleanup of one exceptional vertex.** For `a = p`, `3b = 2p`,
`q = 2p` and `p ≥ 19`: `G` is chordal (indeed split), all modifications are incident with `z`,
the modification degree equals `b`, `max_Q Φ_Q(G) = Φ_P(G)` and `cp(G) - max_Q Φ_Q(G) = p/3`. -/
theorem ExSetup.cleanup_counterexample (hp : 19 ≤ P.card) (hq : R.card = 2 * P.card - 1)
    (hA : A = P) (hb : 3 * B.card = 2 * P.card) :
    IsChordal G ∧ (∀ v w, v ≠ z → (editGraph G P).Adj v w → w = z) ∧
      editDegree G P = B.card ∧ IsGreatest (Set.range (PhiQ G)) (PhiQ G P) ∧
      3 * ((cp G : ℤ) - PhiQ G P) = P.card := by
  have ha : A.card = P.card := by rw [hA]
  have hmax : max 0 (3 * (B.card : ℤ) - 2 * A.card) = 0 := by
    rw [ha]; apply max_eq_left; omega
  have hE4 := hS.theoremE4 hp hq
  have hgap := hS.gap_example_linear hp hq ha hb
  rw [hmax, add_zero] at hE4 hgap
  refine ⟨hS.isChordal_of_full hA, fun v w hv hvw => hS.edit_only_at_z hv hvw, ?_, hE4, hgap⟩
  rw [hS.editDegree_eq, ha, Nat.sub_self, zero_add]

end Research

end PaperVI
