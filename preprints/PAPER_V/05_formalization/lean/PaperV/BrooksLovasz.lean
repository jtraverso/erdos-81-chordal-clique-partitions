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
Paper IV — Brooks B, Route L (Lovász) primitives for `good_triple_of_two_connected`.

Hand-proved, linchpin-class building blocks for the 2-connected case of Brooks Δ=3, via Lovász's
good-triple argument. Case 2 (endblock theory) is completed in `PaperV.BrooksLovaszEndblock`, and
the chain is closed in `PaperV.BrooksReg`/`PaperV.BrooksMain`; nothing here is left open.
-/
module

public import PaperV.BrooksHub

import Mathlib.Tactic.Ext
import Mathlib.Tactic.Push
import Mathlib.Tactic.Set

@[expose] public section

open SimpleGraph Finset

namespace PaperV.Brooks

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **P2 (distance-2 candidate).** In a connected `G`, if `x` has a non-neighbour `w ≠ x`, then `x`
has a neighbour `u` which has a neighbour `b` with `¬ G.Adj x b` and `b ≠ x`. (I.e. a vertex `b` at
distance 2 from `x`, with common neighbour `u`.) Proof: the set `{x} ∪ N(x)` is not closed under
adjacency (it omits `w` yet `x` reaches `w`), so some neighbour of `x` has an edge leaving it. -/
theorem exists_dist2_pair (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    {x w : V} (hwx : w ≠ x) (hxw : ¬ G.Adj x w) :
    ∃ u b, G.Adj x u ∧ G.Adj u b ∧ ¬ G.Adj x b ∧ b ≠ x := by
  classical
  set S : Set V := {y | y = x ∨ G.Adj x y} with hSdef
  have hxS : x ∈ S := Or.inl rfl
  have hwS : w ∉ S := by
    intro hmem; rcases hmem with heq | hadj
    · exact hwx heq
    · exact hxw hadj
  have hnotclosed : ¬ ∀ s ∈ S, ∀ y, G.Adj s y → y ∈ S := by
    intro hcl
    obtain ⟨p⟩ := hconn.preconnected x w
    exact hwS (mem_of_walk_closed G S hcl p hxS)
  push_neg at hnotclosed
  obtain ⟨s, hsS, y, hsy, hyS⟩ := hnotclosed
  have hyx : y ≠ x := by rintro rfl; exact hyS (Or.inl rfl)
  have hxy : ¬ G.Adj x y := fun h => hyS (Or.inr h)
  rcases hsS with rfl | hxs
  · exact absurd hsy hxy
  · exact ⟨s, y, hxs, hsy, hxy, hyx⟩

/-- G ≠ ⊤ ⇒ some vertex has a non-neighbour (≠ itself). -/
theorem exists_nonneighbor_of_ne_top (G : SimpleGraph V) [DecidableRel G.Adj]
    (hne : G ≠ ⊤) : ∃ x w, w ≠ x ∧ ¬ G.Adj x w := by
  classical
  by_contra hcon
  push_neg at hcon
  apply hne
  ext u v
  simp only [SimpleGraph.top_adj]
  constructor
  · exact fun h => h.ne
  · intro huv
    exact hcon u v huv.symm

/-- **Reduction of the bad-graph lemma to its kernel.** Contrapositive shape: if `G` is connected,
`G ≠ ⊤`, and `G` has no good triple, then every good-triple *candidate* `(v₀,a,b)` has `G−{a,b}`
disconnected. In particular a candidate exists (via `exists_dist2_pair`), so the residual content
is purely: "every distance-2 pair is a 2-cut ⇒ `G` is 2-regular". -/
theorem exists_candidate_of_ne_top (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hne : G ≠ ⊤) :
    ∃ v₀ a b : V, G.Adj v₀ a ∧ G.Adj v₀ b ∧ a ≠ b ∧ ¬ G.Adj a b := by
  classical
  obtain ⟨x, w, hwx, hxw⟩ := exists_nonneighbor_of_ne_top G hne
  obtain ⟨u, b, hxu, hub, hxb, hbx⟩ := exists_dist2_pair G hconn hwx hxw
  exact ⟨u, x, b, hxu.symm, hub, hbx.symm, hxb⟩

end PaperV.Brooks
