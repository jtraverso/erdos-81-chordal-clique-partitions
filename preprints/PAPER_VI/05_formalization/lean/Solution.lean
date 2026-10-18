/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
SPDX-License-Identifier: Apache-2.0

The Apache-2.0 grant applies to the author-written formalization in this file.
Existing mathematical attributions, author credits and provenance below are retained.
-/

/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.ListEdgeColoringComplete

/-!
# Proof of the statement in `Challenge.lean`

The theorem is `LeanPool.ListEdgeColoringComplete.exists_listEdgeColoring_complete`, proved in
`LeanPool/ListEdgeColoringComplete/` (an extended-star polynomial with a nonzero coefficient and
Mathlib's combinatorial Nullstellensatz).
-/

@[expose] public section

namespace HaggkvistJanssen

/-- **Häggkvist–Janssen.** For lists of at least `|V|` colours on the edges of the complete graph
on `V`, there is a proper edge colouring (a colouring of the line graph) choosing every colour
from the list of its edge. -/
theorem exists_listEdgeColoring_complete {V Color : Type*} [Fintype V]
    (lists : (⊤ : SimpleGraph V).edgeSet → Finset Color)
    (hLists : ∀ e, Fintype.card V ≤ (lists e).card) :
    ∃ coloring : (⊤ : SimpleGraph V).lineGraph.Coloring Color, ∀ e, coloring e ∈ lists e :=
  LeanPool.ListEdgeColoringComplete.exists_listEdgeColoring_complete lists hLists

end HaggkvistJanssen
