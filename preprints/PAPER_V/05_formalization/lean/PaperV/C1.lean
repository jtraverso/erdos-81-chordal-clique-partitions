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
Paper IV — C1 (combined OCT bound, Opción A). Gives Lemma 3.5 (parity localization) a genuine use:
the odd-cycle transversal of a subcubic K₄-free conflict graph is bounded by BOTH the internal-edge
vertex cover (Lemma 3.5) AND one third of the vertex count (Brooks, via `oct_le_third_of_cubic`).

  oct H ≤ min( τ(internal edges w.r.t. A) , ⌊|V(H)|/3⌋ ).

Applied to the copy conflict graph `H[T₂]` with `A = φ'(P')` this is the combined estimate of §5.2
(N1's Brooks bound refined by König on the bipartite internal graph).
-/
module

public import PaperV.Parity
public import PaperV.BrooksOct

@[expose] public section

open SimpleGraph Finset

namespace PaperV

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **C1 (combined bound).** For a subcubic, K₄-free conflict graph `H` and any bipartition
witness `A`, the OCT defect is at most the minimum of the internal-edge cover number (Lemma 3.5)
and `⌊|V|/3⌋` (Brooks). -/
theorem oct_le_min_tau_third (H : SimpleGraph V) [DecidableRel H.Adj]
    (hΔ : H.maxDegree ≤ 3) (hK4 : H.CliqueFree 4) (A : Finset V) :
    oct H ≤ min (tau (internalGraph H A)) (Fintype.card V / 3) :=
  le_min (parity_localization H A) (oct_le_third_of_cubic H hΔ hK4)

end PaperV
