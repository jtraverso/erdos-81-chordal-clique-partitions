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
Paper IV — Chromatic index `χ'` and the edge-colouring defect (Tuza–Vizing Tier 3, partial).

Mathlib has no edge chromatic number. We DEFINE `χ'(G)` as the vertex chromatic number of the line
graph (`colorable_lineGraph_iff_edge` makes this exactly the least number of colours in a proper
edge-colouring) and connect it to the defect: `D_q(L(G)) = 0 ↔ χ'(G) ≤ q`, so `D_q(L(G))` is literally
the `q`-edge-colouring defect and `χ'(G)` its zero-threshold.

What remains BLOCKED (research-grade, not in Mathlib): **Vizing's theorem** `χ'(G) ≤ Δ(G) + 1`. Its
Kempe-chain/fan proof is out of reach cheaply; keep the `Δ`-based upper bounds on `oct(L(M_C))` at the
manuscript level. Everything below is Vizing-free.
-/
module

public import PaperV.LineGraph
public import PaperV.DqBasic

import Mathlib.Tactic.Ext

@[expose] public section

open SimpleGraph Finset

namespace PaperV

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Chromatic index** `χ'(G)` (edge chromatic number), absent from Mathlib: the vertex chromatic
number of the line graph. By `colorable_lineGraph_iff_edge` this is the least `q` admitting a proper
`q`-edge-colouring. -/
noncomputable def edgeChromaticNumber (G : SimpleGraph V) : ℕ∞ := (G.lineGraph).chromaticNumber

/-- `χ'(G) ≤ q` iff `G` admits a proper `q`-edge-colouring (edges sharing a vertex get distinct
colours). -/
theorem edgeChromaticNumber_le_iff (G : SimpleGraph V) (q : ℕ) :
    edgeChromaticNumber G ≤ (q : ℕ∞) ↔
      ∃ c : ↑G.edgeSet → Fin q, ∀ e f : ↑G.edgeSet,
        e ≠ f → ((↑(↑e : Sym2 V) : Set V) ∩ ↑(↑f : Sym2 V)).Nonempty → c e ≠ c f := by
  unfold edgeChromaticNumber
  rw [chromaticNumber_le_iff_colorable, colorable_lineGraph_iff_edge]

/-- **The edge-colouring defect vanishes exactly at/above the chromatic index:**
`D_q(L(G)) = 0 ↔ χ'(G) ≤ q`. Hence `D_q(L(G))` is the `q`-edge-colouring defect of `G` and `χ'(G)`
its threshold. Specialisation of `Dq_eq_zero_iff_chromatic` to the line graph. -/
theorem Dq_lineGraph_eq_zero_iff_edgeChromatic (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (G.lineGraph).Adj] {q : ℕ} (hq : 1 ≤ q) :
    Dq (G.lineGraph) q = 0 ↔ edgeChromaticNumber G ≤ (q : ℕ∞) :=
  Dq_eq_zero_iff_chromatic (G.lineGraph) hq

/-- **Lower half of Vizing:** `Δ(G) ≤ χ'(G)`. The `Δ` edges at a maximum-degree vertex are pairwise
adjacent in `L(G)` (they share that vertex), forming a clique of size `Δ`; a clique caps the chromatic
number from below. (The upper bound `χ'(G) ≤ Δ(G)+1` — Vizing proper — needs Kempe-chain machinery
absent from Mathlib and stays out of scope.) -/
theorem maxDegree_le_edgeChromaticNumber (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] :
    (G.maxDegree : ℕ∞) ≤ edgeChromaticNumber G := by
  classical
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  have hsub : ∀ e ∈ G.incidenceFinset v, e ∈ G.edgeSet := by
    intro e he
    rw [mem_incidenceFinset] at he
    exact G.incidenceSet_subset v he
  have hvmem : ∀ e ∈ G.incidenceFinset v, v ∈ e := by
    intro e he
    rw [mem_incidenceFinset] at he
    exact he.2
  let emb : {x // x ∈ G.incidenceFinset v} ↪ ↑G.edgeSet :=
    ⟨fun e => ⟨e.1, hsub e.1 e.2⟩, fun a b h => Subtype.ext (by simpa using h)⟩
  let s : Finset ↑G.edgeSet := (G.incidenceFinset v).attach.map emb
  have hcard : s.card = G.degree v := by
    rw [Finset.card_map, Finset.card_attach, G.card_incidenceFinset_eq_degree]
  have hclique : (G.lineGraph).IsClique ↑s := by
    intro a ha b hb hab
    simp only [s, emb, Finset.coe_map, Set.mem_image, Finset.mem_coe, Finset.mem_attach,
      true_and, Subtype.exists, Function.Embedding.coeFn_mk] at ha hb
    obtain ⟨ea, hea, rfl⟩ := ha
    obtain ⟨eb, heb, rfl⟩ := hb
    refine ⟨hab, v, ?_, ?_⟩
    · change v ∈ ea
      exact hvmem ea hea
    · change v ∈ eb
      exact hvmem eb heb
  have hcl := hclique.card_le_chromaticNumber
  rw [hcard] at hcl
  rw [edgeChromaticNumber, hv]
  exact hcl

end PaperV
