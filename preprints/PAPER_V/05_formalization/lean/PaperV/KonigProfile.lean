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
Paper V — Kőnig's theorem for the edge-defect profile: bipartite graphs are Class 1.

With `Galvin.konig_multigraph` (bipartite multigraphs, ported/returned and re-gated) the zero set of the
edge-defect profile `q ↦ D_q(L(G))` is pinned exactly for the bipartite family:

  `G` 2-colourable, `Δ(G) ≥ 1`  ⟹  `D_Δ(L(G)) = 0`  (so `G` is Class 1),  and  `D_q(L(G)) > 0` for `q < Δ`.

This turns the scope statement of Proposition 3.10 ("Δ and the Class 1/2 bit determine WHERE the profile
vanishes") into a machine-checked classical instance, complementing the P₄/C₄ witnesses of `DefectOne.lean`.

Bridge: a 2-colouring `col : V → Fin 2` orients every edge from its colour-0 endpoint to its colour-1 endpoint;
the oriented edges form a bipartite multigraph on `left, right : E → V` with degrees ≤ Δ(G); Kőnig colours it with
`Δ` colours; two edges of `G` sharing a vertex share it on the same side, so the colouring is a proper edge colouring
of `G`, i.e. a `Δ`-colouring of `L(G)` (`colorable_lineGraph_iff_edge`).

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.GalvinMultigraph
public import PaperV.EdgeDefectProfile

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Set

@[expose] public section

open SimpleGraph Finset

namespace PaperV
namespace Konig

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Oriented edges of `G` with respect to a 2-colouring: the pair `(a, b)` with `G.Adj a b` and `col a = 0`. -/
def OEdge (G : SimpleGraph V) [DecidableRel G.Adj] (col : V → Fin 2) : Type _ :=
  {p : V × V // G.Adj p.1 p.2 ∧ col p.1 = 0}

instance (G : SimpleGraph V) [DecidableRel G.Adj] (col : V → Fin 2) : Fintype (OEdge G col) := by
  unfold OEdge; infer_instance

instance (G : SimpleGraph V) [DecidableRel G.Adj] (col : V → Fin 2) : DecidableEq (OEdge G col) := by
  unfold OEdge; infer_instance

/-- In a proper 2-colouring the second endpoint of an oriented edge has colour `1`. -/
theorem col_snd (G : SimpleGraph V) [DecidableRel G.Adj] (C : G.Coloring (Fin 2)) (p : OEdge G C) :
    C p.1.2 = 1 := by
  have hne : C p.1.1 ≠ C p.1.2 := C.valid p.2.1
  have h0 := p.2.2
  have : ∀ x : Fin 2, x ≠ 0 → x = 1 := by decide
  exact this _ (fun h => hne (h0.trans h.symm))

/-- Every edge of `G` has an oriented representative. -/
theorem exists_orient (G : SimpleGraph V) [DecidableRel G.Adj] (C : G.Coloring (Fin 2)) (e : G.edgeSet) :
    ∃ p : OEdge G C, s(p.1.1, p.1.2) = (e : Sym2 V) := by
  obtain ⟨⟨a, b⟩, hab⟩ := e
  have hadj : G.Adj a b := hab
  have hne : C a ≠ C b := C.valid hadj
  have h2 : ∀ x y : Fin 2, x ≠ y → x = 0 ∨ y = 0 := by decide
  rcases h2 _ _ hne with ha | hb
  · exact ⟨⟨(a, b), hadj, ha⟩, rfl⟩
  · exact ⟨⟨(b, a), hadj.symm, hb⟩, Sym2.eq_swap⟩

/-- The oriented representative of an edge. -/
noncomputable def orient (G : SimpleGraph V) [DecidableRel G.Adj] (C : G.Coloring (Fin 2)) (e : G.edgeSet) :
    OEdge G C :=
  (exists_orient G C e).choose

theorem orient_spec (G : SimpleGraph V) [DecidableRel G.Adj] (C : G.Coloring (Fin 2)) (e : G.edgeSet) :
    s((orient G C e).1.1, (orient G C e).1.2) = (e : Sym2 V) :=
  (exists_orient G C e).choose_spec

theorem orient_injective (G : SimpleGraph V) [DecidableRel G.Adj] (C : G.Coloring (Fin 2)) :
    Function.Injective (orient G C) := by
  intro e f h
  apply Subtype.ext
  rw [← orient_spec G C e, ← orient_spec G C f, h]

/-- A vertex of an edge is its colour-0 endpoint or its colour-1 endpoint. -/
theorem mem_orient (G : SimpleGraph V) [DecidableRel G.Adj] (C : G.Coloring (Fin 2)) (e : G.edgeSet) (v : V)
    (hv : v ∈ (e : Sym2 V)) :
    (C v = 0 ∧ v = (orient G C e).1.1) ∨ (C v = 1 ∧ v = (orient G C e).1.2) := by
  rw [← orient_spec G C e, Sym2.mem_iff] at hv
  rcases hv with rfl | rfl
  · exact Or.inl ⟨(orient G C e).2.2, rfl⟩
  · exact Or.inr ⟨col_snd G C _, rfl⟩

/-- Left degrees of the oriented multigraph are bounded by the degrees of `G`. -/
theorem degL_le (G : SimpleGraph V) [DecidableRel G.Adj] (col : V → Fin 2) (u : V) :
    Galvin.degL (fun p : OEdge G col => p.1.1) u ≤ G.maxDegree := by
  classical
  unfold Galvin.degL
  calc (Finset.univ.filter fun p : OEdge G col => p.1.1 = u).card
      ≤ (G.neighborFinset u).card := by
        apply Finset.card_le_card_of_injOn (fun p => p.1.2)
        · intro p hp
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp
          simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset]
          rw [← hp]; exact p.2.1
        · intro p hp q hq hpq
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp hq
          exact Subtype.ext (Prod.ext (hp.trans hq.symm) hpq)
    _ = G.degree u := SimpleGraph.card_neighborFinset_eq_degree G u
    _ ≤ G.maxDegree := SimpleGraph.degree_le_maxDegree G u

/-- Right degrees of the oriented multigraph are bounded by the degrees of `G`. -/
theorem degR_le (G : SimpleGraph V) [DecidableRel G.Adj] (col : V → Fin 2) (r : V) :
    Galvin.degR (fun p : OEdge G col => p.1.2) r ≤ G.maxDegree := by
  classical
  unfold Galvin.degR
  calc (Finset.univ.filter fun p : OEdge G col => p.1.2 = r).card
      ≤ (G.neighborFinset r).card := by
        apply Finset.card_le_card_of_injOn (fun p => p.1.1)
        · intro p hp
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp
          simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset]
          rw [← hp]; exact p.2.1.symm
        · intro p hp q hq hpq
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp hq
          exact Subtype.ext (Prod.ext hpq (hp.trans hq.symm))
    _ = G.degree r := SimpleGraph.card_neighborFinset_eq_degree G r
    _ ≤ G.maxDegree := SimpleGraph.degree_le_maxDegree G r

/-- **Kőnig for the line graph.** A 2-colourable `G` has a proper edge colouring with `Δ(G)` colours, i.e. `L(G)`
is `Δ(G)`-colourable. -/
theorem lineGraph_colorable_maxDegree_of_bipartite (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Colorable 2) : (G.lineGraph).Colorable G.maxDegree := by
  classical
  let C : G.Coloring (Fin 2) := hG.some
  obtain ⟨φ, hφlt, hφprop⟩ := Galvin.konig_multigraph (fun p : OEdge G C => p.1.1)
    (fun p : OEdge G C => p.1.2) Finset.univ G.maxDegree
    (fun u => by
      have := degL_le G C u
      unfold Galvin.degL at this
      simpa [Galvin.degLOn] using this)
    (fun r => by
      have := degR_le G C r
      unfold Galvin.degR at this
      simpa [Galvin.degROn] using this)
  rw [colorable_lineGraph_iff_edge]
  refine ⟨fun e => ⟨φ (orient G C e), hφlt _ (Finset.mem_univ _)⟩, ?_⟩
  intro e f hef hsh
  obtain ⟨v, hve, hvf⟩ := hsh
  intro heq
  have heq' : φ (orient G C e) = φ (orient G C f) := by
    have := congrArg Fin.val heq
    simpa using this
  have hne : orient G C e ≠ orient G C f := fun h => hef (orient_injective G C h)
  apply hφprop (orient G C e) (Finset.mem_univ _) (orient G C f) (Finset.mem_univ _) hne _ heq'
  rcases mem_orient G C e v hve with ⟨h0, rfl⟩ | ⟨h1, rfl⟩
  · rcases mem_orient G C f _ hvf with ⟨_, h⟩ | ⟨h1', _⟩
    · exact Or.inl h
    · exact absurd (h0.symm.trans h1') (by decide)
  · rcases mem_orient G C f _ hvf with ⟨h0', _⟩ | ⟨_, h⟩
    · exact absurd (h1.symm.trans h0') (by decide)
    · exact Or.inr h

/-- **`D_Δ(L(G)) = 0` for bipartite `G`** with `Δ(G) ≥ 1`. -/
theorem Dq_lineGraph_maxDegree_eq_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (G.lineGraph).Adj] (hG : G.Colorable 2) (hΔ : 1 ≤ G.maxDegree) :
    Dq (G.lineGraph) G.maxDegree = 0 :=
  (Dq_eq_zero_iff (G.lineGraph) hΔ).mpr (lineGraph_colorable_maxDegree_of_bipartite G hG)

/-- **Bipartite graphs are Class 1.** -/
theorem isClassOne_of_bipartite (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (G.lineGraph).Adj] [Nonempty V] (hG : G.Colorable 2) (hΔ : 1 ≤ G.maxDegree) :
    IsClassOne G := by
  have h := (Dq_lineGraph_eq_zero_iff G hΔ).mp (Dq_lineGraph_maxDegree_eq_zero G hG hΔ)
  rcases h with h | ⟨_, h⟩
  · omega
  · exact h

/-- **Exact zero set of the profile for bipartite `G`:** `D_q(L(G)) = 0 ↔ Δ(G) ≤ q` (for `q ≥ 1`). -/
theorem Dq_lineGraph_eq_zero_iff_of_bipartite (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (G.lineGraph).Adj] [Nonempty V] (hG : G.Colorable 2) (hΔ : 1 ≤ G.maxDegree)
    {q : ℕ} (hq : 1 ≤ q) :
    Dq (G.lineGraph) q = 0 ↔ G.maxDegree ≤ q := by
  rw [Dq_lineGraph_eq_zero_iff G hq]
  constructor
  · rintro (h | ⟨h, _⟩) <;> omega
  · intro h
    rcases Nat.lt_or_ge G.maxDegree q with hlt | hge
    · exact Or.inl hlt
    · exact Or.inr ⟨by omega, isClassOne_of_bipartite G hG hΔ⟩

end Konig
end PaperV
