/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
SPDX-License-Identifier: Apache-2.0

The Apache-2.0 grant applies to the author-written formalization in this file.
Existing mathematical attributions, author credits and provenance below are retained.
-/

/-
Paper V formalization and integration.
Authors: Juan Pablo Traverso Gianini

Original mathematical attributions and existing source/port provenance are
retained below; this author credit does not reattribute those prior results.
-/

module

public import PaperV.Vizing.Step

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Lift
import Mathlib.Tactic.Push
import Mathlib.Tactic.Set

@[expose] public section

/-!
# Vizing's theorem, upper bound

Iterating the extension step colours all edges, giving a proper edge colouring with
`Δ + 1` colours; equivalently, the line graph is `(Δ + 1)`-colourable.
-/

open SimpleGraph Finset

namespace Vizing

namespace PEC

variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [Fintype C] [DecidableEq C]
  {G : SimpleGraph V}

/-- The colouring that colours nothing. -/
def empty (G : SimpleGraph V) (C : Type*) : PEC G C where
  col := fun _ _ => none
  col_symm := fun _ _ => rfl
  col_adj := by intro u v γ h; exact absurd h (by simp)
  col_proper := by intro u v w γ h; exact absurd h (by simp)

/-- The set of (ordered) uncoloured edges. -/
noncomputable def uncoloured [DecidableRel G.Adj] (c : PEC G C) : Finset (V × V) :=
  {p ∈ (Finset.univ : Finset (V × V)) | G.Adj p.1 p.2 ∧ c.col p.1 p.2 = none}

omit [DecidableEq V] [Fintype C] [DecidableEq C] in
lemma mem_uncoloured [DecidableRel G.Adj] (c : PEC G C) (p : V × V) :
    p ∈ c.uncoloured ↔ G.Adj p.1 p.2 ∧ c.col p.1 p.2 = none := by
  classical
  simp [uncoloured]

/-- Every graph has a proper edge colouring with more than `Δ` colours. -/
theorem exists_total [DecidableRel G.Adj] (hcard : G.maxDegree < Fintype.card C) :
    ∃ c : PEC G C, ∀ u v, G.Adj u v → c.col u v ≠ none := by
  classical
  suffices H : ∀ (k : ℕ) (c : PEC G C), c.uncoloured.card ≤ k →
      ∃ c' : PEC G C, ∀ u v, G.Adj u v → c'.col u v ≠ none by
    exact H (empty G C).uncoloured.card (empty G C) le_rfl
  intro k
  induction k with
  | zero =>
    intro c hk
    refine ⟨c, fun u v huv hcol => ?_⟩
    have hmem : (u, v) ∈ c.uncoloured := (c.mem_uncoloured (u, v)).2 ⟨huv, hcol⟩
    have := Finset.card_pos.2 ⟨_, hmem⟩
    omega
  | succ k ih =>
    intro c hk
    by_cases hall : ∀ u v, G.Adj u v → c.col u v ≠ none
    · exact ⟨c, hall⟩
    · push_neg at hall
      obtain ⟨x, y, hadj, hnone⟩ := hall
      obtain ⟨c1, hext, hc1⟩ := vizing_step c hcard hadj (by simpa using hnone)
      refine ih c1 ?_
      have hsub : c1.uncoloured ⊆ c.uncoloured := by
        intro p hp
        rw [mem_uncoloured] at hp ⊢
        refine ⟨hp.1, ?_⟩
        by_contra hcon
        exact (hext p.1 p.2 hcon) hp.2
      have hxy : (x, y) ∈ c.uncoloured := (c.mem_uncoloured (x, y)).2 ⟨hadj, by simpa using hnone⟩
      have hxy' : (x, y) ∉ c1.uncoloured := by
        rw [mem_uncoloured]
        rintro ⟨-, h⟩
        exact hc1 h
      have hlt : c1.uncoloured.card < c.uncoloured.card :=
        Finset.card_lt_card ⟨hsub, fun hcon => hxy' (hcon hxy)⟩
      omega

/-! ### From total colourings to colourings of the line graph -/

/-- The colour of an edge, as a function on `Sym2 V`. -/
def edgeColor (c : PEC G C) [Inhabited C] (e : Sym2 V) : C :=
  Sym2.lift ⟨fun u v => (c.col u v).getD default, fun u v => by simp only [c.col_symm u v]⟩ e

omit [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] in
@[simp] lemma edgeColor_mk (c : PEC G C) [Inhabited C] (u v : V) :
    c.edgeColor s(u, v) = (c.col u v).getD default := rfl

/-- A total proper partial colouring gives a colouring of the line graph. -/
noncomputable def lineGraphColoring [Inhabited C] (c : PEC G C)
    (htot : ∀ u v, G.Adj u v → c.col u v ≠ none) : (G.lineGraph).Coloring C :=
  Coloring.mk (fun e => c.edgeColor e.1) (by
    rintro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ hadj
    rw [lineGraph_adj_iff_exists] at hadj
    obtain ⟨hne, v, hv₁, hv₂⟩ := hadj
    obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.1 hv₁
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hv₂
    have huv : G.Adj v u := by rwa [SimpleGraph.mem_edgeSet] at he₁
    have hvw : G.Adj v w := by rwa [SimpleGraph.mem_edgeSet] at he₂
    simp only [edgeColor_mk]
    intro hcol
    obtain ⟨γ, hγ⟩ : ∃ γ, c.col v u = some γ := Option.ne_none_iff_exists'.1 (htot v u huv)
    obtain ⟨δ, hδ⟩ : ∃ δ, c.col v w = some δ := Option.ne_none_iff_exists'.1 (htot v w hvw)
    rw [hγ, hδ] at hcol
    simp only [Option.getD_some] at hcol
    subst hcol
    have huw : u = w := c.col_proper hγ hδ
    subst huw
    exact hne (Subtype.ext rfl))

end PEC

/-- **Vizing's theorem (upper bound)**: the line graph of a finite simple graph `G` is
`(Δ(G) + 1)`-colourable, i.e. `G` has a proper edge colouring with `Δ(G) + 1` colours. -/
theorem lineGraph_colorable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : (G.lineGraph).Colorable (G.maxDegree + 1) := by
  classical
  obtain ⟨c, hc⟩ := PEC.exists_total (G := G) (C := Fin (G.maxDegree + 1))
    (by simp)
  exact ⟨c.lineGraphColoring hc⟩

end Vizing
