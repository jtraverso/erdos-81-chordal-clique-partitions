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
Paper IV — §6.2 (CLON-2) counterexample: the per-clone-step defect is NOT bounded by 2.
Ledger node L-C3 (finite). The certificate reconstructs the conflict graph H[T₂] of a
realizable clone step on 8 vertices (14 triangle-copies, edge-sharing conflicts); it has
14 vertices, 19 edges, and `oct(H[T₂]) = 4 > 2`.

We encode that concrete conflict graph `Hclon` on `Fin 14` and prove `oct Hclon = 4`.
- Upper bound: deleting O = {0,1,2,5} leaves a bipartite graph
  (classes {3,4,6,9,12} / {7,8,10,11,13}), so oct ≤ 4.
- Lower bound: the four triangles {0,9,10}, {5,6,8}, {1,12,13}, {2,3,7} are vertex-disjoint
  odd cycles, so any odd-cycle transversal has ≥ 4 vertices; oct ≥ 4.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.Core

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

open SimpleGraph Finset

namespace PaperV

/-- The 19 edges of the CLON-2 conflict graph `H[T₂]` (as ordered pairs; symmetrised in
`Hclon`). Vertices are `Fin 14`. -/
def clonRaw : List (Fin 14 × Fin 14) :=
  [(0,9),(0,10),(0,11),(1,11),(1,12),(1,13),(2,3),(2,7),(3,5),(3,7),
   (4,7),(4,8),(4,11),(5,6),(5,8),(6,8),(9,10),(10,12),(12,13)]

/-- The CLON-2 conflict graph `H[T₂]` on `Fin 14`. -/
def Hclon : SimpleGraph (Fin 14) where
  Adj a b := (a, b) ∈ clonRaw ∨ (b, a) ∈ clonRaw
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel Hclon.Adj := fun a b => by unfold Hclon; infer_instance

private lemma defect_hits_triangle (O : Finset (Fin 14)) (a b d : Fin 14)
    (hab : Hclon.Adj a b) (had : Hclon.Adj a d) (hbd : Hclon.Adj b d)
    (hcol : (Hclon.induce ((O : Set (Fin 14))ᶜ)).Colorable 2) :
    a ∈ O ∨ b ∈ O ∨ d ∈ O := by
  by_contra h
  simp only [not_or] at h
  obtain ⟨c, hc⟩ := hcol
  let a' : ↥((O : Set (Fin 14))ᶜ) := ⟨a, by simpa using h.1⟩
  let b' : ↥((O : Set (Fin 14))ᶜ) := ⟨b, by simpa using h.2.1⟩
  let d' : ↥((O : Set (Fin 14))ᶜ) := ⟨d, by simpa using h.2.2⟩
  have hab' : c a' ≠ c b' := SimpleGraph.Adj.ne (hc hab)
  have had' : c a' ≠ c d' := SimpleGraph.Adj.ne (hc had)
  have hbd' : c b' ≠ c d' := SimpleGraph.Adj.ne (hc hbd)
  have ha_lt := (c a').isLt
  have hb_lt := (c b').isLt
  have hd_lt := (c d').isLt
  simp only [Fin.ne_iff_vne] at hab' had' hbd'
  omega

private lemma clon2_upper_coloring :
    (Hclon.induce (((({0, 1, 2, 5} : Finset (Fin 14)) : Set (Fin 14)))ᶜ)).Colorable 2 := by
  let A : Finset (Fin 14) := {3, 4, 6, 9, 12}
  refine ⟨SimpleGraph.Coloring.mk (fun w => if (w : Fin 14) ∈ A then 0 else 1) ?_⟩
  intro v w hvw
  change Hclon.Adj (v : Fin 14) (w : Fin 14) at hvw
  fin_cases v <;> fin_cases w <;> simp_all [A, Hclon, clonRaw]

private lemma four_disjoint_hits_card
    (O T1 T2 T3 T4 : Finset (Fin 14))
    (h12 : Disjoint T1 T2) (h13 : Disjoint T1 T3) (h14 : Disjoint T1 T4)
    (h23 : Disjoint T2 T3) (h24 : Disjoint T2 T4) (h34 : Disjoint T3 T4)
    (h1 : (O ∩ T1).Nonempty) (h2 : (O ∩ T2).Nonempty)
    (h3 : (O ∩ T3).Nonempty) (h4 : (O ∩ T4).Nonempty) :
    4 ≤ O.card := by
  obtain ⟨x1, hx1O⟩ := h1
  obtain ⟨x2, hx2O⟩ := h2
  obtain ⟨x3, hx3O⟩ := h3
  obtain ⟨x4, hx4O⟩ := h4
  simp only [Finset.mem_inter] at hx1O hx2O hx3O hx4O
  have hx12 : x1 ≠ x2 := fun h => by
    subst x2
    exact Finset.disjoint_left.mp h12 hx1O.2 hx2O.2
  have hx13 : x1 ≠ x3 := fun h => by
    subst x3
    exact Finset.disjoint_left.mp h13 hx1O.2 hx3O.2
  have hx14 : x1 ≠ x4 := fun h => by
    subst x4
    exact Finset.disjoint_left.mp h14 hx1O.2 hx4O.2
  have hx23 : x2 ≠ x3 := fun h => by
    subst x3
    exact Finset.disjoint_left.mp h23 hx2O.2 hx3O.2
  have hx24 : x2 ≠ x4 := fun h => by
    subst x4
    exact Finset.disjoint_left.mp h24 hx2O.2 hx4O.2
  have hx34 : x3 ≠ x4 := fun h => by
    subst x4
    exact Finset.disjoint_left.mp h34 hx3O.2 hx4O.2
  have hsub : {x1, x2, x3, x4} ⊆ O := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hx1O.1
    · exact hx2O.1
    · exact hx3O.1
    · exact hx4O.1
  have hc := Finset.card_le_card hsub
  simpa [hx12, hx13, hx14, hx23, hx24, hx34] using hc

/-- **CLON-2 (§6.2).** The conflict graph of the realizable clone step has odd-cycle-transversal
number `4`, which exceeds `2`; hence the per-clone-step defect is not universally bounded by 2. -/
theorem clon2_oct : oct Hclon = 4 := by
  apply Nat.le_antisymm
  · unfold oct Dq
    let O : Finset (Fin 14) := {0, 1, 2, 5}
    apply Nat.sInf_le
    refine ⟨O, ?_, by decide⟩
    simpa [IsDefectSet, O] using clon2_upper_coloring
  · unfold oct Dq
    let S : Set ℕ := {n | ∃ O : Finset (Fin 14), IsDefectSet Hclon 2 O ∧ O.card = n}
    have hne : S.Nonempty := defectSet_nonempty Hclon (by norm_num)
    have hmin : sInf S ∈ S := Nat.sInf_mem hne
    obtain ⟨O, hcol, hcard⟩ := hmin
    rw [← hcard]
    unfold IsDefectSet at hcol
    let T1 : Finset (Fin 14) := {0, 9, 10}
    let T2 : Finset (Fin 14) := {5, 6, 8}
    let T3 : Finset (Fin 14) := {1, 12, 13}
    let T4 : Finset (Fin 14) := {2, 3, 7}
    have hit1 := defect_hits_triangle O 0 9 10 (by decide) (by decide) (by decide) hcol
    have hit2 := defect_hits_triangle O 5 6 8 (by decide) (by decide) (by decide) hcol
    have hit3 := defect_hits_triangle O 1 12 13 (by decide) (by decide) (by decide) hcol
    have hit4 := defect_hits_triangle O 2 3 7 (by decide) (by decide) (by decide) hcol
    have h1 : (O ∩ T1).Nonempty := by
      rcases hit1 with h | h | h
      · exact ⟨0, by simp [T1, h]⟩
      · exact ⟨9, by simp [T1, h]⟩
      · exact ⟨10, by simp [T1, h]⟩
    have h2 : (O ∩ T2).Nonempty := by
      rcases hit2 with h | h | h
      · exact ⟨5, by simp [T2, h]⟩
      · exact ⟨6, by simp [T2, h]⟩
      · exact ⟨8, by simp [T2, h]⟩
    have h3 : (O ∩ T3).Nonempty := by
      rcases hit3 with h | h | h
      · exact ⟨1, by simp [T3, h]⟩
      · exact ⟨12, by simp [T3, h]⟩
      · exact ⟨13, by simp [T3, h]⟩
    have h4 : (O ∩ T4).Nonempty := by
      rcases hit4 with h | h | h
      · exact ⟨2, by simp [T4, h]⟩
      · exact ⟨3, by simp [T4, h]⟩
      · exact ⟨7, by simp [T4, h]⟩
    exact four_disjoint_hits_card O T1 T2 T3 T4 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) h1 h2 h3 h4

/-- Headline form: the CLON-2 defect strictly exceeds 2. -/
theorem clon2_defect_gt_two : 2 < oct Hclon := by
  rw [clon2_oct]; norm_num

end PaperV
