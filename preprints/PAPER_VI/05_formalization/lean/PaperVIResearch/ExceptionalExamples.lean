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
Paper VI research round — Theorem E, part 5: consequences.

* The modification graph of the one-exceptional-vertex graph is a star at `z`:
  `h = Δ(G △ S) = (p - a) + b`.
* Split graphs are chordal (no induced cycle of length `≥ 4`).
* **Partial-star obstruction.** With `a = p` (so `G` is split, hence chordal) and
  `b = ⌊p/2⌋ + 1`, the reference formula `cp = s - u - 2m` fails although `h = b`:
  `cp(G) = s - u - 2m + (2b - p) > s - u - 2m`.
-/
module

public import PaperVIResearch.ExceptionalTriangles
public import PaperVI.Rigidity

@[expose] public section

namespace PaperVI

namespace Research

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Adjacency in `cycleGraph n`, in terms of values. -/
theorem cycle_adj_val {n : ℕ} (hn : 2 ≤ n) (i j : Fin n) :
    (SimpleGraph.cycleGraph n).Adj i j ↔ (j.val = i.val + 1 ∨ i.val = j.val + 1 ∨
      (i.val = 0 ∧ j.val + 1 = n) ∨ (j.val = 0 ∧ i.val + 1 = n)) := by
  rw [SimpleGraph.cycleGraph_adj']
  have hi := i.isLt
  have hj := j.isLt
  rcases le_or_gt j i with h | h
  · have e1 : ((i - j : Fin n) : ℕ) = i - j := Fin.coe_sub_iff_le.mpr h
    rcases eq_or_lt_of_le h with h' | h'
    · subst h'; simp only [or_self]; omega
    · have e2 : ((j - i : Fin n) : ℕ) = n + j - i := Fin.coe_sub_iff_lt.mpr h'
      rw [e1, e2]; have : (j : ℕ) < i := h'; omega
  · have e1 : ((j - i : Fin n) : ℕ) = j - i := Fin.coe_sub_iff_le.mpr h.le
    have e2 : ((i - j : Fin n) : ℕ) = n + i - j := Fin.coe_sub_iff_lt.mpr h
    rw [e1, e2]; have : (i : ℕ) < j := h; omega

omit [Fintype V] [DecidableEq V] in
/-- **Split graphs are chordal.** If `V = K ∪ I` with `K` a clique and `I` independent, then
`G` has no induced cycle of length at least four. -/
theorem isChordal_of_split (G : SimpleGraph V) (K I : Set V) (hcov : ∀ v, v ∈ K ∨ v ∈ I)
    (hK : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → G.Adj u v) (hI : ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) :
    IsChordal G := by
  intro n hn
  refine ⟨fun f => ?_⟩
  have hadj : ∀ i j : Fin n, G.Adj (f i) (f j) ↔ (j.val = i.val + 1 ∨ i.val = j.val + 1 ∨
      (i.val = 0 ∧ j.val + 1 = n) ∨ (j.val = 0 ∧ i.val + 1 = n)) := fun i j => by
    rw [f.map_adj_iff, cycle_adj_val (by omega)]
  have hne : ∀ i j : Fin n, i ≠ j → f i ≠ f j := fun i j h h' => h (f.injective h')
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  let i3 : Fin n := ⟨3, by omega⟩
  let iL : Fin n := ⟨n - 1, by omega⟩
  have a01 : G.Adj (f i0) (f i1) := (hadj i0 i1).mpr (by simp [i0, i1])
  have a12 : G.Adj (f i1) (f i2) := (hadj i1 i2).mpr (by simp [i1, i2])
  have a23 : G.Adj (f i2) (f i3) := (hadj i2 i3).mpr (by simp [i2, i3])
  have aL0 : G.Adj (f iL) (f i0) := (hadj iL i0).mpr (by simp [iL, i0]; omega)
  have n02 : ¬ G.Adj (f i0) (f i2) := fun h => by
    have := (hadj i0 i2).mp h; simp only [i0, i2] at this; omega
  have n13 : ¬ G.Adj (f i1) (f i3) := fun h => by
    have := (hadj i1 i3).mp h; simp only [i1, i3] at this; omega
  have nL1 : ¬ G.Adj (f iL) (f i1) := fun h => by
    have := (hadj iL i1).mp h; simp only [iL, i1] at this; omega
  have d02 : f i0 ≠ f i2 := hne _ _ (by simp only [i0, i2, ne_eq, Fin.mk.injEq]; omega)
  have d13 : f i1 ≠ f i3 := hne _ _ (by simp only [i1, i3, ne_eq, Fin.mk.injEq]; omega)
  have dL1 : f iL ≠ f i1 := hne _ _ (by simp only [iL, i1, ne_eq, Fin.mk.injEq]; omega)
  -- membership facts
  have inI_of_notK : ∀ v, v ∉ K → v ∈ I := fun v hv => (hcov v).resolve_left hv
  have notI_of_adj : ∀ u v, G.Adj u v → u ∈ I → v ∉ I := fun u v h hu hv => hI u hu v hv h
  by_cases h1 : f i1 ∈ K
  · by_cases h2 : f i2 ∈ K
    · have h0 : f i0 ∉ K := fun h0 => n02 (hK _ h0 _ h2 d02)
      have hL : f iL ∈ K := by
        by_contra hL
        exact notI_of_adj _ _ aL0 (inI_of_notK _ hL) (inI_of_notK _ h0)
      exact nL1 (hK _ hL _ h1 dL1)
    · have h3 : f i3 ∈ K := by
        by_contra h3
        exact notI_of_adj _ _ a23 (inI_of_notK _ h2) (inI_of_notK _ h3)
      exact n13 (hK _ h1 _ h3 d13)
  · have h0 : f i0 ∈ K := by
      by_contra h0
      exact notI_of_adj _ _ a01 (inI_of_notK _ h0) (inI_of_notK _ h1)
    have h2 : f i2 ∈ K := by
      by_contra h2
      exact notI_of_adj _ _ a12 (inI_of_notK _ h1) (inI_of_notK _ h2)
    exact n02 (hK _ h0 _ h2 d02)

section Examples

variable {G : SimpleGraph V} [DecidableRel G.Adj] {P R A B : Finset V} {z : V}
  (hS : ExSetup G P R A B z)
include hS

omit [Fintype V] [DecidableRel G.Adj] in
/-- `G` and the reference graph agree away from `z`. -/
theorem ExSetup.editAdj_iff (u v : V) :
    (editGraph G P).Adj u v ↔
      (u = z ∧ (v ∈ P \ A ∨ v ∈ B)) ∨ (v = z ∧ (u ∈ P \ A ∨ u ∈ B)) := by
  rw [editGraph_adj]
  have hzv : ∀ w, G.Adj z w ↔ w ∈ A ∨ w ∈ B := hS.adjz
  constructor
  · rintro (⟨hadj, hS'⟩ | ⟨hS', hadj⟩)
    · push_neg at hS'
      rcases hS.cover u with hu | hu | rfl
      · exact absurd hu (hS' hadj.ne).1
      · rcases hS.cover v with hv | hv | rfl
        · exact absurd hv (hS' hadj.ne).2
        · exact absurd hadj (hS.indepR u hu v hv)
        · right; refine ⟨rfl, ?_⟩
          rcases (hzv u).mp hadj.symm with h | h
          · exact absurd (hS.AsubP h) (hS' hadj.ne).1
          · exact Or.inr h
      · left; refine ⟨rfl, ?_⟩
        rcases (hzv v).mp hadj with h | h
        · exact absurd (hS.AsubP h) (hS' hadj.ne).2
        · exact Or.inr h
    · obtain ⟨huv, hP'⟩ := hS'
      rcases hS.cover u with hu | hu | rfl
      · rcases hS.cover v with hv | hv | rfl
        · exact absurd (hS.adjPP u hu v hv huv) hadj
        · exact absurd (hS.adjPR u hu v hv) hadj
        · right; refine ⟨rfl, Or.inl (mem_sdiff.mpr ⟨hu, fun hA => hadj ?_⟩)⟩
          exact ((hzv u).mpr (Or.inl hA)).symm
      · rcases hP' with hP' | hP'
        · exact absurd hP' (fun h => hS.notR_of_P h hu)
        · exact absurd ((hS.adjPR v hP' u hu).symm) hadj
      · left
        rcases hP' with hP' | hP'
        · exact absurd hP' hS.zP
        · refine ⟨rfl, Or.inl (mem_sdiff.mpr ⟨hP', fun hA => hadj ?_⟩)⟩
          exact (hzv v).mpr (Or.inl hA)
  · rintro (⟨rfl, hv⟩ | ⟨rfl, hu⟩)
    · rcases hv with hv | hv
      · rw [mem_sdiff] at hv
        right
        refine ⟨⟨fun h => hS.zP (h ▸ hv.1), Or.inr hv.1⟩, fun h => hv.2 ?_⟩
        rcases (hzv v).mp h with h | h
        · exact h
        · exact absurd (hS.BsubR h) (hS.notR_of_P hv.1)
      · left
        refine ⟨(hzv v).mpr (Or.inr hv), ?_⟩
        rintro ⟨-, h | h⟩
        · exact hS.zP h
        · exact hS.notR_of_P h (hS.BsubR hv)
    · rcases hu with hu | hu
      · rw [mem_sdiff] at hu
        right
        refine ⟨⟨fun h => hS.zP (h ▸ hu.1), Or.inl hu.1⟩, fun h => hu.2 ?_⟩
        rcases (hzv u).mp h.symm with h | h
        · exact h
        · exact absurd (hS.BsubR h) (hS.notR_of_P hu.1)
      · left
        refine ⟨((hzv u).mpr (Or.inr hu)).symm, ?_⟩
        rintro ⟨-, h | h⟩
        · exact hS.notR_of_P h (hS.BsubR hu)
        · exact hS.zP h

/-- **The modification parameter.** `h = Δ(G △ S) = (p - a) + b`: the modification graph is a
star centred at `z` with leaves `(P \ A) ∪ B`. -/
theorem ExSetup.editDegree_eq : editDegree G P = (P.card - A.card) + B.card := by
  classical
  have hdisj : Disjoint (P \ A) B := by
    rw [disjoint_left]
    intro v hv hvB
    exact hS.notR_of_P (mem_sdiff.mp hv).1 (hS.BsubR hvB)
  have hcard : ((P \ A) ∪ B).card = (P.card - A.card) + B.card := by
    rw [card_union_of_disjoint hdisj, card_sdiff_of_subset hS.AsubP]
  have hnz : (editGraph G P).neighborFinset z = (P \ A) ∪ B := by
    ext v
    rw [SimpleGraph.mem_neighborFinset, hS.editAdj_iff, mem_union]
    constructor
    · rintro (⟨-, h⟩ | ⟨rfl, h⟩)
      · exact h
      · rcases h with h | h
        · exact absurd (mem_sdiff.mp h).1 hS.zP
        · exact absurd (hS.BsubR h) hS.zR
    · intro h; exact Or.inl ⟨rfl, h⟩
  have hdz : (editGraph G P).degree z = (P.card - A.card) + B.card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hnz, hcard]
  have hother : ∀ w, (editGraph G P).degree w ≤ (editGraph G P).degree z := by
    intro w
    by_cases hw : w = z
    · rw [hw]
    · rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
      have hsub : (editGraph G P).neighborFinset w ⊆ {z} := by
        intro v hv
        rw [SimpleGraph.mem_neighborFinset, hS.editAdj_iff] at hv
        rcases hv with ⟨h, -⟩ | ⟨h, -⟩
        · exact absurd h hw
        · exact mem_singleton.mpr h
      by_cases hz : z ∈ (editGraph G P).neighborFinset w
      · have h1 : (editGraph G P).neighborFinset w = {z} :=
          (subset_singleton_iff.mp hsub).resolve_left (ne_empty_of_mem hz)
        rw [h1, card_singleton]
        exact card_pos.mpr ⟨w, (SimpleGraph.mem_neighborFinset _ _ _).mpr
          ((SimpleGraph.mem_neighborFinset _ _ _).mp hz).symm⟩
      · have : (editGraph G P).neighborFinset w = ∅ := by
          rcases subset_singleton_iff.mp hsub with h | h
          · exact h
          · exact absurd (h ▸ mem_singleton_self z) hz
        rw [this, card_empty]; exact Nat.zero_le _
  unfold editDegree
  apply le_antisymm
  · convert (editGraph G P).maxDegree_le_of_forall_degree_le _ (fun w => (hother w).trans hdz.le)
  · rw [← hdz]
    convert (editGraph G P).degree_le_maxDegree z

omit [Fintype V] [DecidableRel G.Adj] in
/-- If `a = p`, the graph is split: `P ∪ {z}` is a clique and `R` is independent. -/
theorem ExSetup.isChordal_of_full (hA : A = P) : IsChordal G := by
  refine isChordal_of_split G ((insert z P : Finset V) : Set V) (R : Set V) ?_ ?_ ?_
  · intro v
    rcases hS.cover v with h | h | rfl
    · left; simp [h]
    · right; exact h
    · left; simp
  · intro u hu v hv huv
    simp only [coe_insert, Set.mem_insert_iff, mem_coe] at hu hv
    rcases hu with rfl | hu <;> rcases hv with rfl | hv
    · exact absurd rfl huv
    · exact (hS.adjz v).mpr (Or.inl (hA ▸ hv))
    · exact ((hS.adjz u).mpr (Or.inl (hA ▸ hu))).symm
    · exact hS.adjPP u hu v hv huv
  · intro u hu v hv
    exact hS.indepR u hu v hv

/-- **Partial-star obstruction (split/chordal).** Let `p ≥ 1`, `a = p` and `b = ⌊p/2⌋ + 1`
(with `q ≥ p + 3`; for `p = 0` the defect is `D = 3` instead). Then `G` is chordal, its modification parameter is `h = b`, and the reference
formula fails: `cp(G) = s - u - 2m + (2b - p) ≥ s - u - 2m + 1`. Since `h = b ≈ p/2`, no
uniform threshold `h ≤ c p` with `c > 1/2` (asymptotically) can give the reference formula for
all chordal graphs. -/
theorem ExSetup.partial_star_obstruction (hp : 1 ≤ P.card) (hq : P.card + 2 ≤ R.card)
    (hA : A = P) (hB : B.card = P.card / 2 + 1) :
    IsChordal G ∧ editDegree G P = B.card ∧
    (cp G : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P + (2 * B.card - P.card) ∧
    (sCount G P : ℤ) - uCount G P - 2 * mCount G P < cp G := by
  have hcp := (hS.theoremE1 hq).1
  have hD : Dval A.card B.card = 2 * (B.card : ℤ) - P.card := by
    unfold Dval; rw [hA, hB]; push_cast; omega
  refine ⟨hS.isChordal_of_full hA, by rw [hS.editDegree_eq, hA]; simp, by rw [hcp, hD], ?_⟩
  have hpos : (1 : ℤ) ≤ 2 * (B.card : ℤ) - P.card := by rw [hB]; push_cast; omega
  rw [hcp, hD]; linarith

end Examples

end Research

end PaperVI
