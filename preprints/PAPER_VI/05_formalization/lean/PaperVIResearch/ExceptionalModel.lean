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
Paper VI research round — concrete models of the one-exceptional-vertex graph.

For all `p, r, a, b` with `a ≤ p` and `b ≤ r` there is an actual graph on `Fin (p + r + 1)`
satisfying `ExSetup` with `|P| = p`, `|R| = r = q - 1`, `|A| = a`, `|B| = b`. Hence the
hypotheses of Theorem E are never vacuous, and the exact formulas apply to these graphs.
-/
module

public import PaperVIResearch.ExceptionalCleanup

@[expose] public section

namespace PaperVI

namespace Research

open Finset

/-- `|{i < n : j ≤ i < k}| = k - j` for `k ≤ n`. -/
theorem card_fin_Ico (n j k : ℕ) (hk : k ≤ n) :
    (univ.filter (fun i : Fin n => j ≤ i.val ∧ i.val < k)).card = k - j := by
  rw [← card_map Fin.valEmbedding]
  have : (univ.filter (fun i : Fin n => j ≤ i.val ∧ i.val < k)).map Fin.valEmbedding =
      Ico j k := by
    ext m
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Ico]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hm; exact ⟨⟨m, by omega⟩, hm, rfl⟩
  rw [this, Nat.card_Ico]

/-- One direction of the adjacency of the model: core–core, core–`R`, and `z` to its
neighbours (the first `a` core vertices and the first `b` vertices of `R`). -/
def exBase (p r a b u v : ℕ) : Prop :=
  (u < p ∧ v < p) ∨ (u < p ∧ p ≤ v ∧ v < p + r) ∨ (u = p + r ∧ (v < a ∨ (p ≤ v ∧ v < p + b)))

instance (p r a b u v : ℕ) : Decidable (exBase p r a b u v) := by
  unfold exBase; infer_instance

/-- The model graph on `Fin (p + r + 1)`: vertices `0..p-1` form the clique `P`, vertices
`p..p+r-1` the independent set `R`, and `p + r` is the exceptional vertex `z`. -/
def exModel (p r a b : ℕ) : SimpleGraph (Fin (p + r + 1)) where
  Adj u v := u ≠ v ∧ (exBase p r a b u.val v.val ∨ exBase p r a b v.val u.val)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (p r a b : ℕ) : DecidableRel (exModel p r a b).Adj := fun u v => by
  show Decidable (u ≠ v ∧ (exBase p r a b u.val v.val ∨ exBase p r a b v.val u.val))
  infer_instance

/-- The parts of the model. -/
def exP (p r : ℕ) : Finset (Fin (p + r + 1)) := univ.filter (fun i => 0 ≤ i.val ∧ i.val < p)
/-- The independent set `R`. -/
def exR (p r : ℕ) : Finset (Fin (p + r + 1)) :=
  univ.filter (fun i => p ≤ i.val ∧ i.val < p + r)
/-- The core neighbours of `z`. -/
def exA (p r a : ℕ) : Finset (Fin (p + r + 1)) := univ.filter (fun i => 0 ≤ i.val ∧ i.val < a)
/-- The `R`-neighbours of `z`. -/
def exB (p r b : ℕ) : Finset (Fin (p + r + 1)) :=
  univ.filter (fun i => p ≤ i.val ∧ i.val < p + b)
/-- The exceptional vertex. -/
def exZ (p r : ℕ) : Fin (p + r + 1) := ⟨p + r, by omega⟩

/-- **The model satisfies the setup of Theorem E**, with the prescribed part sizes. -/
theorem exModel_setup {p r a b : ℕ} (ha : a ≤ p) (hb : b ≤ r) :
    ExSetup (exModel p r a b) (exP p r) (exR p r) (exA p r a) (exB p r b) (exZ p r) ∧
      (exP p r).card = p ∧ (exR p r).card = r ∧ (exA p r a).card = a ∧
      (exB p r b).card = b := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [disjoint_left]
    intro v h1 h2
    simp only [exP, exR, mem_filter, mem_univ, true_and] at h1 h2
    omega
  · simp [exP, exZ]
  · simp [exR, exZ]
  · intro v
    simp only [exP, exR, mem_filter, mem_univ, true_and, exZ, Fin.ext_iff]
    omega
  · intro u hu v hv huv
    simp only [exP, mem_filter, mem_univ, true_and] at hu hv
    exact ⟨huv, Or.inl (Or.inl ⟨hu.2, hv.2⟩)⟩
  · intro u hu x hx
    simp only [exP, exR, mem_filter, mem_univ, true_and] at hu hx
    refine ⟨fun h => ?_, Or.inl (Or.inr (Or.inl ⟨hu.2, hx⟩))⟩
    rw [Fin.ext_iff] at h
    omega
  · intro x hx y hy h
    simp only [exR, mem_filter, mem_univ, true_and] at hx hy
    simp only [exModel, exBase] at h
    omega
  · intro v hv
    simp only [exA, exP, mem_filter, mem_univ, true_and] at hv ⊢
    omega
  · intro v hv
    simp only [exB, exR, mem_filter, mem_univ, true_and] at hv ⊢
    omega
  · intro v
    simp only [exModel, exBase, exA, exB, exZ, mem_filter, mem_univ, true_and, ne_eq,
      Fin.ext_iff]
    omega
  · simpa [exP] using card_fin_Ico (p + r + 1) 0 p (by omega)
  · simpa [exR] using card_fin_Ico (p + r + 1) p (p + r) (by omega)
  · simpa [exA] using card_fin_Ico (p + r + 1) 0 a (by omega)
  · simpa [exB] using card_fin_Ico (p + r + 1) p (p + b) (by omega)

/-- **Theorem E1 on the concrete model.** For `a ≤ p`, `b ≤ r` and `r ≥ p + 2` (i.e.
`q ≥ p + 3`): `cp = p r + a - binom(p,2) - 2b + D(a,b)`. -/
theorem exModel_cp {p r a b : ℕ} (ha : a ≤ p) (hb : b ≤ r) (hq : p + 2 ≤ r) :
    (cp (exModel p r a b) : ℤ) = (p : ℤ) * r + a - (p.choose 2 : ℤ) - 2 * b + Dval a b := by
  obtain ⟨hS, hP, hR, hA, hB⟩ := exModel_setup ha hb
  have := hS.cp_eq_explicit (by omega)
  rw [hP, hR, hA, hB] at this
  exact this

/-- **Linear gap on the concrete model.** For every `p ≥ 19` divisible by three, the split
graph `exModel p (2p - 1) p (2p/3)` has `cp - max_Q Φ_Q = p/3`. -/
theorem exModel_linear_gap {t : ℕ} (ht : 7 ≤ t) :
    IsChordal (exModel (3 * t) (6 * t - 1) (3 * t) (2 * t)) ∧
    IsGreatest (Set.range (PhiQ (exModel (3 * t) (6 * t - 1) (3 * t) (2 * t))))
      (PhiQ (exModel (3 * t) (6 * t - 1) (3 * t) (2 * t)) (exP (3 * t) (6 * t - 1))) ∧
    (cp (exModel (3 * t) (6 * t - 1) (3 * t) (2 * t)) : ℤ) -
      PhiQ (exModel (3 * t) (6 * t - 1) (3 * t) (2 * t)) (exP (3 * t) (6 * t - 1)) = t := by
  obtain ⟨hS, hP, hR, hA, hB⟩ := exModel_setup (p := 3 * t) (r := 6 * t - 1) (a := 3 * t)
    (b := 2 * t) le_rfl (by omega)
  have hAP : exA (3 * t) (6 * t - 1) (3 * t) = exP (3 * t) (6 * t - 1) := rfl
  obtain ⟨h1, -, -, h4, h5⟩ := hS.cleanup_counterexample (by omega) (by omega) hAP
    (by rw [hB, hP]; ring)
  refine ⟨h1, h4, ?_⟩
  rw [hP] at h5
  push_cast at h5
  linarith

end Research

end PaperVI
