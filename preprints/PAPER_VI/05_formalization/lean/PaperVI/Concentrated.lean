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
Paper VI — Section 8: concentrated modifications. The value (27) and the failure of the
formula with the original core.
-/
module

public import PaperVI.JoinVariant
public import PaperVI.Examples

@[expose] public section

open Finset
namespace PaperVI
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- With the original core `P`, the full exterior star at `w ∉ P` has `q - 1` edges. -/
theorem mCount_star (P : Finset V) {w : V} (hw : w ∉ P) :
    mCount (refGraph (insert w P)) P = Pᶜ.card - 1 := by
  have hcomp : w ∈ Pᶜ := mem_compl.mpr hw
  rw [← card_erase_of_mem hcomp, mCount]
  have : extEdges (refGraph (insert w P)) P = (Pᶜ.erase w).image (fun z => s(w, z)) := by
    ext e
    induction e using Sym2.ind with
    | h x y =>
      rw [mem_extEdges, mem_image]
      simp only [refGraph, mem_insert, mem_erase, mem_compl]
      constructor
      · rintro ⟨⟨hxy, (hx | hx) | (hy | hy)⟩, hxP, hyP⟩
        · subst hx; exact ⟨y, ⟨fun h => hxy h.symm, hyP⟩, rfl⟩
        · exact absurd hx hxP
        · subst hy; exact ⟨x, ⟨hxy, hxP⟩, Sym2.eq_swap⟩
        · exact absurd hy hyP
      · rintro ⟨z, ⟨hzw, hzP⟩, he⟩
        rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨⟨fun h => hzw h.symm, Or.inl (Or.inl rfl)⟩, hw, hzP⟩
        · exact ⟨⟨hzw, Or.inr (Or.inl rfl)⟩, hzP, hw⟩
  rw [this, card_image_of_injective _ (fun a b h => Sym2.congr_right.mp h)]

/-- **Section 8: the original-core formula fails for concentrated modifications.** Let
`n = 3p` with `p ≥ 1`, let `P` be a core of `p` vertices and `w ∉ P`. Adding the full exterior
star at `w` to `S = K_P ∨ I_O` gives `G' = K_{P ∪ {w}} ∨ I`. Relative to the original core `P`
it has `C = A = 0` and `m = 2p - 1`, yet
`cp(G') = M(3p) - 1 ≠ M(3p) + C - A - 2m = M(3p) - 2(2p-1)`. -/
theorem concentrated_formula_fails (p : ℕ) (hp : 1 ≤ p) (hn : Fintype.card V = 3 * p)
    (P : Finset V) (hP : P.card = p) {w : V} (hw : w ∉ P) :
    Cdef (refGraph (insert w P)) P = 0 ∧ Adef (refGraph (insert w P)) P = 0 ∧
    mCount (refGraph (insert w P)) P = 2 * p - 1 ∧
    (cp (refGraph (insert w P)) : ℤ) = Mval (3 * p) - 1 ∧
    (cp (refGraph (insert w P)) : ℤ) ≠
      Mval (3 * p) + Cdef (refGraph (insert w P)) P - Adef (refGraph (insert w P)) P -
        2 * mCount (refGraph (insert w P)) P := by
  have hjoin : ∀ a ∈ P, ∀ v, a ≠ v → (refGraph (insert w P)).Adj a v :=
    fun a ha v hav => ⟨hav, Or.inl (mem_insert_of_mem ha)⟩
  have hqc : Pᶜ.card = Fintype.card V - P.card := card_compl P
  have hpn : P.card ≤ Fintype.card V := card_le_univ P
  have hu := uCount_join (refGraph (insert w P)) P hjoin
  have hs := sCount_join (refGraph (insert w P)) P hjoin
  have hC : Cdef (refGraph (insert w P)) P = 0 := by unfold Cdef; rw [hu]; ring
  have hA : Adef (refGraph (insert w P)) P = 0 := by
    unfold Adef; rw [hs, hqc]; push_cast [hpn]; ring
  have hm : mCount (refGraph (insert w P)) P = 2 * p - 1 := by
    rw [mCount_star P hw, hqc, hn, hP]; omega
  have hcp := cp_concentrated_example p hp hn (insert w P) (by rw [card_insert_of_notMem hw, hP])
  refine ⟨hC, hA, hm, hcp, ?_⟩
  rw [hcp, hC, hA, hm]
  push_cast [show 1 ≤ 2 * p by omega]
  omega
end PaperVI
