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
/- A saturated core vertex admits an unprotected load-relief owner when the
target lifting has the same load budget and the new target block is unprotected. -/
module
public import PaperVI.Lifting
@[expose] public section
namespace PaperVIRecourse
open Finset PaperVI
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

/-- The physical load budget of the target leaves a removable owner outside the
protected target-aligned assignments. This is the extra fact needed to preserve
an aligned prefix during Proposition 9.1's repair. -/
theorem exists_unprotected_owner
    {σ : Sym2 V → ℕ} {r : ℕ} {T Tstar : Sym2 V → Finset V}
    (hstar : LiftInv G P σ r (extEdges G P) Tstar)
    {Q D : Finset (Sym2 V)} {e0 : Sym2 V} {a : V}
    (he0 : e0 ∈ extEdges G P) (he0Q : e0 ∉ Q) (ha : a ∈ Tstar e0)
    (hD : D ⊆ extEdges G P) (hDa : ∀ e ∈ D, a ∈ T e)
    (hagree : ∀ e ∈ Q, T e = Tstar e) (hsat : r ≤ D.card) :
    ∃ e ∈ D, e ∉ Q := by
  classical
  by_contra h
  have hDQ : D ⊆ Q := by
    intro e he
    by_contra heQ
    exact h ⟨e,he,heQ⟩
  have he0D : e0 ∉ D := fun he => he0Q (hDQ he)
  have hsub : insert e0 D ⊆ (extEdges G P).filter (fun e => a ∈ Tstar e) := by
    intro e he
    rcases mem_insert.mp he with rfl | he
    · exact mem_filter.mpr ⟨he0,ha⟩
    · exact mem_filter.mpr ⟨hD he,by rw [← hagree e (hDQ he)]; exact hDa e he⟩
  have hc := card_le_card hsub
  rw [card_insert_of_notMem he0D] at hc
  have ht := hstar.load a
  omega

end PaperVIRecourse
