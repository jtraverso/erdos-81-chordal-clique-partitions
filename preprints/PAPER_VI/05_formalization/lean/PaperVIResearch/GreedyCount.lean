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
Paper VI research round — Priority 4, step 1: counting list edge colourings greedily.

If every edge of a finite edge set `F` conflicts (shares an end) with at most `D` other edges
of `F`, and every list has at least `p + D` colours, then there are at least `p^{|F|}` proper
list colourings of `F`. Colourings are encoded as total functions `Sym2 V → C` taking a fixed
default value off `F`, so distinct colourings of `F` are distinct functions.
-/
module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Sym.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace PaperVI

namespace Research

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [Fintype C] [DecidableEq C]

/-- Two edges share an end. -/
def Shares (e e' : Sym2 V) : Prop := ∃ v ∈ e.toFinset, v ∈ e'.toFinset

instance (e e' : Sym2 V) : Decidable (Shares e e') := by unfold Shares; infer_instance

open Classical in
/-- The proper list colourings of an edge set `F` (with default value `d₀` off `F`). -/
noncomputable def listColorings (F : Finset (Sym2 V)) (L : Sym2 V → Finset C) (d₀ : C) :
    Finset (Sym2 V → C) :=
  univ.filter (fun c => (∀ e ∈ F, c e ∈ L e) ∧ (∀ e, e ∉ F → c e = d₀) ∧
    ∀ e ∈ F, ∀ e' ∈ F, e ≠ e' → Shares e e' → c e ≠ c e')

theorem mem_listColorings {F : Finset (Sym2 V)} {L : Sym2 V → Finset C} {d₀ : C}
    {c : Sym2 V → C} : c ∈ listColorings F L d₀ ↔ (∀ e ∈ F, c e ∈ L e) ∧
      (∀ e, e ∉ F → c e = d₀) ∧ ∀ e ∈ F, ∀ e' ∈ F, e ≠ e' → Shares e e' → c e ≠ c e' := by
  simp [listColorings]

/-- **Greedy count.** If every edge of `F` shares an end with at most `D` other edges of `F` and
every list has at least `p + D` colours, there are at least `p^{|F|}` proper list colourings. -/
theorem pow_le_card_listColorings (F : Finset (Sym2 V)) (L : Sym2 V → Finset C) (d₀ : C)
    (p D : ℕ) (hL : ∀ e ∈ F, p + D ≤ (L e).card)
    (hD : ∀ e ∈ F, (F.filter (fun e' => e' ≠ e ∧ Shares e e')).card ≤ D) :
    p ^ F.card ≤ (listColorings F L d₀).card := by
  suffices key : ∀ F' ⊆ F, p ^ F'.card ≤ (listColorings F' L d₀).card from key F subset_rfl
  intro F'
  induction F' using Finset.induction_on with
  | empty =>
    intro _
    rw [card_empty, pow_zero, Nat.one_le_iff_ne_zero, ← pos_iff_ne_zero, card_pos]
    exact ⟨fun _ => d₀, mem_listColorings.mpr ⟨by simp, fun _ _ => rfl, by simp⟩⟩
  | insert e₀ F₁ he₀ ih =>
    intro hsub
    have hF₁ : F₁ ⊆ F := (subset_insert _ _).trans hsub
    have he₀F : e₀ ∈ F := hsub (mem_insert_self _ _)
    have ih' := ih hF₁
    -- restriction map
    let φ : (Sym2 V → C) → (Sym2 V → C) := fun c => Function.update c e₀ d₀
    have hmaps : ∀ c ∈ listColorings (insert e₀ F₁) L d₀, φ c ∈ listColorings F₁ L d₀ := by
      intro c hc
      obtain ⟨h1, h2, h3⟩ := mem_listColorings.mp hc
      refine mem_listColorings.mpr ⟨fun e he => ?_, fun e he => ?_, fun e he e' he' hee' hs => ?_⟩
      · have hne : e ≠ e₀ := fun h => he₀ (h ▸ he)
        simp only [φ, Function.update_of_ne hne]
        exact h1 e (mem_insert_of_mem he)
      · by_cases hne : e = e₀
        · subst hne; simp [φ]
        · simp only [φ, Function.update_of_ne hne]
          exact h2 e (fun h => (mem_insert.mp h).elim hne he)
      · have hne : e ≠ e₀ := fun h => he₀ (h ▸ he)
        have hne' : e' ≠ e₀ := fun h => he₀ (h ▸ he')
        simp only [φ, Function.update_of_ne hne, Function.update_of_ne hne']
        exact h3 e (mem_insert_of_mem he) e' (mem_insert_of_mem he') hee' hs
    rw [card_eq_sum_card_fiberwise hmaps]
    have hfib : ∀ c ∈ listColorings F₁ L d₀,
        p ≤ ((listColorings (insert e₀ F₁) L d₀).filter (fun c' => φ c' = c)).card := by
      intro c hc
      obtain ⟨h1, h2, h3⟩ := mem_listColorings.mp hc
      set bad := (F₁.filter (fun e' => e' ≠ e₀ ∧ Shares e₀ e')).image c with hbad
      have hbadcard : bad.card ≤ D := by
        refine card_image_le.trans ((card_le_card ?_).trans (hD e₀ he₀F))
        exact filter_subset_filter _ hF₁
      set good := L e₀ \ bad with hgood
      have hgoodcard : p ≤ good.card := by
        have h1 := le_card_sdiff bad (L e₀)
        rw [← hgood] at h1
        have := hL e₀ he₀F
        omega
      have himg : good.image (fun x => Function.update c e₀ x) ⊆
          (listColorings (insert e₀ F₁) L d₀).filter (fun c' => φ c' = c) := by
        intro c' hc'
        obtain ⟨x, hx, rfl⟩ := mem_image.mp hc'
        rw [hgood, mem_sdiff] at hx
        rw [mem_filter, mem_listColorings]
        refine ⟨⟨fun e he => ?_, fun e he => ?_, fun e he e' he' hee' hs => ?_⟩, ?_⟩
        · rcases mem_insert.mp he with rfl | he
          · rw [Function.update_self]; exact hx.1
          · have hne : e ≠ e₀ := fun h => he₀ (h ▸ he)
            rw [Function.update_of_ne hne]; exact h1 e he
        · have hne : e ≠ e₀ := fun h => he (h ▸ mem_insert_self _ _)
          rw [Function.update_of_ne hne]
          exact h2 e (fun h => he (mem_insert_of_mem h))
        · rcases mem_insert.mp he with rfl | hF <;> rcases mem_insert.mp he' with rfl | hF'
          · exact absurd rfl hee'
          · have hne' : e' ≠ e := fun h => hee' h.symm
            rw [Function.update_self, Function.update_of_ne hne']
            intro hxe
            apply hx.2
            rw [hbad, mem_image]
            exact ⟨e', mem_filter.mpr ⟨hF', hne', hs⟩, hxe.symm⟩
          · have hne : e ≠ e' := hee'
            rw [Function.update_self, Function.update_of_ne hne]
            intro hxe
            apply hx.2
            rw [hbad, mem_image]
            have hs' : Shares e' e := by
              obtain ⟨v, hv, hv'⟩ := hs; exact ⟨v, hv', hv⟩
            exact ⟨e, mem_filter.mpr ⟨hF, hne, hs'⟩, hxe⟩
          · have hne : e ≠ e₀ := fun h => he₀ (h ▸ hF)
            have hne' : e' ≠ e₀ := fun h => he₀ (h ▸ hF')
            rw [Function.update_of_ne hne, Function.update_of_ne hne']
            exact h3 e hF e' hF' hee' hs
        · funext e
          by_cases hne : e = e₀
          · subst hne; simp [φ, h2 e he₀]
          · simp [φ, Function.update_of_ne hne]
      have hinj : Set.InjOn (fun x => Function.update c e₀ x) good := by
        intro x _ y _ hxy
        have := congrFun hxy e₀
        simpa using this
      calc p ≤ good.card := hgoodcard
        _ = (good.image (fun x => Function.update c e₀ x)).card :=
            (card_image_of_injOn hinj).symm
        _ ≤ _ := card_le_card himg
    calc p ^ (insert e₀ F₁).card = p ^ F₁.card * p := by
          rw [card_insert_of_notMem he₀, pow_succ]
      _ ≤ (listColorings F₁ L d₀).card * p := Nat.mul_le_mul_right _ ih'
      _ = ∑ _c ∈ listColorings F₁ L d₀, p := by rw [sum_const, smul_eq_mul]
      _ ≤ _ := sum_le_sum hfib

end Research

end PaperVI
