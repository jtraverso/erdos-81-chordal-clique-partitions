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

/- Paper V, F3: a finite greedy list constructor with local conflict bounds. -/
module

public import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

@[expose] public section

open Finset

namespace PaperV.GreedyLists

variable {E H : Type*} [DecidableEq E] [DecidableEq H]

def neighbors (R : E → E → Prop) [DecidableRel R] (B : Finset E) (e : E) : Finset E :=
  B.filter (fun f => e ≠ f ∧ R e f)

/-- A finite greedy construction. Lists and conflicts are checked on actual bases. -/
theorem exists_on [Nonempty H] (R : E → E → Prop) [DecidableRel R]
    (hsymm : ∀ ⦃a b⦄, R a b → R b a) (B : Finset E) (L : E → Finset H)
    (hL : ∀ e ∈ B, (neighbors R B e).card < (L e).card) :
    ∃ c : E → H,
      (∀ e ∈ B, c e ∈ L e) ∧
      (∀ e ∈ B, ∀ f ∈ B, e ≠ f → R e f → c e ≠ c f) := by
  classical
  revert hL
  induction B using Finset.induction_on with
  | empty =>
      intro _
      exact ⟨fun _ => Classical.arbitrary H, by simp, by simp⟩
  | @insert e B he ih =>
      intro hL
      have hLB : ∀ f ∈ B, (neighbors R B f).card < (L f).card := by
        intro f hf
        have hn : neighbors R B f ⊆ neighbors R (insert e B) f := by
          intro g hg
          simp only [neighbors, Finset.mem_filter] at hg ⊢
          exact ⟨Finset.mem_insert_of_mem hg.1, hg.2⟩
        exact lt_of_le_of_lt (Finset.card_le_card hn) (hL f (Finset.mem_insert_of_mem hf))
      obtain ⟨c, hcL, hcR⟩ := ih hLB
      let used := (neighbors R (insert e B) e).image c
      have hu : used.card < (L e).card :=
        lt_of_le_of_lt Finset.card_image_le (hL e (Finset.mem_insert_self _ _))
      have hnot : ¬ L e ⊆ used := by
        intro hs
        have hcard := Finset.card_le_card hs
        omega
      obtain ⟨a, haL, hau⟩ := Finset.not_subset.mp hnot
      let c' : E → H := fun f => if f = e then a else c f
      refine ⟨c', ?_, ?_⟩
      · intro f hf
        rcases Finset.mem_insert.mp hf with rfl | hf
        · simpa [c'] using haL
        · have hfe : f ≠ e := fun h => he (h ▸ hf)
          simpa [c', hfe] using hcL f hf
      · intro f hf g hg hfg hR
        by_cases hfe : f = e <;> by_cases hge : g = e
        · exact False.elim (hfg (hfe.trans hge.symm))
        · have hgB : g ∈ B := (Finset.mem_insert.mp hg).resolve_left hge
          have hgN : g ∈ neighbors R (insert e B) e := by
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_insert_of_mem hgB, (fun h => hge h.symm), hfe ▸ hR⟩
          have hcu : c g ∈ used := Finset.mem_image.mpr ⟨g, hgN, rfl⟩
          intro h
          have hcol : a = c g := by simpa only [c', if_pos hfe, if_neg hge] using h
          exact hau (hcol.symm ▸ hcu)
        · have hfB : f ∈ B := (Finset.mem_insert.mp hf).resolve_left hfe
          have hfN : f ∈ neighbors R (insert e B) e := by
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_insert_of_mem hfB, (fun h => hfe h.symm), hge ▸ hsymm hR⟩
          have hcu : c f ∈ used := Finset.mem_image.mpr ⟨f, hfN, rfl⟩
          intro h
          have hcol : c f = a := by simpa only [c', if_neg hfe, if_pos hge] using h
          exact hau (hcol ▸ hcu)
        · have hfB : f ∈ B := (Finset.mem_insert.mp hf).resolve_left hfe
          have hgB : g ∈ B := (Finset.mem_insert.mp hg).resolve_left hge
          simpa only [c', if_neg hfe, if_neg hge] using hcR f hfB g hgB hfg hR

/-- The empty-base case needs no host, and the nonempty-base case obtains one
from a nonempty list. Thus no extra nonempty-host hypothesis is imposed here. -/
theorem exists_all [Fintype E] (R : E → E → Prop) [DecidableRel R]
    (hsymm : ∀ ⦃a b⦄, R a b → R b a) (L : E → Finset H)
    (hL : ∀ e, (neighbors R Finset.univ e).card < (L e).card) :
    ∃ c : E → H,
      (∀ e, c e ∈ L e) ∧
      (∀ e f, e ≠ f → R e f → c e ≠ c f) := by
  classical
  cases isEmpty_or_nonempty E with
  | inl h =>
      letI := h
      exact ⟨fun e => isEmptyElim e, fun e => isEmptyElim e, fun e => isEmptyElim e⟩
  | inr h =>
      letI := h
      let e := Classical.arbitrary E
      have hpos : 0 < (L e).card := lt_of_le_of_lt (Nat.zero_le _) (hL e)
      obtain ⟨a, _⟩ := Finset.card_pos.mp hpos
      letI : Nonempty H := ⟨a⟩
      obtain ⟨c, hcL, hcR⟩ := exists_on R hsymm Finset.univ L (fun e _ => hL e)
      exact ⟨c, fun e => hcL e (Finset.mem_univ _),
        fun e f => hcR e (Finset.mem_univ _) f (Finset.mem_univ _)⟩

section Endpoints

variable {V : Type*} [DecidableEq V] [Fintype E]

def degree (ends : E → Finset V) (v : V) : ℕ :=
  (Finset.univ.filter (fun e => v ∈ ends e)).card

/-- Local degree-sum bound for bases whose actual endpoints are u,v. -/
theorem conflict_degree_le (ends : E → Finset V) (e : E) (u v : V)
    (he : ends e = {u, v}) :
    (neighbors (fun a b => ¬ Disjoint (ends a) (ends b)) Finset.univ e).card ≤
      degree ends u - 1 + (degree ends v - 1) := by
  classical
  let U := Finset.univ.filter (fun f => u ∈ ends f)
  let W := Finset.univ.filter (fun f => v ∈ ends f)
  have heU : e ∈ U := by simp [U, he]
  have heW : e ∈ W := by simp [W, he]
  have hsub : neighbors (fun a b => ¬ Disjoint (ends a) (ends b)) Finset.univ e ⊆
      U.erase e ∪ W.erase e := by
    intro f hf
    simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    obtain ⟨x, hx, hxf⟩ := Finset.not_disjoint_iff.mp hf.2
    rw [he] at hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hf.1.symm, by simp [U, hxf]⟩)
    · have hxv : x = v := Finset.mem_singleton.mp hx
      subst x
      exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hf.1.symm, by simp [W, hxf]⟩)
  calc
    _ ≤ (U.erase e ∪ W.erase e).card := Finset.card_le_card hsub
    _ ≤ (U.erase e).card + (W.erase e).card := Finset.card_union_le _ _
    _ = _ := by rw [Finset.card_erase_of_mem heU, Finset.card_erase_of_mem heW]; rfl

/-- F3's degree-sum greedy condition, including the empty-base case. -/
theorem exists_host_assignment (ends : E → Finset V) (L : E → Finset H)
    (hends : ∀ e, ∃ u v, u ≠ v ∧ ends e = {u, v})
    (hL : ∀ e u v, ends e = {u, v} →
      degree ends u + degree ends v - 1 ≤ (L e).card) :
    ∃ c : E → H, (∀ e, c e ∈ L e) ∧
      (∀ e f, e ≠ f → ¬ Disjoint (ends e) (ends f) → c e ≠ c f) := by
  classical
  apply exists_all (fun a b => ¬ Disjoint (ends a) (ends b))
    (fun _ _ h hd => h hd.symm) L
  intro e
  obtain ⟨u, v, _, he⟩ := hends e
  have hdeg := conflict_degree_le ends e u v he
  have hu : 1 ≤ degree ends u := by
    apply Finset.one_le_card.mpr
    exact ⟨e, by simp [he]⟩
  have hv : 1 ≤ degree ends v := by
    apply Finset.one_le_card.mpr
    exact ⟨e, by simp [he]⟩
  have hl := hL e u v he
  omega

end Endpoints
end PaperV.GreedyLists
