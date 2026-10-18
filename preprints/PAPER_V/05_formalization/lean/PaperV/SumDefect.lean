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
Paper IV — The colourability defect is additive over disjoint unions (v0.9.15 candidate).

`D_q(G ⊔ H) = D_q(G) + D_q(H)` (and `oct(G ⊔ H) = oct G + oct H`): the defect of a disjoint union of
graphs is the sum of the defects. The heart is `induce_sum_colorable_iff` — a deletion set `O` of the
sum `G ⊕g H` makes the survivors `q`-colourable iff its `inl`/`inr` preimages do so on each side —
proved by building colourings directly by casing on `Sum.inl`/`Sum.inr` (no explicit subtype iso).
`card_preimage_sum` splits `|O| = |O_V| + |O_W|`; the additivity is then `sInf` bookkeeping.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Sum
public import PaperV.Core

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Set

@[expose] public section
open SimpleGraph Finset
namespace PaperV
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem induce_sum_colorable_iff (G : SimpleGraph V) (H : SimpleGraph W) (O : Finset (V ⊕ W)) (q : ℕ) :
    ((G.sum H).induce ((O : Set (V ⊕ W))ᶜ)).Colorable q ↔
      (G.induce (((O.preimage Sum.inl (Sum.inl_injective.injOn) : Finset V) : Set V)ᶜ)).Colorable q ∧
      (H.induce (((O.preimage Sum.inr (Sum.inr_injective.injOn) : Finset W) : Set W)ᶜ)).Colorable q := by
  set OV := O.preimage Sum.inl (Sum.inl_injective.injOn) with hOV
  set OW := O.preimage Sum.inr (Sum.inr_injective.injOn) with hOW
  constructor
  · rintro ⟨c⟩
    refine ⟨⟨⟨fun v => c ⟨Sum.inl v.1, ?_⟩, ?_⟩⟩, ⟨⟨fun w => c ⟨Sum.inr w.1, ?_⟩, ?_⟩⟩⟩
    · have := v.2; simp only [hOV, Finset.mem_preimage] at this; simpa using this
    · intro a b hab; exact c.valid hab
    · have := w.2; simp only [hOW, Finset.mem_preimage] at this; simpa using this
    · intro a b hab; exact c.valid hab
  · rintro ⟨⟨cG⟩, ⟨cH⟩⟩
    refine ⟨⟨fun x => ?_, ?_⟩⟩
    · rcases hx : x.1 with v | w
      · exact cG ⟨v, by have := x.2; simp only [Set.mem_compl_iff, Finset.mem_coe, hOV,
          Finset.mem_preimage] at this ⊢; rw [hx] at this; simpa using this⟩
      · exact cH ⟨w, by have := x.2; simp only [Set.mem_compl_iff, Finset.mem_coe, hOW,
          Finset.mem_preimage] at this ⊢; rw [hx] at this; simpa using this⟩
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hab
      have hadj : (G.sum H).Adj x y := hab
      match x, y, hadj with
      | Sum.inl v, Sum.inl v', hadj => exact cG.valid hadj
      | Sum.inr w, Sum.inr w', hadj => exact cH.valid hadj

theorem card_preimage_sum (O : Finset (V ⊕ W)) :
    (O.preimage Sum.inl (Sum.inl_injective.injOn)).card
      + (O.preimage Sum.inr (Sum.inr_injective.injOn)).card = O.card := by
  have hunion : O = (O.preimage Sum.inl (Sum.inl_injective.injOn)).map ⟨Sum.inl, Sum.inl_injective⟩ ∪
      (O.preimage Sum.inr (Sum.inr_injective.injOn)).map ⟨Sum.inr, Sum.inr_injective⟩ := by
    ext x; rcases x with v | w <;> simp [Finset.mem_preimage, Sum.exists]
  have hdisj : Disjoint
      ((O.preimage Sum.inl (Sum.inl_injective.injOn)).map ⟨Sum.inl, Sum.inl_injective⟩)
      ((O.preimage Sum.inr (Sum.inr_injective.injOn)).map ⟨Sum.inr, Sum.inr_injective⟩) := by
    rw [Finset.disjoint_left]; rintro a ha hb
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at ha hb
    obtain ⟨v, _, rfl⟩ := ha; obtain ⟨w, _, hw⟩ := hb; simp at hw
  conv_rhs => rw [hunion]
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map]

/-- **Defect is additive over disjoint unions:** `D_q(G ⊔ H) = D_q(G) + D_q(H)`. -/
theorem Dq_sum (G : SimpleGraph V) (H : SimpleGraph W) {q : ℕ} (hq : 1 ≤ q) :
    Dq (G.sum H) q = Dq G q + Dq H q := by
  apply le_antisymm
  · obtain ⟨OG, hOG, hOGc⟩ := Nat.sInf_mem (defectSet_nonempty G hq)
    obtain ⟨OH, hOH, hOHc⟩ := Nat.sInf_mem (defectSet_nonempty H hq)
    have e1 : OG.card = Dq G q := hOGc
    have e2 : OH.card = Dq H q := hOHc
    set O := OG.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ OH.map ⟨Sum.inr, Sum.inr_injective⟩ with hO
    have hpreV : O.preimage Sum.inl (Sum.inl_injective.injOn) = OG := by
      ext v; simp [hO, Finset.mem_preimage, Sum.inl.injEq]
    have hpreW : O.preimage Sum.inr (Sum.inr_injective.injOn) = OH := by
      ext w; simp [hO, Finset.mem_preimage, Sum.inr.injEq]
    have hdefect : IsDefectSet (G.sum H) q O := by
      rw [IsDefectSet, induce_sum_colorable_iff, hpreV, hpreW]; exact ⟨hOG, hOH⟩
    have hcard : O.card = Dq G q + Dq H q := by
      rw [← card_preimage_sum O, hpreV, hpreW, e1, e2]
    calc Dq (G.sum H) q ≤ O.card := Nat.sInf_le ⟨O, hdefect, rfl⟩
      _ = Dq G q + Dq H q := hcard
  · obtain ⟨O, hO, hOc⟩ := Nat.sInf_mem (defectSet_nonempty (G.sum H) hq)
    have hOcd : O.card = Dq (G.sum H) q := hOc
    rw [IsDefectSet, induce_sum_colorable_iff] at hO
    have hleG : Dq G q ≤ (O.preimage Sum.inl (Sum.inl_injective.injOn)).card :=
      Nat.sInf_le ⟨_, hO.1, rfl⟩
    have hleH : Dq H q ≤ (O.preimage Sum.inr (Sum.inr_injective.injOn)).card :=
      Nat.sInf_le ⟨_, hO.2, rfl⟩
    have hcp := card_preimage_sum O
    omega

/-- `oct(G ⊔ H) = oct(G) + oct(H)`. -/
theorem oct_sum (G : SimpleGraph V) (H : SimpleGraph W) :
    oct (G.sum H) = oct G + oct H := Dq_sum G H (by norm_num)

end PaperV
