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
Paper VI research round — Priority 3: extending a preassigned PHYSICAL partial lifting.

The bounded-load lifting induction of Paper VI is restarted from an arbitrary legal partial
family of exterior blocks (`LiftInv` on a set `D₀` of exterior edges: core sets inside `P` of
the prescribed sizes, all block edges present, no core pair reused, incident exterior edges
with disjoint core sets, load at most `r`). Every preassigned block is retained verbatim.
The proof re-runs the induction step of `PaperVI.lift_step` (which only uses the invariant,
never how the earlier blocks were produced); no extendability is assumed.
-/
module

public import PaperVI.TheoremB

@[expose] public section

namespace PaperVI

namespace Research

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

/-- One step of the lifting induction, recording that the previously processed core sets are
retained unchanged (a strengthening of `PaperVI.lift_step`, with the same proof). -/
theorem lift_step_retain {σ : Sym2 V → ℕ} {c r need : ℕ}
    (hσc : ∀ e ∈ extEdges G P, σ e ≤ c)
    (hneed : ∀ e ∈ extEdges G P, σ e * (editDegree G P + (c - 1) * r + 1) ≤
      need + (editDegree G P + (c - 1) * r))
    (hcand : ∀ k bx by_ dx dy sat nD : ℕ, P.card ≤ k + bx + by_ + c * dx + c * dy + sat →
      bx + dx + 1 ≤ editDegree G P → by_ + dy + 1 ≤ editDegree G P → r * sat ≤ c * nD →
      nD + 1 ≤ mCount G P → 2 * mCount G P ≤ Pᶜ.card * editDegree G P → need ≤ k)
    {D : Finset (Sym2 V)} {T : Sym2 V → Finset V} (hinv : LiftInv G P σ r D T)
    (hD : D ⊆ extEdges G P) {e0 : Sym2 V} (he0 : e0 ∈ extEdges G P) (he0D : e0 ∉ D) :
    ∃ T', LiftInv G P σ r (insert e0 D) T' ∧ ∀ e ∈ D, T' e = T e := by
  induction e0 using Sym2.ind with
  | h x y =>
  obtain ⟨bx, by_, dx, dy, sat, h1, h2, h3, h4, h5⟩ :=
    candidates_count G P hinv hσc hD he0 he0D
  have hK := hcand _ _ _ _ _ _ _ h1 h2 h3 h4 h5 (two_mCount_le G P)
  set K := candidates G P r D T x y with hKdef
  have hKP : K ⊆ P := filter_subset _ _
  have hdeg := forbidden_degree G P hinv hσc hD K hKP
  have hk : σ s(x, y) * (editDegree G P + (c - 1) * r + 1) ≤
      K.card + (editDegree G P + (c - 1) * r) := (hneed _ he0).trans (by omega)
  obtain ⟨N, hNK, hNc, hNgood⟩ := exists_good_clique (forbidden G D T) (forbidden_symm G D T)
    _ _ K hdeg hk
  have hNmem : ∀ a ∈ N, a ∈ P ∧ G.Adj x a ∧ G.Adj y a ∧
      (∀ e ∈ D, (x ∈ e ∨ y ∈ e) → a ∉ T e) ∧ (D.filter (fun e => a ∈ T e)).card < r := by
    intro a ha
    have := hNK ha
    simp only [hKdef, candidates, mem_filter] at this
    exact this
  have hNgood' : ∀ a ∈ N, ∀ b ∈ N, a ≠ b → G.Adj a b ∧ ∀ e ∈ D, a ∈ T e → b ∉ T e := by
    intro a ha b hb hab
    have := hNgood a ha b hb hab
    simp only [forbidden, not_or, not_not, not_exists, not_and] at this
    exact ⟨this.1, this.2⟩
  let T' : Sym2 V → Finset V := fun e => if e = s(x, y) then N else T e
  have hT'0 : T' s(x, y) = N := by simp [T']
  have hT'D : ∀ e ∈ D, T' e = T e := fun e he => by
    have : e ≠ s(x, y) := fun h => he0D (h ▸ he)
    simp [T', this]
  have hne : ∀ e ∈ D, e ≠ s(x, y) := fun e he h => he0D (h ▸ he)
  refine ⟨T', ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hT'D⟩
  · intro e he
    rw [mem_insert] at he
    rcases he with rfl | he
    · rw [hT'0]; exact hNK.trans hKP
    · rw [hT'D e he]; exact hinv.sub e he
  · intro e he
    rw [mem_insert] at he
    rcases he with rfl | he
    · rw [hT'0, hNc]
    · rw [hT'D e he]; exact hinv.card e he
  · intro e he a ha b hb hab
    rw [mem_insert] at he
    rcases he with rfl | he
    · rw [hT'0] at ha hb; exact (hNgood' a ha b hb hab).1
    · rw [hT'D e he] at ha hb; exact hinv.coreAdj e he a ha b hb hab
  · intro e he a ha z hz
    rw [mem_insert] at he
    rcases he with rfl | he
    · rw [hT'0] at ha
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · exact (hNmem a ha).2.1.symm
      · exact (hNmem a ha).2.2.1.symm
    · rw [hT'D e he] at ha; exact hinv.crossAdj e he a ha z hz
  · intro e he e' he' hee' a ha b hb hab hae'
    rw [mem_insert] at he he'
    rcases he with rfl | he <;> rcases he' with rfl | he'
    · exact absurd rfl hee'
    · rw [hT'0] at ha hb; rw [hT'D e' he'] at hae' ⊢
      exact (hNgood' a ha b hb hab).2 e' he' hae'
    · rw [hT'D e he] at ha hb; rw [hT'0] at hae' ⊢
      intro hbN
      exact (hNgood' a hae' b hbN hab).2 e he ha hb
    · rw [hT'D e he] at ha hb; rw [hT'D e' he'] at hae' ⊢
      exact hinv.pairDisj e he e' he' hee' a ha b hb hab hae'
  · intro e he e' he' hee' z hz hz' a ha
    rw [mem_insert] at he he'
    rcases he with rfl | he <;> rcases he' with rfl | he'
    · exact absurd rfl hee'
    · rw [hT'0] at ha; rw [hT'D e' he']
      refine (hNmem a ha).2.2.2.1 e' he' ?_
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · exact Or.inl hz'
      · exact Or.inr hz'
    · rw [hT'D e he] at ha; rw [hT'0]
      intro haN
      refine (hNmem a haN).2.2.2.1 e he ?_ ha
      rw [Sym2.mem_iff] at hz'
      rcases hz' with rfl | rfl
      · exact Or.inl hz
      · exact Or.inr hz
    · rw [hT'D e he] at ha; rw [hT'D e' he']
      exact hinv.incDisj e he e' he' hee' z hz hz' a ha
  · intro a
    have hfD : D.filter (fun e => a ∈ T' e) = D.filter (fun e => a ∈ T e) :=
      filter_congr fun e he => by rw [hT'D e he]
    rw [filter_insert, hT'0]
    split_ifs with haN
    · rw [card_insert_of_notMem (fun h => he0D (mem_filter.mp h).1), hfD]
      have := (hNmem a haN).2.2.2.2
      omega
    · rw [hfD]; exact hinv.load a


/-- **Extension principle for physical liftings.** Under the counting hypotheses of the lifting
lemma, every legal partial lifting `T₀` on a set `D₀ ⊆ E(H)` of exterior edges (invariant
`LiftInv` with load at most `r`) extends to a legal lifting of ALL exterior edges with load at
most `r` that coincides with `T₀` on `D₀`: all preassigned physical blocks are retained. -/
theorem extend_lift {σ : Sym2 V → ℕ} {c r need : ℕ}
    (hσc : ∀ e ∈ extEdges G P, σ e ≤ c)
    (hneed : ∀ e ∈ extEdges G P, σ e * (editDegree G P + (c - 1) * r + 1) ≤
      need + (editDegree G P + (c - 1) * r))
    (hcand : ∀ k bx by_ dx dy sat nD : ℕ, P.card ≤ k + bx + by_ + c * dx + c * dy + sat →
      bx + dx + 1 ≤ editDegree G P → by_ + dy + 1 ≤ editDegree G P → r * sat ≤ c * nD →
      nD + 1 ≤ mCount G P → 2 * mCount G P ≤ Pᶜ.card * editDegree G P → need ≤ k)
    {D₀ : Finset (Sym2 V)} {T₀ : Sym2 V → Finset V} (hinv : LiftInv G P σ r D₀ T₀)
    (hD₀ : D₀ ⊆ extEdges G P) :
    ∃ T, LiftInv G P σ r (extEdges G P) T ∧ ∀ e ∈ D₀, T e = T₀ e := by
  have key : ∃ T, LiftInv G P σ r (D₀ ∪ (extEdges G P \ D₀)) T ∧ ∀ e ∈ D₀, T e = T₀ e := by
    refine Finset.induction_on' (motive := fun D => ∃ T, LiftInv G P σ r (D₀ ∪ D) T ∧
      ∀ e ∈ D₀, T e = T₀ e) (extEdges G P \ D₀) ⟨T₀, by simpa using hinv, fun _ _ => rfl⟩ ?_
    intro e0 D he0 hD he0D ih
    obtain ⟨T, hT, hagree⟩ := ih
    have he0' : e0 ∉ D₀ ∪ D := by
      rw [mem_union, not_or]
      exact ⟨(mem_sdiff.mp he0).2, he0D⟩
    have hsub : D₀ ∪ D ⊆ extEdges G P :=
      union_subset hD₀ (hD.trans sdiff_subset)
    obtain ⟨T', hT', hret⟩ := lift_step_retain G P hσc hneed hcand hT hsub
      (mem_sdiff.mp he0).1 he0'
    refine ⟨T', ?_, fun e he => (hret e (mem_union_left _ he)).trans (hagree e he)⟩
    have : D₀ ∪ insert e0 D = insert e0 (D₀ ∪ D) := by
      ext; simp only [mem_union, mem_insert]; tauto
    rw [this]; exact hT'
  obtain ⟨T, hT, hagree⟩ := key
  rw [union_sdiff_of_subset hD₀] at hT
  exact ⟨T, hT, hagree⟩

end Research

end PaperVI
