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
Paper VI optimisation round — Priority 3 (continued): the construction with separate budgets.

The single modification parameter `h = Δ(G △ S)` enters the construction in three different
roles. Here they are separated:

* `h_O` bounds `β_x + d_H(x)` at every exterior vertex `x` (missing crossing edges at `x` plus
  exterior degree); it controls the candidate count in the lifting step and `2m ≤ q h_O`;
* `h_C` bounds the number `c_a` of missing core neighbours of every core vertex; it controls the
  forbidden-pair degree;
* `h_A` bounds the number `α_a` of missing exterior neighbours of every core vertex; it only
  enters the list condition of the completion.

All three are at most `h`, so the baseline engine is the special case `h_O = h_C = h_A = h`.
The proofs are the baseline proofs (`PaperVI.Lifting`, `PaperVI.Engine`) with the three local
bounds supplied separately.
-/
module

public import PaperVIOpt.Parametric

@[expose] public section

namespace PaperVI

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Separate local budgets `h_O, h_C, h_A` (see the module documentation). -/
structure Budgets (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) (hO hC hA : ℕ) :
    Prop where
  ext : ∀ x, x ∉ P →
    (P.filter (fun a => ¬ G.Adj x a)).card + (Pᶜ.filter (fun y => G.Adj x y)).card ≤ hO
  core : ∀ a ∈ P, (P.filter (fun b => b ≠ a ∧ ¬ G.Adj a b)).card ≤ hC
  cross : ∀ a ∈ P, (Pᶜ.filter (fun x => ¬ G.Adj a x)).card ≤ hA

variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) {hO hC hA : ℕ}

/-- The uniform budgets `h_O = h_C = h_A = h`. -/
theorem budgets_editDegree : Budgets G P (editDegree G P) (editDegree G P) (editDegree G P) where
  ext x hx := ext_local_bound G P x hx
  core a ha := le_trans (Nat.le_add_right _ _) (core_local_bound G P a ha)
  cross a ha := le_trans (Nat.le_add_left _ _) (core_local_bound G P a ha)

/-- (3): `2m ≤ qh`. -/
theorem two_mCount_le_budget (hb : Budgets G P hO hC hA) : 2 * mCount G P ≤ Pᶜ.card * hO := by
  classical
  have h1 : ∑ x ∈ Pᶜ, ((extEdges G P).filter (fun e => x ∈ e)).card = 2 * mCount G P := by
    rw [sum_card_filter_comm, mCount, card_eq_sum_ones, mul_sum, mul_one]
    refine sum_congr rfl fun e he => ?_
    induction e using Sym2.ind with
    | h x y =>
      rw [mem_extEdges] at he
      have : Pᶜ.filter (fun z => z ∈ s(x, y)) = {x, y} := by
        ext z
        simp only [mem_filter, mem_compl, Sym2.mem_iff, mem_insert, mem_singleton]
        constructor
        · exact fun h => h.2
        · rintro (rfl | rfl)
          · exact ⟨he.2.1, Or.inl rfl⟩
          · exact ⟨he.2.2, Or.inr rfl⟩
      rw [this, card_pair he.1.ne]
  rw [← h1]
  calc ∑ x ∈ Pᶜ, ((extEdges G P).filter (fun e => x ∈ e)).card
      ≤ ∑ _x ∈ Pᶜ, hO := by
        refine sum_le_sum fun x hx => ?_
        have hx' : x ∉ P := by simpa using hx
        exact (card_extEdges_incident_le G P x).trans
          (le_trans (Nat.le_add_left _ _) (hb.ext x hx'))
    _ = _ := by rw [sum_const, smul_eq_mul]

/-- Bound on the number of candidates (estimates (14)–(15) and (19), before arithmetic). -/
theorem candidates_count_budget (hb : Budgets G P hO hC hA)
    {σ : Sym2 V → ℕ} {c r : ℕ} {D : Finset (Sym2 V)}
    {T : Sym2 V → Finset V} (hinv : LiftInv G P σ r D T) (hσc : ∀ e ∈ extEdges G P, σ e ≤ c)
    (hD : D ⊆ extEdges G P) {x y : V} (he0 : s(x, y) ∈ extEdges G P) (he0D : s(x, y) ∉ D) :
    ∃ bx by_ dx dy sat : ℕ,
      P.card ≤ (candidates G P r D T x y).card + bx + by_ + c * dx + c * dy + sat ∧
      bx + dx + 1 ≤ hO ∧ by_ + dy + 1 ≤ hO ∧
      r * sat ≤ c * D.card ∧ D.card + 1 ≤ mCount G P := by
  rw [mem_extEdges] at he0
  obtain ⟨hxy, hx, hy⟩ := he0
  refine ⟨(P.filter (fun a => ¬ G.Adj x a)).card, (P.filter (fun a => ¬ G.Adj y a)).card,
    (D.filter (fun e => x ∈ e)).card, (D.filter (fun e => y ∈ e)).card,
    (P.filter (fun a => r ≤ (D.filter (fun e => a ∈ T e)).card)).card, ?_, ?_, ?_, ?_, ?_⟩
  · -- covering of `P`
    have hcov : P ⊆ candidates G P r D T x y ∪ P.filter (fun a => ¬ G.Adj x a) ∪
        P.filter (fun a => ¬ G.Adj y a) ∪ (D.filter (fun e => x ∈ e)).biUnion T ∪
        (D.filter (fun e => y ∈ e)).biUnion T ∪
        P.filter (fun a => r ≤ (D.filter (fun e => a ∈ T e)).card) := by
      intro a ha
      by_cases h1 : G.Adj x a
      · by_cases h2 : G.Adj y a
        · by_cases h3 : ∀ e ∈ D, (x ∈ e ∨ y ∈ e) → a ∉ T e
          · by_cases h4 : (D.filter (fun e => a ∈ T e)).card < r
            · simp only [mem_union]
              left; left; left; left; left
              simp only [candidates, mem_filter]
              exact ⟨ha, h1, h2, h3, h4⟩
            · simp only [mem_union]; right
              simp only [mem_filter]; exact ⟨ha, by omega⟩
          · push_neg at h3
            obtain ⟨e, he, hxy', hae⟩ := h3
            rcases hxy' with hxe | hye
            · simp only [mem_union]; left; left; right
              simp only [mem_biUnion, mem_filter]; exact ⟨e, ⟨he, hxe⟩, hae⟩
            · simp only [mem_union]; left; right
              simp only [mem_biUnion, mem_filter]; exact ⟨e, ⟨he, hye⟩, hae⟩
        · simp only [mem_union]; left; left; left; right
          simp only [mem_filter]; exact ⟨ha, h2⟩
      · simp only [mem_union]; left; left; left; left; right
        simp only [mem_filter]; exact ⟨ha, h1⟩
    have hU : ∀ Dz ⊆ D, (Dz.biUnion T).card ≤ c * Dz.card := by
      intro Dz hDz
      refine (card_biUnion_le).trans ?_
      calc ∑ e ∈ Dz, (T e).card ≤ ∑ _e ∈ Dz, c :=
            sum_le_sum fun e he => (hinv.card e (hDz he)).symm ▸ hσc e (hD (hDz he))
        _ = c * Dz.card := by rw [sum_const, smul_eq_mul, mul_comm]
    refine (card_le_card hcov).trans ?_
    refine (card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
    refine (card_union_le _ _).trans (add_le_add ?_ (hU _ (filter_subset _ _)))
    refine (card_union_le _ _).trans (add_le_add ?_ (hU _ (filter_subset _ _)))
    refine (card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
    exact card_union_le _ _
  · have hsub : insert s(x, y) (D.filter (fun e => x ∈ e)) ⊆
        (extEdges G P).filter (fun e => x ∈ e) := by
      intro e he
      rw [mem_insert] at he
      rcases he with rfl | he
      · simp only [mem_filter, mem_extEdges, Sym2.mem_iff, true_or, and_true]
        exact ⟨hxy, hx, hy⟩
      · simp only [mem_filter] at he ⊢; exact ⟨hD he.1, he.2⟩
    have hnot : s(x, y) ∉ D.filter (fun e => x ∈ e) := fun h => he0D (mem_filter.mp h).1
    have h1 : (D.filter (fun e => x ∈ e)).card + 1 ≤
        ((extEdges G P).filter (fun e => x ∈ e)).card := by
      have := card_le_card hsub
      rwa [card_insert_of_notMem hnot] at this
    have h2 := card_extEdges_incident_le G P x
    have h3 := hb.ext x hx
    omega
  · have hsub : insert s(x, y) (D.filter (fun e => y ∈ e)) ⊆
        (extEdges G P).filter (fun e => y ∈ e) := by
      intro e he
      rw [mem_insert] at he
      rcases he with rfl | he
      · simp only [mem_filter, mem_extEdges, Sym2.mem_iff, or_true, and_true]
        exact ⟨hxy, hx, hy⟩
      · simp only [mem_filter] at he ⊢; exact ⟨hD he.1, he.2⟩
    have hnot : s(x, y) ∉ D.filter (fun e => y ∈ e) := fun h => he0D (mem_filter.mp h).1
    have h1 : (D.filter (fun e => y ∈ e)).card + 1 ≤
        ((extEdges G P).filter (fun e => y ∈ e)).card := by
      have := card_le_card hsub
      rwa [card_insert_of_notMem hnot] at this
    have h2 := card_extEdges_incident_le G P y
    have h3 := hb.ext y hy
    omega
  · calc r * (P.filter (fun a => r ≤ (D.filter (fun e => a ∈ T e)).card)).card
        = ∑ _a ∈ P.filter (fun a => r ≤ (D.filter (fun e => a ∈ T e)).card), r := by
          rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ a ∈ P.filter (fun a => r ≤ (D.filter (fun e => a ∈ T e)).card),
            (D.filter (fun e => a ∈ T e)).card :=
          sum_le_sum fun a ha => (mem_filter.mp ha).2
      _ ≤ ∑ a, (D.filter (fun e => a ∈ T e)).card :=
          sum_le_sum_of_subset (subset_univ _)
      _ = ∑ e ∈ D, (T e).card := sum_load D T
      _ ≤ ∑ _e ∈ D, c := sum_le_sum fun e he => (hinv.card e he).symm ▸ hσc e (hD he)
      _ = c * D.card := by rw [sum_const, smul_eq_mul, mul_comm]
  · have hmem : s(x, y) ∈ extEdges G P := by rw [mem_extEdges]; exact ⟨hxy, hx, hy⟩
    have : D ⊂ extEdges G P :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hD, fun h => he0D (h ▸ hmem)⟩
    exact card_lt_card this

/-- Bound on the forbidden degree inside the candidate set: at most `h + (c-1) r`. -/
theorem forbidden_degree_budget (hb : Budgets G P hO hC hA)
    {σ : Sym2 V → ℕ} {c r : ℕ} {D : Finset (Sym2 V)}
    {T : Sym2 V → Finset V} (hinv : LiftInv G P σ r D T) (hσc : ∀ e ∈ extEdges G P, σ e ≤ c)
    (hD : D ⊆ extEdges G P) (K : Finset V) (hK : K ⊆ P) :
    ∀ a ∈ K, ((K.erase a).filter (forbidden G D T a)).card ≤
      hC + (c - 1) * r := by
  intro a ha
  have haP := hK ha
  have hsub : (K.erase a).filter (forbidden G D T a) ⊆
      P.filter (fun b => b ≠ a ∧ ¬ G.Adj a b) ∪
        (D.filter (fun e => a ∈ T e)).biUnion (fun e => (T e).erase a) := by
    intro b hb
    simp only [mem_filter, mem_erase] at hb
    obtain ⟨⟨hba, hbK⟩, hf⟩ := hb
    rcases hf with hf | ⟨e, he, hae, hbe⟩
    · exact mem_union_left _ (mem_filter.mpr ⟨hK hbK, hba, hf⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨e, mem_filter.mpr ⟨he, hae⟩,
        mem_erase.mpr ⟨hba, hbe⟩⟩)
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  have h1 := hb.core a haP
  have h2 : ((D.filter (fun e => a ∈ T e)).biUnion (fun e => (T e).erase a)).card ≤
      (c - 1) * r := by
    refine card_biUnion_le.trans ?_
    calc ∑ e ∈ D.filter (fun e => a ∈ T e), ((T e).erase a).card
        ≤ ∑ _e ∈ D.filter (fun e => a ∈ T e), (c - 1) := by
          refine sum_le_sum fun e he => ?_
          rw [mem_filter] at he
          rw [card_erase_of_mem he.2, hinv.card e he.1]
          have := hσc e (hD he.1)
          omega
      _ = (c - 1) * (D.filter (fun e => a ∈ T e)).card := by
          rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ (c - 1) * r := Nat.mul_le_mul_left _ (hinv.load a)
  omega

/-- One step of the lifting induction: process the exterior edge `xy`. -/
theorem lift_step_budget (hb : Budgets G P hO hC hA) {σ : Sym2 V → ℕ} {c r need : ℕ}
    (hσc : ∀ e ∈ extEdges G P, σ e ≤ c)
    (hneed : ∀ e ∈ extEdges G P, σ e * (hC + (c - 1) * r + 1) ≤
      need + (hC + (c - 1) * r))
    (hcand : ∀ k bx by_ dx dy sat nD : ℕ, P.card ≤ k + bx + by_ + c * dx + c * dy + sat →
      bx + dx + 1 ≤ hO → by_ + dy + 1 ≤ hO → r * sat ≤ c * nD →
      nD + 1 ≤ mCount G P → 2 * mCount G P ≤ Pᶜ.card * hO → need ≤ k)
    {D : Finset (Sym2 V)} {T : Sym2 V → Finset V} (hinv : LiftInv G P σ r D T)
    (hD : D ⊆ extEdges G P) {e0 : Sym2 V} (he0 : e0 ∈ extEdges G P) (he0D : e0 ∉ D) :
    ∃ T', LiftInv G P σ r (insert e0 D) T' := by
  induction e0 using Sym2.ind with
  | h x y =>
  obtain ⟨bx, by_, dx, dy, sat, h1, h2, h3, h4, h5⟩ :=
    candidates_count_budget G P hb hinv hσc hD he0 he0D
  have hK := hcand _ _ _ _ _ _ _ h1 h2 h3 h4 h5 (two_mCount_le_budget G P hb)
  set K := candidates G P r D T x y with hKdef
  have hKP : K ⊆ P := filter_subset _ _
  have hdeg := forbidden_degree_budget G P hb hinv hσc hD K hKP
  have hk : σ s(x, y) * (hC + (c - 1) * r + 1) ≤
      K.card + (hC + (c - 1) * r) := (hneed _ he0).trans (by omega)
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
  refine ⟨T', ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
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

/-- **The lifting lemma.** Under the counting hypothesis `hcand` and the size condition
`hneed`, every exterior edge `e` receives a core set `T e` of size `σ e` such that the lifting
invariant holds for all exterior edges with maximum load `r`. -/
theorem exists_lift_budget (hb : Budgets G P hO hC hA) {σ : Sym2 V → ℕ} {c r need : ℕ}
    (hσc : ∀ e ∈ extEdges G P, σ e ≤ c)
    (hneed : ∀ e ∈ extEdges G P, σ e * (hC + (c - 1) * r + 1) ≤
      need + (hC + (c - 1) * r))
    (hcand : ∀ k bx by_ dx dy sat nD : ℕ, P.card ≤ k + bx + by_ + c * dx + c * dy + sat →
      bx + dx + 1 ≤ hO → by_ + dy + 1 ≤ hO → r * sat ≤ c * nD →
      nD + 1 ≤ mCount G P → 2 * mCount G P ≤ Pᶜ.card * hO → need ≤ k) :
    ∃ T, LiftInv G P σ r (extEdges G P) T := by
  refine Finset.induction_on' (motive := fun D => ∃ T, LiftInv G P σ r D T) (extEdges G P)
    ⟨fun _ => ∅, by constructor <;> simp⟩ ?_
  intro e0 D he0 hD he0D ih
  obtain ⟨T, hT⟩ := ih
  exact lift_step_budget G P hb hσc hneed hcand hT hD he0 he0D

/-- At most `h + 2r` exterior vertices are unavailable at a core vertex after lifting. -/
theorem card_unavail_le_budget (hb : Budgets G P hO hC hA)
    {σ : Sym2 V → ℕ} {r : ℕ} {T : Sym2 V → Finset V}
    (hT : LiftInv G P σ r (extEdges G P) T) (a : V) (ha : a ∈ P) :
    (Pᶜ.filter (fun x => ¬ availPair G P T a x)).card ≤ hA + 2 * r := by
  have hsub : Pᶜ.filter (fun x => ¬ availPair G P T a x) ⊆
      Pᶜ.filter (fun x => ¬ G.Adj a x) ∪
        ((extEdges G P).filter (fun e => a ∈ T e)).biUnion Sym2.toFinset := by
    intro x hx
    rw [mem_filter] at hx
    obtain ⟨hxc, hx⟩ := hx
    unfold availPair at hx
    by_cases hadj : G.Adj a x
    · have hu : usedPair G P T a x := by tauto
      obtain ⟨e, he, hae, hxe⟩ := hu
      exact mem_union_right _ (mem_biUnion.mpr ⟨e, mem_filter.mpr ⟨he, hae⟩,
        Sym2.mem_toFinset.mpr hxe⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨hxc, hadj⟩)
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  have h1 := hb.cross a ha
  have h2 : (((extEdges G P).filter (fun e => a ∈ T e)).biUnion Sym2.toFinset).card ≤ 2 * r := by
    refine card_biUnion_le.trans ?_
    calc ∑ e ∈ (extEdges G P).filter (fun e => a ∈ T e), e.toFinset.card
        ≤ ∑ _e ∈ (extEdges G P).filter (fun e => a ∈ T e), 2 := by
          refine sum_le_sum fun e _ => ?_
          rw [Sym2.card_toFinset]; split_ifs <;> omega
      _ = 2 * ((extEdges G P).filter (fun e => a ∈ T e)).card := by
          rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ 2 * r := Nat.mul_le_mul_left _ (hT.load a)
  omega

/-- **The general construction.** Under the counting hypothesis `hcand`, the size condition
`hneed` and the list condition `p + 2(h + 2r) ≤ q`, there is an exact clique partition of `G`
in which every block has type `(1,1)`, `(2,1)`, or `(σ e, 2)` where `e` is an exterior edge
contained in the block. -/
theorem exists_partition_of_lift_budget (hb : Budgets G P hO hC hA) {σ : Sym2 V → ℕ} {c r need : ℕ}
    (hσc : ∀ e ∈ extEdges G P, σ e ≤ c)
    (hneed : ∀ e ∈ extEdges G P, σ e * (hC + (c - 1) * r + 1) ≤
      need + (hC + (c - 1) * r))
    (hcand : ∀ k bx by_ dx dy sat nD : ℕ, P.card ≤ k + bx + by_ + c * dx + c * dy + sat →
      bx + dx + 1 ≤ hO → by_ + dy + 1 ≤ hO → r * sat ≤ c * nD →
      nD + 1 ≤ mCount G P → 2 * mCount G P ≤ Pᶜ.card * hO → need ≤ k)
    (hlist : P.card + 2 * (hA + 2 * r) ≤ Pᶜ.card) :
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ ∀ B ∈ Bs,
      (coreSize P B = 1 ∧ extSize P B = 1) ∨ (coreSize P B = 2 ∧ extSize P B = 1) ∨
      ∃ e ∈ extEdges G P, (∀ v ∈ e, v ∈ B) ∧ coreSize P B = σ e ∧ extSize P B = 2 := by
  obtain ⟨T, hT⟩ := exists_lift_budget G P hb hσc hneed hcand
  obtain ⟨f, hf1, hf2, hf3⟩ := exists_completion_coloring P (availPair G P T)
    (hA + 2 * r) (card_unavail_le_budget G P hb hT) hlist
  have hf1' := fun a ha b hb hab (_ : residPair G P T a b) => hf1 a ha b hb hab
  have hf2' := fun a ha b hb hab (_ : residPair G P T a b) => hf2 a ha b hb hab
  have hf3' := fun a ha b hb b' hb' hab hab' hbb' (_ : residPair G P T a b)
    (_ : residPair G P T a b') => hf3 a ha b hb b' hb' hab hab' hbb'
  exact ⟨allBlocks G P T f, allBlocks_isCliquePartition hT hf1' hf2' hf3',
    fun B hB => allBlocks_types hT hf2' hB⟩

/-! ### Explicit theorems with separate budgets -/

/-- **Explicit lifting capacity, separate budgets.** The abstract counting hypothesis of
`exists_partition_of_lift` follows from the explicit capacity inequality
`r (need + 2c(h-1)) + c(m-1) ≤ r p` (required only when `h ≥ 1` and `m ≥ 1`) together with
`c ≥ 1` and `r ≥ 1`. -/
theorem exists_partition_param_budget (hb : Budgets G P hO hC hA)
    {σ : Sym2 V → ℕ} {c r need : ℕ} (hc : 1 ≤ c)
    (hσc : ∀ e ∈ extEdges G P, σ e ≤ c)
    (hneed : ∀ e ∈ extEdges G P, σ e * (hC + (c - 1) * r + 1) ≤
      need + (hC + (c - 1) * r))
    (hcap : 1 ≤ hO → 1 ≤ mCount G P → 0 < r ∧
      (r : ℤ) * (need + 2 * c * ((hO : ℤ) - 1)) + c * ((mCount G P : ℤ) - 1) ≤
        r * P.card)
    (hlist : P.card + 2 * (hA + 2 * r) ≤ Pᶜ.card) :
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ ∀ B ∈ Bs,
      (coreSize P B = 1 ∧ extSize P B = 1) ∨ (coreSize P B = 2 ∧ extSize P B = 1) ∨
      ∃ e ∈ extEdges G P, (∀ v ∈ e, v ∈ B) ∧ coreSize P B = σ e ∧ extSize P B = 2 := by
  refine exists_partition_of_lift_budget G P hb hσc hneed ?_ hlist
  intro k bx by_ dx dy sat nD h1 h2 h3 h4 h5 _h6
  obtain ⟨hr, hineq⟩ := hcap (by omega) (by omega)
  have hbx : bx + c * dx ≤ c * (hO - 1) := by
    have : bx + dx ≤ hO - 1 := by omega
    calc bx + c * dx ≤ c * bx + c * dx := by nlinarith
      _ = c * (bx + dx) := by ring
      _ ≤ c * (hO - 1) := Nat.mul_le_mul_left _ this
  have hby : by_ + c * dy ≤ c * (hO - 1) := by
    have : by_ + dy ≤ hO - 1 := by omega
    calc by_ + c * dy ≤ c * by_ + c * dy := by nlinarith
      _ = c * (by_ + dy) := by ring
      _ ≤ c * (hO - 1) := Nat.mul_le_mul_left _ this
  have hsat : r * sat ≤ c * (mCount G P - 1) :=
    h4.trans (Nat.mul_le_mul_left _ (by omega))
  have hh1 : 1 ≤ hO := by omega
  have hm1 : 1 ≤ mCount G P := by omega
  have e1 : ((hO - 1 : ℕ) : ℤ) = (hO : ℤ) - 1 := by push_cast [hh1]; ring
  have e2 : ((mCount G P - 1 : ℕ) : ℤ) = (mCount G P : ℤ) - 1 := by push_cast [hm1]; ring
  have hbxZ : (bx : ℤ) + c * dx ≤ c * ((hO : ℤ) - 1) := by
    rw [← e1]; exact_mod_cast hbx
  have hbyZ : (by_ : ℤ) + c * dy ≤ c * ((hO : ℤ) - 1) := by
    rw [← e1]; exact_mod_cast hby
  have hsatZ : (r : ℤ) * sat ≤ c * ((mCount G P : ℤ) - 1) := by
    rw [← e2]; exact_mod_cast hsat
  have h1Z : (P.card : ℤ) ≤ k + bx + by_ + c * dx + c * dy + sat := by exact_mod_cast h1
  have hrZ : (0 : ℤ) < r := by exact_mod_cast hr
  have key : (r : ℤ) * need ≤ r * k := by nlinarith
  exact_mod_cast le_of_mul_le_mul_left key hrZ

/-- **Theorem A with separate budgets.** With budgets `h_O, h_C, h_A` and a load cap `r`, if
`p + 2(h_A + 2r) ≤ q` and, when `h_O, m ≥ 1`, `r ≥ 1` and
`r (h_C + 4h_O + r - 2) + 2(m - 1) ≤ r p`, then
`cp(G) = cp_{≤4}(G) = s - u - 2m = pq - binom(p,2) + C - A - 2m`, attained by a partition with
`m` blocks `K_4` of type `(2,2)`, `u - m` triangles `(2,1)` and `s - 2u - 2m` crossing edges. -/
theorem cp_budget_K4 (hb : Budgets G P hO hC hA) (r : ℕ)
    (hcap : 1 ≤ hO → 1 ≤ mCount G P → 0 < r ∧
      (r : ℤ) * ((hC : ℤ) + 4 * hO + r - 2) + 2 * ((mCount G P : ℤ) - 1) ≤ r * P.card)
    (hlist : P.card + 2 * (hA + 2 * r) ≤ Pᶜ.card) :
    (cp G : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P ∧
    (cp G : ℤ) = (P.card : ℤ) * ((Fintype.card V : ℤ) - P.card) - (P.card.choose 2 : ℤ) +
      Cdef G P - Adef G P - 2 * mCount G P ∧
    cp G = cpLe 4 G ∧
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ Bs.card = cp G ∧
      (∀ B ∈ Bs, B.card ≤ 4) ∧ (∀ B ∈ Bs, IsTypeA P B) ∧
      typeCount P Bs 2 2 = mCount G P ∧
      (typeCount P Bs 2 1 : ℤ) = (uCount G P : ℤ) - mCount G P ∧
      (typeCount P Bs 1 1 : ℤ) = (sCount G P : ℤ) - 2 * uCount G P - 2 * mCount G P := by
  obtain ⟨Bs, hBs, htypes⟩ := exists_partition_param_budget G P hb (σ := fun _ => 2) (c := 2) (r := r)
    (need := hC + r + 2) (by norm_num) (fun _ _ => le_rfl)
    (fun _ _ => by simp only [Nat.add_one_sub_one, one_mul]; omega)
    (fun h1 h2 => by
      obtain ⟨hr, hc⟩ := hcap h1 h2
      refine ⟨hr, ?_⟩
      push_cast
      linarith)
    hlist
  have htA : ∀ B ∈ Bs, IsTypeA P B := fun B hB => by
    rcases htypes B hB with h | h | ⟨e, -, -, hc, hb⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl ⟨hc, hb⟩
  obtain ⟨hcp, h4, hcard, hle, c22, c21, c11⟩ := theoremA_conclusions G P hBs htA
  exact ⟨hcp, hcp.trans (sum_formula_pq G P), h4, Bs, hBs, hcard, hle, htA, c22, c21, c11⟩

/-- **Theorem B with separate budgets.** With budgets `h_O, h_C, h_A`, a load cap `r` and a
prescription `σ : E(H) → {4,5}`, if `p + 2(h_A + 2r) ≤ q` and, when `h_O, m ≥ 1`, `r ≥ 1` and
`r (2h_C + 6h_O + 4r - 3) + 3(m - 1) ≤ r p`, then there is an optimal clique partition in which every
exterior edge `xy` lies in a block `K_{σ(xy)}` with exactly two exterior vertices, every other
block is a `(2,1)` triangle or a crossing edge, `cp(G) = s - u - 2m`, and the block counts are
`N₅ = k`, `N₄ = m - k`, `N₃ = u - m - 2k`, `N₂ = s - 2u - 2m + 2k` with `k = |σ⁻¹(5)|`. -/
theorem cp_budget_B (hb : Budgets G P hO hC hA)
    (r : ℕ) (σ : Sym2 V → ℕ) (hσ : ∀ e ∈ extEdges G P, σ e = 4 ∨ σ e = 5)
    (hcap : 1 ≤ hO → 1 ≤ mCount G P → 0 < r ∧
      (r : ℤ) * (2 * (hC : ℤ) + 6 * hO + 4 * r - 3) + 3 * ((mCount G P : ℤ) - 1) ≤
        r * P.card)
    (hlist : P.card + 2 * (hA + 2 * r) ≤ Pᶜ.card) :
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ Bs.card = cp G ∧
      (cp G : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P ∧
      (cp G : ℤ) = (P.card : ℤ) * ((Fintype.card V : ℤ) - P.card) - (P.card.choose 2 : ℤ) +
        Cdef G P - Adef G P - 2 * mCount G P ∧
      (∀ e ∈ extEdges G P, ∃ B ∈ Bs, (∀ v ∈ e, v ∈ B) ∧ B.card = σ e ∧ extSize P B = 2) ∧
      (∀ B ∈ Bs, (coreSize P B = 2 ∧ extSize P B = 1) ∨ (coreSize P B = 1 ∧ extSize P B = 1) ∨
        ∃ e ∈ extEdges G P, (∀ v ∈ e, v ∈ B) ∧ B.card = σ e ∧ extSize P B = 2) ∧
      ((Bs.filter (fun B => B.card = 5)).card : ℤ) =
        ((extEdges G P).filter (fun e => σ e = 5)).card ∧
      ((Bs.filter (fun B => B.card = 4)).card : ℤ) =
        (mCount G P : ℤ) - ((extEdges G P).filter (fun e => σ e = 5)).card ∧
      ((Bs.filter (fun B => B.card = 3)).card : ℤ) =
        (uCount G P : ℤ) - mCount G P - 2 * ((extEdges G P).filter (fun e => σ e = 5)).card ∧
      ((Bs.filter (fun B => B.card = 2)).card : ℤ) =
        (sCount G P : ℤ) - 2 * uCount G P - 2 * mCount G P +
          2 * ((extEdges G P).filter (fun e => σ e = 5)).card := by
  obtain ⟨Bs, hBs, htypes⟩ := exists_partition_param_budget G P hb (σ := fun e => σ e - 2) (c := 3)
    (r := r) (need := 2 * (hC + 2 * r) + 3) (by norm_num)
    (fun e he => by rcases hσ e he with h | h <;> omega)
    (fun e he => by rcases hσ e he with h | h <;> rw [h] <;> omega)
    (fun h1 h2 => by
      obtain ⟨hr, hc⟩ := hcap h1 h2
      refine ⟨hr, ?_⟩
      push_cast
      linarith)
    hlist
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    prescribed_partition_conclusions G P σ hσ hBs htypes
  exact ⟨Bs, hBs, h1, h2, h2.trans (sum_formula_pq G P), h3, h4, h5, h6, h7, h8⟩

end PaperVI
