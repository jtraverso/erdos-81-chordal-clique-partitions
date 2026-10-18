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
Paper VI — Appendix A: an elementary complete-join variant (Theorem A.1).
For `G = K_p ∨ H` with `q ∈ {2p-1, 2p, 2p+1}` and `p ≥ 24 Δ(H)`, every exterior edge is lifted
to a block `K_5` of type `(3,2)` (core triangles found by Mantel's bound), and the residual core
is completed greedily, without the list-colouring theorem.
-/
module

public import PaperVI.TheoremB
public import PaperVI.Rigidity

@[expose] public section

namespace PaperVI

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Mantel's bound -/

omit [Fintype V] in
/-- **Mantel's bound** (ordered form): a triangle-free symmetric relation on a finite set `K`
has at most `|K|² / 2` ordered adjacent pairs. -/
theorem mantel_ordered (K : Finset V) (adj : V → V → Prop) [DecidableRel adj]
    (hsymm : ∀ a b, adj a b → adj b a)
    (htf : ∀ a ∈ K, ∀ b ∈ K, ∀ c ∈ K, adj a b → adj b c → adj a c → False) :
    2 * ((K ×ˢ K).filter (fun p => adj p.1 p.2)).card ≤ K.card ^ 2 := by
  set deg : V → ℕ := fun u => (K.filter (adj u)).card with hdeg
  have hA : ((K ×ˢ K).filter (fun p => adj p.1 p.2)).card = ∑ u ∈ K, deg u := by
    rw [card_filter, sum_product]
    refine sum_congr rfl fun u _ => ?_
    show _ = (K.filter (adj u)).card
    rw [card_filter]
  rcases K.eq_empty_or_nonempty with rfl | hK
  · simp
  obtain ⟨a0, ha0, hmax⟩ := exists_max_image K deg hK
  set N := K.filter (adj a0) with hN
  have hNK : N ⊆ K := filter_subset _ _
  have hind : ∀ b ∈ N, ∀ c ∈ N, ¬ adj b c := by
    intro b hb c hc hbc
    simp only [hN, mem_filter] at hb hc
    exact htf a0 ha0 b hb.1 c hc.1 hb.2 hbc hc.2
  have hsplit : ∑ u ∈ K, deg u = ∑ u ∈ K \ N, deg u + ∑ u ∈ N, deg u :=
    (sum_sdiff hNK).symm
  have hNdeg : ∑ u ∈ N, deg u ≤ ∑ v ∈ K \ N, deg v := by
    have h1 : ∀ u ∈ N, deg u = ((K \ N).filter (fun v => adj u v)).card := by
      intro u hu
      simp only [hdeg]
      congr 1
      ext v
      simp only [mem_filter, mem_sdiff]
      constructor
      · rintro ⟨hv, huv⟩; exact ⟨⟨hv, fun hvN => hind u hu v hvN huv⟩, huv⟩
      · rintro ⟨⟨hv, -⟩, huv⟩; exact ⟨hv, huv⟩
    rw [sum_congr rfl h1, sum_card_filter_comm]
    refine sum_le_sum fun v _ => card_le_card fun u hu => ?_
    simp only [mem_filter] at hu ⊢
    exact ⟨hNK hu.1, hsymm _ _ hu.2⟩
  have hdel : ∑ v ∈ K \ N, deg v ≤ (K.card - N.card) * N.card := by
    calc ∑ v ∈ K \ N, deg v ≤ ∑ _v ∈ K \ N, N.card :=
          sum_le_sum fun v hv => hmax v (mem_sdiff.mp hv).1
      _ = (K.card - N.card) * N.card := by
          rw [sum_const, card_sdiff_of_subset hNK, smul_eq_mul]
  have hNle : N.card ≤ K.card := card_le_card hNK
  rw [hA]
  have key : 4 * ((K.card - N.card) * N.card) ≤ K.card ^ 2 := by
    obtain ⟨t, ht⟩ : ∃ t, K.card = N.card + t := ⟨K.card - N.card, by omega⟩
    rw [ht, Nat.add_sub_cancel_left]
    nlinarith [sq_nonneg ((N.card : ℤ) - t)]
  omega

/-! ### Greedy completion -/

omit [Fintype V] in
/-- **Greedy completion (Appendix A).** Colour the edges of a graph `J` on `P` with colours from
`R`, avoiding at each vertex `a` the forbidden colours `U a`, so that edges at a common vertex
receive distinct colours. This is possible when `|U_a ∩ R| + d_J(a) ≤ c` at every vertex and
`2c ≤ |R| + 1`, since an edge `ab` then sees at most `2c - 2` forbidden colours. -/
theorem exists_greedy_coloring (P R : Finset V) (J : V → V → Prop) [DecidableRel J]
    (hJsymm : ∀ a b, J a b → J b a) (U : V → V → Prop) [DecidableRel U] (c : ℕ)
    (hbound : ∀ a ∈ P, (R.filter (U a)).card + (P.filter (J a)).card ≤ c)
    (hR : 2 * c ≤ R.card + 1) :
    ∃ g : Sym2 V → V, ∀ a ∈ P, ∀ b ∈ P, J a b →
      g s(a, b) ∈ R ∧ ¬ U a (g s(a, b)) ∧ ¬ U b (g s(a, b)) ∧
      ∀ b' ∈ P, b' ≠ b → J a b' → g s(a, b) ≠ g s(a, b') := by
  set EJ := ((P ×ˢ P).filter (fun p => J p.1 p.2)).image (fun p => s(p.1, p.2)) with hEJ
  have hmemEJ : ∀ a b, a ∈ P → b ∈ P → J a b → s(a, b) ∈ EJ := fun a b ha hb hab =>
    mem_image.mpr ⟨(a, b), mem_filter.mpr ⟨mem_product.mpr ⟨ha, hb⟩, hab⟩, rfl⟩
  let Inv : Finset (Sym2 V) → (Sym2 V → V) → Prop := fun E g =>
    ∀ a ∈ P, ∀ b ∈ P, J a b → s(a, b) ∈ E →
      g s(a, b) ∈ R ∧ ¬ U a (g s(a, b)) ∧ ¬ U b (g s(a, b)) ∧
      ∀ b' ∈ P, b' ≠ b → J a b' → s(a, b') ∈ E → g s(a, b) ≠ g s(a, b')
  have key : ∃ g, Inv EJ g := by
    refine Finset.induction_on' (motive := fun E => ∃ g, Inv E g) EJ
      ⟨fun e => (Quot.out e).1, by intro a _ b _ _ h; simp at h⟩ ?_
    intro e0 E he0 _ he0E ⟨g, hg⟩
    obtain ⟨⟨a0, b0⟩, hmem0, rfl⟩ := mem_image.mp he0
    simp only [mem_filter, mem_product] at hmem0
    obtain ⟨⟨ha0, hb0⟩, hab0J⟩ := hmem0
    dsimp only at ha0 hb0 hab0J he0E ⊢
    set F := R.filter (U a0) ∪ R.filter (U b0) ∪
      ((P.filter (J a0)).erase b0).image (fun b' => g s(a0, b')) ∪
      ((P.filter (J b0)).erase a0).image (fun a' => g s(b0, a')) with hF
    have hFcard : F.card < R.card := by
      have h1 := card_union_le (R.filter (U a0) ∪ R.filter (U b0) ∪
        ((P.filter (J a0)).erase b0).image (fun b' => g s(a0, b')))
        (((P.filter (J b0)).erase a0).image (fun a' => g s(b0, a')))
      have h2 := card_union_le (R.filter (U a0) ∪ R.filter (U b0))
        (((P.filter (J a0)).erase b0).image (fun b' => g s(a0, b')))
      have h3 := card_union_le (R.filter (U a0)) (R.filter (U b0))
      have h4 := card_image_le (s := (P.filter (J a0)).erase b0) (f := fun b' => g s(a0, b'))
      have h5 := card_image_le (s := (P.filter (J b0)).erase a0) (f := fun a' => g s(b0, a'))
      have h6 := card_erase_of_mem (s := P.filter (J a0)) (a := b0) (mem_filter.mpr ⟨hb0, hab0J⟩)
      have h7 := card_erase_of_mem (s := P.filter (J b0)) (a := a0)
        (mem_filter.mpr ⟨ha0, hJsymm _ _ hab0J⟩)
      have h8 := hbound a0 ha0
      have h9 := hbound b0 hb0
      have h10 : 1 ≤ (P.filter (J a0)).card := card_pos.mpr ⟨b0, mem_filter.mpr ⟨hb0, hab0J⟩⟩
      have h11 : 1 ≤ (P.filter (J b0)).card :=
        card_pos.mpr ⟨a0, mem_filter.mpr ⟨ha0, hJsymm _ _ hab0J⟩⟩
      rw [hF]
      omega
    obtain ⟨x, hxR, hxF⟩ := exists_mem_notMem_of_card_lt_card hFcard
    have hxU : ∀ v, (v = a0 ∨ v = b0) → ¬ U v x := by
      rintro v (rfl | rfl) hU
      · exact hxF (by rw [hF]; simp [hxR, hU])
      · exact hxF (by rw [hF]; simp [hxR, hU])
    have hxa0 : ∀ b' ∈ P, J a0 b' → b' ≠ b0 → x ≠ g s(a0, b') := by
      intro b' hb' hJ hne hx
      exact hxF (by rw [hF]; simp only [mem_union, mem_image, mem_erase, mem_filter]
                    exact Or.inl (Or.inr ⟨b', ⟨hne, hb', hJ⟩, hx.symm⟩))
    have hxb0 : ∀ a' ∈ P, J b0 a' → a' ≠ a0 → x ≠ g s(b0, a') := by
      intro a' ha' hJ hne hx
      exact hxF (by rw [hF]; simp only [mem_union, mem_image, mem_erase, mem_filter]
                    exact Or.inr ⟨a', ⟨hne, ha', hJ⟩, hx.symm⟩)
    refine ⟨fun e => if e = s(a0, b0) then x else g e, ?_⟩
    intro a ha b hb hab hmemab
    by_cases habe : s(a, b) = s(a0, b0)
    · simp only [habe, if_true]
      have hcases := Sym2.eq_iff.mp habe
      refine ⟨hxR, hxU a (by tauto), hxU b (by tauto), ?_⟩
      intro b' hb' hbb' hab' _
      have hne : s(a, b') ≠ s(a0, b0) := by
        rw [← habe]; intro h; exact hbb' (Sym2.congr_right.mp h)
      simp only [hne, if_false]
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hxa0 b' hb' hab' hbb'
      · exact hxb0 b' hb' hab' hbb'
    · simp only [habe, if_false]
      have hE : s(a, b) ∈ E := (mem_insert.mp hmemab).resolve_left habe
      obtain ⟨h1, h2, h3, h4⟩ := hg a ha b hb hab hE
      refine ⟨h1, h2, h3, ?_⟩
      intro b' hb' hbb' hab' hmem'
      by_cases hab'e : s(a, b') = s(a0, b0)
      · simp only [hab'e, if_true]
        rcases Sym2.eq_iff.mp hab'e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact (hxa0 b hb hab hbb'.symm).symm
        · exact (hxb0 b hb hab hbb'.symm).symm
      · simp only [hab'e, if_false]
        exact h4 b' hb' hbb' hab' ((mem_insert.mp hmem').resolve_left hab'e)
  obtain ⟨g, hg⟩ := key
  refine ⟨g, fun a ha b hb hab => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hg a ha b hb hab (hmemEJ a b ha hb hab)
  exact ⟨h1, h2, h3, fun b' hb' hbb' hab' => h4 b' hb' hbb' hab' (hmemEJ a b' ha hb' hab')⟩

/-! ### Arithmetic of (25) -/

/-- The estimate (25) in untruncated form: with `k ≥ p - 6(d-1)` candidates, at most `D ≤ m - 1`
processed edges, `2m ≤ qd`, `q ≤ 2p+1` and `p ≥ 24d`, we have `2k + 12D < k²`. -/
theorem arith_mantel {p q d k D m : ℕ} (hd : 1 ≤ d) (hp : 24 * d ≤ p) (hk : p + 6 ≤ k + 6 * d)
    (hD : D + 1 ≤ m) (hm : 2 * m ≤ q * d) (hq : q ≤ 2 * p + 1) : 2 * k + 12 * D < k ^ 2 := by
  have h1 : 12 * D + 12 ≤ 6 * q * d := by nlinarith
  have h2 : q * d ≤ (2 * p + 1) * d := Nat.mul_le_mul_right d hq
  have h3 : 4 * k ≥ 3 * p + 24 := by omega
  nlinarith

variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

/-- `2m ≤ q d` when `d` bounds the exterior degrees. -/
theorem two_mCount_le_of {d : ℕ} (hd : ∀ x ∉ P, (Pᶜ.filter (G.Adj x)).card ≤ d) :
    2 * mCount G P ≤ Pᶜ.card * d := by
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
      ≤ ∑ _x ∈ Pᶜ, d := by
        refine sum_le_sum fun x hx => ?_
        have hx' : x ∉ P := by simpa using hx
        exact (card_extEdges_incident_le G P x).trans (hd x hx')
    _ = _ := by rw [sum_const, smul_eq_mul]

/-! ### The lifting by core triangles -/

/-- One step of the Appendix A induction. -/
theorem join_lift_step (hjoin : ∀ a ∈ P, ∀ v, a ≠ v → G.Adj a v) {d : ℕ}
    (hd : ∀ x ∉ P, (Pᶜ.filter (G.Adj x)).card ≤ d) (hp : 24 * d ≤ P.card)
    (hq1 : Pᶜ.card ≤ 2 * P.card + 1)
    {D : Finset (Sym2 V)} {T : Sym2 V → Finset V}
    (hinv : LiftInv G P (fun _ => 3) (mCount G P) D T)
    (hD : D ⊆ extEdges G P) {e0 : Sym2 V} (he0 : e0 ∈ extEdges G P) (he0D : e0 ∉ D) :
    ∃ T', LiftInv G P (fun _ => 3) (mCount G P) (insert e0 D) T' := by
  classical
  have hDm : D.card + 1 ≤ mCount G P := by
    have := card_le_card (insert_subset he0 hD)
    rw [card_insert_of_notMem he0D] at this
    exact this
  induction e0 using Sym2.ind with
  | h x y =>
  obtain ⟨hxy, hx, hy⟩ := (mem_extEdges G P).mp he0
  set K := P.filter (fun a => ∀ e ∈ D, (x ∈ e ∨ y ∈ e) → a ∉ T e) with hK
  have hKP : K ⊆ P := filter_subset _ _
  have hd1 : 1 ≤ d := by
    have := hd x hx
    have h1 : 0 < (Pᶜ.filter (G.Adj x)).card :=
      card_pos.mpr ⟨y, mem_filter.mpr ⟨mem_compl.mpr hy, hxy⟩⟩
    omega
  have hinc : ∀ z ∉ P, z ∈ s(x, y) → (D.filter (fun e => z ∈ e)).card + 1 ≤ d := by
    intro z hz hze
    have hsub : insert s(x, y) (D.filter (fun e => z ∈ e)) ⊆
        (extEdges G P).filter (fun e => z ∈ e) := by
      intro e he
      rw [mem_insert] at he
      rcases he with rfl | he
      · exact mem_filter.mpr ⟨he0, hze⟩
      · exact mem_filter.mpr ⟨hD (mem_filter.mp he).1, (mem_filter.mp he).2⟩
    have := card_le_card hsub
    rw [card_insert_of_notMem (fun h => he0D (mem_filter.mp h).1)] at this
    exact this.trans ((card_extEdges_incident_le G P z).trans (hd z hz))
  have hDx := hinc x hx (Sym2.mem_mk_left x y)
  have hDy := hinc y hy (Sym2.mem_mk_right x y)
  have hbU : ∀ z, ((D.filter (fun e => z ∈ e)).biUnion T).card ≤
      3 * (D.filter (fun e => z ∈ e)).card := by
    intro z
    calc ((D.filter (fun e => z ∈ e)).biUnion T).card
        ≤ ∑ e ∈ D.filter (fun e => z ∈ e), (T e).card := card_biUnion_le
      _ = ∑ _e ∈ D.filter (fun e => z ∈ e), 3 :=
          sum_congr rfl fun e he => hinv.card e (mem_filter.mp he).1
      _ = 3 * (D.filter (fun e => z ∈ e)).card := by rw [sum_const, smul_eq_mul, mul_comm]
  have hKc : P.card + 6 ≤ K.card + 6 * d := by
    have hsub : P ⊆ K ∪ ((D.filter (fun e => x ∈ e)).biUnion T ∪
        (D.filter (fun e => y ∈ e)).biUnion T) := by
      intro a ha
      by_cases haK : a ∈ K
      · exact mem_union_left _ haK
      · simp only [hK, mem_filter, not_and, not_forall, not_not] at haK
        obtain ⟨e, he, hxe, hae⟩ := haK ha
        refine mem_union_right _ ?_
        rcases hxe with hxe | hye
        · exact mem_union_left _ (mem_biUnion.mpr ⟨e, mem_filter.mpr ⟨he, hxe⟩, hae⟩)
        · exact mem_union_right _ (mem_biUnion.mpr ⟨e, mem_filter.mpr ⟨he, hye⟩, hae⟩)
    have h1 := card_le_card hsub
    have h2 := card_union_le K ((D.filter (fun e => x ∈ e)).biUnion T ∪
        (D.filter (fun e => y ∈ e)).biUnion T)
    have h3 := card_union_le ((D.filter (fun e => x ∈ e)).biUnion T)
        ((D.filter (fun e => y ∈ e)).biUnion T)
    have h4 := hbU x
    have h5 := hbU y
    omega
  let adj : V → V → Prop := fun a b => a ≠ b ∧ ¬ ∃ e ∈ D, a ∈ T e ∧ b ∈ T e
  have hadj_symm : ∀ a b, adj a b → adj b a := fun a b h =>
    ⟨h.1.symm, fun ⟨e, he, h1, h2⟩ => h.2 ⟨e, he, h2, h1⟩⟩
  have hcount : K.card ^ 2 ≤ ((K ×ˢ K).filter (fun p => adj p.1 p.2)).card + K.card +
      6 * D.card := by
    have hsub : K ×ˢ K ⊆ (K ×ˢ K).filter (fun p => adj p.1 p.2) ∪
        (K.diag ∪ D.biUnion (fun e => (T e).offDiag)) := by
      rintro ⟨a, b⟩ hab
      by_cases h : adj a b
      · exact mem_union_left _ (mem_filter.mpr ⟨hab, h⟩)
      · refine mem_union_right _ ?_
        rw [mem_product] at hab
        by_cases hab' : a = b
        · subst hab'
          exact mem_union_left _ (mem_diag.mpr ⟨hab.1, rfl⟩)
        · have : ∃ e ∈ D, a ∈ T e ∧ b ∈ T e := by
            by_contra hc; exact h ⟨hab', hc⟩
          obtain ⟨e, he, hae, hbe⟩ := this
          exact mem_union_right _ (mem_biUnion.mpr ⟨e, he, mem_offDiag.mpr ⟨hae, hbe, hab'⟩⟩)
    have h1 := card_le_card hsub
    have h2 := card_union_le ((K ×ˢ K).filter (fun p => adj p.1 p.2))
      (K.diag ∪ D.biUnion (fun e => (T e).offDiag))
    have h3 := card_union_le K.diag (D.biUnion (fun e => (T e).offDiag))
    have h4 : (D.biUnion (fun e => (T e).offDiag)).card ≤ 6 * D.card := by
      calc (D.biUnion (fun e => (T e).offDiag)).card ≤ ∑ e ∈ D, (T e).offDiag.card :=
            card_biUnion_le
        _ = ∑ _e ∈ D, 6 := sum_congr rfl fun e he => by
            rw [offDiag_card, hinv.card e he]
        _ = 6 * D.card := by rw [sum_const, smul_eq_mul, mul_comm]
    rw [card_product, diag_card] at *
    rw [sq]
    omega
  have harith := arith_mantel hd1 hp hKc hDm (two_mCount_le_of G P hd) hq1
  have htri : ∃ a ∈ K, ∃ b ∈ K, ∃ c ∈ K, adj a b ∧ adj b c ∧ adj a c := by
    by_contra hno
    have hm := mantel_ordered K adj hadj_symm
      (fun a ha b hb c hc h1 h2 h3 => hno ⟨a, ha, b, hb, c, hc, h1, h2, h3⟩)
    omega
  obtain ⟨a, ha, b, hb, c, hc, hab, hbc, hac⟩ := htri
  set N : Finset V := {a, b, c} with hNdef
  have hNK : N ⊆ K := by
    intro v hv
    simp only [hNdef, mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> assumption
  have hNc : N.card = 3 := card_eq_three.mpr ⟨a, b, c, hab.1, hac.1, hbc.1, rfl⟩
  have hNpair : ∀ u ∈ N, ∀ v ∈ N, u ≠ v → adj u v := by
    intro u hu v hv huv
    simp only [hNdef, mem_insert, mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
      first | exact absurd rfl huv | assumption | exact hadj_symm _ _ ‹_›
  have hNmem : ∀ u ∈ N, u ∈ P ∧ ∀ e ∈ D, (x ∈ e ∨ y ∈ e) → u ∉ T e := by
    intro u hu
    have := hNK hu
    simp only [hK, mem_filter] at this
    exact this
  have hNgood : ∀ u ∈ N, ∀ v ∈ N, u ≠ v → ∀ e ∈ D, u ∈ T e → v ∉ T e := by
    intro u hu v hv huv e he hue hve
    exact (hNpair u hu v hv huv).2 ⟨e, he, hue, hve⟩
  let T' : Sym2 V → Finset V := fun e => if e = s(x, y) then N else T e
  have hT'0 : T' s(x, y) = N := by simp [T']
  have hT'D : ∀ e ∈ D, T' e = T e := fun e he => by
    have : e ≠ s(x, y) := fun h => he0D (h ▸ he)
    simp [T', this]
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
  · intro e he u hu v hv huv
    rw [mem_insert] at he
    rcases he with rfl | he
    · rw [hT'0] at hu hv; exact hjoin u (hNmem u hu).1 v huv
    · rw [hT'D e he] at hu hv; exact hinv.coreAdj e he u hu v hv huv
  · intro e he u hu z hz
    rw [mem_insert] at he
    rcases he with rfl | he
    · rw [hT'0] at hu
      have hzP : z ∉ P := by
        rw [Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · exact hx
        · exact hy
      exact hjoin u (hNmem u hu).1 z (fun h => hzP (h ▸ (hNmem u hu).1))
    · rw [hT'D e he] at hu; exact hinv.crossAdj e he u hu z hz
  · intro e he e' he' hee' u hu v hv huv hue'
    rw [mem_insert] at he he'
    rcases he with rfl | he <;> rcases he' with rfl | he'
    · exact absurd rfl hee'
    · rw [hT'0] at hu hv; rw [hT'D e' he'] at hue' ⊢
      exact hNgood u hu v hv huv e' he' hue'
    · rw [hT'D e he] at hu hv; rw [hT'0] at hue' ⊢
      intro hvN
      exact hNgood u hue' v hvN huv e he hu hv
    · rw [hT'D e he] at hu hv; rw [hT'D e' he'] at hue' ⊢
      exact hinv.pairDisj e he e' he' hee' u hu v hv huv hue'
  · intro e he e' he' hee' z hz hz' u hu
    rw [mem_insert] at he he'
    rcases he with rfl | he <;> rcases he' with rfl | he'
    · exact absurd rfl hee'
    · rw [hT'0] at hu; rw [hT'D e' he']
      refine (hNmem u hu).2 e' he' ?_
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · exact Or.inl hz'
      · exact Or.inr hz'
    · rw [hT'D e he] at hu; rw [hT'0]
      intro huN
      refine (hNmem u huN).2 e he ?_ hu
      rw [Sym2.mem_iff] at hz'
      rcases hz' with rfl | rfl
      · exact Or.inl hz
      · exact Or.inr hz
    · rw [hT'D e he] at hu; rw [hT'D e' he']
      exact hinv.incDisj e he e' he' hee' z hz hz' u hu
  · intro u
    calc ((insert s(x, y) D).filter (fun e => u ∈ T' e)).card ≤ (insert s(x, y) D).card :=
          card_filter_le _ _
      _ ≤ (extEdges G P).card := card_le_card (insert_subset he0 hD)

/-- **The lifting of Appendix A.** Every exterior edge receives a core triangle, edge-disjoint
from the others and vertex-disjoint from those of incident exterior edges. -/
theorem join_lift (hjoin : ∀ a ∈ P, ∀ v, a ≠ v → G.Adj a v) {d : ℕ}
    (hd : ∀ x ∉ P, (Pᶜ.filter (G.Adj x)).card ≤ d) (hp : 24 * d ≤ P.card)
    (hq1 : Pᶜ.card ≤ 2 * P.card + 1) :
    ∃ T, LiftInv G P (fun _ => 3) (mCount G P) (extEdges G P) T := by
  refine Finset.induction_on' (motive := fun D => ∃ T, LiftInv G P (fun _ => 3) (mCount G P) D T)
    (extEdges G P) ⟨fun _ => ∅, by constructor <;> simp⟩ ?_
  intro e0 D he0 hD he0D ih
  obtain ⟨T, hT⟩ := ih
  exact join_lift_step G P hjoin hd hp hq1 hT hD he0 he0D

/-- Identity (26): at a core vertex the used crossing edges and the residual core degree add up
to at most `p - 1`. -/
theorem used_add_resid_le (hjoin : ∀ a ∈ P, ∀ v, a ≠ v → G.Adj a v) {T : Sym2 V → Finset V}
    {r : ℕ} (hT : LiftInv G P (fun _ => 3) r (extEdges G P) T) {a : V} (ha : a ∈ P) :
    (Pᶜ.filter (usedPair G P T a)).card + (P.filter (residPair G P T a)).card ≤ P.card - 1 := by
  classical
  set E := (extEdges G P).filter (fun e => a ∈ T e) with hE
  have hU : (Pᶜ.filter (usedPair G P T a)).card ≤ 2 * E.card := by
    calc (Pᶜ.filter (usedPair G P T a)).card ≤ (E.biUnion (fun e => e.toFinset)).card :=
          card_le_card (by
            intro x hx
            simp only [mem_filter] at hx
            obtain ⟨e, he, hae, hxe⟩ := hx.2
            exact mem_biUnion.mpr ⟨e, mem_filter.mpr ⟨he, hae⟩, Sym2.mem_toFinset.mpr hxe⟩)
      _ ≤ ∑ e ∈ E, e.toFinset.card := card_biUnion_le
      _ ≤ ∑ _e ∈ E, 2 := sum_le_sum fun e _ => by rw [Sym2.card_toFinset]; split_ifs <;> omega
      _ = 2 * E.card := by rw [sum_const, smul_eq_mul, mul_comm]
  have hC : 2 * E.card ≤ (P.filter (fun b => b ≠ a ∧ coveredPair G P T a b)).card := by
    have hdisj : (E : Set (Sym2 V)).PairwiseDisjoint (fun e => (T e).erase a) := by
      intro e he e' he' hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro b hb hb'
      rw [mem_erase] at hb hb'
      have he1 := mem_filter.mp (mem_coe.mp he)
      have he1' := mem_filter.mp (mem_coe.mp he')
      exact hT.pairDisj e he1.1 e' he1'.1 hne a he1.2 b hb.2 (Ne.symm hb.1) he1'.2 hb'.2
    calc 2 * E.card = ∑ e ∈ E, ((T e).erase a).card := by
          rw [sum_congr rfl (fun e he => by
            rw [card_erase_of_mem (mem_filter.mp he).2, hT.card e (mem_filter.mp he).1])]
          rw [sum_const, smul_eq_mul, mul_comm]
      _ = (E.biUnion (fun e => (T e).erase a)).card := (card_biUnion hdisj).symm
      _ ≤ _ := card_le_card (by
          intro b hb
          obtain ⟨e, he, hb⟩ := mem_biUnion.mp hb
          rw [mem_erase] at hb
          have he1 := mem_filter.mp he
          exact mem_filter.mpr ⟨hT.sub e he1.1 hb.2, hb.1, e, he1.1, he1.2, hb.2⟩)
  have hpart : (P.filter (residPair G P T a)).card +
      (P.filter (fun b => b ≠ a ∧ coveredPair G P T a b)).card = P.card - 1 := by
    rw [← card_erase_of_mem ha,
      ← card_filter_add_card_filter_not (s := P.erase a) (residPair G P T a)]
    congr 2
    · ext b
      simp only [mem_filter, mem_erase]
      constructor
      · rintro ⟨hb, hres⟩; exact ⟨⟨hres.1.ne.symm, hb⟩, hres⟩
      · rintro ⟨⟨-, hb⟩, hres⟩; exact ⟨hb, hres⟩
    · ext b
      simp only [mem_filter, mem_erase, residPair, not_and, not_not]
      constructor
      · rintro ⟨hb, hba, hcov⟩; exact ⟨⟨hba, hb⟩, fun _ => hcov⟩
      · rintro ⟨⟨hba, hb⟩, hcov⟩; exact ⟨hb, hba, hcov (hjoin a ha b (Ne.symm hba))⟩
  omega

/-- The construction of Appendix A: a clique partition in which every exterior edge lies in a
block with three core vertices and two exterior vertices, and every other block is a triangle
of type `(2,1)` or a crossing edge. -/
theorem exists_partition_join (hjoin : ∀ a ∈ P, ∀ v, a ≠ v → G.Adj a v) {d : ℕ}
    (hd : ∀ x ∉ P, (Pᶜ.filter (G.Adj x)).card ≤ d) (hp : 24 * d ≤ P.card)
    (hq1 : Pᶜ.card ≤ 2 * P.card + 1) (hq0 : 2 * P.card ≤ Pᶜ.card + 1) :
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ ∀ B ∈ Bs,
      (coreSize P B = 1 ∧ extSize P B = 1) ∨ (coreSize P B = 2 ∧ extSize P B = 1) ∨
      ∃ e ∈ extEdges G P, (∀ v ∈ e, v ∈ B) ∧ coreSize P B = 3 ∧ extSize P B = 2 := by
  classical
  obtain ⟨T, hT⟩ := join_lift G P hjoin hd hp hq1
  obtain ⟨g, hg⟩ := exists_greedy_coloring P Pᶜ (residPair G P T)
    (fun _ _ h => residPair_symm h) (usedPair G P T) (P.card - 1)
    (fun a ha => used_add_resid_le G P hjoin hT ha) (by omega)
  let f : V → V → V := fun a b => g s(a, b)
  have hf1 : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → residPair G P T a b → f a b = f b a :=
    fun a _ b _ _ _ => by simp only [f, Sym2.eq_swap]
  have hf2 : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → residPair G P T a b →
      f a b ∉ P ∧ availPair G P T a (f a b) ∧ availPair G P T b (f a b) := by
    intro a ha b hb _ hres
    obtain ⟨h1, h2, h3, -⟩ := hg a ha b hb hres
    have hx : f a b ∉ P := by simpa using h1
    exact ⟨hx, ⟨hjoin a ha _ (fun h => hx (h ▸ ha)), h2⟩,
      ⟨hjoin b hb _ (fun h => hx (h ▸ hb)), h3⟩⟩
  have hf3 : ∀ a ∈ P, ∀ b ∈ P, ∀ b' ∈ P, a ≠ b → a ≠ b' → b ≠ b' → residPair G P T a b →
      residPair G P T a b' → f a b ≠ f a b' :=
    fun a ha b hb b' hb' _ _ hbb' hres hres' =>
      (hg a ha b hb hres).2.2.2 b' hb' (Ne.symm hbb') hres'
  exact ⟨allBlocks G P T f, allBlocks_isCliquePartition hT hf1 hf2 hf3,
    fun B hB => allBlocks_types hT hf2 hB⟩

theorem uCount_join (hjoin : ∀ a ∈ P, ∀ v, a ≠ v → G.Adj a v) :
    uCount G P = P.card.choose 2 := by
  unfold uCount
  have : coreEdges G P = innerEdges G P := rfl
  rw [this, card_innerEdges_of_isClique _ P (fun a ha b _ hab => hjoin a ha b hab)]

theorem sCount_join (hjoin : ∀ a ∈ P, ∀ v, a ≠ v → G.Adj a v) :
    sCount G P = P.card * Pᶜ.card := by
  rw [card_compl, ← card_crossEdges_top P]
  unfold sCount
  congr 1
  ext e
  induction e using Sym2.ind with
  | h x y =>
    rw [mem_crossEdges, mem_crossEdges, SimpleGraph.top_adj]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1.ne, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rcases h2 with ⟨hx, -⟩ | ⟨-, hy⟩
      · exact hjoin x hx y h1
      · exact (hjoin y hy x h1.symm).symm

/-- **Theorem A.1 (complete-join variant).** Let `G = K_p ∨ H`, i.e. every core vertex of `P`
is adjacent to every other vertex, `H = G[Pᶜ]`, `q = |Pᶜ| ∈ {2p-1, 2p, 2p+1}`, and let `d` bound
the degrees of `H` (e.g. `d = Δ(H)`). If `p ≥ 24d`, then `cp(K_p ∨ H) = M(n) - 2e(H)`, and there
is an optimal clique partition (an exact partition of `E(G)`) in which every exterior edge lies
in a block `K_5` of type `(3,2)`, all other blocks being triangles of type `(2,1)` and crossing
edges. Its block counts are `N₅ = m`, `N₃ = binom(p,2) - 3m`, `N₂ = pq - 2 binom(p,2)`. -/
theorem theoremA1
    (hq : Pᶜ.card + 1 = 2 * P.card ∨ Pᶜ.card = 2 * P.card ∨ Pᶜ.card = 2 * P.card + 1)
    (hjoin : ∀ a ∈ P, ∀ v, a ≠ v → G.Adj a v) {d : ℕ}
    (hd : ∀ x ∉ P, (Pᶜ.filter (G.Adj x)).card ≤ d) (hp : 24 * d ≤ P.card) :
    (cp G : ℤ) = Mval (Fintype.card V) - 2 * mCount G P ∧
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ Bs.card = cp G ∧
      (∀ e ∈ extEdges G P, ∃ B ∈ Bs, (∀ v ∈ e, v ∈ B) ∧ B.card = 5 ∧ extSize P B = 2) ∧
      (∀ B ∈ Bs, (coreSize P B = 2 ∧ extSize P B = 1) ∨ (coreSize P B = 1 ∧ extSize P B = 1) ∨
        ∃ e ∈ extEdges G P, (∀ v ∈ e, v ∈ B) ∧ B.card = 5 ∧ extSize P B = 2) ∧
      (Bs.filter (fun B => B.card = 5)).card = mCount G P ∧
      ((Bs.filter (fun B => B.card = 3)).card : ℤ) = (P.card.choose 2 : ℤ) - 3 * mCount G P ∧
      ((Bs.filter (fun B => B.card = 2)).card : ℤ) =
        (P.card : ℤ) * Pᶜ.card - 2 * (P.card.choose 2 : ℤ) := by
  have hqc : Pᶜ.card = Fintype.card V - P.card := card_compl P
  have hpn : P.card ≤ Fintype.card V := card_le_univ P
  have hP : P.card = (Fintype.card V + 1) / 3 := by omega
  have hq1 : Pᶜ.card ≤ 2 * P.card + 1 := by omega
  have hq0 : 2 * P.card ≤ Pᶜ.card + 1 := by omega
  obtain ⟨Bs, hBs, htypes⟩ := exists_partition_join G P hjoin hd hp hq1 hq0
  obtain ⟨hcp, -, hM, hext, hblocks, h5, -, h3, h2⟩ :=
    theoremB_of_partition G P hP (fun _ => 5) (fun _ _ => Or.inr rfl) hBs htypes
  have hfil : (extEdges G P).filter (fun e => (fun _ => 5) e = 5) = extEdges G P :=
    filter_true_of_mem fun _ _ => rfl
  rw [hfil] at h5 h3 h2
  have hu := uCount_join G P hjoin
  have hs := sCount_join G P hjoin
  have hC : Cdef G P = 0 := by unfold Cdef; rw [hu]; ring
  have hA : Adef G P = 0 := by
    unfold Adef; rw [hs, hqc]; push_cast [hpn]; ring
  refine ⟨by rw [hM, hC, hA]; ring, Bs, hBs, hcp, hext, hblocks, by exact_mod_cast h5, ?_, ?_⟩
  · rw [h3, hu]; unfold mCount; ring
  · rw [h2, hu, hs]; push_cast; unfold mCount; ring

end PaperVI
