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
Paper VI — the general construction: lifting with bounded load followed by the
Häggkvist–Janssen completion, producing an exact clique partition with prescribed block
types; and the block-type counting identities.
-/
module

public import PaperVI.Assembly

@[expose] public section

namespace PaperVI

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (P : Finset V)

/-- At most `h + 2r` exterior vertices are unavailable at a core vertex after lifting. -/
theorem card_unavail_le {σ : Sym2 V → ℕ} {r : ℕ} {T : Sym2 V → Finset V}
    (hT : LiftInv G P σ r (extEdges G P) T) (a : V) (ha : a ∈ P) :
    (Pᶜ.filter (fun x => ¬ availPair G P T a x)).card ≤ editDegree G P + 2 * r := by
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
  have h1 := core_local_bound G P a ha
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
theorem exists_partition_of_lift {σ : Sym2 V → ℕ} {c r need : ℕ}
    (hσc : ∀ e ∈ extEdges G P, σ e ≤ c)
    (hneed : ∀ e ∈ extEdges G P, σ e * (editDegree G P + (c - 1) * r + 1) ≤
      need + (editDegree G P + (c - 1) * r))
    (hcand : ∀ k bx by_ dx dy sat nD : ℕ, P.card ≤ k + bx + by_ + c * dx + c * dy + sat →
      bx + dx + 1 ≤ editDegree G P → by_ + dy + 1 ≤ editDegree G P → r * sat ≤ c * nD →
      nD + 1 ≤ mCount G P → 2 * mCount G P ≤ Pᶜ.card * editDegree G P → need ≤ k)
    (hlist : P.card + 2 * (editDegree G P + 2 * r) ≤ Pᶜ.card) :
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ ∀ B ∈ Bs,
      (coreSize P B = 1 ∧ extSize P B = 1) ∨ (coreSize P B = 2 ∧ extSize P B = 1) ∨
      ∃ e ∈ extEdges G P, (∀ v ∈ e, v ∈ B) ∧ coreSize P B = σ e ∧ extSize P B = 2 := by
  obtain ⟨T, hT⟩ := exists_lift G P hσc hneed hcand
  obtain ⟨f, hf1, hf2, hf3⟩ := exists_completion_coloring P (availPair G P T)
    (editDegree G P + 2 * r) (card_unavail_le G P hT) hlist
  have hf1' := fun a ha b hb hab (_ : residPair G P T a b) => hf1 a ha b hb hab
  have hf2' := fun a ha b hb hab (_ : residPair G P T a b) => hf2 a ha b hb hab
  have hf3' := fun a ha b hb b' hb' hab hab' hbb' (_ : residPair G P T a b)
    (_ : residPair G P T a b') => hf3 a ha b hb b' hb' hab hab' hbb'
  exact ⟨allBlocks G P T f, allBlocks_isCliquePartition hT hf1' hf2' hf3',
    fun B hB => allBlocks_types hT hf2' hB⟩

/-! ### Counting blocks by type -/

/-- Number of blocks of type `(a, b)`. -/
def typeCount (Bs : Finset (Finset V)) (a b : ℕ) : ℕ :=
  (Bs.filter (fun B => coreSize P B = a ∧ extSize P B = b)).card

omit [Fintype V] in
theorem card_eq_coreSize_add_extSize (B : Finset V) : B.card = coreSize P B + extSize P B := by
  unfold coreSize extSize
  rw [add_comm]; exact (card_sdiff_add_card_inter B P).symm

/-- If every block has one of the types `(1,1), (2,1), (2,2), (3,2), (1,2)`, then counting
core, exterior and crossing edges gives the block numbers. -/
theorem type_counts {Bs : Finset (Finset V)} (hBs : IsCliquePartition G Bs)
    (htypes : ∀ B ∈ Bs, (coreSize P B = 1 ∧ extSize P B = 1) ∨
      (coreSize P B = 2 ∧ extSize P B = 1) ∨ (coreSize P B = 2 ∧ extSize P B = 2) ∨
      (coreSize P B = 3 ∧ extSize P B = 2) ∨ (coreSize P B = 1 ∧ extSize P B = 2)) :
    uCount G P = typeCount P Bs 2 1 + typeCount P Bs 2 2 + 3 * typeCount P Bs 3 2 ∧
    mCount G P = typeCount P Bs 2 2 + typeCount P Bs 3 2 + typeCount P Bs 1 2 ∧
    sCount G P = typeCount P Bs 1 1 + 2 * typeCount P Bs 2 1 + 4 * typeCount P Bs 2 2 +
      6 * typeCount P Bs 3 2 + 2 * typeCount P Bs 1 2 ∧
    Bs.card = typeCount P Bs 1 1 + typeCount P Bs 2 1 + typeCount P Bs 2 2 +
      typeCount P Bs 3 2 + typeCount P Bs 1 2 := by
  obtain ⟨h1, h2, h3⟩ := partition_sums G P hBs
  let ind : ℕ → ℕ → Finset V → ℕ := fun a b B =>
    if coreSize P B = a ∧ extSize P B = b then 1 else 0
  have hN : ∀ a b, typeCount P Bs a b = ∑ B ∈ Bs, ind a b B := fun a b => by
    simp only [typeCount, card_filter, ind]
  have key : ∀ g : Finset V → ℕ, ∀ w11 w21 w22 w32 w12 : ℕ,
      (∀ B ∈ Bs, g B = w11 * ind 1 1 B + w21 * ind 2 1 B + w22 * ind 2 2 B +
        w32 * ind 3 2 B + w12 * ind 1 2 B) →
      ∑ B ∈ Bs, g B = w11 * typeCount P Bs 1 1 + w21 * typeCount P Bs 2 1 +
        w22 * typeCount P Bs 2 2 + w32 * typeCount P Bs 3 2 + w12 * typeCount P Bs 1 2 := by
    intro g w11 w21 w22 w32 w12 hg
    rw [sum_congr rfl hg]
    simp only [sum_add_distrib, ← mul_sum, hN]
  have hpt : ∀ B ∈ Bs, ∀ a b : ℕ, ind a b B = if coreSize P B = a ∧ extSize P B = b then 1 else 0 :=
    fun _ _ _ _ => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← h1]
    have := key (fun B => (coreSize P B).choose 2) 0 1 1 3 0 (fun B hB => by
      simp only [ind]
      rcases htypes B hB with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
        simp [ha, hb])
    simpa using this
  · rw [← h2]
    have := key (fun B => (extSize P B).choose 2) 0 0 1 1 1 (fun B hB => by
      simp only [ind]
      rcases htypes B hB with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
        simp [ha, hb])
    simpa using this
  · rw [← h3]
    have := key (fun B => coreSize P B * extSize P B) 1 2 4 6 2 (fun B hB => by
      simp only [ind]
      rcases htypes B hB with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
        simp [ha, hb])
    simpa using this
  · rw [card_eq_sum_ones]
    have := key (fun _ => 1) 1 1 1 1 1 (fun B hB => by
      simp only [ind]
      rcases htypes B hB with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
        simp [ha, hb])
    simpa using this

/-- The block containing an exterior edge has the type prescribed for that edge. -/
theorem type_of_block_containing_ext {σ : Sym2 V → ℕ} {Bs : Finset (Finset V)}
    (htypes : ∀ B ∈ Bs, (coreSize P B = 1 ∧ extSize P B = 1) ∨
      (coreSize P B = 2 ∧ extSize P B = 1) ∨
      ∃ e ∈ extEdges G P, (∀ v ∈ e, v ∈ B) ∧ coreSize P B = σ e ∧ extSize P B = 2)
    {e : Sym2 V} (he : e ∈ extEdges G P) {B : Finset V} (hB : B ∈ Bs)
    (heB : ∀ v ∈ e, v ∈ B) : coreSize P B = σ e ∧ extSize P B = 2 := by
  induction e using Sym2.ind with
  | h x y =>
  rw [mem_extEdges] at he
  obtain ⟨hxy, hx, hy⟩ := he
  have hsub : ({x, y} : Finset V) ⊆ B \ P := by
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact mem_sdiff.mpr ⟨heB _ (by simp), hx⟩
    · exact mem_sdiff.mpr ⟨heB _ (by simp), hy⟩
  have h2 : 2 ≤ extSize P B := by
    have := card_le_card hsub
    rw [card_pair hxy.ne] at this
    exact this
  rcases htypes B hB with ⟨-, h⟩ | ⟨-, h⟩ | ⟨e', he', he'B, hc, hb⟩
  · omega
  · omega
  · have heq : B \ P = {x, y} :=
      (eq_of_subset_of_card_le hsub (by rw [card_pair hxy.ne]; exact hb.le)).symm
    induction e' using Sym2.ind with
    | h x' y' =>
    rw [mem_extEdges] at he'
    have hx' : x' ∈ B \ P := mem_sdiff.mpr ⟨he'B _ (by simp), he'.2.1⟩
    have hy' : y' ∈ B \ P := mem_sdiff.mpr ⟨he'B _ (by simp), he'.2.2⟩
    rw [heq] at hx' hy'
    simp only [mem_insert, mem_singleton] at hx' hy'
    have hne := he'.1.ne
    have : s(x', y') = s(x, y) := by
      rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
      · exact absurd rfl hne
      · rfl
      · exact Sym2.eq_swap
      · exact absurd rfl hne
    rw [this] at hc
    exact ⟨hc, hb⟩

omit [DecidableEq V] in
/-- Every edge of `G` lies in some block of a clique partition. -/
theorem exists_block_of_edge {Bs : Finset (Finset V)} (hBs : IsCliquePartition G Bs)
    {e : Sym2 V} (he : e ∈ G.edgeFinset) : ∃ B ∈ Bs, ∀ v ∈ e, v ∈ B := by
  induction e using Sym2.ind with
  | h x y =>
  obtain ⟨B, ⟨hB, hx, hy⟩, -⟩ := hBs.existsUnique x y (SimpleGraph.mem_edgeFinset.mp he)
  exact ⟨B, hB, fun v hv => by rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption⟩

omit [DecidableEq V] in
/-- Blocks containing the same exterior edge coincide. -/
theorem block_unique_of_edge {Bs : Finset (Finset V)} (hBs : IsCliquePartition G Bs)
    {e : Sym2 V} (he : e ∈ G.edgeFinset) {B B' : Finset V} (hB : B ∈ Bs) (hB' : B' ∈ Bs)
    (heB : ∀ v ∈ e, v ∈ B) (heB' : ∀ v ∈ e, v ∈ B') : B = B' := by
  induction e using Sym2.ind with
  | h x y =>
  obtain ⟨B0, -, hu⟩ := hBs.existsUnique x y (SimpleGraph.mem_edgeFinset.mp he)
  exact (hu B ⟨hB, heB x (by simp), heB y (by simp)⟩).trans
    (hu B' ⟨hB', heB' x (by simp), heB' y (by simp)⟩).symm

/-- The number of blocks of type `(j, 2)` equals the number of exterior edges `e` with
`σ e = j`. -/
theorem typeCount_ext_eq {σ : Sym2 V → ℕ} {Bs : Finset (Finset V)}
    (hBs : IsCliquePartition G Bs)
    (htypes : ∀ B ∈ Bs, (coreSize P B = 1 ∧ extSize P B = 1) ∨
      (coreSize P B = 2 ∧ extSize P B = 1) ∨
      ∃ e ∈ extEdges G P, (∀ v ∈ e, v ∈ B) ∧ coreSize P B = σ e ∧ extSize P B = 2) (j : ℕ) :
    typeCount P Bs j 2 = ((extEdges G P).filter (fun e => σ e = j)).card := by
  classical
  have hex : ∀ e ∈ (extEdges G P).filter (fun e => σ e = j), ∃ B ∈ Bs, ∀ v ∈ e, v ∈ B :=
    fun e he => exists_block_of_edge G hBs (extEdges_subset (mem_filter.mp he).1)
  symm
  refine card_bij (fun e he => Classical.choose (hex e he)) ?_ ?_ ?_
  · intro e he
    obtain ⟨hB, heB⟩ := Classical.choose_spec (hex e he)
    have := type_of_block_containing_ext G P htypes (mem_filter.mp he).1 hB heB
    rw [mem_filter]
    exact ⟨hB, this.1.trans (mem_filter.mp he).2, this.2⟩
  · intro e1 he1 e2 he2 heq
    obtain ⟨hB1, heB1⟩ := Classical.choose_spec (hex e1 he1)
    obtain ⟨hB2, heB2⟩ := Classical.choose_spec (hex e2 he2)
    have heq2 : Classical.choose (hex e1 he1) = Classical.choose (hex e2 he2) := heq
    rw [heq2] at heB1
    set B := Classical.choose (hex e2 he2)
    have h1 := (mem_filter.mp he1).1
    have h2 := (mem_filter.mp he2).1
    have ht := type_of_block_containing_ext G P htypes h2 hB2 heB2
    induction e1 using Sym2.ind with
    | h x y =>
    induction e2 using Sym2.ind with
    | h x' y' =>
    rw [mem_extEdges] at h1 h2
    have hsub : ({x', y'} : Finset V) ⊆ B \ P := by
      intro v hv
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact mem_sdiff.mpr ⟨heB2 _ (by simp), h2.2.1⟩
      · exact mem_sdiff.mpr ⟨heB2 _ (by simp), h2.2.2⟩
    have heq' : B \ P = {x', y'} :=
      (eq_of_subset_of_card_le hsub (by rw [card_pair h2.1.ne]; exact ht.2.le)).symm
    have hx : x ∈ B \ P := mem_sdiff.mpr ⟨heB1 _ (by simp), h1.2.1⟩
    have hy : y ∈ B \ P := mem_sdiff.mpr ⟨heB1 _ (by simp), h1.2.2⟩
    rw [heq'] at hx hy
    simp only [mem_insert, mem_singleton] at hx hy
    have hne := h1.1.ne
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hne
    · rfl
    · exact Sym2.eq_swap
    · exact absurd rfl hne
  · intro B hB
    rw [mem_filter] at hB
    obtain ⟨hB, hc, hb⟩ := hB
    rcases htypes B hB with ⟨-, h⟩ | ⟨-, h⟩ | ⟨e, he, heB, hce, -⟩
    · omega
    · omega
    · have he' : e ∈ (extEdges G P).filter (fun e => σ e = j) :=
        mem_filter.mpr ⟨he, hce.symm.trans hc⟩
      refine ⟨e, he', ?_⟩
      obtain ⟨hB', heB'⟩ := Classical.choose_spec (hex e he')
      exact block_unique_of_edge G hBs (extEdges_subset he) hB' hB heB' heB

end PaperVI
