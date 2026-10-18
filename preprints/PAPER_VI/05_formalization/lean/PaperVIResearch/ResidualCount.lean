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
Paper VI research round — Priority 4, step 3: the residual core graph after a lifting, its
lists, and the extension of an arbitrary prefix colouring to a full completion.
-/
module

public import PaperVI.TheoremB
public import PaperVIResearch.GreedyCount

@[expose] public section

namespace PaperVI

namespace Research

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (P : Finset V) (T : Sym2 V → Finset V)

/-- The residual core graph after a lifting `T`: core pairs not covered by a lifting block. -/
def residGraph : SimpleGraph V where
  Adj a b := a ∈ P ∧ b ∈ P ∧ a ≠ b ∧ residPair G P T a b
  symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.1.symm, residPair_symm h.2.2.2⟩⟩
  loopless := ⟨fun _ h => h.2.2.1 rfl⟩

instance : DecidableRel (residGraph G P T).Adj := fun a b => by
  show Decidable (a ∈ P ∧ b ∈ P ∧ a ≠ b ∧ residPair G P T a b)
  infer_instance

theorem residGraph_adj {a b : V} :
    (residGraph G P T).Adj a b ↔ a ∈ P ∧ b ∈ P ∧ a ≠ b ∧ residPair G P T a b := Iff.rfl

/-- The residual list of a core pair: exterior vertices available at both ends. -/
def residList (e : Sym2 V) : Finset V :=
  Pᶜ.filter (fun x => ∀ v ∈ e.toFinset, availPair G P T v x)

variable {G P T}

/-- Residual lists are long: each loses at most `2(h + 2r)` exterior vertices. -/
theorem card_residList {σ : Sym2 V → ℕ} {r : ℕ} (hT : LiftInv G P σ r (extEdges G P) T)
    {e : Sym2 V} (he : e ∈ (residGraph G P T).edgeFinset) :
    Pᶜ.card ≤ (residList G P T e).card + 2 * (editDegree G P + 2 * r) := by
  induction e using Sym2.ind with
  | h a b =>
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, residGraph_adj] at he
  have hsub : Pᶜ \ (Pᶜ.filter (fun x => ¬ availPair G P T a x) ∪
      Pᶜ.filter (fun x => ¬ availPair G P T b x)) ⊆ residList G P T s(a, b) := by
    intro x hx
    simp only [mem_sdiff, mem_union, mem_filter, not_or, not_and, not_not] at hx
    simp only [residList, mem_filter, Sym2.mem_toFinset, Sym2.mem_iff]
    refine ⟨hx.1, ?_⟩
    rintro v (rfl | rfl)
    · exact hx.2.1 hx.1
    · exact hx.2.2 hx.1
  have h1 := card_le_card hsub
  have h2 := le_card_sdiff (Pᶜ.filter (fun x => ¬ availPair G P T a x) ∪
    Pᶜ.filter (fun x => ¬ availPair G P T b x)) Pᶜ
  have h3 := card_union_le (Pᶜ.filter (fun x => ¬ availPair G P T a x))
    (Pᶜ.filter (fun x => ¬ availPair G P T b x))
  have h4 := card_unavail_le G P hT a he.1
  have h5 := card_unavail_le G P hT b he.2.1
  omega

omit [Fintype V] in
/-- In an edge set of maximum degree `d`, every edge shares an end with at most `2(d - 1)` other
edges. -/
theorem card_conflicts_le {K : Finset (Sym2 V)} {d : ℕ}
    (hKd : ∀ v, (K.filter (fun e => v ∈ e)).card ≤ d) {e : Sym2 V} (he : e ∈ K) :
    (K.filter (fun e' => e' ≠ e ∧ Shares e e')).card ≤ 2 * (d - 1) := by
  induction e using Sym2.ind with
  | h u v =>
  have hsub : K.filter (fun e' => e' ≠ s(u, v) ∧ Shares s(u, v) e') ⊆
      (K.filter (fun e => u ∈ e)).erase s(u, v) ∪ (K.filter (fun e => v ∈ e)).erase s(u, v) := by
    intro e' he'
    rw [mem_filter] at he'
    obtain ⟨he'K, hne, w, hw, hw'⟩ := he'
    rw [Sym2.mem_toFinset, Sym2.mem_iff] at hw
    rw [Sym2.mem_toFinset] at hw'
    rcases hw with rfl | rfl
    · exact mem_union_left _ (mem_erase.mpr ⟨hne, mem_filter.mpr ⟨he'K, hw'⟩⟩)
    · exact mem_union_right _ (mem_erase.mpr ⟨hne, mem_filter.mpr ⟨he'K, hw'⟩⟩)
  have h1 := card_le_card hsub
  have h2 := card_union_le ((K.filter (fun e => u ∈ e)).erase s(u, v))
    ((K.filter (fun e => v ∈ e)).erase s(u, v))
  have hu : s(u, v) ∈ K.filter (fun e => u ∈ e) := mem_filter.mpr ⟨he, Sym2.mem_mk_left u v⟩
  have hv : s(u, v) ∈ K.filter (fun e => v ∈ e) := mem_filter.mpr ⟨he, Sym2.mem_mk_right u v⟩
  have h3 := card_erase_of_mem hu
  have h4 := card_erase_of_mem hv
  have h5 := hKd u
  have h6 := hKd v
  have h7 : 1 ≤ (K.filter (fun e => u ∈ e)).card := card_pos.mpr ⟨_, hu⟩
  have h8 : 1 ≤ (K.filter (fun e => v ∈ e)).card := card_pos.mpr ⟨_, hv⟩
  omega

/-- **Prefix extension.** Let `K` be a set of residual core pairs of maximum degree `d`, and `c`
any proper list colouring of `K` from the residual lists. If `p + 2(h + 2r + d) ≤ q`, then `c`
extends to a completion `f` of all residual core pairs, satisfying the hypotheses of the
assembly, with `f a b = c(ab)` on `K`. The extension uses the Häggkvist–Janssen theorem
(through `exists_completion_coloring`) with the colours used by `K` at each end removed. -/
theorem prefix_extend {σ : Sym2 V → ℕ} {r d : ℕ} (hT : LiftInv G P σ r (extEdges G P) T)
    {K : Finset (Sym2 V)} (hKd : ∀ v, (K.filter (fun e => v ∈ e)).card ≤ d)
    (hq : P.card + 2 * (editDegree G P + 2 * r + d) ≤ Pᶜ.card)
    {x₀ : V} {c : Sym2 V → V} (hc : c ∈ listColorings K (residList G P T) x₀) :
    ∃ f : V → V → V, (∀ a ∈ P, ∀ b ∈ P, a ≠ b → residPair G P T a b → f a b = f b a) ∧
      (∀ a ∈ P, ∀ b ∈ P, a ≠ b → residPair G P T a b →
        f a b ∉ P ∧ availPair G P T a (f a b) ∧ availPair G P T b (f a b)) ∧
      (∀ a ∈ P, ∀ b ∈ P, ∀ b' ∈ P, a ≠ b → a ≠ b' → b ≠ b' → residPair G P T a b →
        residPair G P T a b' → f a b ≠ f a b') ∧
      ∀ a b, s(a, b) ∈ K → f a b = c s(a, b) := by
  classical
  obtain ⟨hc1, -, hc3⟩ := mem_listColorings.mp hc
  let avail' : V → V → Prop := fun a x => availPair G P T a x ∧ ∀ e ∈ K, a ∈ e → c e ≠ x
  have hF : ∀ a ∈ P, (Pᶜ.filter (fun x => ¬ avail' a x)).card ≤
      editDegree G P + 2 * r + d := by
    intro a ha
    have hsub : Pᶜ.filter (fun x => ¬ avail' a x) ⊆
        Pᶜ.filter (fun x => ¬ availPair G P T a x) ∪ (K.filter (fun e => a ∈ e)).image c := by
      intro x hx
      rw [mem_filter] at hx
      obtain ⟨hxc, hx⟩ := hx
      by_cases hav : availPair G P T a x
      · have : ∃ e ∈ K, a ∈ e ∧ c e = x := by
          by_contra hne
          push_neg at hne
          exact hx ⟨hav, fun e he hae => hne e he hae⟩
        obtain ⟨e, he, hae, rfl⟩ := this
        exact mem_union_right _ (mem_image.mpr ⟨e, mem_filter.mpr ⟨he, hae⟩, rfl⟩)
      · exact mem_union_left _ (mem_filter.mpr ⟨hxc, hav⟩)
    refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
    have h1 := card_unavail_le G P hT a ha
    have h2 := (card_image_le (s := K.filter (fun e => a ∈ e)) (f := c)).trans (hKd a)
    omega
  obtain ⟨f', hf1, hf2, hf3⟩ := exists_completion_coloring P avail' _ hF hq
  let f : V → V → V := fun a b => if s(a, b) ∈ K then c s(a, b) else f' a b
  have hfK : ∀ a b, s(a, b) ∈ K → f a b = c s(a, b) := fun a b h => by simp only [f, if_pos h]
  have hfK' : ∀ a b, s(a, b) ∉ K → f a b = f' a b := fun a b h => by simp only [f, if_neg h]
  have hlist : ∀ a b, s(a, b) ∈ K → c s(a, b) ∉ P ∧ availPair G P T a (c s(a, b)) ∧
      availPair G P T b (c s(a, b)) := by
    intro a b h
    have := hc1 _ h
    simp only [residList, mem_filter, mem_compl, Sym2.mem_toFinset, Sym2.mem_iff] at this
    exact ⟨this.1, this.2 a (Or.inl rfl), this.2 b (Or.inr rfl)⟩
  refine ⟨f, ?_, ?_, ?_, hfK⟩
  · intro a ha b hb hab _
    have hs : s(b, a) = s(a, b) := Sym2.eq_swap
    by_cases h : s(a, b) ∈ K
    · rw [hfK a b h, hfK b a (hs ▸ h), hs]
    · rw [hfK' a b h, hfK' b a (hs ▸ h), hf1 a ha b hb hab]
  · intro a ha b hb hab _
    by_cases h : s(a, b) ∈ K
    · rw [hfK a b h]; exact hlist a b h
    · rw [hfK' a b h]
      exact ⟨(hf2 a ha b hb hab).1, (hf2 a ha b hb hab).2.1.1, (hf2 a ha b hb hab).2.2.1⟩
  · intro a ha b hb b' hb' hab hab' hbb' _ _
    have hshare : Shares s(a, b) s(a, b') := ⟨a, by simp, by simp⟩
    have hne : s(a, b) ≠ s(a, b') := by
      intro h
      rw [Sym2.eq_iff] at h
      rcases h with ⟨-, h⟩ | ⟨h, -⟩
      · exact hbb' h
      · exact hab' h
    by_cases h : s(a, b) ∈ K <;> by_cases h' : s(a, b') ∈ K
    · rw [hfK a b h, hfK a b' h']
      exact hc3 _ h _ h' hne hshare
    · rw [hfK a b h, hfK' a b' h']
      exact (hf2 a ha b' hb' hab').2.1.2 _ h (Sym2.mem_mk_left a b)
    · rw [hfK' a b h, hfK a b' h']
      exact fun heq => (hf2 a ha b hb hab).2.1.2 _ h' (Sym2.mem_mk_left a b') heq.symm
    · rw [hfK' a b h, hfK' a b' h']
      exact hf3 a ha b hb b' hb' hab hab' hbb'

/-- **Distinct prefixes give distinct partitions.** If two completions agree with the prefix
colourings `c`, `c'` on `K` and assemble to the same family of blocks, then `c = c'`: the
triangle of the assembled partition through a pair of `K` recovers its colour. -/
theorem prefix_injective {σ : Sym2 V → ℕ} {r : ℕ} (hT : LiftInv G P σ r (extEdges G P) T)
    {K : Finset (Sym2 V)} (hK : K ⊆ (residGraph G P T).edgeFinset) {x₀ : V}
    {c c' : Sym2 V → V} (hc : c ∈ listColorings K (residList G P T) x₀)
    (hc' : c' ∈ listColorings K (residList G P T) x₀) {f f' : V → V → V}
    (hf1 : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → residPair G P T a b → f a b = f b a)
    (hf2 : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → residPair G P T a b →
        f a b ∉ P ∧ availPair G P T a (f a b) ∧ availPair G P T b (f a b))
    (hf3 : ∀ a ∈ P, ∀ b ∈ P, ∀ b' ∈ P, a ≠ b → a ≠ b' → b ≠ b' → residPair G P T a b →
        residPair G P T a b' → f a b ≠ f a b')
    (hfK : ∀ a b, s(a, b) ∈ K → f a b = c s(a, b))
    (hfK' : ∀ a b, s(a, b) ∈ K → f' a b = c' s(a, b))
    (heq : allBlocks G P T f = allBlocks G P T f') : c = c' := by
  have hBs := allBlocks_isCliquePartition hT hf1 hf2 hf3
  funext e
  by_cases he : e ∈ K
  · induction e using Sym2.ind with
    | h a b =>
    have hadj := hK he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, residGraph_adj] at hadj
    obtain ⟨ha, hb, hab, hres⟩ := hadj
    have hB : ({a, b, f a b} : Finset V) ∈ allBlocks G P T f :=
      mem_allBlocks.mpr (Or.inr (Or.inl (mem_triBlocks.mpr ⟨a, b, ha, hb, hab, hres, rfl⟩)))
    have hB' : ({a, b, f' a b} : Finset V) ∈ allBlocks G P T f := by
      rw [heq]
      exact mem_allBlocks.mpr (Or.inr (Or.inl (mem_triBlocks.mpr ⟨a, b, ha, hb, hab, hres, rfl⟩)))
    obtain ⟨B, -, hBu⟩ := hBs.existsUnique a b hres.1
    have e1 := hBu _ ⟨hB, by simp, by simp⟩
    have e2 := hBu _ ⟨hB', by simp, by simp⟩
    have hmem : f a b ∈ ({a, b, f' a b} : Finset V) := by
      rw [e2, ← e1]; simp
    simp only [mem_insert, mem_singleton] at hmem
    have hx := (hf2 a ha b hb hab hres).1
    rcases hmem with h | h | h
    · rw [h] at hx; exact absurd ha hx
    · rw [h] at hx; exact absurd hb hx
    · rw [← hfK a b he, ← hfK' a b he, h]
  · rw [(mem_listColorings.mp hc).2.1 e he, (mem_listColorings.mp hc').2.1 e he]

/-- The residual graph lives on `P`. -/
theorem residGraph_degree_le (a : V) :
    (residGraph G P T).degree a ≤ P.card - 1 := by
  classical
  by_cases ha : a ∈ P
  · rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have : (residGraph G P T).neighborFinset a ⊆ P.erase a := by
      intro b hb
      rw [SimpleGraph.mem_neighborFinset, residGraph_adj] at hb
      exact mem_erase.mpr ⟨hb.2.2.1.symm, hb.2.1⟩
    exact (card_le_card this).trans (card_erase_of_mem ha).le
  · rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have : (residGraph G P T).neighborFinset a = ∅ := by
      ext b
      rw [SimpleGraph.mem_neighborFinset, residGraph_adj]
      simp [ha]
    rw [this, card_empty]
    exact Nat.zero_le _

/-- Minimum degree of the residual graph on `P`: at most `h` non-neighbours and at most
`(c - 1) r` partners covered by lifting blocks. -/
theorem residGraph_degree_ge {σ : Sym2 V → ℕ} {c r : ℕ} (hT : LiftInv G P σ r (extEdges G P) T)
    (hσc : ∀ e ∈ extEdges G P, σ e ≤ c) {a : V} (ha : a ∈ P) :
    P.card ≤ (residGraph G P T).degree a + 1 + editDegree G P + (c - 1) * r := by
  let cov := ((extEdges G P).filter (fun e => a ∈ T e)).biUnion (fun e => (T e).erase a)
  have hsub : P ⊆ insert a ((residGraph G P T).neighborFinset a) ∪
      P.filter (fun b => b ≠ a ∧ ¬ G.Adj a b) ∪ cov := by
    intro b hb
    by_cases hba : b = a
    · subst hba; simp
    by_cases hadj : G.Adj a b
    · by_cases hcov : coveredPair G P T a b
      · obtain ⟨e, he, hae, hbe⟩ := hcov
        exact mem_union_right _ (mem_biUnion.mpr ⟨e, mem_filter.mpr ⟨he, hae⟩,
          mem_erase.mpr ⟨hba, hbe⟩⟩)
      · refine mem_union_left _ (mem_union_left _ (mem_insert_of_mem ?_))
        rw [SimpleGraph.mem_neighborFinset, residGraph_adj]
        exact ⟨ha, hb, fun h => hba h.symm, hadj, hcov⟩
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hb, hba, hadj⟩))
  have h1 := card_le_card hsub
  have h2 := card_union_le (insert a ((residGraph G P T).neighborFinset a) ∪
      P.filter (fun b => b ≠ a ∧ ¬ G.Adj a b)) cov
  have h3 := card_union_le (insert a ((residGraph G P T).neighborFinset a))
      (P.filter (fun b => b ≠ a ∧ ¬ G.Adj a b))
  have h4 := card_insert_le a ((residGraph G P T).neighborFinset a)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at h4
  have h5 := core_local_bound G P a ha
  have h6 : cov.card ≤ (c - 1) * r := by
    refine card_biUnion_le.trans ?_
    calc ∑ e ∈ (extEdges G P).filter (fun e => a ∈ T e), ((T e).erase a).card
        ≤ ∑ _e ∈ (extEdges G P).filter (fun e => a ∈ T e), (c - 1) := by
          refine sum_le_sum fun e he => ?_
          rw [mem_filter] at he
          rw [card_erase_of_mem he.2, hT.card e he.1]
          have := hσc e he.1
          omega
      _ = (c - 1) * ((extEdges G P).filter (fun e => a ∈ T e)).card := by
          rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ (c - 1) * r := Nat.mul_le_mul_left _ (hT.load a)
  omega

/-- Edge count of the residual graph: `p (p - 1 - h - (c-1) r) ≤ 2 e(J)`. -/
theorem residGraph_card_edges {σ : Sym2 V → ℕ} {c r : ℕ}
    (hT : LiftInv G P σ r (extEdges G P) T) (hσc : ∀ e ∈ extEdges G P, σ e ≤ c) :
    P.card * (P.card - 1 - editDegree G P - (c - 1) * r) ≤
      2 * (residGraph G P T).edgeFinset.card := by
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  calc P.card * (P.card - 1 - editDegree G P - (c - 1) * r)
      = ∑ _a ∈ P, (P.card - 1 - editDegree G P - (c - 1) * r) := by
        rw [sum_const, smul_eq_mul]
    _ ≤ ∑ a ∈ P, (residGraph G P T).degree a := by
        refine sum_le_sum fun a ha => ?_
        have := residGraph_degree_ge hT hσc ha
        omega
    _ ≤ ∑ a, (residGraph G P T).degree a :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)

end Research

end PaperVI
