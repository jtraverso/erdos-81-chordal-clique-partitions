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
Paper VI research round — Priority 4: many optimal partitions for every exterior prescription
(Theorem N), using Vizing's theorem and the Häggkvist–Janssen completion.

Partitions are counted as labelled families of vertex sets (`Finset (Finset V)`), not up to
isomorphism.
-/
module

public import PaperVIResearch.ResidualCount
public import PaperVIResearch.VizingExtraction
public import PaperVI.Optimal
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

namespace PaperVI

namespace Research

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (P : Finset V)

/-- `Bs` is an optimal clique partition of `G` realizing the exterior prescription `σ`: every
exterior edge lies in a block of order `σ e` with exactly two exterior vertices. -/
def RealizesPrescription (σ : Sym2 V → ℕ) (Bs : Finset (Finset V)) : Prop :=
  IsCliquePartition G Bs ∧ Bs.card = cp G ∧
    ∀ e ∈ extEdges G P, ∃ B ∈ Bs, (∀ v ∈ e, v ∈ B) ∧ B.card = σ e ∧ extSize P B = 2

/-- Arithmetic of the window count: with `d = ⌊p/8⌋` and `p ≥ 16`, at most `12` windows. -/
theorem windows_le_twelve {p Δ : ℕ} (hp : 16 ≤ p) (hΔ : Δ ≤ p - 1) : Δ / (p / 8) + 1 ≤ 12 := by
  have hd : 0 < p / 8 := by omega
  have : Δ / (p / 8) < 12 := by
    rw [Nat.div_lt_iff_lt_mul hd]
    omega
  omega

/-- Arithmetic of the edge count: `p²/64 ≤ |K|`. -/
theorem prefix_size_arith {p h eJ k K : ℕ} (hp : 16 ≤ p) (hh : 63 * h ≤ p)
    (hJ : p * (p - 1 - h - 2 * (7 * h)) ≤ 2 * eJ) (hk : k ≤ 12) (hK : eJ ≤ k * K) :
    p * p / 64 ≤ K := by
  have h1 : 3 * p ≤ 8 * (p - 1 - h - 2 * (7 * h)) := by omega
  have h2 : 3 * (p * p) ≤ 16 * eJ := by
    have := Nat.mul_le_mul_left p h1
    nlinarith
  have h3 : eJ ≤ 12 * K := hK.trans (Nat.mul_le_mul_right K hk)
  have h4 : p * p ≤ 64 * K := by omega
  exact (Nat.div_le_iff_le_mul_add_pred (by norm_num)).mpr (by omega)

/-- **Theorem N, lower bound for one prescription.** Under the hypothesis of Theorem B
(`p = ⌊(n+1)/3⌋`, `p ≥ 63h`) and `p ≥ 16`, every prescription `σ` of orders `4`/`5` to the
exterior edges is realized by at least `p^⌊p²/64⌋` optimal clique partitions.

Proof: fix one lifting with load `≤ 7h`. The residual core graph `J` has minimum degree
`≥ p - 1 - 15h`, hence `≥ p²/4`-ish edges; Vizing's theorem colours `J` with `≤ p` colours and
a window of `⌊p/8⌋` colour classes gives `K ⊆ J` of maximum degree `≤ ⌊p/8⌋` with
`|K| ≥ p²/64`. Greedy colouring from the residual lists gives `≥ p^{|K|}` prefixes; each
extends (Häggkvist–Janssen) to a completion, and distinct prefixes give distinct optimal
partitions. -/
theorem prescribed_count (hP : P.card = (Fintype.card V + 1) / 3)
    (hh : 63 * editDegree G P ≤ P.card) (hp : 16 ≤ P.card) (σ : Sym2 V → ℕ)
    (hσ : ∀ e ∈ extEdges G P, σ e = 4 ∨ σ e = 5) :
    P.card ^ (P.card * P.card / 64) ≤
      Nat.card {Bs : Finset (Finset V) // RealizesPrescription G P σ Bs} := by
  classical
  have hq : Pᶜ.card = Fintype.card V - P.card := card_compl P
  have hq1 : Pᶜ.card ≤ 2 * P.card + 1 := by
    rw [hq, hP]; exact q_le_two_p_add_one _
  have hq0 : 2 * P.card ≤ Pᶜ.card + 1 := by
    rw [hq, hP]; exact two_p_le_q_add_one _
  set h := editDegree G P with hhdef
  set p := P.card with hpdef
  -- one lifting with load `≤ 7h`
  obtain ⟨T, hT⟩ := exists_lift G P (σ := fun e => σ e - 2) (c := 3) (r := 7 * h)
    (need := 30 * h + 3)
    (fun e he => by rcases hσ e he with h | h <;> omega)
    (fun e he => by rcases hσ e he with h | h <;> rw [h] <;> omega)
    (fun k bx by_ dx dy sat nD h1 h2 h3 h4 h5 h6 =>
      arith_candidates_B hq1 hh h1 h2 h3 h4 h5 h6)
  have hσc : ∀ e ∈ extEdges G P, (fun e => σ e - 2) e ≤ 3 := fun e he => by
    dsimp only; rcases hσ e he with h | h <;> omega
  -- the residual graph and the Vizing extraction
  set J := residGraph G P T with hJ
  set d := p / 8 with hd
  obtain ⟨K, hKJ, hKd, hKcard⟩ := exists_sparse_dense_subgraph J d (by omega)
  have hEJ := residGraph_card_edges hT hσc
  have hmax : J.maxDegree ≤ p - 1 :=
    SimpleGraph.maxDegree_le_of_forall_degree_le _ _ (fun v => residGraph_degree_le v)
  have hKbig : p * p / 64 ≤ K.card :=
    prefix_size_arith hp hh (by simpa using hEJ) (windows_le_twelve hp hmax) hKcard
  -- greedy count of prefix colourings
  obtain ⟨x₀, -⟩ : P.Nonempty := card_pos.mp (by omega)
  have hL : ∀ e ∈ K, p + 2 * (d - 1) ≤ (residList G P T e).card := by
    intro e he
    have := card_residList hT (hKJ he)
    omega
  have hcount := pow_le_card_listColorings K (residList G P T) x₀ p (2 * (d - 1)) hL
    (fun e he => card_conflicts_le hKd he)
  -- every prefix extends
  have hq' : p + 2 * (h + 2 * (7 * h) + d) ≤ Pᶜ.card := by omega
  have hext := fun (c : listColorings K (residList G P T) x₀) =>
    prefix_extend hT hKd hq' c.2
  let fc := fun c => Classical.choose (hext c)
  have hfc := fun c => Classical.choose_spec (hext c)
  have hreal : ∀ c, RealizesPrescription G P σ (allBlocks G P T (fc c)) := by
    intro c
    obtain ⟨hf1, hf2, hf3, -⟩ := hfc c
    have hBs := allBlocks_isCliquePartition hT hf1 hf2 hf3
    obtain ⟨hcard, -, -, hreal, -⟩ := theoremB_of_partition G P hP σ hσ hBs
      (fun B hB => allBlocks_types hT hf2 hB)
    exact ⟨hBs, hcard, hreal⟩
  let F : listColorings K (residList G P T) x₀ →
      {Bs : Finset (Finset V) // RealizesPrescription G P σ Bs} :=
    fun c => ⟨allBlocks G P T (fc c), hreal c⟩
  have hF : Function.Injective F := by
    intro c c' hcc
    obtain ⟨hf1, hf2, hf3, hfK⟩ := hfc c
    obtain ⟨-, -, -, hfK'⟩ := hfc c'
    exact Subtype.ext (prefix_injective hT hKJ c.2 c'.2 hf1 hf2 hf3 hfK hfK'
      (congrArg Subtype.val hcc))
  calc p ^ (p * p / 64) ≤ p ^ K.card := Nat.pow_le_pow_right (by omega) hKbig
    _ ≤ (listColorings K (residList G P T) x₀).card := hcount
    _ = Nat.card (listColorings K (residList G P T) x₀) := (Nat.card_eq_finsetCard _).symm
    _ ≤ _ := Nat.card_le_card_of_injective F hF

/-- Distinct prescriptions `τ` (choice of `K_5`/`K_4` per exterior edge) are realized by disjoint
families of partitions: the order of the block through an exterior edge recovers its label. -/
theorem realizes_prescription_unique {τ τ' : {e // e ∈ extEdges G P} → Bool}
    {Bs : Finset (Finset V)} (h1 : RealizesPrescription G P (prescription G P τ) Bs)
    (h2 : RealizesPrescription G P (prescription G P τ') Bs) : τ = τ' := by
  funext ⟨e, he⟩
  obtain ⟨B, hB1, heB, hcB, -⟩ := h1.2.2 e he
  obtain ⟨B', hB1', heB', hcB', -⟩ := h2.2.2 e he
  have := block_unique_of_edge G h1.1 (extEdges_subset he) hB1 hB1' heB heB'
  rw [this, hcB'] at hcB
  unfold prescription at hcB
  rw [dif_pos he, dif_pos he] at hcB
  cases h1 : τ ⟨e, he⟩ <;> cases h2 : τ' ⟨e, he⟩ <;> simp_all

/-- **Theorem N, total lower bound.** Under the hypothesis of Theorem B and `p ≥ 16`, the number
`N(G)` of optimal clique partitions (labelled) satisfies `N(G) ≥ 2^m · p^⌊p²/64⌋`. -/
theorem total_count (hP : P.card = (Fintype.card V + 1) / 3)
    (hh : 63 * editDegree G P ≤ P.card) (hp : 16 ≤ P.card) :
    2 ^ mCount G P * P.card ^ (P.card * P.card / 64) ≤
      Nat.card {Bs : Finset (Finset V) // IsCliquePartition G Bs ∧ Bs.card = cp G} := by
  classical
  have hσ : ∀ τ, ∀ e ∈ extEdges G P, prescription G P τ e = 4 ∨ prescription G P τ e = 5 := by
    intro τ e he
    unfold prescription
    rw [dif_pos he]
    split_ifs <;> simp
  let S : ({e // e ∈ extEdges G P} → Bool) → Finset (Finset (Finset V)) :=
    fun τ => univ.filter (fun Bs => RealizesPrescription G P (prescription G P τ) Bs)
  have hS : ∀ τ, P.card ^ (P.card * P.card / 64) ≤ (S τ).card := by
    intro τ
    have := prescribed_count G P hP hh hp (prescription G P τ) (hσ τ)
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
    convert this
  have hdisj : ((univ : Finset ({e // e ∈ extEdges G P} → Bool)) : Set _).PairwiseDisjoint S := by
    intro τ _ τ' _ hne
    rw [Function.onFun, disjoint_left]
    intro Bs h1 h2
    exact hne (realizes_prescription_unique G P (mem_filter.mp h1).2 (mem_filter.mp h2).2)
  have hsub : univ.biUnion S ⊆
      univ.filter (fun Bs => IsCliquePartition G Bs ∧ Bs.card = cp G) := by
    intro Bs hBs
    obtain ⟨τ, -, hτ⟩ := mem_biUnion.mp hBs
    have := (mem_filter.mp hτ).2
    exact mem_filter.mpr ⟨mem_univ _, this.1, this.2.1⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc 2 ^ mCount G P * P.card ^ (P.card * P.card / 64)
      = ∑ _τ : {e // e ∈ extEdges G P} → Bool, P.card ^ (P.card * P.card / 64) := by
        rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe,
          smul_eq_mul, mCount]
    _ ≤ ∑ τ, (S τ).card := sum_le_sum fun τ _ => hS τ
    _ = (univ.biUnion S).card := (card_biUnion hdisj).symm
    _ ≤ _ := card_le_card hsub

/-- At most `(n+1)^5` vertex sets of order at most five. -/
theorem card_small_finsets_le :
    (univ.filter (fun B : Finset V => B.card ≤ 5)).card ≤ (Fintype.card V + 1) ^ 5 := by
  have hsub : univ.filter (fun B : Finset V => B.card ≤ 5) ⊆
      (range 6).biUnion (fun k => powersetCard k (univ : Finset V)) := by
    intro B hB
    rw [mem_filter] at hB
    exact mem_biUnion.mpr ⟨B.card, mem_range.mpr (by omega),
      mem_powersetCard.mpr ⟨subset_univ _, rfl⟩⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  rw [add_pow]
  refine sum_le_sum fun k hk => ?_
  rw [card_powersetCard, card_univ, one_pow, mul_one, Nat.cast_id]
  have h1 := Nat.choose_le_pow (Fintype.card V) k
  have h2 : 1 ≤ Nat.choose 5 k := Nat.choose_pos (by rw [mem_range] at hk; omega)
  calc (Fintype.card V).choose k ≤ Fintype.card V ^ k := h1
    _ ≤ Fintype.card V ^ k * Nat.choose 5 k := Nat.le_mul_of_pos_right _ h2

/-- **Upper bound.** If every optimal clique partition has blocks of order at most five, then
`N(G) ≤ (n+1)^{5 e(G)}`: an optimal partition is determined by the map sending each edge to its
block. -/
theorem optimal_count_le (h5 : ∀ Bs, IsCliquePartition G Bs → Bs.card = cp G → ∀ B ∈ Bs,
      B.card ≤ 5) :
    Nat.card {Bs : Finset (Finset V) // IsCliquePartition G Bs ∧ Bs.card = cp G} ≤
      (Fintype.card V + 1) ^ (5 * G.edgeFinset.card) := by
  classical
  have hblk : ∀ (Bs : {Bs : Finset (Finset V) // IsCliquePartition G Bs ∧ Bs.card = cp G})
      (e : G.edgeSet), ∃ B ∈ Bs.1, ∀ v ∈ (e : Sym2 V), v ∈ B := fun Bs e =>
    exists_block_of_edge G Bs.2.1 (SimpleGraph.mem_edgeFinset.mpr e.2)
  let Φ : {Bs : Finset (Finset V) // IsCliquePartition G Bs ∧ Bs.card = cp G} →
      G.edgeSet → {B : Finset V // B.card ≤ 5} := fun Bs e =>
    ⟨Classical.choose (hblk Bs e),
      h5 Bs.1 Bs.2.1 Bs.2.2 _ (Classical.choose_spec (hblk Bs e)).1⟩
  have hrec : ∀ Bs, Bs.1 = univ.image (fun e => (Φ Bs e).1) := by
    intro Bs
    ext B
    constructor
    · intro hB
      obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp (Bs.2.1.two_le B hB)
      have hadj : G.Adj u v := Bs.2.1.isClique B hB hu hv huv
      let e : G.edgeSet := ⟨s(u, v), hadj⟩
      refine mem_image.mpr ⟨e, mem_univ _, ?_⟩
      have hs := Classical.choose_spec (hblk Bs e)
      refine block_unique_of_edge G Bs.2.1 (SimpleGraph.mem_edgeFinset.mpr hadj) hs.1 hB hs.2 ?_
      intro w hw
      rcases Sym2.mem_iff.mp hw with rfl | rfl
      · exact hu
      · exact hv
    · intro hB
      obtain ⟨e, -, rfl⟩ := mem_image.mp hB
      exact (Classical.choose_spec (hblk Bs e)).1
  have hΦ : Function.Injective Φ := by
    intro Bs Bs' h
    apply Subtype.ext
    rw [hrec Bs, hrec Bs', h]
  refine (Nat.card_le_card_of_injective Φ hΦ).trans ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_subtype,
    ← SimpleGraph.edgeFinset_card, pow_mul]
  exact Nat.pow_le_pow_left (card_small_finsets_le) _

/-- **Theorem N (growth order).** Under the hypothesis of Theorem B and `p ≥ 16`,
`2^m · p^⌊p²/64⌋ ≤ N(G) ≤ (n+1)^{5 e(G)}`, where `N(G)` is the number of optimal clique
partitions (labelled). Since `n ≤ 3p + 1` and `e(G) ≤ n²/2`, this gives
`log N(G) = Θ(p² log p)`. -/
theorem theoremN (hP : P.card = (Fintype.card V + 1) / 3)
    (hh : 63 * editDegree G P ≤ P.card) (hp : 16 ≤ P.card) :
    2 ^ mCount G P * P.card ^ (P.card * P.card / 64) ≤
        Nat.card {Bs : Finset (Finset V) // IsCliquePartition G Bs ∧ Bs.card = cp G} ∧
      Nat.card {Bs : Finset (Finset V) // IsCliquePartition G Bs ∧ Bs.card = cp G} ≤
        (Fintype.card V + 1) ^ (5 * G.edgeFinset.card) := by
  refine ⟨total_count G P hP hh hp, optimal_count_le G fun Bs hBs hopt => ?_⟩
  have hn : 2 ≤ Fintype.card V := by omega
  obtain ⟨-, -, -, hcp, -⟩ := theoremB G P hn hP hh (fun _ => 4) (fun _ _ => Or.inl rfl)
  exact fun B hB => (optimal_types_of_cp_eq G P hcp hBs hopt B hB).2

end Research

end PaperVI
