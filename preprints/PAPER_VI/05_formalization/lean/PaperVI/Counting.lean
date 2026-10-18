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
Paper VI — counting identities for clique partitions, the slack identity (11) and the
lower bounds `cp(G) ≥ s - u - 2m`, `cp_{≤3}(G) ≥ s - u - m`.
-/
module

public import PaperVI.Defs

@[expose] public section

namespace PaperVI

open Finset

variable {V : Type*} [DecidableEq V]

/-! ### Arithmetic of `binom(·,2)` and the slack -/

theorem two_mul_choose_two (a : ℕ) : 2 * (a.choose 2 : ℤ) = (a : ℤ) * ((a : ℤ) - 1) := by
  induction a with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
    push_cast
    linarith

theorem choose_two_add (a b : ℕ) :
    ((a + b).choose 2 : ℤ) = (a.choose 2 : ℤ) + (b.choose 2 : ℤ) + (a : ℤ) * b := by
  have h1 := two_mul_choose_two (a + b)
  have h2 := two_mul_choose_two a
  have h3 := two_mul_choose_two b
  push_cast at h1
  linarith

theorem int_mul_pred_nonneg (t : ℤ) : 0 ≤ t * (t - 1) := by
  rcases le_or_gt t 0 with h | h <;> nlinarith

/-- Formula (10): `2 ℓ(a,b) = (a-b)(a-b-1) + (b-1)(b-2)`. -/
theorem two_mul_slack (a b : ℕ) :
    2 * slack a b = ((a : ℤ) - b) * ((a : ℤ) - b - 1) + ((b : ℤ) - 1) * ((b : ℤ) - 2) := by
  unfold slack
  have h2 := two_mul_choose_two a
  have h3 := two_mul_choose_two b
  linarith

/-- The slack of every clique type is nonnegative. -/
theorem slack_nonneg (a b : ℕ) : 0 ≤ slack a b := by
  have h := two_mul_slack a b
  have h1 := int_mul_pred_nonneg ((a : ℤ) - b)
  have h2 := int_mul_pred_nonneg ((b : ℤ) - 1)
  have : ((b : ℤ) - 1) * ((b : ℤ) - 1 - 1) = ((b : ℤ) - 1) * ((b : ℤ) - 2) := by ring
  linarith

/-- (12): the zero-slack types are exactly `(1,1), (2,1), (2,2), (3,2)`. -/
theorem slack_eq_zero_iff (a b : ℕ) :
    slack a b = 0 ↔ (a = 1 ∧ b = 1) ∨ (a = 2 ∧ b = 1) ∨ (a = 2 ∧ b = 2) ∨ (a = 3 ∧ b = 2) := by
  have h := two_mul_slack a b
  have h1 := int_mul_pred_nonneg ((a : ℤ) - b)
  have h2 := int_mul_pred_nonneg ((b : ℤ) - 1)
  have e2 : ((b : ℤ) - 1) * ((b : ℤ) - 1 - 1) = ((b : ℤ) - 1) * ((b : ℤ) - 2) := by ring
  constructor
  · intro h0
    have hA : ((a : ℤ) - b) * ((a : ℤ) - b - 1) = 0 := by linarith
    have hB : ((b : ℤ) - 1) * ((b : ℤ) - 2) = 0 := by linarith
    rcases mul_eq_zero.mp hA with hA | hA <;> rcases mul_eq_zero.mp hB with hB | hB <;> omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> decide

/-! ### Edges inside cliques -/

theorem card_sym2_filter_not_isDiag (X : Finset V) :
    (X.sym2.filter (fun e => ¬ e.IsDiag)).card = X.card.choose 2 := by
  have h1 := card_filter_add_card_filter_not (s := X.sym2) (fun e => e.IsDiag)
  have h2 : X.sym2.filter (fun e => e.IsDiag) = X.image (fun a => s(a, a)) := by
    ext e
    induction e using Sym2.ind with
    | h a b =>
      simp only [mem_filter, mem_sym2_iff, Sym2.mem_iff, Sym2.mk_isDiag_iff, mem_image,
        Sym2.eq_iff]
      constructor
      · rintro ⟨h, rfl⟩; exact ⟨a, h a (Or.inl rfl), by tauto⟩
      · rintro ⟨c, hc, h⟩
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          exact ⟨by rintro _ (rfl | rfl) <;> exact hc, rfl⟩
  rw [h2, card_image_of_injective _ (fun a b h => by simpa using h), card_sym2] at h1
  have h3 : (X.card + 1).choose 2 = X.card.choose 2 + X.card := by
    rw [Nat.choose_succ_succ', Nat.choose_one_right]; ring
  omega

/-- The edges of `G` inside a set `X`. -/
def innerEdges (G : SimpleGraph V) [Fintype G.edgeSet] (X : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∀ v ∈ e.toFinset, v ∈ X)

/-- A clique on `k` vertices has `binom(k,2)` edges. -/
theorem card_innerEdges_of_isClique (G : SimpleGraph V) [Fintype G.edgeSet] (X : Finset V)
    (hX : G.IsClique (X : Set V)) : (innerEdges G X).card = X.card.choose 2 := by
  rw [← card_sym2_filter_not_isDiag]
  congr 1
  ext e
  induction e using Sym2.ind with
  | h a b =>
    simp only [innerEdges, mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      Sym2.mem_toFinset, Sym2.mem_iff, mem_sym2_iff, Sym2.mk_isDiag_iff]
    constructor
    · rintro ⟨hab, h⟩; exact ⟨fun c hc => h c hc, hab.ne⟩
    · rintro ⟨h, hab⟩
      exact ⟨hX (h a (Or.inl rfl)) (h b (Or.inr rfl)) hab, fun c hc => h c hc⟩

/-! ### The three kinds of edges -/

theorem card_kinds (P : Finset V) (S : Finset (Sym2 V)) :
    (S.filter (fun e => ∀ v ∈ e.toFinset, v ∈ P)).card +
      (S.filter (fun e => ∀ v ∈ e.toFinset, v ∉ P)).card +
      (S.filter (fun e => (∃ v ∈ e.toFinset, v ∈ P) ∧ ∃ v ∈ e.toFinset, v ∉ P)).card
      = S.card := by
  have h1 := card_filter_add_card_filter_not (s := S) (fun e => ∀ v ∈ e.toFinset, v ∈ P)
  have h2 := card_filter_add_card_filter_not
    (s := S.filter (fun e => ¬ ∀ v ∈ e.toFinset, v ∈ P)) (fun e => ∀ v ∈ e.toFinset, v ∉ P)
  rw [filter_filter, filter_filter] at h2
  have e1 : S.filter (fun e => (¬ ∀ v ∈ e.toFinset, v ∈ P) ∧ ∀ v ∈ e.toFinset, v ∉ P) =
      S.filter (fun e => ∀ v ∈ e.toFinset, v ∉ P) := by
    apply filter_congr
    intro e _
    induction e using Sym2.ind with
    | h a b =>
      simp only [Sym2.mem_toFinset, Sym2.mem_iff, forall_eq_or_imp, forall_eq, not_and]
      tauto
  have e2 : S.filter (fun e => (¬ ∀ v ∈ e.toFinset, v ∈ P) ∧ ¬ ∀ v ∈ e.toFinset, v ∉ P) =
      S.filter (fun e => (∃ v ∈ e.toFinset, v ∈ P) ∧ ∃ v ∈ e.toFinset, v ∉ P) := by
    apply filter_congr
    intro e _
    simp only [not_forall, not_not, exists_prop]
    tauto
  rw [e1, e2] at h2
  omega

/-! ### Summing over a clique partition -/

theorem sum_card_filter_inside {G : SimpleGraph V} [Fintype G.edgeSet] {Bs : Finset (Finset V)}
    (hBs : IsCliquePartition G Bs) (S : Finset (Sym2 V)) (hS : S ⊆ G.edgeFinset) :
    ∑ B ∈ Bs, (S.filter (fun e => ∀ v ∈ e.toFinset, v ∈ B)).card = S.card := by
  rw [← card_biUnion]
  · congr 1
    ext e
    simp only [mem_biUnion, mem_filter]
    constructor
    · rintro ⟨B, -, he, -⟩; exact he
    · intro he
      induction e using Sym2.ind with
      | h u v =>
        have hadj : G.Adj u v := by simpa using hS he
        obtain ⟨B, ⟨hB, hu, hv⟩, -⟩ := hBs.existsUnique u v hadj
        refine ⟨B, hB, he, ?_⟩
        simp only [Sym2.mem_toFinset, Sym2.mem_iff]
        rintro w (rfl | rfl) <;> assumption
  · intro B1 hB1 B2 hB2 hne
    simp only [Function.onFun]
    rw [disjoint_left]
    intro e he1 he2
    simp only [mem_filter] at he1 he2
    induction e using Sym2.ind with
    | h u v =>
      have hadj : G.Adj u v := by simpa using hS he1.1
      obtain ⟨B, -, hB⟩ := hBs.existsUnique u v hadj
      have m1 : u ∈ B1 := he1.2 u (by simp)
      have m2 : v ∈ B1 := he1.2 v (by simp)
      have m3 : u ∈ B2 := he2.2 u (by simp)
      have m4 : v ∈ B2 := he2.2 v (by simp)
      exact hne ((hB B1 ⟨hB1, m1, m2⟩).trans (hB B2 ⟨hB2, m3, m4⟩).symm)

variable (G : SimpleGraph V) [Fintype G.edgeSet] (P : Finset V)

theorem coreEdges_filter_inside (B : Finset V) :
    (coreEdges G P).filter (fun e => ∀ v ∈ e.toFinset, v ∈ B) = innerEdges G (B ∩ P) := by
  unfold coreEdges innerEdges
  rw [filter_filter]
  apply filter_congr
  intro e _
  simp only [mem_inter]
  constructor
  · rintro ⟨h1, h2⟩ v hv; exact ⟨h2 v hv, h1 v hv⟩
  · intro h; exact ⟨fun v hv => (h v hv).2, fun v hv => (h v hv).1⟩

theorem extEdges_filter_inside (B : Finset V) :
    (extEdges G P).filter (fun e => ∀ v ∈ e.toFinset, v ∈ B) = innerEdges G (B \ P) := by
  unfold extEdges innerEdges
  rw [filter_filter]
  apply filter_congr
  intro e _
  simp only [mem_sdiff]
  constructor
  · rintro ⟨h1, h2⟩ v hv; exact ⟨h2 v hv, h1 v hv⟩
  · intro h; exact ⟨fun v hv => (h v hv).2, fun v hv => (h v hv).1⟩

theorem crossEdges_filter_inside_card (B : Finset V) (hB : G.IsClique (B : Set V)) :
    ((crossEdges G P).filter (fun e => ∀ v ∈ e.toFinset, v ∈ B)).card =
      coreSize P B * extSize P B := by
  have hk := card_kinds P (innerEdges G B)
  have e1 : (innerEdges G B).filter (fun e => ∀ v ∈ e.toFinset, v ∈ P) =
      (coreEdges G P).filter (fun e => ∀ v ∈ e.toFinset, v ∈ B) := by
    unfold innerEdges coreEdges; rw [filter_filter, filter_filter]
    exact filter_congr (fun _ _ => And.comm)
  have e2 : (innerEdges G B).filter (fun e => ∀ v ∈ e.toFinset, v ∉ P) =
      (extEdges G P).filter (fun e => ∀ v ∈ e.toFinset, v ∈ B) := by
    unfold innerEdges extEdges; rw [filter_filter, filter_filter]
    exact filter_congr (fun _ _ => And.comm)
  have e3 : (innerEdges G B).filter
      (fun e => (∃ v ∈ e.toFinset, v ∈ P) ∧ ∃ v ∈ e.toFinset, v ∉ P) =
      (crossEdges G P).filter (fun e => ∀ v ∈ e.toFinset, v ∈ B) := by
    unfold innerEdges crossEdges; rw [filter_filter, filter_filter]
    exact filter_congr (fun _ _ => And.comm)
  rw [e1, e2, e3, coreEdges_filter_inside, extEdges_filter_inside,
    card_innerEdges_of_isClique G (B ∩ P) (hB.subset (by simp)),
    card_innerEdges_of_isClique G (B \ P) (hB.subset (fun x hx => (mem_sdiff.mp hx).1)),
    card_innerEdges_of_isClique G B hB] at hk
  have hcard : B.card = (B ∩ P).card + (B \ P).card := by
    rw [add_comm]; exact (card_sdiff_add_card_inter B P).symm
  rw [hcard] at hk
  have := choose_two_add (B ∩ P).card (B \ P).card
  unfold coreSize extSize
  zify
  linarith

/-- The edges of `K` inside a vertex set `Q` (stated without a `Fintype V` instance, so that
the decidability instance is fixed). -/
def insideFilter (K : Finset (Sym2 V)) (Q : Finset V) : Finset (Sym2 V) :=
  K.filter (fun e => ∀ v ∈ e.toFinset, v ∈ Q)

theorem coreEdges_subset : coreEdges G P ⊆ G.edgeFinset := filter_subset _ _
theorem extEdges_subset' : extEdges G P ⊆ G.edgeFinset := filter_subset _ _
theorem crossEdges_subset : crossEdges G P ⊆ G.edgeFinset := filter_subset _ _

theorem card_insideFilter_core (B : Finset V) (hB : G.IsClique (B : Set V)) :
    (insideFilter (coreEdges G P) B).card = (coreSize P B).choose 2 := by
  unfold insideFilter
  rw [coreEdges_filter_inside, card_innerEdges_of_isClique G _
    (hB.subset (fun v hv => (mem_inter.mp hv).1))]
  rfl

theorem card_insideFilter_ext (B : Finset V) (hB : G.IsClique (B : Set V)) :
    (insideFilter (extEdges G P) B).card = (extSize P B).choose 2 := by
  unfold insideFilter
  rw [extEdges_filter_inside, card_innerEdges_of_isClique G _
    (hB.subset (fun v hv => (mem_sdiff.mp hv).1))]
  rfl

theorem card_insideFilter_cross (B : Finset V) (hB : G.IsClique (B : Set V)) :
    (insideFilter (crossEdges G P) B).card = coreSize P B * extSize P B :=
  crossEdges_filter_inside_card G P B hB

/-- Counting each core, exterior and crossing edge once over a clique partition. -/
theorem partition_sums {Bs : Finset (Finset V)} (hBs : IsCliquePartition G Bs) :
    ∑ B ∈ Bs, (coreSize P B).choose 2 = uCount G P ∧
    ∑ B ∈ Bs, (extSize P B).choose 2 = mCount G P ∧
    ∑ B ∈ Bs, coreSize P B * extSize P B = sCount G P := by
  refine ⟨?_, ?_, ?_⟩
  · rw [uCount, ← sum_card_filter_inside hBs (coreEdges G P) (filter_subset _ _)]
    refine sum_congr rfl fun B hB => ?_
    rw [coreEdges_filter_inside, card_innerEdges_of_isClique G _
      ((hBs.isClique B hB).subset (by simp))]
    rfl
  · rw [mCount, ← sum_card_filter_inside hBs (extEdges G P) (filter_subset _ _)]
    refine sum_congr rfl fun B hB => ?_
    rw [extEdges_filter_inside, card_innerEdges_of_isClique G _
      ((hBs.isClique B hB).subset (fun x hx => (mem_sdiff.mp hx).1))]
    rfl
  · rw [sCount, ← sum_card_filter_inside hBs (crossEdges G P) (filter_subset _ _)]
    refine sum_congr rfl fun B hB => ?_
    rw [crossEdges_filter_inside_card G P B (hBs.isClique B hB)]

/-- The slack identity (11): `|Π| - (s - u - 2m) = Σ_Q ℓ(a_Q, b_Q)`. -/
theorem slack_identity {Bs : Finset (Finset V)} (hBs : IsCliquePartition G Bs) :
    (Bs.card : ℤ) - ((sCount G P : ℤ) - uCount G P - 2 * mCount G P) =
      ∑ B ∈ Bs, slack (coreSize P B) (extSize P B) := by
  obtain ⟨h1, h2, h3⟩ := partition_sums G P hBs
  simp only [slack, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul,
    mul_one]
  rw [← h1, ← h2, ← h3]
  push_cast
  ring

/-- The Erdős–Faudree–Ordman type lower bound: every clique partition has at least
`s - u - 2m` blocks. -/
theorem card_ge_of_isCliquePartition {Bs : Finset (Finset V)} (hBs : IsCliquePartition G Bs) :
    (sCount G P : ℤ) - uCount G P - 2 * mCount G P ≤ Bs.card := by
  have h := slack_identity G P hBs
  have : 0 ≤ ∑ B ∈ Bs, slack (coreSize P B) (extSize P B) :=
    sum_nonneg fun B _ => slack_nonneg _ _
  linarith

/-- Lower bound (17): a clique partition into blocks of order at most three has at least
`s - u - m` blocks. -/
theorem card_ge_of_isCliquePartition_le_three {Bs : Finset (Finset V)}
    (hBs : IsCliquePartition G Bs) (h3 : ∀ B ∈ Bs, B.card ≤ 3) :
    (sCount G P : ℤ) - uCount G P - mCount G P ≤ Bs.card := by
  obtain ⟨h1, h2, h3'⟩ := partition_sums G P hBs
  have key : ∀ B ∈ Bs, ((coreSize P B * extSize P B : ℕ) : ℤ) - (coreSize P B).choose 2 -
      (extSize P B).choose 2 ≤ 1 := by
    intro B hB
    have hc : B.card = (B ∩ P).card + (B \ P).card := by
      rw [add_comm]; exact (card_sdiff_add_card_inter B P).symm
    have hle := h3 B hB
    unfold coreSize extSize
    have : (B ∩ P).card + (B \ P).card ≤ 3 := hc ▸ hle
    have ha3 : (B ∩ P).card ≤ 3 := by omega
    have hb3 : (B \ P).card ≤ 3 := by omega
    interval_cases ha : (B ∩ P).card <;> interval_cases hb : (B \ P).card <;> simp_all
  have hsum := sum_le_sum key
  simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one] at hsum
  rw [← Nat.cast_sum, ← Nat.cast_sum, ← Nat.cast_sum, h1, h2, h3'] at hsum
  linarith

/-! ### Existence of clique partitions and the minima -/

theorem isCliquePartition_edges [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsCliquePartition G (G.edgeFinset.image Sym2.toFinset) := by
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    simp only [mem_image, SimpleGraph.mem_edgeFinset] at hB
    obtain ⟨e, he, rfl⟩ := hB
    rw [Sym2.card_toFinset_of_not_isDiag _ (G.not_isDiag_of_mem_edgeSet he)]
  · intro B hB
    simp only [mem_image, SimpleGraph.mem_edgeFinset] at hB
    obtain ⟨e, he, rfl⟩ := hB
    induction e using Sym2.ind with
    | h a b =>
      intro x hx y hy hxy
      rw [Finset.mem_coe, Sym2.mem_toFinset, Sym2.mem_iff] at hx hy
      have hab : G.Adj a b := he
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · exact hab
      · exact hab.symm
      · exact absurd rfl hxy
  · intro u v huv
    refine ⟨s(u, v).toFinset, ⟨mem_image.mpr ⟨s(u, v), by simpa using huv, rfl⟩, by simp,
      by simp⟩, ?_⟩
    rintro B ⟨hB, hu, hv⟩
    simp only [mem_image, SimpleGraph.mem_edgeFinset] at hB
    obtain ⟨e, he, rfl⟩ := hB
    rw [Sym2.mem_toFinset] at hu hv
    rw [(Sym2.mem_and_mem_iff huv.ne).mp ⟨hu, hv⟩]

omit [DecidableEq V] in
theorem cp_le [Fintype V] {G : SimpleGraph V} {Bs : Finset (Finset V)}
    (hBs : IsCliquePartition G Bs) : cp G ≤ Bs.card :=
  Nat.sInf_le ⟨Bs, hBs, rfl⟩

theorem exists_cp [Fintype V] (G : SimpleGraph V) :
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ Bs.card = cp G := by
  classical
  have hne : {k | ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ Bs.card = k}.Nonempty :=
    ⟨_, _, isCliquePartition_edges G, rfl⟩
  exact Nat.sInf_mem hne

omit [DecidableEq V] in
theorem cpLe_le [Fintype V] {G : SimpleGraph V} {r : ℕ} {Bs : Finset (Finset V)}
    (hBs : IsCliquePartition G Bs) (hr : ∀ B ∈ Bs, B.card ≤ r) : cpLe r G ≤ Bs.card :=
  Nat.sInf_le ⟨Bs, hBs, hr, rfl⟩

theorem exists_cpLe [Fintype V] (G : SimpleGraph V) {r : ℕ} (hr : 2 ≤ r) :
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ (∀ B ∈ Bs, B.card ≤ r) ∧
      Bs.card = cpLe r G := by
  classical
  have hne : {k | ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ (∀ B ∈ Bs, B.card ≤ r) ∧
      Bs.card = k}.Nonempty := by
    refine ⟨_, _, isCliquePartition_edges G, ?_, rfl⟩
    intro B hB
    simp only [mem_image, SimpleGraph.mem_edgeFinset] at hB
    obtain ⟨e, he, rfl⟩ := hB
    rw [Sym2.card_toFinset_of_not_isDiag _ (G.not_isDiag_of_mem_edgeSet he)]
    exact hr
  exact Nat.sInf_mem hne

theorem cp_le_cpLe [Fintype V] (G : SimpleGraph V) {r : ℕ} (hr : 2 ≤ r) : cp G ≤ cpLe r G := by
  obtain ⟨Bs, hBs, -, hc⟩ := exists_cpLe G hr
  exact hc ▸ cp_le hBs

/-- The lower bound for `cp(G)` itself. -/
theorem cp_ge [Fintype V] :
    (sCount G P : ℤ) - uCount G P - 2 * mCount G P ≤ cp G := by
  obtain ⟨Bs, hBs, hc⟩ := exists_cp G
  have := card_ge_of_isCliquePartition G P hBs
  rw [hc] at this
  exact this

theorem cpLe_three_ge [Fintype V] :
    (sCount G P : ℤ) - uCount G P - mCount G P ≤ cpLe 3 G := by
  obtain ⟨Bs, hBs, h3, hc⟩ := exists_cpLe G (r := 3) (by norm_num)
  have := card_ge_of_isCliquePartition_le_three G P hBs h3
  rw [hc] at this
  exact this

end PaperVI

