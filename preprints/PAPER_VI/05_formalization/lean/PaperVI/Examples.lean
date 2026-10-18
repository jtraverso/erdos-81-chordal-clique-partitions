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
Paper VI — the unperturbed case `h = 0` (including `n = 2`) and the concentrated
modification example (27) of Section 8.
-/
module

public import PaperVI.Rigidity

@[expose] public section

namespace PaperVI

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

instance (P : Finset V) : DecidableRel (refGraph P).Adj := fun u v => by
  unfold refGraph; infer_instance

omit [Fintype V] [DecidableEq V] in
theorem editGraph_refGraph (P : Finset V) : editGraph (refGraph P) P = ⊥ := by
  unfold editGraph; exact symmDiff_self _

omit [DecidableEq V] in
theorem editDegree_refGraph (P : Finset V) : editDegree (refGraph P) P = 0 := by
  unfold editDegree
  convert SimpleGraph.maxDegree_bot_eq_zero (V := V)
  exact editGraph_refGraph P

theorem uCount_refGraph (P : Finset V) : uCount (refGraph P) P = P.card.choose 2 := by
  unfold uCount
  have : coreEdges (refGraph P) P = innerEdges (refGraph P) P := rfl
  rw [this, card_innerEdges_of_isClique _ P (fun a ha b _ hab =>
    show a ≠ b ∧ (a ∈ P ∨ b ∈ P) from ⟨hab, Or.inl ha⟩)]

theorem mCount_refGraph (P : Finset V) : mCount (refGraph P) P = 0 := by
  unfold mCount
  rw [card_eq_zero, eq_empty_iff_forall_notMem]
  intro e he
  induction e using Sym2.ind with
  | h x y =>
    rw [mem_extEdges] at he
    obtain ⟨⟨-, h⟩, hx, hy⟩ := he
    tauto

theorem sCount_refGraph (P : Finset V) :
    sCount (refGraph P) P = P.card * (Fintype.card V - P.card) := by
  rw [← card_crossEdges_top P]
  unfold sCount
  congr 1
  ext e
  induction e using Sym2.ind with
  | h x y =>
    rw [mem_crossEdges, mem_crossEdges, SimpleGraph.top_adj]
    simp only [refGraph]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by tauto⟩, h2⟩

/-- The unperturbed reference graph: if `q ≤ 2p + 1` and `p ≤ q`, then
`cp(K_P ∨ I_O) = pq - binom(p,2)`. -/
theorem cp_refGraph (P : Finset V) (hq1 : Pᶜ.card ≤ 2 * P.card + 1) (hpq : P.card ≤ Pᶜ.card) :
    (cp (refGraph P) : ℤ) = (P.card : ℤ) * ((Fintype.card V : ℤ) - P.card) -
      (P.card.choose 2 : ℤ) := by
  have h0 := editDegree_refGraph P
  obtain ⟨Bs, hBs, htypes⟩ := exists_partition_A (refGraph P) P hq1 (by rw [h0]; omega)
  have hcp := (theoremA_conclusions (refGraph P) P hBs htypes).1
  rw [hcp, uCount_refGraph, mCount_refGraph, sCount_refGraph]
  have hpn : P.card ≤ Fintype.card V := card_le_univ P
  push_cast [hpn]
  ring

/-- **The case `h = 0`.** For every order `n` (in particular `n = 2`; the hypothesis `n ≥ 2`
of the paper is not needed here), `cp(K_p ∨ I_q) = M(n)`, and this graph satisfies `h = 0`. -/
theorem cp_refGraph_eq_Mval (P : Finset V)
    (hP : P.card = (Fintype.card V + 1) / 3) :
    editDegree (refGraph P) P = 0 ∧ cp (refGraph P) = Mval (Fintype.card V) := by
  refine ⟨editDegree_refGraph P, ?_⟩
  have hq : Pᶜ.card = Fintype.card V - P.card := card_compl P
  have hq1 : Pᶜ.card ≤ 2 * P.card + 1 := by rw [hq, hP]; exact q_le_two_p_add_one _
  have hpq : P.card ≤ Pᶜ.card := by rw [hq, hP]; exact p_le_q _
  have h := cp_refGraph P hq1 hpq
  have hM := Mval_eq (Fintype.card V)
  rw [← hP] at hM
  have hpn : P.card ≤ Fintype.card V := card_le_univ P
  have : ((Fintype.card V - P.card : ℕ) : ℤ) = (Fintype.card V : ℤ) - P.card := by
    push_cast [hpn]; ring
  rw [this] at hM
  exact_mod_cast h.trans hM.symm

/-- **Example (27) of Section 8.** For `n = 3p`, the graph `K_{p+1} ∨ I_{2p-1}` (a complete
split graph with a core of `p + 1` vertices) has `cp = M(3p) - 1`. -/
theorem cp_concentrated_example (p : ℕ) (hp : 1 ≤ p) (hn : Fintype.card V = 3 * p)
    (P' : Finset V) (hP' : P'.card = p + 1) :
    (cp (refGraph P') : ℤ) = Mval (3 * p) - 1 := by
  have hM := Mval_eq (3 * p)
  have e1 : (3 * p + 1) / 3 = p := by omega
  have e2 : 3 * p - p = 2 * p := by omega
  rw [e1, e2] at hM
  have hq : P'ᶜ.card = 3 * p - (p + 1) := by rw [card_compl, hn, hP']
  have hc : (p + 1).choose 2 = p.choose 2 + p := by
    rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
  rcases Nat.lt_or_ge 1 p with hp2 | hp1
  · -- `p ≥ 2`: the reference construction applies to the core `P'`
    have h := cp_refGraph P' (by rw [hq, hP']; omega) (by rw [hq, hP']; omega)
    rw [h, hM, hP', hn, hc]
    push_cast
    ring
  · -- `p = 1`: the graph is a triangle
    have hp1' : p = 1 := by omega
    subst hp1'
    -- lower bound `s - u - 2m = 1`
    have hlow := cp_ge (refGraph P') P'
    rw [uCount_refGraph, mCount_refGraph, sCount_refGraph, hP', hn] at hlow
    -- upper bound: the whole vertex set is one block
    have hup : cp (refGraph P') ≤ 1 := by
      have hpart : IsCliquePartition (refGraph P') {univ} := by
        refine ⟨fun B hB => ?_, fun B hB => ?_, fun u v huv => ?_⟩
        · rw [mem_singleton] at hB; subst hB; rw [card_univ, hn]; norm_num
        · rw [mem_singleton] at hB; subst hB
          intro x _ y _ hxy
          refine ⟨hxy, ?_⟩
          by_contra hcon
          push_neg at hcon
          have hsub : ({x, y} : Finset V) ⊆ P'ᶜ := by
            intro z hz
            simp only [mem_insert, mem_singleton] at hz
            rcases hz with rfl | rfl
            · exact mem_compl.mpr hcon.1
            · exact mem_compl.mpr hcon.2
          have := card_le_card hsub
          rw [card_pair hxy, hq] at this
          omega
        · exact ⟨univ, ⟨mem_singleton_self _, mem_univ _, mem_univ _⟩,
            fun B hB => mem_singleton.mp hB.1⟩
      have := cp_le hpart
      rwa [card_singleton] at this
    have : Mval (3 * 1) = 2 := by decide
    rw [this]
    norm_num at hlow ⊢
    omega

end PaperVI
