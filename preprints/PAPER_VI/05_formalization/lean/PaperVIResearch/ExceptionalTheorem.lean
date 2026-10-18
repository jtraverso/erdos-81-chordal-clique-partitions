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
Paper VI research round — Theorem E, part 3: the exact formulas.

For the one-exceptional-vertex graph (`ExSetup`) with `q ≥ p + 3` (i.e. `p + 2 ≤ |R|`):

* (E1) `cp(G) = cp_{≤4}(G) = Φ + D(a,b)`, `D(a,b) = max(0, 2b-a, 3b-2a)`, with an explicit
  physical optimal partition; the fractional optimum (equality covering, canonical model over
  `ℝ`) is the same number, certified by the three explicit signed edge duals;
* `cp_{≤3}(G) = Φ + 3b - 2 min(a,b)`;
* (E2) `ν₃(G) = ν₃*(G) = u + min(a,b)`;
* (E3) `cp_{≤3}(G) - cp(G) = min(b, max(0, a-b))`;
* the edge counts `u = binom(p,2)`, `m = b`, `s = p(q-1) + a`.
-/
module

public import PaperVIResearch.ExceptionalConstruction

@[expose] public section

namespace PaperVI

namespace Research

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `s = Σ_{a ∈ P} |N(a) ∩ O|`: crossing edges counted from the core side. -/
theorem sCount_eq_sum (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) :
    sCount G P = ∑ a ∈ P, (Pᶜ.filter (G.Adj a)).card := by
  have himg : crossEdges G P =
      ((P ×ˢ Pᶜ).filter (fun ax => G.Adj ax.1 ax.2)).image (fun ax => s(ax.1, ax.2)) := by
    ext e
    induction e using Sym2.ind with
    | h u w =>
      simp only [crossEdges, mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        Sym2.mem_toFinset, Sym2.mem_iff, mem_image, mem_product, mem_compl, Prod.exists]
      constructor
      · rintro ⟨hadj, ⟨v, hv, hvP⟩, ⟨v', hv', hv'P⟩⟩
        rcases hv with rfl | rfl <;> rcases hv' with rfl | rfl
        · exact absurd hvP hv'P
        · exact ⟨_, _, ⟨⟨hvP, hv'P⟩, hadj⟩, rfl⟩
        · exact ⟨_, _, ⟨⟨hvP, hv'P⟩, hadj.symm⟩, Sym2.eq_swap⟩
        · exact absurd hvP hv'P
      · rintro ⟨a, x, ⟨⟨ha, hx⟩, hadj⟩, hax⟩
        rw [Sym2.eq_iff] at hax
        rcases hax with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨hadj, ⟨_, Or.inl rfl, ha⟩, ⟨_, Or.inr rfl, hx⟩⟩
        · exact ⟨hadj.symm, ⟨_, Or.inr rfl, ha⟩, ⟨_, Or.inl rfl, hx⟩⟩
  rw [sCount, himg, card_image_of_injOn, card_filter, sum_product]
  · exact sum_congr rfl fun a _ => (card_filter _ _).symm
  · rintro ⟨a, x⟩ hax ⟨a', x'⟩ hax' h
    simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_compl] at hax hax'
    simp only at h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd hax.1.1 hax'.1.2

section TheoremE

variable {G : SimpleGraph V} [DecidableRel G.Adj] {P R A B : Finset V} {z : V}
  (hS : ExSetup G P R A B z)
include hS

/-- `u = binom(p,2)`. -/
theorem ExSetup.uCount_eq : uCount G P = P.card.choose 2 := by
  have : coreEdges G P = innerEdges G P := rfl
  rw [uCount, this, card_innerEdges_of_isClique G P (fun u hu v hv huv => hS.adjPP u hu v hv huv)]

/-- `m = b`. -/
theorem ExSetup.mCount_eq : mCount G P = B.card := by
  rw [mCount, hS.extEdges_eq, card_image_of_injective _ (fun v w h => Sym2.congr_right.mp h)]

/-- `s = p (q - 1) + a`, where `q - 1 = |R|`. -/
theorem ExSetup.sCount_eq : sCount G P = P.card * R.card + A.card := by
  have hPc : Pᶜ = insert z R := by
    ext v
    simp only [mem_compl, mem_insert]
    constructor
    · intro hv
      rcases hS.cover v with h | h | h
      · exact absurd h hv
      · exact Or.inr h
      · exact Or.inl h
    · rintro (rfl | h)
      · exact hS.zP
      · exact fun hP => hS.notR_of_P hP h
  have hrow : ∀ a ∈ P, (Pᶜ.filter (G.Adj a)).card = R.card + if a ∈ A then 1 else 0 := by
    intro a ha
    rw [hPc, filter_insert]
    have hRf : R.filter (G.Adj a) = R := filter_true_of_mem (fun x hx => hS.adjPR a ha x hx)
    have hza : G.Adj a z ↔ a ∈ A := by
      rw [SimpleGraph.adj_comm, hS.adjz]
      constructor
      · rintro (h | h)
        · exact h
        · exact absurd (hS.BsubR h) (hS.notR_of_P ha)
      · exact Or.inl
    by_cases haA : a ∈ A
    · rw [if_pos (hza.mpr haA), if_pos haA, hRf, card_insert_of_notMem hS.zR]
    · rw [if_neg (fun h => haA (hza.mp h)), if_neg haA, hRf, add_zero]
  rw [sCount_eq_sum, sum_congr rfl hrow, sum_add_distrib, sum_const, smul_eq_mul, sum_boole,
    filter_mem_eq_inter, inter_eq_right.mpr hS.AsubP]
  simp

/-- The three signed duals give the lower bound `cp(G) ≥ Φ + D(a,b)`. -/
theorem ExSetup.cp_ge :
    (sCount G P : ℤ) - uCount G P - 2 * mCount G P + Dval A.card B.card ≤ cp G := by
  have key : ∀ cP cR : ℤ, ((cP = 0 ∧ cR = 0) ∨ (cP = -1 ∧ cR = 2) ∨ (cP = -2 ∧ cR = 3)) →
      (sCount G P : ℤ) - uCount G P - 2 * mCount G P + cP * A.card + cR * B.card ≤ cp G := by
    intro cP cR hc
    rw [← hS.sum_exW cP cR]
    exact dual_bound_cp G _ (fun Q hQ => hS.setWeight_le_one hQ
      (fun k j zq hj hz _ => dual_arith k j zq hj hz cP cR hc))
  have h1 := key 0 0 (Or.inl ⟨rfl, rfl⟩)
  have h2 := key (-1) 2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have h3 := key (-2) 3 (Or.inr (Or.inr ⟨rfl, rfl⟩))
  unfold Dval
  have : max 0 (max (2 * (B.card : ℤ) - A.card) (3 * (B.card : ℤ) - 2 * A.card)) ≤
      cp G - ((sCount G P : ℤ) - uCount G P - 2 * mCount G P) :=
    max_le (by linarith) (max_le (by linarith) (by linarith))
  linarith

/-- The same lower bound for every fractional clique partition (equality covering, staging
model over `ℝ`). -/
theorem ExSetup.frac_ge {x : Finset V → ℝ} (hx : IsFracPartition G x) :
    (((sCount G P : ℤ) - uCount G P - 2 * mCount G P + Dval A.card B.card : ℤ) : ℝ) ≤
      fracValue x := by
  have key : ∀ cP cR : ℤ, ((cP = 0 ∧ cR = 0) ∨ (cP = -1 ∧ cR = 2) ∨ (cP = -2 ∧ cR = 3)) →
      (((sCount G P : ℤ) - uCount G P - 2 * mCount G P + cP * A.card + cR * B.card : ℤ) : ℝ)
        ≤ fracValue x := by
    intro cP cR hc
    rw [← hS.sum_exW cP cR]
    exact frac_dual_bound G hx _ (fun Q hQ => hS.setWeight_le_one (hx.support Q hQ).2
      (fun k j zq hj hz _ => dual_arith k j zq hj hz cP cR hc))
  have h1 := key 0 0 (Or.inl ⟨rfl, rfl⟩)
  have h2 := key (-1) 2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have h3 := key (-2) 3 (Or.inr (Or.inr ⟨rfl, rfl⟩))
  push_cast at h1 h2 h3 ⊢
  unfold Dval
  push_cast
  have : max 0 (max (2 * (B.card : ℝ) - A.card) (3 * (B.card : ℝ) - 2 * A.card)) ≤
      fracValue x - ((sCount G P : ℝ) - uCount G P - 2 * mCount G P) :=
    max_le (by linarith) (max_le (by linarith) (by linarith))
  linarith

/-- The lower bound for `cp_{≤3}`: `cp_{≤3}(G) ≥ Φ + 3b - 2 min(a,b)`. -/
theorem ExSetup.cpLe_three_ge :
    (sCount G P : ℤ) - uCount G P - 2 * mCount G P + Dthree A.card B.card ≤ cpLe 3 G := by
  have h3 : (sCount G P : ℤ) - uCount G P - 2 * mCount G P + (-2) * A.card + 3 * B.card ≤
      cpLe 3 G := by
    rw [← hS.sum_exW (-2) 3]
    exact dual_bound_cpLe G (by norm_num) _ (fun Q hQ _ => hS.setWeight_le_one hQ
      (fun k j zq hj hz _ => dual_arith k j zq hj hz (-2) 3 (Or.inr (Or.inr ⟨rfl, rfl⟩))))
  have h01 : (sCount G P : ℤ) - uCount G P - 2 * mCount G P + 0 * A.card + 1 * B.card ≤
      cpLe 3 G := by
    rw [← hS.sum_exW 0 1]
    exact dual_bound_cpLe G (by norm_num) _ (fun Q hQ hQ3 => hS.setWeight_le_one hQ
      (fun k j zq hj hz hc => dual_arith_le_three k j zq hj hz (by omega)))
  unfold Dthree
  rcases le_total (A.card : ℤ) B.card with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

omit [Fintype V] [DecidableRel G.Adj] hS in
/-- Blocks produced by the construction have order `coreSize + extSize`. -/
theorem card_le_of_starClass {T : V → Finset V} {c : ℕ}
    (hTA : ∀ x ∈ B, T x ⊆ A ∧ (T x).card ≤ c) {Q : Finset V}
    (hQ : (∃ x ∈ B, Q = insert z (insert x (T x))) ∨
      (extSize P Q = 1 ∧ (coreSize P Q = 1 ∨ coreSize P Q = 2))) :
    Q.card ≤ max 3 (c + 2) := by
  rcases hQ with ⟨x, hx, rfl⟩ | ⟨h1, h2⟩
  · have := card_insert_le z (insert x (T x))
    have := card_insert_le x (T x)
    have := (hTA x hx).2
    omega
  · rw [card_eq_coreSize_add_extSize P Q]; omega

/-- **Theorem E1 (one exceptional vertex).** If `q ≥ p + 3` then
`cp(G) = cp_{≤4}(G) = s - u - 2m + D(a,b)`, attained by an explicit physical partition: every
star block `{z, x} ∪ T x` (`T x ⊆ A` pairwise disjoint, `|T x| ≤ 2`) is a block, and every
other block is a crossing edge or a triangle of type `(2,1)`. -/
theorem ExSetup.theoremE1 (hq : P.card + 2 ≤ R.card) :
    (cp G : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P + Dval A.card B.card ∧
    cp G = cpLe 4 G ∧
    ∃ T : V → Finset V, (∀ x ∈ B, T x ⊆ A ∧ (T x).card ≤ 2) ∧
      (∀ x ∈ B, ∀ y ∈ B, x ≠ y → Disjoint (T x) (T y)) ∧
      ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ Bs.card = cp G ∧
        (∀ Q ∈ Bs, Q.card ≤ 4) ∧
        (∀ x ∈ B, insert z (insert x (T x)) ∈ Bs) ∧
        (∀ Q ∈ Bs, (∃ x ∈ B, Q = insert z (insert x (T x))) ∨
          (extSize P Q = 1 ∧ (coreSize P Q = 1 ∨ coreSize P Q = 2))) := by
  obtain ⟨T, hT1, hTd, hTs⟩ := exists_star_assign_gen 2 Dval
    (fun a => le_max_left _ _) Dval_step B A
  obtain ⟨Bs, hBs, hstar, hclass, hcard⟩ :=
    hS.exists_partition_star (fun x hx => (hT1 x hx).1) hTd hq
  have hle4 : ∀ Q ∈ Bs, Q.card ≤ 4 := fun Q hQ => by
    have := card_le_of_starClass (P := P) hT1 (hclass Q hQ); omega
  have hlow := hS.cp_ge
  have h1 := cp_le hBs
  have h2 := cpLe_le hBs hle4
  have h3 := cp_le_cpLe G (r := 4) (by norm_num)
  have hBc : (Bs.card : ℤ) = cp G := by
    have : (Bs.card : ℤ) ≤ (cp G : ℤ) := by rw [hcard]; linarith
    have h1' : (cp G : ℤ) ≤ Bs.card := by exact_mod_cast h1
    linarith
  refine ⟨by rw [← hBc, hcard]; linarith [hTs], by omega, T, hT1, hTd, Bs, hBs,
    by exact_mod_cast hBc, hle4, hstar, hclass⟩

/-- **Theorem E1, explicit numbers.** `cp(G) = p(q-1) + a - binom(p,2) - 2b + D(a,b)`. -/
theorem ExSetup.cp_eq_explicit (hq : P.card + 2 ≤ R.card) :
    (cp G : ℤ) = (P.card : ℤ) * R.card + A.card - (P.card.choose 2 : ℤ) - 2 * B.card +
      Dval A.card B.card := by
  rw [(hS.theoremE1 hq).1, hS.sCount_eq, hS.uCount_eq, hS.mCount_eq]
  push_cast; ring

/-- **Theorem E1, fractional part.** The minimum cost of a fractional clique partition with
equality covering (canonical model over `ℝ`) equals `cp(G) = Φ + D(a,b)`: every fractional
partition costs at least this, and the indicator of the physical optimum attains it. -/
theorem ExSetup.theoremE1_frac (hq : P.card + 2 ≤ R.card) :
    (∀ x : Finset V → ℝ, IsFracPartition G x → (cp G : ℝ) ≤ fracValue x) ∧
    ∃ x : Finset V → ℝ, IsFracPartition G x ∧ fracValue x = cp G := by
  obtain ⟨hcp, -, -, -, -, Bs, hBs, hcard, -⟩ := hS.theoremE1 hq
  refine ⟨fun x hx => ?_, ?_⟩
  · have := hS.frac_ge hx
    rw [← hcp] at this
    exact_mod_cast this
  · obtain ⟨hfrac, hval⟩ := isFracPartition_indicator G hBs
    exact ⟨_, hfrac, by rw [hval, hcard]⟩

/-- **Restricted number.** `cp_{≤3}(G) = Φ + 3b - 2 min(a,b) = s - u + b - 2 min(a,b)`, with a
physical optimal partition into star blocks of order at most three, crossing edges and
triangles of type `(2,1)`. -/
theorem ExSetup.cpLe_three_eq (hq : P.card + 2 ≤ R.card) :
    (cpLe 3 G : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P + Dthree A.card B.card ∧
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ Bs.card = cpLe 3 G ∧
      ∀ Q ∈ Bs, Q.card ≤ 3 := by
  obtain ⟨T, hT1, hTd, hTs⟩ := exists_star_assign_gen 1 Dthree
    (fun a => by unfold Dthree; push_cast; omega) Dthree_step B A
  obtain ⟨Bs, hBs, -, hclass, hcard⟩ :=
    hS.exists_partition_star (fun x hx => (hT1 x hx).1) hTd hq
  have hle3 : ∀ Q ∈ Bs, Q.card ≤ 3 := fun Q hQ => by
    have := card_le_of_starClass (P := P) hT1 (hclass Q hQ); omega
  have hlow := hS.cpLe_three_ge
  have h2 := cpLe_le hBs hle3
  have hBc : (Bs.card : ℤ) = cpLe 3 G := by
    have : (Bs.card : ℤ) ≤ (cpLe 3 G : ℤ) := by rw [hcard]; linarith
    have h2' : (cpLe 3 G : ℤ) ≤ Bs.card := by exact_mod_cast h2
    linarith
  exact ⟨by rw [← hBc, hcard]; linarith, Bs, hBs, by exact_mod_cast hBc, hle3⟩

/-- **Theorem E3 (restriction gap).** `cp_{≤3}(G) - cp(G) = min(b, max(0, a - b))`. -/
theorem ExSetup.theoremE3 (hq : P.card + 2 ≤ R.card) :
    (cpLe 3 G : ℤ) - cp G = min (B.card : ℤ) (max 0 ((A.card : ℤ) - B.card)) := by
  rw [(hS.cpLe_three_eq hq).1, (hS.theoremE1 hq).1]
  unfold Dthree Dval
  omega

end TheoremE

end Research

end PaperVI
