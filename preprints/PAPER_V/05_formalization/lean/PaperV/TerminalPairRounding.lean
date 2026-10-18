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

module

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

public import Mathlib.Algebra.Group.Action.Defs

@[expose] public section
/-!
# Sparse Terminal-Pair Rounding — deterministic interface layers (P4-133, abstract)

Conditional interfaces: they take the finite discrepancy/colouring certificates as DATA.
Not the existence statement of P4-133 (that needs Beck–Fiala + Vizing). Params per V3486:
`m = a + b` (hosts / density denominator), objects indexed by `ι`.
-/

open Finset

namespace PaperV.TerminalPair

variable {ι B : Type*} [DecidableEq B] [Fintype ι] [DecidableEq ι]

/-- Objects in `S` whose role-`r` endpoint is `w`. -/
def roleRow (vrole : Fin 4 → ι → B) (S : Finset ι) (r : Fin 4) (w : B) : Finset ι :=
  S.filter (fun P => vrole r P = w)

/-- Incidence degree of the terminal graph `F_S` at `w`: sum over the four roles. -/
def incDeg (vrole : Fin 4 → ι → B) (S : Finset ι) (w : B) : ℕ :=
  ∑ r : Fin 4, (roleRow vrole S r w).card

/-- **Layer 2 (deterministic degree bound).** Given a discrepancy-4 certificate in
multiplicative ℕ-form and the base-degree bound `Δ(F) ≤ m`, the selected terminal graph
has incidence degree `≤ a + 16` at every vertex. Certificates are hypotheses (data). -/
theorem incDeg_le_of_discrepancy
    (vrole : Fin 4 → ι → B) (S Pall : Finset ι) (a m : ℕ) (hm : 0 < m) (w : B)
    (hbase : (∑ r : Fin 4, (roleRow vrole Pall r w).card) ≤ m)
    (hcert : ∀ r : Fin 4,
      m * (roleRow vrole S r w).card ≤ a * (roleRow vrole Pall r w).card + 4 * m) :
    incDeg vrole S w ≤ a + 16 := by
  have hmul : m * incDeg vrole S w ≤ m * (a + 16) := by
    have hsum : m * incDeg vrole S w
        = ∑ r : Fin 4, m * (roleRow vrole S r w).card := by
      rw [incDeg, Finset.mul_sum]
    rw [hsum]
    calc ∑ r : Fin 4, m * (roleRow vrole S r w).card
        ≤ ∑ r : Fin 4, (a * (roleRow vrole Pall r w).card + 4 * m) :=
          Finset.sum_le_sum (fun r _ => hcert r)
      _ = a * (∑ r : Fin 4, (roleRow vrole Pall r w).card) + 4 * m * 4 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]; ring_nf
          simp [Finset.sum_const, Finset.card_univ]; ring
      _ ≤ a * m + 16 * m := by
          have := Nat.mul_le_mul_left a hbase; omega
      _ = m * (a + 16) := by ring
  exact Nat.le_of_mul_le_mul_left hmul hm



/-- **Layer 3 (deterministic extraction).** Given a proper edge colouring of `F_S` with
`cnum` colours *as data* (`col P i` = colour of object `P`'s `i`-th terminal edge), a set
`D` of removed colour classes with `|D| ≤ 17`, and the vertex-cover certificate that each
removed class meets at most `xc = |X|` objects of `S`, the surviving subfamily `S'` avoids
`D`, uses a palette of size `cnum − |D| = a`, and loses at most `17·xc` objects. No Vizing:
the colouring is a hypothesis. -/
theorem extract_a_edge_colorable
    (S : Finset ι) (cnum a xc : ℕ)
    (col : ι → Fin 2 → Fin cnum)
    (D : Finset (Fin cnum))
    (ha : a ≤ cnum) (hDcard : D.card = cnum - a)
    (hclass : ∀ k ∈ D,
      (S.filter (fun P => col P 0 = k ∨ col P 1 = k)).card ≤ xc) :
    ∃ S' : Finset ι, S' ⊆ S ∧
      (∀ P ∈ S', ∀ i, col P i ∈ (Finset.univ \ D)) ∧
      (Finset.univ \ D).card = a ∧
      S.card ≤ S'.card + D.card * xc := by
  classical
  set q : ι → Prop := fun P => col P 0 ∈ D ∨ col P 1 ∈ D with hq
  refine ⟨S.filter (fun P => ¬ q P), Finset.filter_subset _ _, ?_, ?_, ?_⟩
  · -- S' avoids D on both edges
    intro P hP i
    simp only [Finset.mem_filter, hq, not_or] at hP
    have := hP.2
    fin_cases i
    · simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]; exact this.1
    · simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]; exact this.2
  · -- palette size = a
    have hpal : (Finset.univ \ D).card = Fintype.card (Fin cnum) - D.card := by
      rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl]
    rw [hpal, Fintype.card_fin, hDcard]
    omega
  · -- cardinality loss ≤ 17·xc
    have hsplit : (S.filter q).card + (S.filter (fun P => ¬ q P)).card = S.card :=
      Finset.card_filter_add_card_filter_not (s := S) q
    have hsub : S.filter q ⊆
        D.biUnion (fun k => S.filter (fun P => col P 0 = k ∨ col P 1 = k)) := by
      intro P hP
      simp only [Finset.mem_filter, hq] at hP
      obtain ⟨hPS, hcol⟩ := hP
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      rcases hcol with h | h
      · exact ⟨col P 0, h, hPS, Or.inl rfl⟩
      · exact ⟨col P 1, h, hPS, Or.inr rfl⟩
    have hcard_q : (S.filter q).card ≤ D.card * xc := by
      calc (S.filter q).card
          ≤ (D.biUnion (fun k => S.filter (fun P => col P 0 = k ∨ col P 1 = k))).card :=
            Finset.card_le_card hsub
        _ ≤ ∑ k ∈ D, (S.filter (fun P => col P 0 = k ∨ col P 1 = k)).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _k ∈ D, xc := Finset.sum_le_sum hclass
        _ = D.card * xc := by rw [Finset.sum_const, smul_eq_mul]
    omega

end PaperV.TerminalPair
