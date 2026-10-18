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

public import PaperV.BK
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.NormCast

@[expose] public section
namespace PaperV.BK
open Finset

/-- The exact resource-LP upper certificate also bounds the stronger master LP.
Its prices are 1 on pairs01,05 and 1/2 on the other fifteen listed resources. -/
theorem resource_upper_bound {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (x : Fin 27 → K) (hx : ∀ i, 0 ≤ x i)
    (hp : ∀ e : Finset (Fin 6), (∑ i ∈ univ.filter (fun i => opair i = e), x i) ≤ 1)
    (hd : ∀ (j : Fin 8) (a : Fin 6),
      (∑ i ∈ univ.filter (fun i => ohost i = j ∧ a ∈ opair i), x i) ≤ 1) :
    (∑ i, x i) ≤ 19 / 2 := by
  have p0 := hp {0,1}
  have p1 := hp {0,2}
  have p2 := hp {0,3}
  have p3 := hp {0,4}
  have p4 := hp {0,5}
  have p5 := hp {3,5}
  have p6 := hp {4,5}
  have p7 := hd 1 3
  have p8 := hd 3 2
  have p9 := hd 3 3
  have p10 := hd 3 4
  have p11 := hd 4 1
  have p12 := hd 4 2
  have p13 := hd 4 4
  have p14 := hd 5 3
  have p15 := hd 5 4
  have p16 := hd 7 4
  have h11 := hx 11
  simp only [Finset.sum_filter, Fin.sum_univ_succ] at p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 ⊢
  simp +decide [opair, ohost, objs] at p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 ⊢
  linarith only [p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,h11]

/-- Attainment of the real resource and master objectives by the rational witness.
The odd-set constraints are already checked in `bk_witness_oddset`. -/
theorem real_resource_attainment :
    (∀ i, 0 ≤ (witness i : ℝ)) ∧
    (∀ e : Finset (Fin 6),
      (∑ i ∈ univ.filter (fun i => opair i = e), (witness i : ℝ)) ≤ 1) ∧
    (∀ (j : Fin 8) (a : Fin 6),
      (∑ i ∈ univ.filter (fun i => ohost i = j ∧ a ∈ opair i), (witness i : ℝ)) ≤ 1) ∧
    (∀ (j : Fin 8) (S : Finset (Fin 6)), S.card = 3 →
      (∑ i ∈ univ.filter (fun i => ohost i = j ∧ opair i ⊆ S), (witness i : ℝ)) ≤ 1) ∧
    (∑ i, (witness i : ℝ)) = 19 / 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact_mod_cast bk_witness_nonneg i
  · intro e; exact_mod_cast bk_witness_pair_cap e
  · intro j a; exact_mod_cast bk_witness_degree j a
  · intro j S hS; exact_mod_cast bk_witness_oddset j S hS
  · rw [← Rat.cast_sum]
    change ((lpValue witness : ℚ) : ℝ) = 19 / 2
    rw [bk_witness_value]
    norm_num

/-- A maximum BK packing leaving two disjoint coverable pairs uncovered.
Together with `bk_beta_lt_k` this certifies the exact residual value two. -/
theorem residual_two_attained :
    ∃ R : Finset (Fin 27), Feasible R ∧ R.card = nu ∧
      ({3,4} : Finset (Fin 6)) ∈ cov ∧ ({1,2} : Finset (Fin 6)) ∈ cov ∧
      ({3,4} : Finset (Fin 6)) ∉ R.image opair ∧
      ({1,2} : Finset (Fin 6)) ∉ R.image opair ∧
      Disjoint ({3,4} : Finset (Fin 6)) {1,2} := by
  refine ⟨{4,6,9,12,15,18,21,23,26}, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp +decide [Feasible, opair, ohost, objs]
  · rw [bk_nu]; decide
  all_goals decide

end PaperV.BK
