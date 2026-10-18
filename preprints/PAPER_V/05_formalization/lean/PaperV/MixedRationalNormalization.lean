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

public import PaperV.MixedNormalization
public import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Push
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

@[expose] public section
namespace PaperV.MixedPromotion
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All physical clique masses are rational, embedded in the real resource LP. -/
def RationalMass (y : Finset V → ℝ) : Prop :=
  ∀ T, ∃ q : ℚ, y T = q

theorem promote_rational {y : Finset V → ℝ} (hy : RationalMass y)
    (Q : Finset V) {α : ℝ} (hα : ∃ a : ℚ, α = a) :
    RationalMass (promote y Q α) := by
  classical
  obtain ⟨a, rfl⟩ := hα
  intro T
  obtain ⟨q, hq⟩ := hy T
  refine ⟨q + (if T = Q then 2 * a else 0) -
    (if T ∈ Q.powersetCard 3 then a else 0), ?_⟩
  simp only [promote, hq]
  split_ifs <;> push_cast <;> rfl

/-- The finite normalization can be chosen rational whenever the input is rational.
The step size is always an existing face coordinate, rather than an arbitrary real. -/
theorem exists_normalized_rational (G : SimpleGraph V) {y : Finset V → ℝ}
    (hy : Feasible G y) (hq : RationalMass y) (π : V → V → ℝ) :
    ∃ k z, k ≤ (triangleSupport y).card ∧ PromotionChain G k y z ∧
      Feasible G z ∧ RationalMass z ∧
      (∀ a b, a ≠ b → load z a b = load y a b) ∧
      pricedValue π y ≤ pricedValue π z ∧ Normalized G z := by
  classical
  suffices h : ∀ n (u : Finset V → ℝ), (triangleSupport u).card = n → Feasible G u →
      RationalMass u → ∃ k z, k ≤ n ∧ PromotionChain G k u z ∧
        Feasible G z ∧ RationalMass z ∧
        (∀ a b, a ≠ b → load z a b = load u a b) ∧
        pricedValue π u ≤ pricedValue π z ∧ Normalized G z by
    exact h _ y rfl hy hq
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u hn hu hqu
    by_cases hnorm : Normalized G u
    · exact ⟨0, u, Nat.zero_le _, PromotionChain.refl u, hu, hqu,
        fun _ _ _ => rfl, le_rfl, hnorm⟩
    · unfold Normalized at hnorm
      push Not at hnorm
      obtain ⟨Q, hQ, hcl, hbad⟩ := hnorm
      have hne : (Q.powersetCard 3).Nonempty := by
        rw [Finset.powersetCard_nonempty, hQ]; norm_num
      obtain ⟨T, hT, hmin⟩ := Finset.exists_min_image (Q.powersetCard 3) u hne
      have hpos : 0 < u T := lt_of_le_of_ne (hu.1 T) (Ne.symm (hbad T hT))
      let v := promote u Q (u T)
      have hv : Feasible G v := feasible_promote G hu Q hQ hcl (u T) hpos.le hmin
      have hqv : RationalMass v := promote_rational hqu Q (hqu T)
      have hlt : (triangleSupport v).card < n := by
        rw [← hn]
        exact support_decreases Q hQ (u T) hpos T hT rfl
      obtain ⟨k, z, hk, hchain, hz, hqz, hloads, hvalue, hnormalized⟩ :=
        ih _ hlt v rfl hv hqv
      refine ⟨k + 1, z, by omega,
        PromotionChain.cons Q hQ hcl (u T) hpos hmin hchain,
        hz, hqz, ?_, ?_, hnormalized⟩
      · intro a b hab
        exact (hloads a b hab).trans (load_promote u Q hQ (u T) a b hab)
      · have hid : pricedValue π v = pricedValue π u + 2 * u T :=
          pricedValue_promote π u Q hQ (u T)
        linarith

end PaperV.MixedPromotion
