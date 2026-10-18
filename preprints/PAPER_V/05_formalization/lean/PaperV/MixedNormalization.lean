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

public import PaperV.MixedPromotion
import Mathlib.Tactic.Push
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

@[expose] public section
namespace PaperV.MixedPromotion
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def triangleSupport (y : Finset V → ℝ) : Finset (Finset V) :=
  univ.filter (fun T => T.card = 3 ∧ 0 < y T)

def Normalized (G : SimpleGraph V) (y : Finset V → ℝ) : Prop :=
  ∀ Q : Finset V, Q.card = 4 → G.IsClique (Q : Set V) →
    ∃ T ∈ Q.powersetCard 3, y T = 0

/-- Each step is the physical clique update from `MixedPromotion`, with
strictly positive mass no larger than any of the four face coordinates. -/
inductive PromotionChain (G : SimpleGraph V) :
    ℕ → (Finset V → ℝ) → (Finset V → ℝ) → Prop
  | refl (y) : PromotionChain G 0 y y
  | cons {y z k} (Q : Finset V) (hQ : Q.card = 4)
      (hcl : G.IsClique (Q : Set V)) (α : ℝ) (hα : 0 < α)
      (hface : ∀ T ∈ Q.powersetCard 3, α ≤ y T)
      (tail : PromotionChain G k (promote y Q α) z) :
      PromotionChain G (k + 1) y z

theorem support_decreases {y : Finset V → ℝ} (Q : Finset V)
    (hQ : Q.card = 4) (α : ℝ) (hα : 0 < α)
    (T : Finset V) (hT : T ∈ Q.powersetCard 3) (heq : y T = α) :
    (triangleSupport (promote y Q α)).card < (triangleSupport y).card := by
  classical
  have hsub : triangleSupport (promote y Q α) ⊆ triangleSupport y := by
    intro U hU
    obtain ⟨_, hc, hp⟩ := Finset.mem_filter.mp hU
    have hne : U ≠ Q := by intro e; subst U; omega
    have hle : promote y Q α U ≤ y U := by
      unfold promote
      simp only [hne, ite_false, add_zero]
      by_cases hf : U ∈ Q.powersetCard 3
      · simp only [hf, ite_true]; linarith
      · simp [hf]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, lt_of_lt_of_le hp hle⟩
  have hold : T ∈ triangleSupport y := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_powersetCard.mp hT).2, by simpa [heq] using hα⟩
  have hn : T ≠ Q := by
    intro e; subst T
    have := (Finset.mem_powersetCard.mp hT).2
    omega
  have hz : promote y Q α T = 0 := by simp [promote, hn, hT, heq]
  have hnot : T ∉ triangleSupport (promote y Q α) := by simp [triangleSupport, hz]
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hsub, ?_⟩
  intro e
  exact hnot (by rw [e]; exact hold)

/-- Finite normalization, including an actual sequence of at most as many
updates as there were initially positive triangle coordinates. -/
theorem exists_normalized (G : SimpleGraph V) {y : Finset V → ℝ}
    (hy : Feasible G y) (π : V → V → ℝ) :
    ∃ k z, k ≤ (triangleSupport y).card ∧ PromotionChain G k y z ∧
      Feasible G z ∧ (∀ a b, a ≠ b → load z a b = load y a b) ∧
      pricedValue π y ≤ pricedValue π z ∧ Normalized G z := by
  classical
  suffices h : ∀ n (u : Finset V → ℝ), (triangleSupport u).card = n → Feasible G u →
      ∃ k z, k ≤ n ∧ PromotionChain G k u z ∧
        Feasible G z ∧ (∀ a b, a ≠ b → load z a b = load u a b) ∧
        pricedValue π u ≤ pricedValue π z ∧ Normalized G z by
    exact h _ y rfl hy
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u hn hu
    by_cases hnorm : Normalized G u
    · exact ⟨0, u, Nat.zero_le _, PromotionChain.refl u, hu,
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
      have hlt : (triangleSupport v).card < n := by
        rw [← hn]
        exact support_decreases Q hQ (u T) hpos T hT rfl
      obtain ⟨k, z, hk, hchain, hz, hloads, hvalue, hnormalized⟩ :=
        ih _ hlt v rfl hv
      refine ⟨k + 1, z, by omega,
        PromotionChain.cons Q hQ hcl (u T) hpos hmin hchain, hz, ?_, ?_, hnormalized⟩
      · intro a b hab
        exact (hloads a b hab).trans (load_promote u Q hQ (u T) a b hab)
      · have hid : pricedValue π v = pricedValue π u + 2 * u T :=
          pricedValue_promote π u Q hQ (u T)
        linarith

end PaperV.MixedPromotion
