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

public import PaperV.FractionalUnitBoundary
import Lean.Elab.Tactic.NormCast

public import Mathlib.Data.Rat.Cast.Order

@[expose] public section

/-!
# Paper V: actual rational and real fractional optima of the unit-boundary resource LP

* rational: the central LP has a primal/dual pair of equal value (attached rational strong
  duality); lifting both gives an optimal full primal/dual pair, so actual optimizers exist and
  `Wstar = B0 + Wredstar`;
* real: the rational primal/dual pairs are embedded into the real LPs by explicit maps
  (`primalCast`, `dualCast`); weak duality in `ℝ` then certifies real optimality, real optimizers
  exist and the real optima are the casts of the rational ones.
-/

open Finset Classical

namespace PaperV
namespace FractionalUnitBoundary

open UnitBoundary UnitBoundary.Weighted ResourceCertificate System

/-! ### Explicit rational-to-real embedding of finite LP certificates -/

section Cast

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Embedding of a rational feasible primal into the real LP with the cast matrix. -/
def primalCast {A : ι → κ → ℚ} (p : FiniteLP.PrimalFeasible A) :
    FiniteLP.PrimalFeasible (fun i e => (A i e : ℝ)) where
  weight i := (p.weight i : ℝ)
  weight_nonneg i := by exact_mod_cast p.weight_nonneg i
  capacity e := by
    have h := p.capacity e
    exact_mod_cast h

/-- Embedding of a rational feasible dual into the real LP with cast matrix and gains. -/
def dualCast {A : ι → κ → ℚ} {g : ι → ℚ} (d : FiniteLP.DualFeasible A g) :
    FiniteLP.DualFeasible (fun i e => (A i e : ℝ)) (fun i => (g i : ℝ)) where
  price e := (d.price e : ℝ)
  price_nonneg e := by exact_mod_cast d.price_nonneg e
  demand i := by
    have h := d.demand i
    exact_mod_cast h

omit [Fintype κ] in
theorem primalCast_value {A : ι → κ → ℚ} (g : ι → ℚ) (p : FiniteLP.PrimalFeasible A) :
    FiniteLP.primalValue (fun i => (g i : ℝ)) (primalCast p) =
      ((FiniteLP.primalValue g p : ℚ) : ℝ) := by
  simp [FiniteLP.primalValue, primalCast]

omit [Fintype ι] in
theorem dualCast_value {A : ι → κ → ℚ} {g : ι → ℚ} (d : FiniteLP.DualFeasible A g) :
    FiniteLP.dualValue (dualCast d) = ((FiniteLP.dualValue d : ℚ) : ℝ) := by
  simp [FiniteLP.dualValue, dualCast]

/-- A rational primal/dual pair of equal value embeds into an optimal real primal. -/
theorem primalCast_optimal {A : ι → κ → ℚ} {g : ι → ℚ} (p : FiniteLP.PrimalFeasible A)
    (d : FiniteLP.DualFeasible A g) (h : FiniteLP.primalValue g p = FiniteLP.dualValue d)
    (p' : FiniteLP.PrimalFeasible (fun i e => (A i e : ℝ))) :
    FiniteLP.primalValue (fun i => (g i : ℝ)) p' ≤
      FiniteLP.primalValue (fun i => (g i : ℝ)) (primalCast p) := by
  rw [primalCast_value, h, ← dualCast_value]
  exact FiniteLP.weak_duality p' (dualCast d)

end Cast

variable {I E : Type*} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]

/-! ### Casting the opportunity data -/

section CastData

variable {rho : I → Finset E} {Q D : Finset I} {S : Finset E} {w : I → ℚ}

theorem piW_cast (hw : ∀ o, 0 ≤ w o) (e : E) :
    piW rho Q S (fun o => (w o : ℝ)) e = ((piW rho Q S w e : ℚ) : ℝ) := by
  apply le_antisymm
  · apply piW_le (by exact_mod_cast piW_nonneg e)
    intro o ho
    exact_mod_cast le_piW ho
  · by_cases h : (Rep rho Q S e).Nonempty
    · obtain ⟨o, ho, heq⟩ := exists_eq_piW hw h
      rw [← heq]
      exact le_piW (w := fun o => (w o : ℝ)) ho
    · rw [piW_eq_zero (Finset.not_nonempty_iff_eq_empty.mp h), Rat.cast_zero]
      exact piW_nonneg e

theorem B0_cast (hw : ∀ o, 0 ≤ w o) :
    B0 rho Q S (fun o => (w o : ℝ)) = ((B0 rho Q S w : ℚ) : ℝ) := by
  unfold B0
  push_cast
  simp only [piW_cast hw]

theorem wred_cast (hw : ∀ o, 0 ≤ w o) (d : I) :
    wred rho Q S (fun o => (w o : ℝ)) d = ((wred rho Q S w d : ℚ) : ℝ) := by
  unfold wred
  push_cast
  simp only [piW_cast hw]

theorem centralGain_cast (hw : ∀ o, 0 ≤ w o) :
    centralGain rho Q D S (fun o => (w o : ℝ)) =
      fun d => ((centralGain rho Q D S w d : ℚ) : ℝ) := by
  funext d
  exact wred_cast hw d.1

end CastData

/-! ### Rational optima -/

section RationalOptimum

variable {R : System I E} {Q D : Finset I} {S : Finset E} {w : I → ℚ}

omit [DecidableEq I] in
theorem isIncidence_rat (R : System I E) : IsIncidence R R.incidence := fun _ _ => rfl

omit [DecidableEq I] in
theorem isIncidence_real (R : System I E) : IsIncidence R (realIncidence R) := by
  intro o e
  simp only [realIncidence, System.incidence]
  split_ifs <;> simp

theorem central_nonneg (R : System I E) (d : {d // d ∈ D}) (e : {e // e ∈ S}) :
    0 ≤ centralInc D S R.incidence d e :=
  inc_nonneg (isIncidence_rat R) _ _

theorem central_cover (cfg : Config R.resources Q D S) (d : {d // d ∈ D}) :
    ∃ e, 1 ≤ centralInc D S R.incidence d e := by
  obtain ⟨r, hr⟩ := R.nonempty d.1
  exact ⟨⟨r, cfg.hD d.1 d.2 hr⟩, le_of_eq (inc_eq_one (isIncidence_rat R) hr).symm⟩

/-- Rational strong duality for the central LP with signed reduced gains. -/
theorem central_strong_duality (cfg : Config R.resources Q D S) (w : I → ℚ) :
    ∃ u : FiniteLP.PrimalFeasible (centralInc D S R.incidence),
      ∃ z : FiniteLP.DualFeasible (centralInc D S R.incidence) (centralGain R.resources Q D S w),
        FiniteLP.primalValue (centralGain R.resources Q D S w) u = FiniteLP.dualValue z :=
  FiniteLP.exists_equal_primal_dual _ _ (central_nonneg R) (central_cover cfg)

/-- **Result 2 (rational, existence).** Actual optimizers of the full and central rational LPs
exist, the lifted pair is a full optimal primal/dual pair, and `Wstar = B0 + Wredstar`. -/
theorem rat_optimum (cfg : Config R.resources Q D S) (hQD : ∀ o, o ∈ Q ∨ o ∈ D)
    (hw : ∀ o, 0 ≤ w o) :
    ∃ u : FiniteLP.PrimalFeasible (centralInc D S R.incidence),
      ∃ z : FiniteLP.DualFeasible (centralInc D S R.incidence) (centralGain R.resources Q D S w),
        FiniteLP.primalValue (centralGain R.resources Q D S w) u = FiniteLP.dualValue z ∧
        (∀ u' : FiniteLP.PrimalFeasible (centralInc D S R.incidence),
          FiniteLP.primalValue (centralGain R.resources Q D S w) u' ≤
          FiniteLP.primalValue (centralGain R.resources Q D S w) u) ∧
        (∀ p' : FiniteLP.PrimalFeasible R.incidence, FiniteLP.primalValue w p' ≤
          FiniteLP.primalValue w (extend cfg hQD (isIncidence_rat R) w u)) ∧
        FiniteLP.primalValue w (extend cfg hQD (isIncidence_rat R) w u) =
          FiniteLP.dualValue (liftDual z cfg hQD (isIncidence_rat R) hw) ∧
        FiniteLP.primalValue w (extend cfg hQD (isIncidence_rat R) w u) =
          B0 R.resources Q S w + FiniteLP.primalValue (centralGain R.resources Q D S w) u := by
  obtain ⟨u, z, huz⟩ := central_strong_duality cfg w
  have hval := extend_value cfg hQD (isIncidence_rat R) hw u
  have hdval := liftDual_value z cfg hQD (isIncidence_rat R) hw
  have heq : FiniteLP.primalValue w (extend cfg hQD (isIncidence_rat R) w u) =
      FiniteLP.dualValue (liftDual z cfg hQD (isIncidence_rat R) hw) := by
    rw [hval, hdval, huz]
  refine ⟨u, z, huz, (FiniteLP.optimal_of_equal u z huz).1,
    (FiniteLP.optimal_of_equal _ _ heq).1, heq, hval⟩

/-- Existence of an actual optimal full rational vector. -/
theorem exists_rat_full_optimum (cfg : Config R.resources Q D S) (hQD : ∀ o, o ∈ Q ∨ o ∈ D)
    (hw : ∀ o, 0 ≤ w o) :
    ∃ p : FiniteLP.PrimalFeasible R.incidence,
      ∀ p' : FiniteLP.PrimalFeasible R.incidence,
        FiniteLP.primalValue w p' ≤ FiniteLP.primalValue w p := by
  obtain ⟨u, _, _, _, hp, _⟩ := rat_optimum (w := w) cfg hQD hw
  exact ⟨_, hp⟩

/-- Existence of an actual optimal central rational vector. -/
theorem exists_rat_central_optimum (cfg : Config R.resources Q D S) (w : I → ℚ) :
    ∃ u : FiniteLP.PrimalFeasible (centralInc D S R.incidence),
      ∀ u' : FiniteLP.PrimalFeasible (centralInc D S R.incidence),
        FiniteLP.primalValue (centralGain R.resources Q D S w) u' ≤
        FiniteLP.primalValue (centralGain R.resources Q D S w) u := by
  obtain ⟨u, z, h⟩ := central_strong_duality cfg w
  exact ⟨u, (FiniteLP.optimal_of_equal u z h).1⟩

/-- Every rational full optimum is attained by a dual of the same value (lifted from the
central LP). -/
theorem rat_full_opt_has_dual (cfg : Config R.resources Q D S) (hQD : ∀ o, o ∈ Q ∨ o ∈ D)
    (hw : ∀ o, 0 ≤ w o) (p : FiniteLP.PrimalFeasible R.incidence)
    (hp : ∀ p' : FiniteLP.PrimalFeasible R.incidence,
      FiniteLP.primalValue w p' ≤ FiniteLP.primalValue w p) :
    ∃ y : FiniteLP.DualFeasible R.incidence w, FiniteLP.primalValue w p = FiniteLP.dualValue y := by
  obtain ⟨u, z, _, _, _, heq, _⟩ := rat_optimum (w := w) cfg hQD hw
  refine ⟨liftDual z cfg hQD (isIncidence_rat R) hw, le_antisymm (FiniteLP.weak_duality _ _) ?_⟩
  rw [← heq]
  exact hp _

end RationalOptimum

/-! ### Real optima via explicit embedding -/

section RealOptimum

variable {R : System I E} {Q D : Finset I} {S : Finset E} {w : I → ℚ}

/-- **Result 2 (real version).** Actual optimizers of the real full LP (`realIncidence R`,
gains `w`) and of the real central LP exist; they are the explicit embeddings of the rational
optimizers; and every pair of real optimizers satisfies `Wstar = B0 + Wredstar`, with value equal
to the cast of the rational optimum. -/
theorem real_optimum (cfg : Config R.resources Q D S) (hQD : ∀ o, o ∈ Q ∨ o ∈ D)
    (hw : ∀ o, 0 ≤ w o) :
    ∃ u : FiniteLP.PrimalFeasible (centralInc D S R.incidence),
      (∀ u' : FiniteLP.PrimalFeasible (centralInc D S R.incidence),
        FiniteLP.primalValue (centralGain R.resources Q D S w) u' ≤
          FiniteLP.primalValue (centralGain R.resources Q D S w) u) ∧
      (∀ p' : FiniteLP.PrimalFeasible (realIncidence R),
        FiniteLP.primalValue (fun o => (w o : ℝ)) p' ≤
          FiniteLP.primalValue (fun o => (w o : ℝ))
            (primalCast (extend cfg hQD (isIncidence_rat R) w u))) ∧
      (∀ u' : FiniteLP.PrimalFeasible (centralInc D S (realIncidence R)),
        FiniteLP.primalValue (centralGain R.resources Q D S (fun o => (w o : ℝ))) u' ≤
          FiniteLP.primalValue (centralGain R.resources Q D S (fun o => (w o : ℝ)))
            (primalCast u)) ∧
      FiniteLP.primalValue (fun o => (w o : ℝ))
          (primalCast (extend cfg hQD (isIncidence_rat R) w u)) =
        (((B0 R.resources Q S w + FiniteLP.primalValue (centralGain R.resources Q D S w) u : ℚ))
          : ℝ) := by
  obtain ⟨u, z, huz', hu, _, heq, hval⟩ := rat_optimum (w := w) cfg hQD hw
  refine ⟨u, hu, ?_, ?_, ?_⟩
  · exact primalCast_optimal _ _ heq
  · intro u'
    rw [centralGain_cast hw]
    exact primalCast_optimal u z huz' u'
  · rw [primalCast_value, hval]

/-- **Result 2 (real identity).** Any real optimal full vector and any real optimal central
vector satisfy `Wstar = B0 + Wredstar` (real LPs, real signed reduced gains). -/
theorem real_opt_value_eq (cfg : Config R.resources Q D S) (hQD : ∀ o, o ∈ Q ∨ o ∈ D)
    (hw : ∀ o, 0 ≤ w o) (pR : FiniteLP.PrimalFeasible (realIncidence R))
    (hpR : ∀ p' : FiniteLP.PrimalFeasible (realIncidence R),
      FiniteLP.primalValue (fun o => (w o : ℝ)) p' ≤ FiniteLP.primalValue (fun o => (w o : ℝ)) pR)
    (uR : FiniteLP.PrimalFeasible (centralInc D S (realIncidence R)))
    (huR : ∀ u' : FiniteLP.PrimalFeasible (centralInc D S (realIncidence R)),
      FiniteLP.primalValue (centralGain R.resources Q D S (fun o => (w o : ℝ))) u' ≤
        FiniteLP.primalValue (centralGain R.resources Q D S (fun o => (w o : ℝ))) uR) :
    FiniteLP.primalValue (fun o => (w o : ℝ)) pR =
      ((B0 R.resources Q S w : ℚ) : ℝ) +
        FiniteLP.primalValue (centralGain R.resources Q D S (fun o => (w o : ℝ))) uR := by
  rw [← B0_cast hw]
  exact opt_value_eq cfg hQD (isIncidence_real R) (fun o => by exact_mod_cast hw o) pR hpR uR huR

/-- The real full optimum is the cast of the rational full optimum. -/
theorem real_full_opt_eq_rat (cfg : Config R.resources Q D S) (hQD : ∀ o, o ∈ Q ∨ o ∈ D)
    (hw : ∀ o, 0 ≤ w o) (p : FiniteLP.PrimalFeasible R.incidence)
    (hp : ∀ p' : FiniteLP.PrimalFeasible R.incidence,
      FiniteLP.primalValue w p' ≤ FiniteLP.primalValue w p)
    (pR : FiniteLP.PrimalFeasible (realIncidence R))
    (hpR : ∀ p' : FiniteLP.PrimalFeasible (realIncidence R),
      FiniteLP.primalValue (fun o => (w o : ℝ)) p' ≤ FiniteLP.primalValue (fun o => (w o : ℝ)) pR) :
    FiniteLP.primalValue (fun o => (w o : ℝ)) pR = ((FiniteLP.primalValue w p : ℚ) : ℝ) := by
  obtain ⟨y, hy⟩ := rat_full_opt_has_dual cfg hQD hw p hp
  rw [← primalCast_value]
  exact le_antisymm (primalCast_optimal p y hy pR) (hpR (primalCast p))

/-- The real central optimum is the cast of the rational central optimum. -/
theorem real_central_opt_eq_rat (cfg : Config R.resources Q D S) (hw : ∀ o, 0 ≤ w o)
    (u : FiniteLP.PrimalFeasible (centralInc D S R.incidence))
    (hu : ∀ u' : FiniteLP.PrimalFeasible (centralInc D S R.incidence),
      FiniteLP.primalValue (centralGain R.resources Q D S w) u' ≤
        FiniteLP.primalValue (centralGain R.resources Q D S w) u)
    (uR : FiniteLP.PrimalFeasible (centralInc D S (realIncidence R)))
    (huR : ∀ u' : FiniteLP.PrimalFeasible (centralInc D S (realIncidence R)),
      FiniteLP.primalValue (centralGain R.resources Q D S (fun o => (w o : ℝ))) u' ≤
        FiniteLP.primalValue (centralGain R.resources Q D S (fun o => (w o : ℝ))) uR) :
    FiniteLP.primalValue (centralGain R.resources Q D S (fun o => (w o : ℝ))) uR =
      ((FiniteLP.primalValue (centralGain R.resources Q D S w) u : ℚ) : ℝ) := by
  obtain ⟨u0, z0, h0⟩ := central_strong_duality cfg w
  have hz : FiniteLP.primalValue (centralGain R.resources Q D S w) u = FiniteLP.dualValue z0 :=
    le_antisymm (FiniteLP.weak_duality u z0) (h0 ▸ hu u0)
  rw [centralGain_cast hw] at huR ⊢
  rw [← primalCast_value]
  exact le_antisymm (primalCast_optimal u z0 hz uR) (huR (primalCast u))

end RealOptimum

end FractionalUnitBoundary
end PaperV
