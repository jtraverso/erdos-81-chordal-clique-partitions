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

/-
Paper V — exact fractional unit-boundary elimination and dual lifting (generic ordered field `K`).

Setting: a physical resource system `R : System I E` (every object has a nonempty resource set),
the existing `UnitBoundary.Config R.resources Q D S` (outer/central structure, label disjointness),
`Q ∪ D` covering all objects (`hQD`), a matrix `A` that is the 0/1 incidence of `R`
(`IsIncidence R A`; e.g. `R.incidence` over `ℚ` or `realIncidence R` over `ℝ`) and weights `w ≥ 0`.
The central LP has variables `{d // d ∈ D}`, capacities `{e // e ∈ S}` and signed gains
`wred d = w d - Σ_{e ∈ rho d} pi_e`.

  * `extend`, `extend_central`, `extend_Z`, `extend_value`        (Result 1)
  * `restrict`, `value_le_restrict`, `opt_value_eq`               (Result 2)
  * `privRes_injOn`, `liftDual`, `liftPrice_*`, `liftDual_value`  (Result 3)
  * `lifted_gap_eq`                                               (Result 5)

Axiom target = {propext, Classical.choice, Quot.sound} (see `PaperV/FractionalAxiomGate.lean`).
-/
module

public import PaperV.UnitBoundaryWeighted
public import PaperV.ResourceOptimum
import Lean.Elab.Tactic.NormCast
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set

@[expose] public section

open Finset Classical

namespace PaperV
namespace FractionalUnitBoundary

open UnitBoundary UnitBoundary.Weighted ResourceCertificate System

variable {I E : Type*} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### Opportunity prices, base value and reduced weights -/

section Defs
variable (rho : I → Finset E) (Q D : Finset I) (S : Finset E) (w : I → K)

/-- `pi_e = max ({0} ∪ {w o | o ∈ Q_e})`, where `Q_e = Rep rho Q S e`. -/
noncomputable def piW (e : E) : K :=
  (insert 0 ((Rep rho Q S e).image w)).max' (Finset.insert_nonempty _ _)

/-- `B0 = Σ_{o ∈ Z} w o + Σ_{e ∈ S} pi_e`. -/
noncomputable def B0 : K := ∑ o ∈ Z rho Q S, w o + ∑ e ∈ S, piW rho Q S w e

/-- Signed reduced central weight `wred d = w d - Σ_{e ∈ rho d} pi_e`. -/
noncomputable def wred (d : I) : K := w d - ∑ e ∈ rho d, piW rho Q S w e

/-- Central incidence: variables indexed by `D`, capacities indexed by `S`. -/
def centralInc (A : I → E → K) : {d // d ∈ D} → {e // e ∈ S} → K := fun d e => A d.1 e.1

/-- Central (signed) gains. -/
noncomputable def centralGain : {d // d ∈ D} → K := fun d => wred rho Q S w d.1

end Defs

variable {rho : I → Finset E} {Q D : Finset I} {S : Finset E} {w : I → K}

omit [Fintype I] [Fintype E] [DecidableEq I] [IsStrictOrderedRing K] in
theorem piW_nonneg (e : E) : 0 ≤ piW rho Q S w e :=
  Finset.le_max' _ _ (Finset.mem_insert_self _ _)

omit [Fintype I] [Fintype E] [DecidableEq I] [IsStrictOrderedRing K] in
theorem le_piW {e : E} {o : I} (ho : o ∈ Rep rho Q S e) : w o ≤ piW rho Q S w e :=
  Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem w ho))

omit [Fintype I] [Fintype E] [DecidableEq I] [IsStrictOrderedRing K] in
theorem piW_le {e : E} {c : K} (h0 : 0 ≤ c) (h : ∀ o ∈ Rep rho Q S e, w o ≤ c) :
    piW rho Q S w e ≤ c := by
  unfold piW
  apply Finset.max'_le
  intro y hy
  rcases Finset.mem_insert.mp hy with rfl | hy
  · exact h0
  · obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hy
    exact h o ho

theorem piW_eq_zero {e : E} (h : Rep rho Q S e = ∅) : piW rho Q S w e = 0 :=
  le_antisymm (piW_le le_rfl (by simp [h])) (piW_nonneg e)

theorem exists_eq_piW (hw : ∀ o, 0 ≤ w o) {e : E} (h : (Rep rho Q S e).Nonempty) :
    ∃ o ∈ Rep rho Q S e, w o = piW rho Q S w e := by
  obtain ⟨o, ho, hmax⟩ := Finset.exists_max_image _ w h
  exact ⟨o, ho, le_antisymm (le_piW ho) (piW_le (hw o) hmax)⟩

/-- A chosen maximum-weight representative on `e` (empty if `Q_e` has none). -/
noncomputable def repSet (rho : I → Finset E) (Q : Finset I) (S : Finset E) (w : I → K) (e : E) :
    Finset I :=
  if h : ∃ o ∈ Rep rho Q S e, w o = piW rho Q S w e then {h.choose} else ∅

omit [Fintype I] [Fintype E] [DecidableEq I] [IsStrictOrderedRing K] in
theorem repSet_subset (e : E) : repSet rho Q S w e ⊆ Rep rho Q S e := by
  unfold repSet
  split_ifs with h
  · exact Finset.singleton_subset_iff.mpr h.choose_spec.1
  · exact Finset.empty_subset _

omit [Fintype I] [Fintype E] [DecidableEq I] [IsStrictOrderedRing K] in
theorem card_repSet_le (e : E) : (repSet rho Q S w e).card ≤ 1 := by
  unfold repSet; split_ifs <;> simp

theorem sum_repSet (hw : ∀ o, 0 ≤ w o) (e : E) :
    ∑ o ∈ repSet rho Q S w e, w o = piW rho Q S w e := by
  unfold repSet
  split_ifs with h
  · simpa using h.choose_spec.2
  · rw [Finset.sum_empty]
    by_cases hne : (Rep rho Q S e).Nonempty
    · exact absurd (exists_eq_piW hw hne) h
    · rw [piW_eq_zero (Finset.not_nonempty_iff_eq_empty.mp hne)]


/-! ### Generic sum identities -/

theorem sum_dite_mem_univ {α M : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid M]
    (s : Finset α) (f : {a // a ∈ s} → M) :
    ∑ a, (if h : a ∈ s then f ⟨a, h⟩ else 0) = ∑ a : {a // a ∈ s}, f a := by
  rw [← Finset.sum_subset (Finset.subset_univ s) (fun a _ ha => dif_neg ha)]
  rw [← Finset.sum_coe_sort s]
  exact Finset.sum_congr rfl (fun a _ => dif_pos a.2)

/-! ### The fractional extension of a central vector -/

section Extension

variable (rho : I → Finset E) (Q D : Finset I) (S : Finset E) (w : I → K) (A : I → E → K)

/-- Central load `lambda_e = Σ_{d ∈ D} A d e * u d` (for every resource `e : E`). -/
def lam (u : {d // d ∈ D} → K) (e : E) : K := ∑ d : {d // d ∈ D}, A d.1 e * u d

/-- The explicit extension: `u` on `D`, `1` on `Z`, and mass `1 - lambda_e` on the chosen
heaviest representative of every nonempty `Q_e`, `e ∈ S`. -/
noncomputable def extWeight (u : {d // d ∈ D} → K) (o : I) : K :=
  (if h : o ∈ D then u ⟨o, h⟩ else 0) + (if o ∈ Z rho Q S then 1 else 0) +
    ∑ e ∈ S, (if o ∈ repSet rho Q S w e then 1 - lam D A u e else 0)

omit [Fintype E] [IsStrictOrderedRing K] in
theorem sum_mul_extWeight (u : {d // d ∈ D} → K) (f : I → K) :
    ∑ o, f o * extWeight rho Q D S w A u o =
      ∑ d : {d // d ∈ D}, f d.1 * u d + ∑ o ∈ Z rho Q S, f o +
        ∑ e ∈ S, (1 - lam D A u e) * ∑ o ∈ repSet rho Q S w e, f o := by
  unfold extWeight
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  congr 1
  · simp only [mul_dite, mul_zero]
    exact sum_dite_mem_univ D (fun d => f d.1 * u d)
  · simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum, ← Finset.sum_mul, mul_comm]

end Extension


/-! ### Structural facts from the configuration -/

section Structure

variable {rho : I → Finset E} {Q D : Finset I} {S : Finset E}

omit [Fintype I] [Fintype E] in
theorem mem_Rep_iff' {e : E} {o : I} :
    o ∈ Rep rho Q S e ↔ o ∈ Q ∧ rho o ∩ S = {e} := mem_Rep

omit [Fintype I] [Fintype E] in
theorem res_of_mem_Rep {e : E} {o : I} (ho : o ∈ Rep rho Q S e) : e ∈ rho o ∧ e ∈ S := by
  have h := (mem_Rep.mp ho).2
  have : e ∈ rho o ∩ S := h ▸ Finset.mem_singleton_self e
  exact Finset.mem_inter.mp this

omit [Fintype I] [Fintype E] in
theorem eq_of_mem_Rep {e e' : E} {o : I} (ho : o ∈ Rep rho Q S e) (he' : e' ∈ S)
    (he'o : e' ∈ rho o) : e' = e := by
  have h := (mem_Rep.mp ho).2
  have : e' ∈ rho o ∩ S := Finset.mem_inter.mpr ⟨he'o, he'⟩
  rw [h] at this
  exact Finset.mem_singleton.mp this

omit [Fintype I] [Fintype E] in
theorem not_mem_res_of_mem_Z {e : E} {o : I} (ho : o ∈ Z rho Q S) (he : e ∈ S) : e ∉ rho o := by
  intro h
  have h1 := (mem_Z.mp ho).2
  have : e ∈ rho o ∩ S := Finset.mem_inter.mpr ⟨h, he⟩
  rw [h1] at this
  exact Finset.notMem_empty e this

theorem not_mem_Z_of_mem_Rep {e : E} {o : I} (ho : o ∈ Rep rho Q S e) : o ∉ Z rho Q S := by
  intro hz
  have := res_of_mem_Rep ho
  exact not_mem_res_of_mem_Z hz this.2 this.1

omit [Fintype I] [Fintype E] in
theorem mem_Q_of_mem_Rep {e : E} {o : I} (ho : o ∈ Rep rho Q S e) : o ∈ Q := (mem_Rep.mp ho).1

omit [Fintype I] [Fintype E] [DecidableEq I] in
theorem not_mem_D_of_mem_Q (cfg : Config rho Q D S) {o : I} (ho : o ∈ Q) : o ∉ D :=
  Finset.disjoint_left.mp cfg.hdisj ho

omit [Fintype I] [Fintype E] in
/-- Distinct outer objects sharing a non-shared resource are impossible. -/
theorem card_outer_at_private_le (cfg : Config rho Q D S) {e : E} (he : e ∉ S) :
    (Q.filter (fun o => e ∈ rho o)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hab
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  exact he (cfg.hQ ha'.1 hb'.1 hab (Finset.mem_inter.mpr ⟨ha'.2, hb'.2⟩))

omit [Fintype I] [Fintype E] in
/-- An outer object outside `Z` lies on exactly one shared resource. -/
theorem exists_shared (cfg : Config rho Q D S) {o : I} (hoQ : o ∈ Q) (hoZ : o ∉ Z rho Q S) :
    ∃ b ∈ S, rho o ∩ S = {b} :=
  shared_singleton cfg (Finset.mem_sdiff.mpr ⟨hoQ, hoZ⟩)

end Structure

/-! ### Feasibility and value of the extension -/

section ExtensionFeasible

variable (R : System I E) {Q D : Finset I} {S : Finset E} {w : I → K} {A : I → E → K}

/-- Hypothesis shape: `A` is the 0/1 incidence matrix of the physical system `R`. -/
def IsIncidence (R : System I E) (A : I → E → K) : Prop :=
  ∀ o e, A o e = if e ∈ R.resources o then 1 else 0

variable {R}

omit [DecidableEq I] in
theorem inc_nonneg (hA : IsIncidence R A) (o : I) (e : E) : 0 ≤ A o e := by
  rw [hA]; split_ifs <;> norm_num

omit [DecidableEq I] in
theorem inc_le_one (hA : IsIncidence R A) (o : I) (e : E) : A o e ≤ 1 := by
  rw [hA]; split_ifs <;> norm_num

omit [DecidableEq I] [LinearOrder K] [IsStrictOrderedRing K] in
theorem inc_eq_zero (hA : IsIncidence R A) {o : I} {e : E} (h : e ∉ R.resources o) : A o e = 0 := by
  rw [hA, if_neg h]

omit [DecidableEq I] [LinearOrder K] [IsStrictOrderedRing K] in
theorem inc_eq_one (hA : IsIncidence R A) {o : I} {e : E} (h : e ∈ R.resources o) : A o e = 1 := by
  rw [hA, if_pos h]

omit [DecidableEq I] [LinearOrder K] [IsStrictOrderedRing K] in
/-- `Σ_{e ∈ S} A d e * c e = Σ_{e ∈ rho d} c e` for a central object. -/
theorem sum_S_inc_mul (cfg : Config R.resources Q D S) (hA : IsIncidence R A) {d : I} (hd : d ∈ D)
    (c : E → K) : ∑ e ∈ S, A d e * c e = ∑ e ∈ R.resources d, c e := by
  have hA' : ∀ o e, A o e = if e ∈ R.resources o then (1 : K) else 0 := hA
  simp only [hA', ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (cfg.hD d hd)]

omit [DecidableEq I] [LinearOrder K] [IsStrictOrderedRing K] in
/-- `Σ_e A o e * f e = Σ_{e ∈ rho o} f e`. -/
theorem sum_inc_mul (hA : IsIncidence R A) (o : I) (f : E → K) :
    ∑ e, A o e * f e = ∑ e ∈ R.resources o, f e := by
  have hA' : ∀ o e, A o e = if e ∈ R.resources o then (1 : K) else 0 := hA
  simp only [hA', ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

omit [DecidableEq I] [LinearOrder K] [IsStrictOrderedRing K] in
/-- `Σ_o A o e * f o = Σ_{o : e ∈ rho o} f o`. -/
theorem sum_inc_mul' (hA : IsIncidence R A) (e : E) (f : I → K) :
    ∑ o, A o e * f o = ∑ o ∈ Finset.univ.filter (fun o => e ∈ R.resources o), f o := by
  have hA' : ∀ o e, A o e = if e ∈ R.resources o then (1 : K) else 0 := hA
  simp only [hA', ite_mul, one_mul, zero_mul]
  rw [Finset.sum_filter]

variable (u : FiniteLP.PrimalFeasible (centralInc D S A))

theorem lam_nonneg (hA : IsIncidence R A) (e : E) : 0 ≤ lam D A u.weight e :=
  Finset.sum_nonneg (fun d _ => mul_nonneg (inc_nonneg hA _ _) (u.weight_nonneg d))

omit [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E] [IsStrictOrderedRing K] in
theorem lam_le_one {e : E} (he : e ∈ S) : lam D A u.weight e ≤ 1 :=
  u.capacity ⟨e, he⟩

theorem lam_eq_zero (cfg : Config R.resources Q D S) (hA : IsIncidence R A) {e : E} (he : e ∉ S) :
    lam D A u.weight e = 0 := by
  apply Finset.sum_eq_zero
  intro d _
  rw [inc_eq_zero hA (fun h => he (cfg.hD d.1 d.2 h)), zero_mul]

theorem extWeight_nonneg (o : I) :
    0 ≤ extWeight R.resources Q D S w A u.weight o := by
  unfold extWeight
  refine add_nonneg (add_nonneg ?_ ?_) (Finset.sum_nonneg ?_)
  · split_ifs
    · exact u.weight_nonneg _
    · exact le_rfl
  · split_ifs <;> norm_num
  · intro e he
    split_ifs
    · exact sub_nonneg.mpr (lam_le_one u he)
    · exact le_rfl

end ExtensionFeasible

section ExtensionFeasible2

variable {R : System I E} {Q D : Finset I} {S : Finset E} {w : I → K} {A : I → E → K}
variable (u : FiniteLP.PrimalFeasible (centralInc D S A))

theorem extWeight_central (cfg : Config R.resources Q D S) {d : I} (hd : d ∈ D) :
    extWeight R.resources Q D S w A u.weight d = u.weight ⟨d, hd⟩ := by
  unfold extWeight
  rw [dif_pos hd, if_neg (fun h => not_mem_D_of_mem_Q cfg (Z_subset h) hd)]
  rw [Finset.sum_eq_zero (fun e _ => if_neg (fun h =>
    not_mem_D_of_mem_Q cfg (mem_Q_of_mem_Rep (repSet_subset e h)) hd))]
  ring

theorem extWeight_le_one (cfg : Config R.resources Q D S) (hA : IsIncidence R A) {o : I}
    (hoQ : o ∈ Q) : extWeight R.resources Q D S w A u.weight o ≤ 1 := by
  have hoD := not_mem_D_of_mem_Q cfg hoQ
  unfold extWeight
  rw [dif_neg hoD, zero_add, ← Finset.sum_filter]
  set F := S.filter (fun e => o ∈ repSet R.resources Q S w e) with hFdef
  have hF : F ⊆ R.resources o ∩ S := by
    intro e he
    obtain ⟨heS, ho⟩ := Finset.mem_filter.mp he
    exact Finset.mem_inter.mpr ⟨(res_of_mem_Rep (repSet_subset e ho)).1, heS⟩
  have hsum : ∑ e ∈ F, (1 - lam D A u.weight e) ≤ F.card := by
    have := Finset.sum_le_card_nsmul F (fun e => 1 - lam D A u.weight e) 1
      (fun e _ => by linarith [lam_nonneg u hA e])
    simpa using this
  split_ifs with hZ
  · have hFe : F = ∅ := by
      apply Finset.subset_empty.mp
      rw [← (mem_Z.mp hZ).2]; exact hF
    rw [hFe]; simp
  · have hc : F.card ≤ 1 := (Finset.card_le_card hF).trans (cfg.hunit o hoQ)
    have : (F.card : K) ≤ 1 := by exact_mod_cast hc
    linarith

theorem load_ext_shared (hA : IsIncidence R A) {e : E}
    (he : e ∈ S) : ∑ o, A o e * extWeight R.resources Q D S w A u.weight o ≤ 1 := by
  rw [sum_mul_extWeight]
  have h1 : ∑ d : {d // d ∈ D}, A d.1 e * u.weight d = lam D A u.weight e := rfl
  have h2 : ∑ o ∈ Z R.resources Q S, A o e = 0 :=
    Finset.sum_eq_zero (fun o ho => inc_eq_zero hA (not_mem_res_of_mem_Z ho he))
  have h3 : ∑ e' ∈ S, (1 - lam D A u.weight e') * ∑ o ∈ repSet R.resources Q S w e', A o e =
      (1 - lam D A u.weight e) * ∑ o ∈ repSet R.resources Q S w e, A o e := by
    apply Finset.sum_eq_single_of_mem e he
    intro e' _ hne
    rw [Finset.sum_eq_zero, mul_zero]
    intro o ho
    apply inc_eq_zero hA
    intro heo
    exact hne (eq_of_mem_Rep (repSet_subset e' ho) he heo).symm
  have h4 : ∑ o ∈ repSet R.resources Q S w e, A o e ≤ 1 := by
    calc _ ≤ ∑ o ∈ repSet R.resources Q S w e, (1 : K) :=
          Finset.sum_le_sum (fun o _ => inc_le_one hA o e)
      _ = ((repSet R.resources Q S w e).card : K) := by simp
      _ ≤ 1 := by exact_mod_cast card_repSet_le e
  have h5 := lam_le_one u he
  have h6 : 0 ≤ ∑ o ∈ repSet R.resources Q S w e, A o e :=
    Finset.sum_nonneg (fun o _ => inc_nonneg hA o e)
  rw [h1, h2, h3]
  nlinarith

theorem load_ext_private (cfg : Config R.resources Q D S) (hQD : ∀ o, o ∈ Q ∨ o ∈ D)
    (hA : IsIncidence R A) {e : E} (he : e ∉ S) :
    ∑ o, A o e * extWeight R.resources Q D S w A u.weight o ≤ 1 := by
  rw [sum_inc_mul' hA]
  have hsub : Finset.univ.filter (fun o => e ∈ R.resources o) ⊆
      Q.filter (fun o => e ∈ R.resources o) := by
    intro o ho
    have heo := (Finset.mem_filter.mp ho).2
    rcases hQD o with hQ | hD
    · exact Finset.mem_filter.mpr ⟨hQ, heo⟩
    · exact absurd (cfg.hD o hD heo) he
  calc _ ≤ ∑ o ∈ Q.filter (fun o => e ∈ R.resources o),
          extWeight R.resources Q D S w A u.weight o :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun o _ _ => extWeight_nonneg u o)
    _ ≤ ∑ o ∈ Q.filter (fun o => e ∈ R.resources o), (1 : K) :=
        Finset.sum_le_sum (fun o ho => extWeight_le_one u cfg hA (Finset.mem_filter.mp ho).1)
    _ = ((Q.filter (fun o => e ∈ R.resources o)).card : K) := by simp
    _ ≤ 1 := by exact_mod_cast card_outer_at_private_le cfg he

end ExtensionFeasible2

/-- **Result 1 (construction).** The full feasible vector extending a central feasible `u`. -/
noncomputable def extend {R : System I E} {Q D : Finset I} {S : Finset E} {A : I → E → K}
    (cfg : Config R.resources Q D S) (hQD : ∀ o, o ∈ Q ∨ o ∈ D) (hA : IsIncidence R A)
    (w : I → K) (u : FiniteLP.PrimalFeasible (centralInc D S A)) : FiniteLP.PrimalFeasible A where
  weight := extWeight R.resources Q D S w A u.weight
  weight_nonneg := extWeight_nonneg u
  capacity e := by
    by_cases he : e ∈ S
    · exact load_ext_shared u hA he
    · exact load_ext_private u cfg hQD hA he

section ExtensionValue

variable {R : System I E} {Q D : Finset I} {S : Finset E} {w : I → K} {A : I → E → K}

/-- **Result 1 (central part).** The extension restricts to `u` on `D`. -/
theorem extend_central (cfg : Config R.resources Q D S) (hQD : ∀ o, o ∈ Q ∨ o ∈ D)
    (hA : IsIncidence R A) (u : FiniteLP.PrimalFeasible (centralInc D S A)) (d : {d // d ∈ D}) :
    (extend cfg hQD hA w u).weight d.1 = u.weight d :=
  extWeight_central u cfg d.2

/-- The extension is `1` on every object of `Z`. -/
theorem extend_Z (cfg : Config R.resources Q D S) (hQD : ∀ o, o ∈ Q ∨ o ∈ D)
    (hA : IsIncidence R A) (u : FiniteLP.PrimalFeasible (centralInc D S A)) {o : I}
    (ho : o ∈ Z R.resources Q S) : (extend cfg hQD hA w u).weight o = 1 := by
  show extWeight R.resources Q D S w A u.weight o = 1
  unfold extWeight
  have hoQ := Z_subset ho
  rw [dif_neg (not_mem_D_of_mem_Q cfg hoQ), if_pos ho,
    Finset.sum_eq_zero (fun e _ => if_neg (fun h => not_mem_Z_of_mem_Rep (repSet_subset e h) ho))]
  ring

/-- **Result 1 (exact value).** `value (extend u) = B0 + Σ_d wred d * u d`. -/
theorem extend_value (cfg : Config R.resources Q D S) (hQD : ∀ o, o ∈ Q ∨ o ∈ D)
    (hA : IsIncidence R A) (hw : ∀ o, 0 ≤ w o) (u : FiniteLP.PrimalFeasible (centralInc D S A)) :
    FiniteLP.primalValue w (extend cfg hQD hA w u) =
      B0 R.resources Q S w + FiniteLP.primalValue (centralGain R.resources Q D S w) u := by
  unfold FiniteLP.primalValue
  show ∑ o, w o * extWeight R.resources Q D S w A u.weight o = _
  rw [sum_mul_extWeight]
  simp only [sum_repSet hw]
  have key : ∑ e ∈ S, lam D A u.weight e * piW R.resources Q S w e =
      ∑ d : {d // d ∈ D}, (∑ e ∈ R.resources d.1, piW R.resources Q S w e) * u.weight d := by
    unfold lam
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    rw [← sum_S_inc_mul cfg hA d.2]
    apply Finset.sum_congr rfl
    intro e _
    ring
  unfold B0 centralGain wred
  simp only [sub_mul, one_mul, Finset.sum_sub_distrib]
  rw [key]
  ring

end ExtensionValue

/-! ### Result 2: restriction and the upper bound -/

section Restriction

variable {R : System I E} {Q D : Finset I} {S : Finset E} {w : I → K} {A : I → E → K}

/-- Restriction of a full feasible vector to the central objects. -/
def restrict (hA : IsIncidence R A) (p : FiniteLP.PrimalFeasible A) :
    FiniteLP.PrimalFeasible (centralInc D S A) where
  weight d := p.weight d.1
  weight_nonneg d := p.weight_nonneg d.1
  capacity e := by
    show ∑ d : {d // d ∈ D}, A d.1 e.1 * p.weight d.1 ≤ 1
    calc _ = ∑ o ∈ D, A o e.1 * p.weight o := Finset.sum_coe_sort D (fun o => A o e.1 * p.weight o)
      _ ≤ ∑ o, A o e.1 * p.weight o :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun o _ _ => mul_nonneg (inc_nonneg hA _ _) (p.weight_nonneg o))
      _ ≤ 1 := p.capacity e.1

theorem restrict_weight (hA : IsIncidence R A) (p : FiniteLP.PrimalFeasible A) (d : {d // d ∈ D}) :
    (restrict (S := S) hA p).weight d = p.weight d.1 := rfl

/-- Every coordinate of a full feasible vector is at most one (each resource set is nonempty). -/
theorem weight_le_one (hA : IsIncidence R A) (p : FiniteLP.PrimalFeasible A) (o : I) :
    p.weight o ≤ 1 := by
  obtain ⟨r, hr⟩ := R.nonempty o
  calc p.weight o = A o r * p.weight o := by rw [inc_eq_one hA hr, one_mul]
    _ ≤ ∑ o', A o' r * p.weight o' :=
        Finset.single_le_sum (f := fun o' => A o' r * p.weight o')
          (fun o' _ => mul_nonneg (inc_nonneg hA _ _) (p.weight_nonneg o')) (Finset.mem_univ o)
    _ ≤ 1 := p.capacity r

/-- Sum over a subset of the load at `e` is bounded by one. -/
theorem partial_load_le (hA : IsIncidence R A) (p : FiniteLP.PrimalFeasible A) (T : Finset I)
    (e : E) : ∑ o ∈ T, A o e * p.weight o ≤ 1 :=
  le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun o _ _ => mul_nonneg (inc_nonneg hA _ _) (p.weight_nonneg o))) (p.capacity e)

/-- **Result 2 (upper bound).** Every full feasible vector has objective at most
`B0 + Σ_d wred d * p d`, the reduced value of its restriction to `D`. -/
theorem value_le_restrict (cfg : Config R.resources Q D S) (hQD : ∀ o, o ∈ Q ∨ o ∈ D)
    (hA : IsIncidence R A) (hw : ∀ o, 0 ≤ w o) (p : FiniteLP.PrimalFeasible A) :
    FiniteLP.primalValue w p ≤
      B0 R.resources Q S w + FiniteLP.primalValue (centralGain R.resources Q D S w)
        (restrict (S := S) hA p) := by
  have hA' : ∀ o e, A o e = if e ∈ R.resources o then (1 : K) else 0 := hA
  set x := p.weight with hx
  have huniv : (Finset.univ : Finset I) = Q ∪ D := by
    ext o; simp only [Finset.mem_univ, Finset.mem_union, true_iff]; exact hQD o
  have hsplit : FiniteLP.primalValue w p =
      ∑ o ∈ Q \ Z R.resources Q S, w o * x o + ∑ o ∈ Z R.resources Q S, w o * x o +
        ∑ o ∈ D, w o * x o := by
    unfold FiniteLP.primalValue
    rw [huniv, Finset.sum_union cfg.hdisj, ← Finset.sum_sdiff (Z_subset (res := R.resources))]
  have hZ : ∑ o ∈ Z R.resources Q S, w o * x o ≤ ∑ o ∈ Z R.resources Q S, w o :=
    Finset.sum_le_sum (fun o _ => by
      have := weight_le_one hA p o
      nlinarith [hw o])
  -- outer objects with a shared resource are charged to the price of that resource
  have hstep : ∀ o ∈ Q \ Z R.resources Q S,
      w o * x o ≤ ∑ e ∈ S, piW R.resources Q S w e * (A o e * x o) := by
    intro o ho
    obtain ⟨hoQ, hoZ⟩ := Finset.mem_sdiff.mp ho
    obtain ⟨b, _, hb⟩ := exists_shared cfg hoQ hoZ
    have hsum : ∑ e ∈ S, piW R.resources Q S w e * (A o e * x o) =
        piW R.resources Q S w b * x o := by
      have : ∑ e ∈ S, piW R.resources Q S w e * (A o e * x o) =
          (∑ e ∈ S ∩ R.resources o, piW R.resources Q S w e) * x o := by
        rw [Finset.sum_mul, ← Finset.sum_ite_mem]
        apply Finset.sum_congr rfl
        intro e _
        rw [hA']; split_ifs <;> ring
      rw [this, Finset.inter_comm, hb, Finset.sum_singleton]
    rw [hsum]
    exact mul_le_mul_of_nonneg_right (le_piW (mem_Rep.mpr ⟨hoQ, hb⟩)) (p.weight_nonneg o)
  have hQZ : ∑ o ∈ Q \ Z R.resources Q S, w o * x o ≤
      ∑ e ∈ S, piW R.resources Q S w e * (1 - ∑ o ∈ D, A o e * x o) := by
    calc _ ≤ ∑ o ∈ Q \ Z R.resources Q S, ∑ e ∈ S, piW R.resources Q S w e * (A o e * x o) :=
          Finset.sum_le_sum hstep
      _ = ∑ e ∈ S, piW R.resources Q S w e * ∑ o ∈ Q \ Z R.resources Q S, A o e * x o := by
          rw [Finset.sum_comm]; simp only [Finset.mul_sum]
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro e _
          apply mul_le_mul_of_nonneg_left _ (piW_nonneg e)
          have hd : Disjoint (Q \ Z R.resources Q S) D :=
            Finset.disjoint_of_subset_left Finset.sdiff_subset cfg.hdisj
          have := partial_load_le hA p ((Q \ Z R.resources Q S) ∪ D) e
          rw [Finset.sum_union hd] at this
          linarith
  have hkey : ∑ e ∈ S, piW R.resources Q S w e * ∑ o ∈ D, A o e * x o =
      ∑ o ∈ D, (∑ e ∈ R.resources o, piW R.resources Q S w e) * x o := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro o ho
    rw [← sum_S_inc_mul cfg hA ho, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _
    ring
  have hcentral : FiniteLP.primalValue (centralGain R.resources Q D S w) (restrict (S := S) hA p) =
      ∑ o ∈ D, (w o - ∑ e ∈ R.resources o, piW R.resources Q S w e) * x o := by
    unfold FiniteLP.primalValue centralGain wred
    exact Finset.sum_coe_sort D
      (fun o => (w o - ∑ e ∈ R.resources o, piW R.resources Q S w e) * x o)
  rw [hsplit, hcentral]
  unfold B0
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, sub_mul] at hQZ ⊢
  rw [hkey] at hQZ
  linarith

/-- **Result 2 (fractional optimum identity).** For any optimal full vector `p` and any optimal
central vector `u`, `value p = B0 + value u` (`Wstar = B0 + Wredstar`). -/
theorem opt_value_eq (cfg : Config R.resources Q D S) (hQD : ∀ o, o ∈ Q ∨ o ∈ D)
    (hA : IsIncidence R A) (hw : ∀ o, 0 ≤ w o)
    (p : FiniteLP.PrimalFeasible A)
    (hp : ∀ p' : FiniteLP.PrimalFeasible A, FiniteLP.primalValue w p' ≤ FiniteLP.primalValue w p)
    (u : FiniteLP.PrimalFeasible (centralInc D S A))
    (hu : ∀ u' : FiniteLP.PrimalFeasible (centralInc D S A),
      FiniteLP.primalValue (centralGain R.resources Q D S w) u' ≤
        FiniteLP.primalValue (centralGain R.resources Q D S w) u) :
    FiniteLP.primalValue w p =
      B0 R.resources Q S w + FiniteLP.primalValue (centralGain R.resources Q D S w) u := by
  apply le_antisymm
  · have h1 := value_le_restrict cfg hQD hA hw p
    have h2 := hu (restrict hA p)
    linarith
  · rw [← extend_value cfg hQD hA hw u]
    exact hp _

end Restriction

/-! ### Result 3: explicit dual lifting -/

section DualLift

/-- The chosen private resource of an object (an element of its nonempty resource set). -/
noncomputable def privRes (R : System I E) (o : I) : E := (R.nonempty o).choose

variable {R : System I E} {Q D : Finset I} {S : Finset E} {w : I → K} {A : I → E → K}

omit [DecidableEq I] in
theorem privRes_mem (o : I) : privRes R o ∈ R.resources o := (R.nonempty o).choose_spec

theorem privRes_not_shared {o : I} (ho : o ∈ Z R.resources Q S) : privRes R o ∉ S :=
  fun h => not_mem_res_of_mem_Z ho h (privRes_mem o)

/-- **Result 3 (distinctness).** Chosen private resources of distinct objects of `Z` differ. -/
theorem privRes_injOn (cfg : Config R.resources Q D S) {o o' : I}
    (ho : o ∈ Z R.resources Q S) (ho' : o' ∈ Z R.resources Q S) (hne : o ≠ o') :
    privRes R o ≠ privRes R o' := by
  intro h
  apply privRes_not_shared ho
  apply cfg.hQ (Z_subset ho) (Z_subset ho') hne
  exact Finset.mem_inter.mpr ⟨privRes_mem o, h ▸ privRes_mem o'⟩

variable (R Q S w) in
/-- Lifted prices: `pi_e + z_e` on shared resources, plus `w o` on the chosen private resource
of each `o ∈ Z`; zero elsewhere. -/
noncomputable def liftPrice (zp : {e // e ∈ S} → K) (e : E) : K :=
  (if h : e ∈ S then piW R.resources Q S w e + zp ⟨e, h⟩ else 0) +
    ∑ o ∈ Z R.resources Q S, (if privRes R o = e then w o else 0)

omit [IsStrictOrderedRing K] in
theorem liftPrice_shared (zp : {e // e ∈ S} → K) {e : E} (he : e ∈ S) :
    liftPrice R Q S w zp e = piW R.resources Q S w e + zp ⟨e, he⟩ := by
  unfold liftPrice
  rw [dif_pos he, Finset.sum_eq_zero (fun o ho => if_neg (fun h => privRes_not_shared ho (h ▸ he))),
    add_zero]

omit [IsStrictOrderedRing K] in
theorem liftPrice_chosen (cfg : Config R.resources Q D S) (zp : {e // e ∈ S} → K) {o : I}
    (ho : o ∈ Z R.resources Q S) : liftPrice R Q S w zp (privRes R o) = w o := by
  unfold liftPrice
  rw [dif_neg (privRes_not_shared ho), zero_add, Finset.sum_eq_single_of_mem o ho, if_pos rfl]
  intro o' ho' hne
  exact if_neg (privRes_injOn cfg ho' ho hne)

omit [DecidableEq I] [IsStrictOrderedRing K] in
theorem liftPrice_other (zp : {e // e ∈ S} → K) {e : E} (he : e ∉ S)
    (hnc : ∀ o ∈ Z R.resources Q S, privRes R o ≠ e) : liftPrice R Q S w zp e = 0 := by
  unfold liftPrice
  rw [dif_neg he, Finset.sum_eq_zero (fun o ho => if_neg (hnc o ho))]
  ring

variable (z : FiniteLP.DualFeasible (centralInc D S A) (centralGain R.resources Q D S w))

theorem liftPrice_nonneg (hw : ∀ o, 0 ≤ w o) (e : E) : 0 ≤ liftPrice R Q S w z.price e := by
  unfold liftPrice
  refine add_nonneg ?_ (Finset.sum_nonneg (fun o _ => by split_ifs <;> simp [hw o]))
  split_ifs
  · exact add_nonneg (piW_nonneg e) (z.price_nonneg _)
  · exact le_rfl

theorem liftPrice_demand (cfg : Config R.resources Q D S) (hQD : ∀ o, o ∈ Q ∨ o ∈ D)
    (hA : IsIncidence R A) (hw : ∀ o, 0 ≤ w o) (o : I) :
    w o ≤ ∑ e, A o e * liftPrice R Q S w z.price e := by
  rw [sum_inc_mul hA]
  have hnn := liftPrice_nonneg z hw
  rcases hQD o with hoQ | hoD
  · -- an outer object: one resource already carries enough price
    have hsingle : ∀ r ∈ R.resources o, liftPrice R Q S w z.price r ≤
        ∑ e ∈ R.resources o, liftPrice R Q S w z.price e := fun r hr =>
      Finset.single_le_sum (f := liftPrice R Q S w z.price) (fun e _ => hnn e) hr
    by_cases hoZ : o ∈ Z R.resources Q S
    · rw [← liftPrice_chosen (w := w) cfg z.price hoZ]
      exact hsingle _ (privRes_mem o)
    · obtain ⟨b, hbS, hb⟩ := exists_shared cfg hoQ hoZ
      have hbo : b ∈ R.resources o :=
        (Finset.mem_inter.mp (hb ▸ Finset.mem_singleton_self b : b ∈ R.resources o ∩ S)).1
      refine le_trans ?_ (hsingle b hbo)
      rw [liftPrice_shared z.price hbS]
      exact le_trans (le_piW (mem_Rep.mpr ⟨hoQ, hb⟩)) (le_add_of_nonneg_right (z.price_nonneg _))
  · -- a central object: the central demand plus the opportunity prices
    have hdem := z.demand ⟨o, hoD⟩
    have hz : ∑ e' : {e // e ∈ S}, centralInc D S A ⟨o, hoD⟩ e' * z.price e' =
        ∑ e ∈ R.resources o, (if h : e ∈ S then z.price ⟨e, h⟩ else 0) := by
      rw [← sum_inc_mul hA]
      simp only [mul_dite, mul_zero]
      exact (sum_dite_mem_univ S (fun e => A o e.1 * z.price e)).symm
    have hsplit : ∑ e ∈ R.resources o, liftPrice R Q S w z.price e =
        ∑ e ∈ R.resources o, piW R.resources Q S w e +
          ∑ e ∈ R.resources o, (if h : e ∈ S then z.price ⟨e, h⟩ else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e he
      have heS := cfg.hD o hoD he
      rw [liftPrice_shared z.price heS, dif_pos heS]
    rw [hsplit, ← hz]
    unfold centralGain wred at hdem
    linarith

/-- **Result 3 (construction).** The lifted full dual. -/
noncomputable def liftDual (cfg : Config R.resources Q D S) (hQD : ∀ o, o ∈ Q ∨ o ∈ D)
    (hA : IsIncidence R A) (hw : ∀ o, 0 ≤ w o) : FiniteLP.DualFeasible A w where
  price := liftPrice R Q S w z.price
  price_nonneg := liftPrice_nonneg z hw
  demand := liftPrice_demand z cfg hQD hA hw

/-- **Result 3 (exact value).** `value (liftDual z) = B0 + Σ_{e ∈ S} z_e`. -/
theorem liftDual_value (cfg : Config R.resources Q D S) (hQD : ∀ o, o ∈ Q ∨ o ∈ D)
    (hA : IsIncidence R A) (hw : ∀ o, 0 ≤ w o) :
    FiniteLP.dualValue (liftDual z cfg hQD hA hw) = B0 R.resources Q S w + FiniteLP.dualValue z := by
  unfold FiniteLP.dualValue
  show ∑ e, liftPrice R Q S w z.price e = _
  unfold liftPrice B0
  rw [Finset.sum_add_distrib, sum_dite_mem_univ S (fun e => piW R.resources Q S w e.1 + z.price e),
    Finset.sum_add_distrib, Finset.sum_comm]
  have h1 : ∑ e : {e // e ∈ S}, piW R.resources Q S w e.1 = ∑ e ∈ S, piW R.resources Q S w e :=
    Finset.sum_coe_sort S _
  have h2 : ∑ o ∈ Z R.resources Q S, ∑ e, (if privRes R o = e then w o else 0) =
      ∑ o ∈ Z R.resources Q S, w o := by
    apply Finset.sum_congr rfl
    intro o _
    simp
  rw [h1, h2]
  ring

end DualLift

/-! ### Result 5: certificate cancellation -/

section Cancellation

variable {R : System I E} {Q D : Finset I} {S : Finset E} {w : I → K} {A : I → E → K}

/-- **Result 5.** The full gap of a lifted primal/dual pair equals the central gap `U - L`. -/
theorem lifted_gap_eq (cfg : Config R.resources Q D S) (hQD : ∀ o, o ∈ Q ∨ o ∈ D)
    (hA : IsIncidence R A) (hw : ∀ o, 0 ≤ w o)
    (u : FiniteLP.PrimalFeasible (centralInc D S A))
    (z : FiniteLP.DualFeasible (centralInc D S A) (centralGain R.resources Q D S w))
    {L U : K} (hL : FiniteLP.primalValue (centralGain R.resources Q D S w) u = L)
    (hU : FiniteLP.dualValue z = U) :
    FiniteLP.dualValue (liftDual z cfg hQD hA hw) - FiniteLP.primalValue w (extend cfg hQD hA w u) =
      U - L := by
  rw [liftDual_value z cfg hQD hA hw, extend_value cfg hQD hA hw u, hL, hU]
  ring

end Cancellation

end FractionalUnitBoundary
end PaperV
