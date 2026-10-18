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

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Finite cube-polytope value functions. This module makes no identification
with a WSNF instance or with a particular list of candidate certificates. -/
@[expose] public section
namespace PaperV.FiniteValueStability
open Finset
variable {I : Type*} [Fintype I]

noncomputable def dot (c z : I → ℝ) : ℝ := ∑ i, c i * z i
noncomputable def l1 (c : I → ℝ) : ℝ := ∑ i, |c i|
noncomputable def minimum (A : Finset (I → ℝ)) (hA : A.Nonempty) (c : I → ℝ) : ℝ :=
  A.inf' hA (dot c)

theorem minimum_le (A : Finset (I → ℝ)) (hA : A.Nonempty) (c : I → ℝ)
    {v : I → ℝ} (hv : v ∈ A) : minimum A hA c ≤ dot c v :=
  Finset.inf'_le (dot c) hv

theorem exists_minimizer (A : Finset (I → ℝ)) (hA : A.Nonempty) (c : I → ℝ) :
    ∃ v ∈ A, minimum A hA c = dot c v :=
  Finset.exists_mem_eq_inf' hA (dot c)

theorem dot_sub (c d z : I → ℝ) : dot (c - d) z = dot c z - dot d z := by
  simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem dot_l1_bound (c z : I → ℝ) (hz : ∀ i, |z i| ≤ 1) : |dot c z| ≤ l1 c := by
  calc
    |dot c z| ≤ ∑ i, |c i * z i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ l1 c := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hz i) (abs_nonneg _)).trans_eq (mul_one _)

theorem sensitivity (A : Finset (I → ℝ)) (hA : A.Nonempty)
    (hCube : ∀ v ∈ A, ∀ i, 0 ≤ v i ∧ v i ≤ 1) (c d : I → ℝ) :
    |minimum A hA c - minimum A hA d| ≤ l1 (c - d) := by
  have hone (a b : I → ℝ) : minimum A hA a - minimum A hA b ≤ l1 (a - b) := by
    obtain ⟨v, hv, heq⟩ := exists_minimizer A hA b
    have habs := dot_l1_bound (a - b) v (fun i => by
      rw [abs_of_nonneg (hCube v hv i).1]; exact (hCube v hv i).2)
    rw [dot_sub] at habs
    have hle := minimum_le A hA a hv
    have := (abs_le.mp habs).2
    linarith
  have hsym : l1 (d - c) = l1 (c - d) := by
    unfold l1
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply, abs_sub_comm]
  exact abs_le.mpr ⟨by have := hone d c; rw [hsym] at this; linarith, hone c d⟩

noncomputable def dotLinear (c : I → ℝ) : (I → ℝ) →ₗ[ℝ] ℝ where
  toFun := dot c
  map_add' x y := by simp [dot, mul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    change (∑ i, c i * (r * x i)) = r * ∑ i, c i * x i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _; ring

/-- The finite minimum is the actual minimum over the convex hull. -/
theorem convexHull_minimum (A : Finset (I → ℝ)) (hA : A.Nonempty) (c : I → ℝ) :
    (∀ z ∈ convexHull ℝ (A : Set (I → ℝ)), minimum A hA c ≤ dot c z) ∧
      ∃ v ∈ convexHull ℝ (A : Set (I → ℝ)), minimum A hA c = dot c v := by
  constructor
  · have hs : (A : Set (I → ℝ)) ⊆
        (dotLinear c) ⁻¹' Set.Ici (minimum A hA c) := by
      intro v hv; exact minimum_le A hA c hv
    exact convexHull_min hs ((convex_Ici _).linear_preimage (dotLinear c))
  · obtain ⟨v, hv, heq⟩ := exists_minimizer A hA c
    exact ⟨v, subset_convexHull ℝ (A : Set (I → ℝ)) hv, heq⟩

theorem continuous_dot (v : I → ℝ) : Continuous (fun c => dot c v) := by
  unfold dot
  apply continuous_finsetSum
  intro i _
  exact (continuous_apply i).mul continuous_const

theorem continuous_minimum (A : Finset (I → ℝ)) (hA : A.Nonempty) :
    Continuous (fun c => minimum A hA c) := by
  classical
  induction hA using Finset.Nonempty.cons_induction with
  | singleton v => simpa [minimum] using continuous_dot v
  | cons v S hnot hs ih =>
    simpa only [minimum, Finset.inf'_cons hs] using (continuous_dot v).inf ih

/-- Density is an explicit hypothesis. Only the value formula is extended. -/
theorem dense_extension {Θ : Type*} [TopologicalSpace Θ]
    (A R : Finset (I → ℝ)) (hA : A.Nonempty) (hR : R.Nonempty)
    (c : Θ → I → ℝ) (hc : Continuous c) (D : Set Θ) (hD : Dense D)
    (heq : ∀ θ ∈ D, minimum A hA (c θ) = minimum R hR (c θ)) :
    ∀ θ, minimum A hA (c θ) = minimum R hR (c θ) := by
  have h := Continuous.ext_on hD ((continuous_minimum A hA).comp hc)
    ((continuous_minimum R hR).comp hc) heq
  intro θ
  exact congrFun h θ

theorem minimum_subset (A R : Finset (I → ℝ)) (hA : A.Nonempty)
    (hR : R.Nonempty) (hsub : R ⊆ A) (c : I → ℝ) :
    minimum A hA c ≤ minimum R hR c := by
  exact Finset.le_inf' hR _ (fun v hv => minimum_le A hA c (hsub hv))

/-- The hypothesis on the dense set is the existence of a genuine minimizing
candidate in R, rather than assuming the final value identity. -/
theorem dense_minimizers {Θ : Type*} [TopologicalSpace Θ]
    (A R : Finset (I → ℝ)) (hA : A.Nonempty) (hR : R.Nonempty) (hsub : R ⊆ A)
    (c : Θ → I → ℝ) (hc : Continuous c) (D : Set Θ) (hD : Dense D)
    (hmin : ∀ θ ∈ D, ∃ v ∈ R, ∀ z ∈ A, dot (c θ) v ≤ dot (c θ) z) :
    ∀ θ, minimum A hA (c θ) = minimum R hR (c θ) := by
  apply dense_extension A R hA hR c hc D hD
  intro θ hθ
  obtain ⟨v, hv, hbest⟩ := hmin θ hθ
  apply le_antisymm (minimum_subset A R hA hR hsub (c θ))
  have hb : dot (c θ) v ≤ minimum A hA (c θ) := Finset.le_inf' hA _ hbest
  exact (minimum_le R hR (c θ) hv).trans hb

def UniqueMinimizer (A : Finset (I → ℝ)) (c v : I → ℝ) : Prop :=
  v ∈ A ∧ ∀ z ∈ A, z ≠ v → dot c v < dot c z

/-- A positive strict gap exists whenever there are competing vertices. -/
theorem exists_positive_gap (A : Finset (I → ℝ)) (c v : I → ℝ)
    (hv : UniqueMinimizer A c v) (hne : (A.erase v).Nonempty) :
    ∃ δ > 0, ∀ z ∈ A, z ≠ v → δ ≤ dot c z - dot c v := by
  classical
  let δ := (A.erase v).inf' hne (fun z => dot c z - dot c v)
  refine ⟨δ, ?_, ?_⟩
  · apply (Finset.lt_inf'_iff hne).mpr
    intro z hz
    have hm := Finset.mem_erase.mp hz
    exact sub_pos.mpr (hv.2 z hm.2 hm.1)
  · intro z hz hne
    exact Finset.inf'_le _ (Finset.mem_erase.mpr ⟨hne, hz⟩)

theorem unique_minimizer_stability (A : Finset (I → ℝ))
    (hCube : ∀ v ∈ A, ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (c d v : I → ℝ) (hv : v ∈ A) (δ : ℝ)
    (hgap : ∀ z ∈ A, z ≠ v → δ ≤ dot c z - dot c v)
    (hclose : l1 (d - c) < δ) : UniqueMinimizer A d v := by
  refine ⟨hv, ?_⟩
  intro z hz hne
  have hb : ∀ i, |z i - v i| ≤ 1 := by
    intro i
    have hvb := hCube v hv i
    have hzb := hCube z hz i
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have he := dot_l1_bound (d - c) (z - v) hb
  have hid : dot (d - c) (z - v) =
      (dot d z - dot d v) - (dot c z - dot c v) := by
    simp only [dot, Pi.sub_apply]
    simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib]
  rw [hid] at he
  have hg := hgap z hz hne
  have := (abs_le.mp he).1
  linarith

theorem dot_combination {J : Type*} [Fintype J] (c : I → ℝ) (p : J → ℝ)
    (z : J → I → ℝ) : dot c (∑ j, p j • z j) = ∑ j, p j * dot c (z j) := by
  classical
  simp only [dot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Uniqueness on the finite generating set implies uniqueness on its actual
convex hull, not only uniqueness among the candidate labels. -/
theorem unique_on_convexHull (A : Finset (I → ℝ)) (c v : I → ℝ)
    (hv : UniqueMinimizer A c v) {z : I → ℝ}
    (hz : z ∈ convexHull ℝ (A : Set (I → ℝ))) (heq : dot c z = dot c v) : z = v := by
  classical
  obtain ⟨J, instJ, p, x, hp, hp1, hx, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hz
  letI := instJ
  have hbase (j : J) : dot c v ≤ dot c (x j) := by
    by_cases he : x j = v
    · simp [he]
    · exact (hv.2 (x j) (hx j) he).le
  have hzero : ∑ j, p j * (dot c (x j) - dot c v) = 0 := by
    have hb : ∑ j, p j * dot c (x j) = dot c z := by
      rw [← dot_combination, hsum]
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hp1, one_mul, hb, heq, sub_self]
  have hterm : ∀ j, p j * (dot c (x j) - dot c v) = 0 := by
    have hall : ∀ j ∈ (univ : Finset J), 0 ≤ p j * (dot c (x j) - dot c v) :=
      fun j _ => mul_nonneg (hp j) (sub_nonneg.mpr (hbase j))
    exact fun j => (Finset.sum_eq_zero_iff_of_nonneg hall).mp hzero j (mem_univ j)
  have hxv : ∀ j, p j • x j = p j • v := by
    intro j
    by_cases h0 : p j = 0
    · simp [h0]
    · have hd : dot c (x j) = dot c v := sub_eq_zero.mp ((mul_eq_zero.mp (hterm j)).resolve_left h0)
      have he : x j = v := by
        by_contra hn
        have := hv.2 (x j) (hx j) hn
        linarith
      rw [he]
  calc
    z = ∑ j, p j • x j := hsum.symm
    _ = ∑ j, p j • v := Finset.sum_congr rfl (fun j _ => hxv j)
    _ = v := by rw [← Finset.sum_smul, hp1, one_smul]

theorem stable_convexHull_minimizer (A : Finset (I → ℝ))
    (hCube : ∀ v ∈ A, ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (c d v : I → ℝ) (hv : v ∈ A) (δ : ℝ)
    (hgap : ∀ z ∈ A, z ≠ v → δ ≤ dot c z - dot c v)
    (hclose : l1 (d - c) < δ) :
    (∀ z ∈ convexHull ℝ (A : Set (I → ℝ)), dot d v ≤ dot d z) ∧
    (∀ z ∈ convexHull ℝ (A : Set (I → ℝ)), dot d z = dot d v → z = v) := by
  have huv := unique_minimizer_stability A hCube c d v hv δ hgap hclose
  have hA : A.Nonempty := ⟨v, hv⟩
  have heq : minimum A hA d = dot d v := by
    apply le_antisymm (minimum_le A hA d hv)
    apply Finset.le_inf' hA
    intro z hz
    by_cases h : z = v
    · simp [h]
    · exact (huv.2 z hz h).le
  refine ⟨?_, ?_⟩
  · intro z hz
    rw [← heq]
    exact (convexHull_minimum A hA d).1 z hz
  · intro z hz hval
    exact unique_on_convexHull A d v huv hz hval

end PaperV.FiniteValueStability
