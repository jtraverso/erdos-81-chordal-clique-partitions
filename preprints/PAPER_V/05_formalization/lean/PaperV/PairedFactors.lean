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
PROVENANCE (Paper V). Returned by Aristotle, project `547578ca-4f01-4fd0-8f60-d335886e458b` (Theorem D,
2026-09-14), homed into `PaperV/` unchanged except this header and the scrubbed docstring token; re-verified
against the pinned Mathlib by the Paper V build and aggregate gate. Provenance is not correctness.
-/
/-
TARGET FILE for Aristotle (Paper V, Theorem D — weighted completion by paired factors, finite averaging core).

Setting. `k` factors (indexed by `Fin k`), a finite set `O` of `q` candidates, bases `e : E` each lying in the
factor `factor e`, each with a list `L e ⊆ O` of valid candidates and a penalty `β e ≥ 0`. Put
`b e = q − |L e|`. A configuration chooses `s` "singleton" factors `S ⊆ Fin k` (`|S| = s`), one candidate `ι f`
for every factor and a second candidate `ι' f` for every factor `f ∉ S`, all `2k − s` chosen candidates distinct.
A base `e` is UNCOVERED if none of the candidates of its factor lies in `L e`.

Claim (Theorem D, inequality (D1)): some configuration has total uncovered penalty at most

  (s/(k·q)) · Σ_e β e · b e  +  ((k − s)/(k·q·(q − 1))) · Σ_e β e · b e · (b e − 1).

Proof idea (finite averaging, no probability library needed): average over all configurations (uniform choice
of the `s`-subset `S` and of the injection of the `2k − s` slots into `O`). For a fixed base `e` in factor `f`:
`f ∈ S` for a fraction `s/k` of configurations, and then its single candidate is uniform in `O`, so it misses
`L e` for a fraction `b e / q`; `f ∉ S` for a fraction `(k − s)/k`, and then its two candidates form a uniform
ordered pair of DISTINCT elements of `O`, both outside `L e` for a fraction `b e (b e − 1)/(q (q − 1))`.
Summing `β e` times these fractions gives the expected penalty; some configuration is at most the expectation.
Any correct proof is acceptable (double counting over the finite set of configurations, or Mathlib's finite
uniform probability). Hypotheses: `1 ≤ k`, `2 ≤ q`, `s ≤ k`, `2k − s ≤ q`, `|O| = q`, `L e ⊆ O`, `0 ≤ β e`.

Must have no incomplete declarations with `#print axioms` = [propext, Classical.choice, Quot.sound]. Do not change the statement.
-/
module

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Data.Finset.Prod

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

public import Mathlib.Algebra.Order.Field.Rat

@[expose] public section

namespace PaperV
namespace PairedFactors

variable {O E : Type*} [Fintype O] [DecidableEq O] [Fintype E] [DecidableEq E]

/-- Number of INVALID candidates of the base `e`. -/
def bad (q : ℕ) (L : E → Finset O) (e : E) : ℕ := q - (L e).card

/-- `e` is uncovered by the configuration `(S, ι, ι')`. -/
def Uncovered {k : ℕ} (factor : E → Fin k) (L : E → Finset O) (S : Finset (Fin k)) (ι ι' : Fin k → O)
    (e : E) : Prop :=
  ι (factor e) ∉ L e ∧ (factor e ∉ S → ι' (factor e) ∉ L e)

instance {k : ℕ} (factor : E → Fin k) (L : E → Finset O) (S : Finset (Fin k)) (ι ι' : Fin k → O) (e : E) :
    Decidable (Uncovered factor L S ι ι' e) := by unfold Uncovered; infer_instance

/-!
### Auxiliary counting lemmas for the symmetric group

The averaging is carried out over the finite set of pairs `(σ, π)` with `σ` a permutation of the
factors and `π` a permutation of the candidate set `O`; the configuration attached to `(σ, π)` uses
`σ` to select which factors are singletons and `π` to move a fixed system of `2k - s` distinct
"slots" around `O`.  The two lemmas below compute, without any division, how often a permutation
sends a given point (resp. a given ordered pair of distinct points) into a prescribed set.
-/

open Finset Equiv

section PermCounting

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- All fibers of `π ↦ π x` have the same cardinality. -/
lemma perm_fiber_card_eq (x y z : α) :
    (univ.filter fun π : Perm α => π x = y).card = (univ.filter fun π : Perm α => π x = z).card := by
  refine Finset.card_nbij' (fun π => Equiv.swap y z * π) (fun π => Equiv.swap y z * π) ?_ ?_ ?_ ?_
  · intro π hπ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hπ ⊢
    simp [Equiv.Perm.mul_apply, hπ]
  · intro π hπ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hπ ⊢
    simp [Equiv.Perm.mul_apply, hπ]
  · intro π _; simp [← mul_assoc]
  · intro π _; simp [← mul_assoc]

/-- A uniformly chosen permutation sends `x` into `B` with "probability" `|B| / |α|`. -/
lemma perm_count_single (x : α) (B : Finset α) :
    (univ.filter fun π : Perm α => π x ∈ B).card * Fintype.card α
      = B.card * Fintype.card (Perm α) := by
  set n := (univ.filter fun π : Perm α => π x = x).card with hn
  have h1 : ∀ y : α, (univ.filter fun π : Perm α => π x = y).card = n := fun y =>
    perm_fiber_card_eq x y x
  have hB : (univ.filter fun π : Perm α => π x ∈ B).card = B.card * n := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun π : Perm α => π x) (t := B) (by intro π hπ; simpa using hπ)]
    rw [Finset.sum_congr rfl (fun y hy => ?_), Finset.sum_const, smul_eq_mul]
    have hfe : (univ.filter fun π : Perm α => π x ∈ B).filter (fun π => π x = y)
        = (univ.filter fun π : Perm α => π x = y) := by
      ext π
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ hy, h⟩⟩
    rw [hfe]; exact h1 y
  have htot : Fintype.card (Perm α) = Fintype.card α * n := by
    rw [← Finset.card_univ (α := Perm α), Finset.card_eq_sum_card_fiberwise
      (f := fun π : Perm α => π x) (t := univ) (by intro π _; simp)]
    rw [Finset.sum_congr rfl (fun y _ => h1 y), Finset.sum_const, smul_eq_mul, Finset.card_univ]
  rw [hB, htot]; ring

/-- The action of the symmetric group on ordered pairs of distinct points is transitive. -/
lemma perm_exists_map_pair {α : Type*} [DecidableEq α] (x y u v : α) (hxy : x ≠ y)
    (huv : u ≠ v) : ∃ τ : Perm α, τ x = u ∧ τ y = v := by
  have hyu : Equiv.swap x u y ≠ u := by
    intro h
    have h' := congrArg (Equiv.swap x u) h
    rw [Equiv.swap_apply_self, Equiv.swap_apply_right] at h'
    exact hxy h'.symm
  refine ⟨Equiv.swap (Equiv.swap x u y) v * Equiv.swap x u, ?_, ?_⟩
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hyu) huv
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

/-- All fibers of `π ↦ (π x, π y)` over ordered pairs of distinct points have the same
cardinality. -/
lemma perm_fiber_card_eq₂ (x y u v : α) (hxy : x ≠ y) (huv : u ≠ v) :
    (univ.filter fun π : Perm α => π x = u ∧ π y = v).card
      = (univ.filter fun π : Perm α => π x = x ∧ π y = y).card := by
  obtain ⟨τ, hτ1, hτ2⟩ := perm_exists_map_pair x y u v hxy huv
  refine (Finset.card_nbij' (fun π => τ * π) (fun π => τ⁻¹ * π) ?_ ?_ ?_ ?_).symm
  · intro π hπ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hπ ⊢
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hπ.1, hπ.2]
    exact ⟨hτ1, hτ2⟩
  · intro π hπ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hπ ⊢
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hπ.1, hπ.2, ← hτ1, ← hτ2]
    simp
  · intro π _; simp [← mul_assoc]
  · intro π _; simp [← mul_assoc]

/-- A uniformly chosen permutation sends both points of a fixed pair of distinct points into `B`
with "probability" `|B|(|B| - 1) / (|α|(|α| - 1))`. -/
lemma perm_count_pair (x y : α) (hxy : x ≠ y) (B : Finset α) :
    (univ.filter fun π : Perm α => π x ∈ B ∧ π y ∈ B).card
        * (Fintype.card α * Fintype.card α - Fintype.card α)
      = (B.card * B.card - B.card) * Fintype.card (Perm α) := by
  set m := (univ.filter fun π : Perm α => π x = x ∧ π y = y).card with hm
  have key : ∀ C : Finset α,
      (univ.filter fun π : Perm α => π x ∈ C ∧ π y ∈ C).card = C.offDiag.card * m := by
    intro C
    rw [Finset.card_eq_sum_card_fiberwise (f := fun π : Perm α => (π x, π y)) (t := C.offDiag)
      (by
        intro π hπ
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hπ
        simp only [Finset.mem_coe, Finset.mem_offDiag]
        exact ⟨hπ.1, hπ.2, fun h => hxy ((Equiv.injective π) h)⟩)]
    rw [Finset.sum_congr rfl (fun p hp => ?_), Finset.sum_const, smul_eq_mul]
    rw [Finset.mem_offDiag] at hp
    have hfe : ((univ.filter fun π : Perm α => π x ∈ C ∧ π y ∈ C).filter
        (fun π => (π x, π y) = p)) = (univ.filter fun π : Perm α => π x = p.1 ∧ π y = p.2) := by
      ext π
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
      exact ⟨fun h => h.2, fun ⟨h1, h2⟩ => ⟨⟨h1 ▸ hp.1, h2 ▸ hp.2.1⟩, h1, h2⟩⟩
    rw [hfe]
    exact perm_fiber_card_eq₂ x y p.1 p.2 hxy hp.2.2
  have h2 : Fintype.card (Perm α) = (Fintype.card α * Fintype.card α - Fintype.card α) * m := by
    have h := key univ
    rw [Finset.offDiag_card, Finset.card_univ] at h
    simpa using h
  rw [key B, Finset.offDiag_card, h2]; ring

end PermCounting

/-- A system of `2k - s` distinct "slots" in `O`: a primary candidate `pt i` for every factor
index `i`, and a secondary candidate `pt' i` for the indices `i` with `s ≤ i`, all distinct. -/
lemma exists_slots {O : Type*} [Fintype O] (k q s : ℕ) (hs : s ≤ k)
    (hslots : 2 * k - s ≤ q) (hO : Fintype.card O = q) :
    ∃ pt pt' : Fin k → O, Function.Injective pt ∧
      (∀ i j : Fin k, s ≤ i.1 → pt' i ≠ pt j) ∧
      (∀ i j : Fin k, s ≤ i.1 → s ≤ j.1 → pt' i = pt' j → i = j) := by
  obtain ⟨φ⟩ : Nonempty (Fin (2 * k - s) ↪ O) :=
    Function.Embedding.nonempty_of_card_le (by simpa [hO] using hslots)
  have h1 : ∀ i : Fin k, i.1 < 2 * k - s := fun i => by have := i.isLt; omega
  have h2 : ∀ i : Fin k, (if s ≤ i.1 then k + (i.1 - s) else i.1) < 2 * k - s := by
    intro i; have := i.isLt; split <;> omega
  refine ⟨fun i => φ ⟨i.1, h1 i⟩, fun i => φ ⟨_, h2 i⟩, ?_, ?_, ?_⟩
  · intro i j h
    exact Fin.ext (by simpa using congrArg Fin.val (φ.injective h))
  · intro i j hi h
    have h3 := congrArg Fin.val (φ.injective h)
    simp only [if_pos hi] at h3
    have := j.isLt; omega
  · intro i j hi hj h
    have h3 := congrArg Fin.val (φ.injective h)
    simp only [if_pos hi, if_pos hj] at h3
    have := i.isLt; have := j.isLt
    exact Fin.ext (by omega)

/-- The `s`-element set of "singleton" factor indices, transported by a permutation `σ`. -/
lemma card_filter_lt_perm {k s : ℕ} (hs : s ≤ k) (σ : Equiv.Perm (Fin k)) :
    (univ.filter fun f : Fin k => (σ f).1 < s).card = s := by
  have hA : (univ.filter fun i : Fin k => i.1 < s).card = s := by
    refine (Finset.card_bij (fun i _ => (i : Fin k).1) ?_ ?_ ?_).trans (Finset.card_range s)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simpa using hi
    · intro i _ j _ h
      exact Fin.ext h
    · intro v hv
      simp only [Finset.mem_range] at hv
      exact ⟨⟨v, lt_of_lt_of_le hv hs⟩, by simp [hv], rfl⟩
  refine Eq.trans ?_ hA
  refine Finset.card_nbij' (fun f => σ f) (fun i => σ.symm i) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hf ⊢
    exact hf
  · intro i hi
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hi ⊢
    simpa using hi
  · intro f _
    simp
  · intro i _
    simp

/-- **Theorem D (finite averaging core).** -/
theorem exists_paired_completion (k q s : ℕ) (hk : 1 ≤ k) (hq : 2 ≤ q) (hs : s ≤ k) (hslots : 2 * k - s ≤ q)
    (hO : Fintype.card O = q) (factor : E → Fin k) (L : E → Finset O) (β : E → ℚ) (hβ : ∀ e, 0 ≤ β e) :
    ∃ (S : Finset (Fin k)) (ι ι' : Fin k → O),
      S.card = s ∧ Function.Injective ι ∧ Set.InjOn ι' (↑Sᶜ : Set (Fin k)) ∧
      (∀ f, f ∉ S → ∀ g, ι' f ≠ ι g) ∧
      ∑ e ∈ Finset.univ.filter (Uncovered factor L S ι ι'), β e ≤
        ((s : ℚ) / (k * q)) * ∑ e, β e * (bad q L e : ℚ) +
        (((k : ℚ) - s) / (k * q * (q - 1))) * ∑ e, β e * (bad q L e : ℚ) * ((bad q L e : ℚ) - 1) := by
  obtain ⟨pt, pt', hptinj, hne, hpt'inj⟩ := exists_slots (O := O) k q s hs hslots hO
  set K : ℕ := Fintype.card (Equiv.Perm (Fin k)) with hK
  set P : ℕ := Fintype.card (Equiv.Perm O) with hP
  set Sof : Equiv.Perm (Fin k) → Finset (Fin k) :=
    fun σ => univ.filter (fun f => (σ f).1 < s) with hSof
  set Iof : Equiv.Perm (Fin k) × Equiv.Perm O → Fin k → O := fun c f => c.2 (pt (c.1 f)) with hIof
  set I'of : Equiv.Perm (Fin k) × Equiv.Perm O → Fin k → O := fun c f => c.2 (pt' (c.1 f)) with hI'of
  set R : ℚ := ((s : ℚ) / (k * q)) * ∑ e, β e * (bad q L e : ℚ) +
        (((k : ℚ) - s) / (k * q * (q - 1))) * ∑ e, β e * (bad q L e : ℚ) * ((bad q L e : ℚ) - 1)
    with hR
  set F : Equiv.Perm (Fin k) × Equiv.Perm O → ℚ := fun c =>
      ∑ e ∈ univ.filter (Uncovered factor L (Sof c.1) (Iof c) (I'of c)), β e with hF
  -- basic numerical facts
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq1 : (q : ℚ) - 1 ≠ 0 := sub_ne_zero.mpr (by
    have h2q : (2 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
    intro h; rw [h] at h2q; norm_num at h2q)
  have hsubcast : ∀ n : ℕ, ((n * n - n : ℕ) : ℚ) = (n : ℚ) * ((n : ℚ) - 1) := by
    intro n
    have hle : n ≤ n * n := by nlinarith [Nat.zero_le n]
    rw [Nat.cast_sub hle]; push_cast; ring
  -- Step 1: exchange the order of summation
  have hstep1 : ∑ c : Equiv.Perm (Fin k) × Equiv.Perm O, F c
      = ∑ e : E, β e * ((univ.filter fun c : Equiv.Perm (Fin k) × Equiv.Perm O =>
          Uncovered factor L (Sof c.1) (Iof c) (I'of c) e).card : ℚ) := by
    simp only [hF, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- Step 2: the count for a fixed base
  have hstep2 : ∀ e : E, ((univ.filter fun c : Equiv.Perm (Fin k) × Equiv.Perm O =>
      Uncovered factor L (Sof c.1) (Iof c) (I'of c) e).card : ℚ)
      = (K : ℚ) * P * ((s : ℚ) / (k * q) * (bad q L e : ℚ)
          + ((k : ℚ) - s) / (k * q * (q - 1)) * (bad q L e : ℚ) * ((bad q L e : ℚ) - 1)) := by
    intro e
    set f₀ : Fin k := factor e with hf₀
    set B : Finset O := (L e)ᶜ with hBdef
    have hbB : (B.card : ℚ) = (bad q L e : ℚ) := by
      rw [hBdef, Finset.card_compl, hO, bad]
    have hpairN : (univ.filter fun c : Equiv.Perm (Fin k) × Equiv.Perm O =>
        Uncovered factor L (Sof c.1) (Iof c) (I'of c) e).card
        = ∑ σ : Equiv.Perm (Fin k), (univ.filter fun π : Equiv.Perm O =>
            Uncovered factor L (Sof σ) (Iof (σ, π)) (I'of (σ, π)) e).card := by
      simp only [Finset.card_filter]
      rw [Fintype.sum_prod_type]
    have hsigma : ∀ σ : Equiv.Perm (Fin k),
        ((univ.filter fun π : Equiv.Perm O =>
            Uncovered factor L (Sof σ) (Iof (σ, π)) (I'of (σ, π)) e).card : ℚ)
          = if (σ f₀).1 < s then (bad q L e : ℚ) * P / q
            else (bad q L e : ℚ) * ((bad q L e : ℚ) - 1) * P / (q * ((q : ℚ) - 1)) := by
      intro σ
      by_cases hcase : (σ f₀).1 < s
      · rw [if_pos hcase]
        have hfilt : (univ.filter fun π : Equiv.Perm O =>
            Uncovered factor L (Sof σ) (Iof (σ, π)) (I'of (σ, π)) e)
            = univ.filter fun π : Equiv.Perm O => π (pt (σ f₀)) ∈ B := by
          ext π
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Uncovered, hIof, hI'of, hSof,
            hBdef, Finset.mem_compl, ← hf₀]
          exact ⟨fun h => h.1, fun h => ⟨h, fun hcon => absurd hcase (by simpa using hcon)⟩⟩
        rw [hfilt, eq_div_iff hq0]
        have hcnt := perm_count_single (α := O) (pt (σ f₀)) B
        rw [hO, ← hP] at hcnt
        have : ((univ.filter fun π : Equiv.Perm O => π (pt (σ f₀)) ∈ B).card : ℚ) * (q : ℚ)
            = (B.card : ℚ) * (P : ℚ) := by exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) hcnt
        rw [this, hbB]
      · rw [if_neg hcase]
        have hxy : pt' (σ f₀) ≠ pt (σ f₀) := hne _ _ (by omega)
        have hfilt : (univ.filter fun π : Equiv.Perm O =>
            Uncovered factor L (Sof σ) (Iof (σ, π)) (I'of (σ, π)) e)
            = univ.filter fun π : Equiv.Perm O =>
                π (pt (σ f₀)) ∈ B ∧ π (pt' (σ f₀)) ∈ B := by
          ext π
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Uncovered, hIof, hI'of, hSof,
            hBdef, Finset.mem_compl, ← hf₀]
          exact ⟨fun h => ⟨h.1, h.2 (by simpa using hcase)⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩
        rw [hfilt, eq_div_iff (mul_ne_zero hq0 hq1)]
        have hcnt := perm_count_pair (α := O) (pt (σ f₀)) (pt' (σ f₀)) (Ne.symm hxy) B
        rw [hO, ← hP] at hcnt
        have hcast : ((univ.filter fun π : Equiv.Perm O =>
              π (pt (σ f₀)) ∈ B ∧ π (pt' (σ f₀)) ∈ B).card : ℚ) * ((q : ℚ) * ((q : ℚ) - 1))
            = (B.card : ℚ) * ((B.card : ℚ) - 1) * (P : ℚ) := by
          have := congrArg (fun n : ℕ => (n : ℚ)) hcnt
          simp only [Nat.cast_mul] at this
          rw [hsubcast q, hsubcast B.card] at this
          rw [← this]
        rw [hcast, hbB]
    rw [hpairN]
    push_cast
    rw [Finset.sum_congr rfl (fun σ _ => hsigma σ), Finset.sum_ite, Finset.sum_const,
      Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hN1 : (univ.filter fun σ : Equiv.Perm (Fin k) => (σ f₀).1 < s).card * k = s * K := by
      have hcnt := perm_count_single (α := Fin k) f₀ (univ.filter fun i : Fin k => i.1 < s)
      rw [Fintype.card_fin, ← hK] at hcnt
      have hA : (univ.filter fun i : Fin k => i.1 < s).card = s := by
        refine (Finset.card_bij (fun i _ => (i : Fin k).1) ?_ ?_ ?_).trans (Finset.card_range s)
        · intro i hi
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] using hi
        · intro i _ j _ h
          exact Fin.ext h
        · intro v hv
          simp only [Finset.mem_range] at hv
          exact ⟨⟨v, lt_of_lt_of_le hv hs⟩, by simp [hv], rfl⟩
      rw [hA] at hcnt
      have hset : (univ.filter fun σ : Equiv.Perm (Fin k) => (σ f₀).1 < s)
          = (univ.filter fun σ : Equiv.Perm (Fin k) =>
              σ f₀ ∈ (univ.filter fun i : Fin k => i.1 < s)) := by
        ext σ; simp
      rw [hset]; exact hcnt
    have hN12 : (univ.filter fun σ : Equiv.Perm (Fin k) => (σ f₀).1 < s).card
        + (univ.filter fun σ : Equiv.Perm (Fin k) => ¬((σ f₀).1 < s)).card = K := by
      rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, hK]
    have hN1' : ((univ.filter fun σ : Equiv.Perm (Fin k) => (σ f₀).1 < s).card : ℚ)
        = (s : ℚ) * K / k := by
      rw [eq_div_iff hk0]; exact_mod_cast hN1
    have hN2' : ((univ.filter fun σ : Equiv.Perm (Fin k) => ¬((σ f₀).1 < s)).card : ℚ)
        = (K : ℚ) - (s : ℚ) * K / k := by
      have h := congrArg (fun n : ℕ => (n : ℚ)) hN12
      push_cast at h
      rw [← hN1']
      linarith
    rw [hN1', hN2']
    field_simp
  -- Step 3: the average equals the right-hand side, so some configuration is below it
  have hsum : ∑ c : Equiv.Perm (Fin k) × Equiv.Perm O, F c = ((K : ℚ) * P) * R := by
    rw [hstep1, hR]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hstep2 e]; ring
  have hcardu : (Finset.univ : Finset (Equiv.Perm (Fin k) × Equiv.Perm O)).card = K * P := by
    rw [Finset.card_univ, Fintype.card_prod, hK, hP]
  obtain ⟨c, -, hc⟩ := Finset.exists_le_of_sum_le (f := F) (g := fun _ => R)
    (Finset.univ_nonempty) (by
      rw [hsum, Finset.sum_const, hcardu]
      ring_nf
      exact le_refl _)
  refine ⟨Sof c.1, Iof c, I'of c, ?_, ?_, ?_, ?_, hc⟩
  · exact card_filter_lt_perm hs c.1
  · intro f g h
    exact c.1.injective (hptinj (c.2.injective h))
  · intro f hf g hg h
    simp only [Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe, hSof, Finset.mem_filter,
      Finset.mem_univ, true_and, not_lt] at hf hg
    exact c.1.injective (hpt'inj _ _ hf hg (c.2.injective h))
  · intro f hf g
    simp only [hSof, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hf
    intro h
    exact hne (c.1 f) (c.1 g) hf (c.2.injective h)

end PairedFactors
end PaperV
