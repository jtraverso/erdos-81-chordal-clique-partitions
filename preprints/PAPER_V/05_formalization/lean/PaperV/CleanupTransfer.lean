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
Paper IV/V — Cleanup + colourability transfer with an explicit certificate (C3 core) and the
owned-union lemma (C5).

C3 core (`cleanup_transfer_cert`). Scale a fractional packing to a multiset `X`, discard every object
of a set `Dset` (the objects touching a bad resource set `B`), keep the residual multiset `X₀`, and
supply a certificate `Z` whose deletion makes `H[X₀]` `q`-colourable. Then some feasible family `S`
has  `|X|_w ≤ q · w(S) + w(Z) + Σ_{o∈Dset} w(o)·X(o)`.  Combined with V-CLEAN
(`FiniteLP.discarded_value_le`, cast through `discarded_scaled_le`) the last term is ≤ q·M·|B|; the
manuscript's `|𝒫| ≤ e(G) − V(x) + 5|B| + w(Z)/d` is the K₂-completion reading of this inequality.

C5 (`ResFeasible_biUnion_of_owner`, `wsum_biUnion_of_owner`). Families `P c` of objects whose
resources all have owner `c` (a function on physical resources) form, jointly, a feasible family, with
additive size/weight. Objects with an empty resource set are excluded by hypothesis.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.WeightedTransfer
public import PaperV.UnitBoundaryCompletion
public import PaperV.RationalLP

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set

@[expose] public section

open Finset

namespace PaperV

/-! ### C3 core -/

section Cleanup

variable (C : ConflictSystem)

/-- The residual multiset after discarding the objects in `Dset`. -/
def restrictOut (X : C.O → ℕ) (Dset : Finset C.O) : C.O → ℕ :=
  fun o => if o ∈ Dset then 0 else X o

theorem wMultSize_restrictOut (w X : C.O → ℕ) (Dset : Finset C.O) :
    wMultSize C w (restrictOut C X Dset) + ∑ o ∈ Dset, w o * X o = wMultSize C w X := by
  classical
  unfold wMultSize restrictOut
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun o => o ∈ Dset) (fun o => w o * X o)]
  have h1 : ∑ o ∈ Finset.univ.filter (fun o => o ∈ Dset), w o * X o = ∑ o ∈ Dset, w o * X o := by
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext o; simp
  have h2 : ∑ o, w o * (if o ∈ Dset then 0 else X o) =
      ∑ o ∈ Finset.univ.filter (fun o => ¬ o ∈ Dset), w o * X o := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro o _
    split_ifs <;> simp
  rw [h2, h1]; ring

/-- **C3 core.** With certificate `Z` for the residual multiset, some feasible family absorbs all
but `w(Z)` of the residual weight, up to the factor `q`. -/
theorem cleanup_transfer_cert (w X : C.O → ℕ) (Dset : Finset C.O) (q : ℕ) (hq : 1 ≤ q)
    (Z : Finset (Copies C (restrictOut C X Dset)))
    (hZ : IsDefectSet (Hgraph C (restrictOut C X Dset)) q Z) :
    wMultSize C w X ≤ q * wNu C w + (∑ c ∈ Z, copyWeight C w c) + ∑ o ∈ Dset, w o * X o := by
  have h := transfer_q_weighted_cert C w (restrictOut C X Dset) q hq Z hZ
  have hs := wMultSize_restrictOut C w X Dset
  omega

end Cleanup

/-! ### Cast bridge to V-CLEAN: the discarded scaled weight is at most `q·M·|B|` -/

section ScaledCleanup

variable {I E : Type*} [Fintype I] [Fintype E]
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- If `X i = q · x_i` (scaled fractional weights, `x` primal-feasible) and `w i = g i`, the discarded
scaled weight `Σ_{i∈D} w i · X i` is at most `q · M · |B|` for objects `D` touching `B` with gain ≤ `M`. -/
theorem discarded_scaled_le {A : I → E → K} {g : I → K} (p : FiniteLP.PrimalFeasible A)
    (D : Finset I) (B : Finset E) (M : K) (q : ℕ) (w X : I → ℕ)
    (hA : ∀ i e, 0 ≤ A i e) (hM : 0 ≤ M)
    (hg : ∀ i ∈ D, g i ≤ M) (hcover : ∀ i ∈ D, 1 ≤ ∑ e ∈ B, A i e)
    (hX : ∀ i, (X i : K) = q * p.weight i) (hw : ∀ i, (w i : K) = g i) :
    ((∑ i ∈ D, w i * X i : ℕ) : K) ≤ q * (M * (B.card : K)) := by
  have h := FiniteLP.discarded_value_le p D B M hA hM hg hcover
  have hcast : ((∑ i ∈ D, w i * X i : ℕ) : K) = q * ∑ i ∈ D, g i * p.weight i := by
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hw i, hX i]; ring
  rw [hcast]
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg q)

end ScaledCleanup

/-! ### C5 — owned union -/

namespace UnitBoundary

variable {α R Cl : Type*} [DecidableEq α] [DecidableEq R] [Fintype Cl] [DecidableEq Cl]

/-- Every resource of an object of family `c` has owner `c`. -/
def Owned (res : α → Finset R) (P : Cl → Finset α) (owner : R → Cl) : Prop :=
  ∀ c, ∀ o ∈ P c, ∀ r ∈ res o, owner r = c

/-- Two distinct owned families are disjoint as sets of objects (each object has a resource). -/
theorem disjoint_of_owner {res : α → Finset R} {P : Cl → Finset α} {owner : R → Cl}
    (hne : ∀ c, ∀ o ∈ P c, (res o).Nonempty) (ho : Owned res P owner)
    {c d : Cl} (hcd : c ≠ d) : Disjoint (P c) (P d) := by
  rw [Finset.disjoint_left]
  intro o hc hd
  obtain ⟨r, hr⟩ := hne c o hc
  exact hcd ((ho c o hc r hr).symm.trans (ho d o hd r hr))

/-- **C5.** The union of owned feasible families is feasible. -/
theorem ResFeasible_biUnion_of_owner {res : α → Finset R} {P : Cl → Finset α} {owner : R → Cl}
    (ho : Owned res P owner) (hf : ∀ c, ResFeasible res (P c)) :
    ResFeasible res (Finset.univ.biUnion P) := by
  intro a ha b hb hab
  obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨d, _, hd⟩ := Finset.mem_biUnion.mp hb
  by_cases hcd : c = d
  · subst hcd; exact hf c hc hd hab
  · rw [Finset.disjoint_left]
    intro r hra hrb
    exact hcd ((ho c a hc r hra).symm.trans (ho d b hd r hrb))

/-- Sizes add over owned families. -/
theorem card_biUnion_of_owner {res : α → Finset R} {P : Cl → Finset α} {owner : R → Cl}
    (hne : ∀ c, ∀ o ∈ P c, (res o).Nonempty) (ho : Owned res P owner) :
    (Finset.univ.biUnion P).card = ∑ c, (P c).card := by
  apply Finset.card_biUnion
  intro c _ d _ hcd
  exact disjoint_of_owner hne ho hcd

/-- Weights (gains) add over owned families. -/
theorem wsum_biUnion_of_owner {res : α → Finset R} {P : Cl → Finset α} {owner : R → Cl}
    (hne : ∀ c, ∀ o ∈ P c, (res o).Nonempty) (ho : Owned res P owner) (w : α → ℕ) :
    ∑ o ∈ Finset.univ.biUnion P, w o = ∑ c, ∑ o ∈ P c, w o := by
  apply Finset.sum_biUnion
  intro c _ d _ hcd
  exact disjoint_of_owner hne ho hcd

end UnitBoundary

end PaperV
