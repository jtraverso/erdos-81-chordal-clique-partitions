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
Paper IV/V — Appendix A, weighted version with opportunity costs (Theorems E / E.1 of the
12-Sep-2026 handoff).

Same configuration as `UnitBoundaryCompletion` (`Config res Q D SR`), now with weights `w : α → ℕ`.
For a shared resource `b` let `aW b` be the maximum weight of an outer object whose shared part is
exactly `{b}` (0 if none), and for a central `d` let `wmod d = w d − Σ_{b ∈ res d} aW b ∈ ℤ`
(opportunity cost of the shared resources `d` occupies).

  * Theorem E  (`weighted_optimum_eq`):
        ν_w(Q ∪ D) = w(Z) + Σ_{b∈SR} aW b + max_{C ⊆ D feasible} Σ_{d∈C} wmod d.
  * Theorem E.1 (`weighted_transport`): for two outer families over the same centre, from any
    feasible `P₀` one builds `P₁` (keep the central part, complete optimally in the new system) with
        w(P₁) ≥ w(P₀) + w(Z₁) − w(Z₀) − Σ_b (a₀_b − a₁_b)₊.

Both preserve the witness W2: an outer of weight 1 and a central of weight 100 on one resource give
`1 + max(0, 100 − 1) = 100` — the naive "keep all outers" rule is not what the formula says.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
module

public import PaperV.UnitBoundaryCompletion

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section

open Finset Classical

namespace PaperV

namespace UnitBoundary

namespace Weighted

variable {α R : Type*} [DecidableEq α] [DecidableEq R]
variable {res : α → Finset R} {Q D : Finset α} {SR : Finset R}

/-- Outer objects whose shared part is exactly `{b}`. -/
def Rep (res : α → Finset R) (Q : Finset α) (SR : Finset R) (b : R) : Finset α :=
  Q.filter (fun o => res o ∩ SR = {b})

/-- Best available weight on shared resource `b` (0 if no outer object sits exactly on `b`). -/
def aW (res : α → Finset R) (Q : Finset α) (SR : Finset R) (w : α → ℕ) (b : R) : ℕ :=
  (Rep res Q SR b).sup w

/-- Modified central weight: weight minus the opportunity cost of its shared resources. -/
def wmod (res : α → Finset R) (Q : Finset α) (SR : Finset R) (w : α → ℕ) (d : α) : ℤ :=
  (w d : ℤ) - ∑ b ∈ res d, (aW res Q SR w b : ℤ)

/-- Resources occupied by a family. -/
def occ (res : α → Finset R) (C : Finset α) : Finset R := C.biUnion res

/-- Total weight of a family. -/
def wt (w : α → ℕ) (P : Finset α) : ℕ := ∑ o ∈ P, w o

/-- Weighted packing optimum of a universe. -/
noncomputable def wOpt (res : α → Finset R) (w : α → ℕ) (U : Finset α) : ℕ :=
  (U.powerset.filter (fun P => ResFeasible res P)).sup (wt w)

theorem le_wOpt (res : α → Finset R) (w : α → ℕ) {U P : Finset α} (hP : P ⊆ U)
    (hf : ResFeasible res P) : wt w P ≤ wOpt res w U := by
  classical
  unfold wOpt
  exact Finset.le_sup (f := wt w) (by rw [Finset.mem_filter, Finset.mem_powerset]; exact ⟨hP, hf⟩)

theorem exists_wOpt (res : α → Finset R) (w : α → ℕ) (U : Finset α) :
    ∃ P ⊆ U, ResFeasible res P ∧ wt w P = wOpt res w U := by
  classical
  have hne : (U.powerset.filter (fun P => ResFeasible res P)).Nonempty := by
    refine ⟨∅, ?_⟩
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.empty_subset _, fun a ha => absurd ha (Finset.notMem_empty a)⟩
  obtain ⟨P, hP, hmax⟩ := Finset.exists_mem_eq_sup _ hne (wt w)
  rw [Finset.mem_filter, Finset.mem_powerset] at hP
  exact ⟨P, hP.1, hP.2, by unfold wOpt; exact hmax.symm⟩

/-- Feasible central subfamilies. -/
noncomputable def centralFams (res : α → Finset R) (D : Finset α) : Finset (Finset α) :=
  D.powerset.filter (fun C => ResFeasible res C)

theorem centralFams_nonempty (res : α → Finset R) (D : Finset α) :
    (centralFams res D).Nonempty := by
  classical
  refine ⟨∅, ?_⟩
  unfold centralFams
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨Finset.empty_subset _, fun a ha => absurd ha (Finset.notMem_empty a)⟩

theorem mem_centralFams {C : Finset α} :
    C ∈ centralFams res D ↔ C ⊆ D ∧ ResFeasible res C := by
  unfold centralFams; rw [Finset.mem_filter, Finset.mem_powerset]

/-- Modified weight of a central family. -/
def wmodSum (res : α → Finset R) (Q : Finset α) (SR : Finset R) (w : α → ℕ) (C : Finset α) : ℤ :=
  ∑ d ∈ C, wmod res Q SR w d

/-- Best modified central weight. -/
noncomputable def centralOpt (res : α → Finset R) (Q D : Finset α) (SR : Finset R) (w : α → ℕ) : ℤ :=
  (centralFams res D).sup' (centralFams_nonempty res D) (wmodSum res Q SR w)

theorem wmodSum_le_centralOpt {C : Finset α} (hC : C ⊆ D) (hf : ResFeasible res C) (w : α → ℕ) :
    wmodSum res Q SR w C ≤ centralOpt res Q D SR w :=
  Finset.le_sup' (wmodSum res Q SR w) (mem_centralFams.mpr ⟨hC, hf⟩)

theorem exists_centralOpt (w : α → ℕ) :
    ∃ C ⊆ D, ResFeasible res C ∧ wmodSum res Q SR w C = centralOpt res Q D SR w := by
  obtain ⟨C, hC, hmax⟩ := Finset.exists_mem_eq_sup' (centralFams_nonempty res D) (wmodSum res Q SR w)
  rw [mem_centralFams] at hC
  exact ⟨C, hC.1, hC.2, hmax.symm⟩

/-! ### Basic facts -/

theorem mem_Rep {b : R} {o : α} : o ∈ Rep res Q SR b ↔ o ∈ Q ∧ res o ∩ SR = {b} := Finset.mem_filter

theorem le_aW {b : R} {o : α} (ho : o ∈ Rep res Q SR b) (w : α → ℕ) : w o ≤ aW res Q SR w b :=
  Finset.le_sup (f := w) ho

theorem aW_eq_zero_of_empty {b : R} (w : α → ℕ) (h : Rep res Q SR b = ∅) : aW res Q SR w b = 0 := by
  unfold aW; rw [h]; rfl

/-- An outer object outside `Z` sits exactly on one shared resource, which lies in `SR`. -/
theorem shared_singleton (cfg : Config res Q D SR) {o : α} (ho : o ∈ Q \ Z res Q SR) :
    ∃ b ∈ SR, res o ∩ SR = {b} := by
  have h1 := card_shared_eq_one cfg ho
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp h1
  refine ⟨b, ?_, hb⟩
  have : b ∈ res o ∩ SR := hb ▸ Finset.mem_singleton_self b
  exact (Finset.mem_inter.mp this).2

/-- The weighted total splits over disjoint families. -/
theorem wt_union_disjoint (w : α → ℕ) {P₁ P₂ : Finset α} (h : Disjoint P₁ P₂) :
    wt w (P₁ ∪ P₂) = wt w P₁ + wt w P₂ := by
  unfold wt; exact Finset.sum_union h

/-! ### Choice of best representatives -/

/-- A choice of a heaviest representative on each shared resource that has one. -/
structure WReps (res : α → Finset R) (Q : Finset α) (SR : Finset R) (w : α → ℕ) where
  rep : R → α
  rep_mem : ∀ b, (Rep res Q SR b).Nonempty → rep b ∈ Rep res Q SR b
  rep_max : ∀ b, (Rep res Q SR b).Nonempty → w (rep b) = aW res Q SR w b

theorem exists_wreps [Inhabited α] (res : α → Finset R) (Q : Finset α) (SR : Finset R) (w : α → ℕ) :
    Nonempty (WReps res Q SR w) := by
  classical
  have h : ∀ b, ∃ o, (Rep res Q SR b).Nonempty → o ∈ Rep res Q SR b ∧ w o = aW res Q SR w b := by
    intro b
    by_cases hb : (Rep res Q SR b).Nonempty
    · obtain ⟨o, ho, hmax⟩ := Finset.exists_max_image _ w hb
      refine ⟨o, fun _ => ⟨ho, ?_⟩⟩
      apply le_antisymm (le_aW ho w)
      unfold aW
      exact Finset.sup_le (fun o' ho' => hmax o' ho')
    · exact ⟨default, fun h' => absurd h' hb⟩
  choose f hf using h
  exact ⟨⟨f, fun b hb => (hf b hb).1, fun b hb => (hf b hb).2⟩⟩

/-- Shared resources of `SR` not occupied by `C` and having a representative. -/
def freeRes (res : α → Finset R) (Q : Finset α) (SR : Finset R) (C : Finset α) : Finset R :=
  (SR \ occ res C).filter (fun b => (Rep res Q SR b).Nonempty)

/-- The completion of a central family `C`: all of `Z`, a heaviest representative on every free shared
resource, and `C`. -/
def completion (wr : WReps res Q SR w) (C : Finset α) : Finset α :=
  Z res Q SR ∪ (freeRes res Q SR C).image wr.rep ∪ C

variable {w : α → ℕ}

theorem rep_injOn_freeRes (wr : WReps res Q SR w) (C : Finset α) :
    Set.InjOn wr.rep ((freeRes res Q SR C : Finset R) : Set R) := by
  intro b hb b' hb' h
  simp only [Finset.mem_coe, freeRes, Finset.mem_filter] at hb hb'
  have h1 := (mem_Rep.mp (wr.rep_mem b hb.2)).2
  have h2 := (mem_Rep.mp (wr.rep_mem b' hb'.2)).2
  rw [h] at h1
  rw [h1] at h2
  exact Finset.singleton_injective h2

/-- Weight of the completion. -/
theorem wt_completion (cfg : Config res Q D SR) (wr : WReps res Q SR w) {C : Finset α} (hC : C ⊆ D) :
    wt w (completion wr C) =
      wt w (Z res Q SR) + (∑ b ∈ SR \ occ res C, aW res Q SR w b) + wt w C := by
  classical
  unfold completion
  -- disjointness of the three parts
  have hZR : Disjoint (Z res Q SR) ((freeRes res Q SR C).image wr.rep) := by
    rw [Finset.disjoint_left]
    intro o hoZ hoR
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hoR
    have hb' := (Finset.mem_filter.mp hb).2
    have h1 := (mem_Rep.mp (wr.rep_mem b hb')).2
    have h2 := (mem_Z.mp hoZ).2
    rw [h2] at h1
    exact Finset.singleton_ne_empty b h1.symm
  have hOC : Disjoint (Z res Q SR ∪ (freeRes res Q SR C).image wr.rep) C := by
    rw [Finset.disjoint_left]
    intro o ho hoC
    have hoQ : o ∈ Q := by
      rcases Finset.mem_union.mp ho with h | h
      · exact Z_subset h
      · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h
        exact (mem_Rep.mp (wr.rep_mem b (Finset.mem_filter.mp hb).2)).1
    exact Finset.disjoint_left.mp cfg.hdisj hoQ (hC hoC)
  rw [wt_union_disjoint w hOC, wt_union_disjoint w hZR]
  congr 1
  -- weight of the representatives = Σ over free resources of aW
  unfold wt
  rw [Finset.sum_image (rep_injOn_freeRes wr C)]
  have h1 : ∑ b ∈ freeRes res Q SR C, w (wr.rep b) = ∑ b ∈ freeRes res Q SR C, aW res Q SR w b :=
    Finset.sum_congr rfl (fun b hb => wr.rep_max b (Finset.mem_filter.mp hb).2)
  rw [h1]
  unfold freeRes
  rw [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  split_ifs with h
  · rfl
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    exact (aW_eq_zero_of_empty w h).symm

/-- The completion is feasible when `C ⊆ D` is feasible. -/
theorem completion_feasible (cfg : Config res Q D SR) (wr : WReps res Q SR w) {C : Finset α}
    (hC : C ⊆ D) (hCf : ResFeasible res C) : ResFeasible res (completion wr C) := by
  classical
  -- shared part of a representative on b is {b}
  have hrep : ∀ b ∈ freeRes res Q SR C, wr.rep b ∈ Q ∧ res (wr.rep b) ∩ SR = {b} := by
    intro b hb
    have := wr.rep_mem b (Finset.mem_filter.mp hb).2
    exact mem_Rep.mp this
  have hfree : ∀ b ∈ freeRes res Q SR C, b ∈ SR ∧ b ∉ occ res C := by
    intro b hb
    have := (Finset.mem_filter.mp hb).1
    exact Finset.mem_sdiff.mp this
  intro a ha b hb hab
  unfold completion at ha hb
  rw [Finset.disjoint_left]
  intro r hra hrb
  rcases Finset.mem_union.mp ha with haO | haC <;> rcases Finset.mem_union.mp hb with hbO | hbC
  · -- both outer
    have haQ : a ∈ Q := by
      rcases Finset.mem_union.mp haO with h | h
      · exact Z_subset h
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h; exact (hrep x hx).1
    have hbQ : b ∈ Q := by
      rcases Finset.mem_union.mp hbO with h | h
      · exact Z_subset h
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h; exact (hrep x hx).1
    have hrSR : r ∈ SR := cfg.hQ haQ hbQ hab (Finset.mem_inter.mpr ⟨hra, hrb⟩)
    rcases Finset.mem_union.mp haO with haZ | haR
    · have h := (mem_Z.mp haZ).2
      have : r ∈ res a ∩ SR := Finset.mem_inter.mpr ⟨hra, hrSR⟩
      rw [h] at this; exact Finset.notMem_empty r this
    rcases Finset.mem_union.mp hbO with hbZ | hbR
    · have h := (mem_Z.mp hbZ).2
      have : r ∈ res b ∩ SR := Finset.mem_inter.mpr ⟨hrb, hrSR⟩
      rw [h] at this; exact Finset.notMem_empty r this
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp haR
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hbR
    have ex := (hrep x hx).2
    have ey := (hrep y hy).2
    have h1 : r ∈ res (wr.rep x) ∩ SR := Finset.mem_inter.mpr ⟨hra, hrSR⟩
    have h2 : r ∈ res (wr.rep y) ∩ SR := Finset.mem_inter.mpr ⟨hrb, hrSR⟩
    rw [ex, Finset.mem_singleton] at h1
    rw [ey, Finset.mem_singleton] at h2
    subst h1; subst h2
    exact hab rfl
  · -- a outer, b central
    have hrSR : r ∈ SR := cfg.hD b (hC hbC) hrb
    have hrocc : r ∈ occ res C := Finset.mem_biUnion.mpr ⟨b, hbC, hrb⟩
    rcases Finset.mem_union.mp haO with haZ | haR
    · have h := (mem_Z.mp haZ).2
      have : r ∈ res a ∩ SR := Finset.mem_inter.mpr ⟨hra, hrSR⟩
      rw [h] at this; exact Finset.notMem_empty r this
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp haR
      have ex := (hrep x hx).2
      have h1 : r ∈ res (wr.rep x) ∩ SR := Finset.mem_inter.mpr ⟨hra, hrSR⟩
      rw [ex, Finset.mem_singleton] at h1
      subst h1
      exact (hfree r hx).2 hrocc
  · -- a central, b outer
    have hrSR : r ∈ SR := cfg.hD a (hC haC) hra
    have hrocc : r ∈ occ res C := Finset.mem_biUnion.mpr ⟨a, haC, hra⟩
    rcases Finset.mem_union.mp hbO with hbZ | hbR
    · have h := (mem_Z.mp hbZ).2
      have : r ∈ res b ∩ SR := Finset.mem_inter.mpr ⟨hrb, hrSR⟩
      rw [h] at this; exact Finset.notMem_empty r this
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hbR
      have ey := (hrep y hy).2
      have h2 : r ∈ res (wr.rep y) ∩ SR := Finset.mem_inter.mpr ⟨hrb, hrSR⟩
      rw [ey, Finset.mem_singleton] at h2
      subst h2
      exact (hfree r hy).2 hrocc
  · exact Finset.disjoint_left.mp (hCf haC hbC hab) hra hrb

theorem completion_subset (wr : WReps res Q SR w) {C : Finset α} (hC : C ⊆ D) :
    completion wr C ⊆ Q ∪ D := by
  intro o ho
  unfold completion at ho
  rcases Finset.mem_union.mp ho with h | h
  · rcases Finset.mem_union.mp h with h | h
    · exact Finset.mem_union_left _ (Z_subset h)
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_union_left _ (mem_Rep.mp (wr.rep_mem b (Finset.mem_filter.mp hb).2)).1
  · exact Finset.mem_union_right _ (hC h)

/-! ### Rewriting `Σ_{b ∈ SR \ occ C} aW b` through the modified weights -/

/-- For a feasible central family `C ⊆ D`: `Σ_{b∈SR∖occ C} aW b = Σ_{b∈SR} aW b − Σ_{d∈C} Σ_{b∈res d} aW b`
(as integers), because the resource sets of `C` are disjoint and contained in `SR`. -/
theorem sum_aW_free (cfg : Config res Q D SR) (w : α → ℕ) {C : Finset α} (hC : C ⊆ D)
    (hCf : ResFeasible res C) :
    ((∑ b ∈ SR \ occ res C, aW res Q SR w b : ℕ) : ℤ) =
      (∑ b ∈ SR, aW res Q SR w b : ℕ) - ∑ d ∈ C, ∑ b ∈ res d, (aW res Q SR w b : ℤ) := by
  classical
  have hocc : occ res C ⊆ SR := by
    intro b hb
    obtain ⟨d, hd, hbd⟩ := Finset.mem_biUnion.mp hb
    exact cfg.hD d (hC hd) hbd
  have hsplit : (∑ b ∈ SR, aW res Q SR w b) =
      (∑ b ∈ SR \ occ res C, aW res Q SR w b) + ∑ b ∈ occ res C, aW res Q SR w b := by
    rw [Finset.sum_sdiff hocc]
  have hdisj : (C : Set α).PairwiseDisjoint res := by
    intro a ha b hb hab
    exact hCf ha hb hab
  have hocc_sum : (∑ b ∈ occ res C, (aW res Q SR w b : ℤ)) =
      ∑ d ∈ C, ∑ b ∈ res d, (aW res Q SR w b : ℤ) := by
    unfold occ
    exact Finset.sum_biUnion hdisj
  have hsplit' : ((∑ b ∈ SR, aW res Q SR w b : ℕ) : ℤ) =
      ((∑ b ∈ SR \ occ res C, aW res Q SR w b : ℕ) : ℤ) +
        ∑ b ∈ occ res C, (aW res Q SR w b : ℤ) := by
    rw [hsplit]; push_cast; rfl
  rw [hsplit', hocc_sum]; ring

/-- Weight of the completion in modified-weight form. -/
theorem wt_completion_int (cfg : Config res Q D SR) (wr : WReps res Q SR w) {C : Finset α}
    (hC : C ⊆ D) (hCf : ResFeasible res C) :
    (wt w (completion wr C) : ℤ) =
      (wt w (Z res Q SR) : ℤ) + (∑ b ∈ SR, aW res Q SR w b : ℕ) + wmodSum res Q SR w C := by
  rw [wt_completion cfg wr hC]
  push_cast
  have h := sum_aW_free cfg w hC hCf
  push_cast at h
  rw [h]
  unfold wmodSum wmod wt
  push_cast
  rw [Finset.sum_sub_distrib]
  ring

/-! ### Upper bound: every feasible family is dominated by the completion of its central part -/

/-- Weight of a feasible `P ⊆ Q ∪ D` is at most the weight of the completion of its central part. -/
theorem wt_le_completion_form (cfg : Config res Q D SR) (w : α → ℕ) {P : Finset α} (hPU : P ⊆ Q ∪ D)
    (hf : ResFeasible res P) :
    wt w P ≤ wt w (Z res Q SR) + (∑ b ∈ SR \ occ res (P ∩ D), aW res Q SR w b) + wt w (P ∩ D) := by
  classical
  set PQ := P ∩ Q with hPQ
  set PD := P ∩ D with hPD
  have hcov : P = PQ ∪ PD := by
    ext x; simp only [hPQ, hPD, Finset.mem_union, Finset.mem_inter]
    constructor
    · intro hx; rcases Finset.mem_union.mp (hPU hx) with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hdis : Disjoint PQ PD :=
    Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right cfg.hdisj)
  have hsplit : wt w P = wt w PQ + wt w PD := by rw [hcov, wt_union_disjoint w hdis]
  -- outer part: PQ ∩ Z ≤ wt Z ; PQ \ Z injects into free resources with weight ≤ aW
  have hPQsub : PQ ⊆ Q := Finset.inter_subset_right
  have hPQZ : wt w (PQ ∩ Z res Q SR) ≤ wt w (Z res Q SR) := by
    unfold wt
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun _ _ _ => Nat.zero_le _)
  have hPQsplit : wt w PQ = wt w (PQ ∩ Z res Q SR) + wt w (PQ \ Z res Q SR) := by
    unfold wt; rw [← Finset.sum_inter_add_sum_sdiff]
  -- the shared resource of o ∈ PQ \ Z
  have hsh : ∀ o ∈ PQ \ Z res Q SR, ∃ b ∈ SR \ occ res PD, res o ∩ SR = {b} ∧ w o ≤ aW res Q SR w b := by
    intro o ho
    have ho' : o ∈ Q \ Z res Q SR :=
      Finset.mem_sdiff.mpr ⟨hPQsub (Finset.mem_sdiff.mp ho).1, (Finset.mem_sdiff.mp ho).2⟩
    obtain ⟨b, hbSR, hb⟩ := shared_singleton cfg ho'
    refine ⟨b, Finset.mem_sdiff.mpr ⟨hbSR, ?_⟩, hb, le_aW (mem_Rep.mpr ⟨hPQsub (Finset.mem_sdiff.mp ho).1, hb⟩) w⟩
    -- b is not occupied by the central part: o and d ∈ PD are disjoint
    intro hocc
    obtain ⟨d, hd, hbd⟩ := Finset.mem_biUnion.mp hocc
    have hoP : o ∈ P := (Finset.mem_inter.mp (Finset.mem_sdiff.mp ho).1).1
    have hdP : d ∈ P := (Finset.mem_inter.mp hd).1
    have hne : o ≠ d := by
      intro h; subst h
      exact Finset.disjoint_left.mp cfg.hdisj (hPQsub (Finset.mem_sdiff.mp ho).1) (Finset.mem_inter.mp hd).2
    have hbo : b ∈ res o := (Finset.mem_inter.mp (hb ▸ Finset.mem_singleton_self b)).1
    exact Finset.disjoint_left.mp (hf hoP hdP hne) hbo hbd
  choose sh hsh using hsh
  let g : {o // o ∈ PQ \ Z res Q SR} → R := fun o => sh o.1 o.2
  have hginj : Function.Injective g := by
    intro a b hab
    by_contra hne
    have hne' : a.1 ≠ b.1 := fun h => hne (Subtype.ext h)
    have hfa : a.1 ∈ P := (Finset.mem_inter.mp (Finset.mem_sdiff.mp a.2).1).1
    have hfb : b.1 ∈ P := (Finset.mem_inter.mp (Finset.mem_sdiff.mp b.2).1).1
    have hd := hf hfa hfb hne'
    have h1 := (hsh a.1 a.2).2.1
    have h2 := (hsh b.1 b.2).2.1
    have hra : g a ∈ res a.1 := (Finset.mem_inter.mp (h1 ▸ Finset.mem_singleton_self (g a))).1
    have hrb : g b ∈ res b.1 := (Finset.mem_inter.mp (h2 ▸ Finset.mem_singleton_self (g b))).1
    rw [hab] at hra
    exact Finset.disjoint_left.mp hd hra hrb
  have hout : wt w (PQ \ Z res Q SR) ≤ ∑ b ∈ SR \ occ res PD, aW res Q SR w b := by
    unfold wt
    rw [← Finset.sum_attach (PQ \ Z res Q SR)]
    calc ∑ o ∈ (PQ \ Z res Q SR).attach, w o.1
        ≤ ∑ o ∈ (PQ \ Z res Q SR).attach, aW res Q SR w (g o) :=
          Finset.sum_le_sum (fun o _ => (hsh o.1 o.2).2.2)
      _ = ∑ b ∈ (PQ \ Z res Q SR).attach.image g, aW res Q SR w b :=
          (Finset.sum_image (hginj.injOn)).symm
      _ ≤ ∑ b ∈ SR \ occ res PD, aW res Q SR w b := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro b hb
            obtain ⟨o, _, rfl⟩ := Finset.mem_image.mp hb
            exact (hsh o.1 o.2).1
          · intros; exact Nat.zero_le _
  omega

/-- **Theorem E (weighted unit-boundary completion).** -/
theorem weighted_optimum_eq (cfg : Config res Q D SR) (wr : WReps res Q SR w) :
    (wOpt res w (Q ∪ D) : ℤ) =
      (wt w (Z res Q SR) : ℤ) + (∑ b ∈ SR, aW res Q SR w b : ℕ) + centralOpt res Q D SR w := by
  apply le_antisymm
  · -- upper bound
    obtain ⟨P, hPU, hf, hP⟩ := exists_wOpt res w (Q ∪ D)
    rw [← hP]
    have h1 := wt_le_completion_form cfg w hPU hf
    have hPD : P ∩ D ⊆ D := Finset.inter_subset_right
    have hPDf : ResFeasible res (P ∩ D) := fun a ha b hb hne =>
      hf (Finset.mem_inter.mp ha).1 (Finset.mem_inter.mp hb).1 hne
    have h2 := sum_aW_free cfg w hPD hPDf
    have h3 := wmodSum_le_centralOpt (res := res) (Q := Q) (SR := SR) hPD hPDf w
    have h1' : (wt w P : ℤ) ≤ (wt w (Z res Q SR) : ℤ) +
        ((∑ b ∈ SR \ occ res (P ∩ D), aW res Q SR w b : ℕ) : ℤ) + (wt w (P ∩ D) : ℤ) := by
      exact_mod_cast h1
    have h4 : (wt w (P ∩ D) : ℤ) - ∑ d ∈ P ∩ D, ∑ b ∈ res d, (aW res Q SR w b : ℤ) =
        wmodSum res Q SR w (P ∩ D) := by
      unfold wmodSum wmod wt; push_cast; rw [Finset.sum_sub_distrib]
    linarith
  · -- lower bound: completion of the optimal central family
    obtain ⟨C, hC, hCf, hCopt⟩ := exists_centralOpt (res := res) (Q := Q) (D := D) (SR := SR) w
    have hfeas := completion_feasible cfg wr hC hCf
    have hle := le_wOpt res w (completion_subset wr hC) hfeas
    have heq := wt_completion_int cfg wr hC hCf
    rw [hCopt] at heq
    have : (wt w (completion wr C) : ℤ) ≤ wOpt res w (Q ∪ D) := by exact_mod_cast hle
    linarith

/-- W2 under Theorem E: outer of weight 1, central of weight 100 on the same resource — the optimum
is `1 + max(0, 100 − 1) = 100`, i.e. the central is kept (`wmod = 99 > 0`); the formula charges the
opportunity cost instead of forcing the outer object. -/
theorem w2_weighted_check :
    let res2 : Fin 2 → Finset (Fin 1) := fun _ => {0}
    let w2 : Fin 2 → ℕ := fun i => if i = 0 then 1 else 100
    wmod res2 {0} {0} w2 1 = 99 ∧ aW res2 {0} {0} w2 0 = 1 ∧ wt w2 (Z res2 {0} {0}) = 0 := by
  decide

/-! ### Theorem E.1 — transport between two outer families -/

variable {Q₀ Q₁ : Finset α}

/-- `(x)₊` on integers. -/
def posPart (x : ℤ) : ℤ := max x 0

theorem le_posPart (x : ℤ) : x ≤ posPart x := le_max_left _ _
theorem posPart_nonneg (x : ℤ) : 0 ≤ posPart x := le_max_right _ _

/-- **Theorem E.1 (weighted transport).** Keep the central part `C₀ = P₀ ∩ D` of a feasible `P₀` in
system `0` and complete it optimally in system `1`. The result `P₁` is feasible in `Q₁ ∪ D` and
`w(P₁) ≥ w(P₀) + w(Z₁) − w(Z₀) − Σ_{b∈SR} (a₀_b − a₁_b)₊`. -/
theorem weighted_transport (cfg₀ : Config res Q₀ D SR) (cfg₁ : Config res Q₁ D SR)
    (wr₁ : WReps res Q₁ SR w) {P₀ : Finset α} (hP₀ : P₀ ⊆ Q₀ ∪ D) (hf₀ : ResFeasible res P₀) :
    ResFeasible res (completion wr₁ (P₀ ∩ D)) ∧ completion wr₁ (P₀ ∩ D) ⊆ Q₁ ∪ D ∧
    (wt w P₀ : ℤ) + wt w (Z res Q₁ SR) ≤
      (wt w (completion wr₁ (P₀ ∩ D)) : ℤ) + wt w (Z res Q₀ SR) +
        ∑ b ∈ SR, posPart ((aW res Q₀ SR w b : ℤ) - aW res Q₁ SR w b) := by
  classical
  have hC : P₀ ∩ D ⊆ D := Finset.inter_subset_right
  have hCf : ResFeasible res (P₀ ∩ D) := fun a ha b hb hne =>
    hf₀ (Finset.mem_inter.mp ha).1 (Finset.mem_inter.mp hb).1 hne
  refine ⟨completion_feasible cfg₁ wr₁ hC hCf, completion_subset wr₁ hC, ?_⟩
  have h0 := wt_le_completion_form cfg₀ w hP₀ hf₀
  have h1 := wt_completion cfg₁ wr₁ hC
  -- Σ over free resources: a₁ ≥ a₀ − (a₀ − a₁)₊, and the free set is inside SR
  have hfree : (∑ b ∈ SR \ occ res (P₀ ∩ D), (aW res Q₀ SR w b : ℤ)) ≤
      (∑ b ∈ SR \ occ res (P₀ ∩ D), (aW res Q₁ SR w b : ℤ)) +
        ∑ b ∈ SR, posPart ((aW res Q₀ SR w b : ℤ) - aW res Q₁ SR w b) := by
    have hstep : ∀ b ∈ SR \ occ res (P₀ ∩ D), (aW res Q₀ SR w b : ℤ) ≤
        (aW res Q₁ SR w b : ℤ) + posPart ((aW res Q₀ SR w b : ℤ) - aW res Q₁ SR w b) := by
      intro b _
      have := le_posPart ((aW res Q₀ SR w b : ℤ) - aW res Q₁ SR w b)
      linarith
    calc (∑ b ∈ SR \ occ res (P₀ ∩ D), (aW res Q₀ SR w b : ℤ))
        ≤ ∑ b ∈ SR \ occ res (P₀ ∩ D),
            ((aW res Q₁ SR w b : ℤ) + posPart ((aW res Q₀ SR w b : ℤ) - aW res Q₁ SR w b)) :=
          Finset.sum_le_sum hstep
      _ = (∑ b ∈ SR \ occ res (P₀ ∩ D), (aW res Q₁ SR w b : ℤ)) +
            ∑ b ∈ SR \ occ res (P₀ ∩ D), posPart ((aW res Q₀ SR w b : ℤ) - aW res Q₁ SR w b) :=
          Finset.sum_add_distrib
      _ ≤ (∑ b ∈ SR \ occ res (P₀ ∩ D), (aW res Q₁ SR w b : ℤ)) +
            ∑ b ∈ SR, posPart ((aW res Q₀ SR w b : ℤ) - aW res Q₁ SR w b) := by
          have hsub : ∑ b ∈ SR \ occ res (P₀ ∩ D), posPart ((aW res Q₀ SR w b : ℤ) - aW res Q₁ SR w b)
              ≤ ∑ b ∈ SR, posPart ((aW res Q₀ SR w b : ℤ) - aW res Q₁ SR w b) :=
            Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => posPart_nonneg _)
          linarith
  have h0' : (wt w P₀ : ℤ) ≤ (wt w (Z res Q₀ SR) : ℤ) +
      (∑ b ∈ SR \ occ res (P₀ ∩ D), (aW res Q₀ SR w b : ℤ)) + (wt w (P₀ ∩ D) : ℤ) := by
    have := h0; push_cast at this ⊢; exact_mod_cast h0
  have h1' : (wt w (completion wr₁ (P₀ ∩ D)) : ℤ) = (wt w (Z res Q₁ SR) : ℤ) +
      (∑ b ∈ SR \ occ res (P₀ ∩ D), (aW res Q₁ SR w b : ℤ)) + (wt w (P₀ ∩ D) : ℤ) := by
    rw [h1]; push_cast; rfl
  linarith

end Weighted

end UnitBoundary

end PaperV
