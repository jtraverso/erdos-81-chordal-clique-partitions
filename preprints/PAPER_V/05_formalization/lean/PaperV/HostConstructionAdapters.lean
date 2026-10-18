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

/- Paper V, F3/F4: physical/background and paired-factor construction interfaces. -/
module

public import PaperV.GreedyLists
public import PaperV.HostRealizer
public import PaperV.PairedFactors

@[expose] public section

open Finset

namespace PaperV.Host

variable {E V H : Type*} [Fintype E] [DecidableEq E]
  [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

/-- F3: the actual local degree-sum list condition supplies a proper assignment. -/
theorem greedy_host_assignment (ends : E → Finset V) (L : E → Finset H)
    (hends : ∀ e, ∃ u v, u ≠ v ∧ ends e = {u, v})
    (hL : ∀ e u v, ends e = {u, v} →
      GreedyLists.degree ends u + GreedyLists.degree ends v - 1 ≤ (L e).card) :
    ∃ c : E → H, ProperOn ends L Finset.univ c := by
  obtain ⟨c, hmem, hproper⟩ := GreedyLists.exists_host_assignment ends L hends hL
  exact ⟨c, ⟨fun e _ => hmem e, fun e _ f _ => hproper e f⟩⟩

/-- Exactly one triangle is created per base, so inherited rational weights are preserved. -/
theorem assigned_weight (T : Finset E) (c : E → H) (β : E → ℚ) :
    ∑ t ∈ T.image (fun e => (e, c e)), β t.1 = ∑ e ∈ T, β e := by
  rw [Finset.sum_image]
  intro a _ b _ h
  exact (Prod.mk.inj h).1

section Background

variable {A R : Type*} [DecidableEq A] [DecidableEq R]

/-- Two genuinely compatible physical families can be put in a common tagged
object universe. Feasibility follows from resource exclusion, not an assumption
that the desired union is already feasible. -/
theorem compatible_background_union
    (resA : A → Finset R) (resB : (E × H) → Finset R)
    (P₀ : Finset A) (P₁ : Finset (E × H))
    (h₀ : UnitBoundary.ResFeasible resA P₀)
    (h₁ : UnitBoundary.ResFeasible resB P₁)
    (hcross : ∀ a ∈ P₀, ∀ b ∈ P₁, Disjoint (resA a) (resB b)) :
    UnitBoundary.ResFeasible (Sum.elim resA resB)
      (P₀.image Sum.inl ∪ P₁.image Sum.inr) := by
  intro a ha b hb hab
  rcases Finset.mem_union.mp ha with ha | ha <;>
    rcases Finset.mem_union.mp hb with hb | hb
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    exact h₀ hx hy (fun h => hab (by simp [h]))
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    exact hcross x hx y hy
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    exact (hcross y hy x hx).symm
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    exact h₁ hx hy (fun h => hab (by simp [h]))

end Background

/-- All resources allowed by the lists are fresh relative to a fixed background. -/
theorem proper_assignment_avoids_background {A : Type*} [DecidableEq A]
    (ends : E → Finset V) (L : E → Finset H) (T : Finset E) (c : E → H)
    (hc : ProperOn ends L T c)
    (res₀ : A → Finset (E ⊕ (H × V))) (P₀ : Finset A)
    (h₀ : UnitBoundary.ResFeasible res₀ P₀)
    (hfresh : ∀ a ∈ P₀, ∀ e ∈ T, ∀ h ∈ L e,
      Disjoint (res₀ a) (triRes ends (e, h))) :
    UnitBoundary.ResFeasible (Sum.elim res₀ (triRes ends))
      (P₀.image Sum.inl ∪ (T.image (fun e => (e, c e))).image Sum.inr) := by
  apply compatible_background_union res₀ (triRes ends) P₀ _ h₀
    (resFeasible_of_properOn hc)
  intro a ha t ht
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ht
  exact hfresh a ha e he (c e) (hc.mem e he)

/-- F4: slot-disjointness and matching factors give a proper assignment on
precisely the surviving bases. This is the physical adapter to the finite
averaging theorem `PairedFactors.exists_paired_completion`. -/
theorem paired_factor_assignment
    {k : ℕ} (ends : E → Finset V) (factor : E → Fin k) (L : E → Finset H)
    (hmatching : ∀ e f, e ≠ f → factor e = factor f → Disjoint (ends e) (ends f))
    (S : Finset (Fin k)) (ι ι' : Fin k → H)
    (hι : Function.Injective ι)
    (hι' : Set.InjOn ι' (↑Sᶜ : Set (Fin k)))
    (hcross : ∀ f, f ∉ S → ∀ g, ι' f ≠ ι g) :
    ∃ c : E → H,
      ProperOn ends L (Finset.univ.filter (fun e =>
        ¬ PairedFactors.Uncovered factor L S ι ι' e)) c := by
  classical
  let c : E → H := fun e => if ι (factor e) ∈ L e then ι (factor e) else ι' (factor e)
  let T := Finset.univ.filter (fun e => ¬ PairedFactors.Uncovered factor L S ι ι' e)
  have hvalid : ∀ e ∈ T, c e ∈ L e := by
    intro e he
    have hn := (Finset.mem_filter.mp he).2
    unfold PairedFactors.Uncovered at hn
    by_cases hi : ι (factor e) ∈ L e
    · simpa [c, hi] using hi
    · have hs : factor e ∉ S := by
        intro hs
        exact hn ⟨hi, fun h => False.elim (h hs)⟩
      have hi' : ι' (factor e) ∈ L e := by
        by_contra h
        exact hn ⟨hi, fun _ => h⟩
      simpa [c, hi] using hi'
  have hsecond : ∀ e ∈ T, ι (factor e) ∉ L e → factor e ∉ S := by
    intro e he hi hs
    exact (Finset.mem_filter.mp he).2 ⟨hi, fun h => False.elim (h hs)⟩
  refine ⟨c, ⟨hvalid, ?_⟩⟩
  intro e he f hf hef hover
  have hfactor : factor e ≠ factor f := fun h => hover (hmatching e f hef h)
  by_cases hi : ι (factor e) ∈ L e <;> by_cases hj : ι (factor f) ∈ L f
  · simpa [c, hi, hj] using (fun h => hfactor (hι h))
  · have hs := hsecond f hf hj
    simpa [c, hi, hj] using (fun h => hcross (factor f) hs (factor e) h.symm)
  · have hs := hsecond e he hi
    simpa [c, hi, hj] using hcross (factor e) hs (factor f)
  · have hse : factor e ∈ (↑Sᶜ : Set (Fin k)) := by simpa using hsecond e he hi
    have hsf : factor f ∈ (↑Sᶜ : Set (Fin k)) := by simpa using hsecond f hf hj
    simpa [c, hi, hj] using (fun h => hfactor (hι' hse hsf h))

/-- The finite averaging choice and its physical host assignment in a single
interface. The penalty bound uses the same inherited rational weights. -/
theorem exists_paired_host_completion
    (k q s : ℕ) (hk : 1 ≤ k) (hq : 2 ≤ q) (hs : s ≤ k)
    (hslots : 2 * k - s ≤ q) (hH : Fintype.card H = q)
    (ends : E → Finset V) (factor : E → Fin k) (L : E → Finset H)
    (β : E → ℚ) (hβ : ∀ e, 0 ≤ β e)
    (hmatching : ∀ e f, e ≠ f → factor e = factor f → Disjoint (ends e) (ends f)) :
    ∃ (S : Finset (Fin k)) (ι ι' : Fin k → H) (c : E → H),
      S.card = s ∧ Function.Injective ι ∧ Set.InjOn ι' (↑Sᶜ : Set (Fin k)) ∧
      (∀ f, f ∉ S → ∀ g, ι' f ≠ ι g) ∧
      ProperOn ends L (Finset.univ.filter (fun e =>
        ¬ PairedFactors.Uncovered factor L S ι ι' e)) c ∧
      ∑ e ∈ Finset.univ.filter (PairedFactors.Uncovered factor L S ι ι'), β e ≤
        ((s : ℚ) / (k * q)) * ∑ e, β e * (PairedFactors.bad q L e : ℚ) +
        (((k : ℚ) - s) / (k * q * (q - 1))) *
          ∑ e, β e * (PairedFactors.bad q L e : ℚ) * ((PairedFactors.bad q L e : ℚ) - 1) := by
  obtain ⟨S, ι, ι', hS, hι, hι', hcross, hpen⟩ :=
    PairedFactors.exists_paired_completion k q s hk hq hs hslots hH factor L β hβ
  obtain ⟨c, hc⟩ := paired_factor_assignment ends factor L hmatching S ι ι' hι hι' hcross
  exact ⟨S, ι, ι', c, hS, hι, hι', hcross, hc, hpen⟩

/-- F4's k=0 case is an empty base family and has zero cost; no division by k. -/
theorem empty_factor_completion (ends : E → Finset V) (L : E → Finset H)
    (factor : E → Fin 0) :
    ∃ c : E → H, ProperOn ends L Finset.univ c ∧
      (Finset.univ.image (fun e => (e, c e)) : Finset (E × H)) = ∅ := by
  letI : IsEmpty E := ⟨fun e => Fin.elim0 (factor e)⟩
  refine ⟨fun e => isEmptyElim e, ?_, ?_⟩
  · exact ⟨fun e => isEmptyElim e, fun e => isEmptyElim e⟩
  · exact Finset.eq_empty_of_forall_notMem (fun t ht => by
      obtain ⟨e, _, _⟩ := Finset.mem_image.mp ht
      exact isEmptyElim e)

end PaperV.Host
