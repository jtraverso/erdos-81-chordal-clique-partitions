import Mathlib
/-!
# The Load Identity (Lemma 1)
This file formalizes Lemma 1 (*Load identity*) of the paper
*Clique Partitions of Split Graphs and the 1/6 Barrier*.
Setup.  In a split graph `G = (C ∪ I, E)` the clique side is `C`.  We work with the set
`I≥2` of independent-side vertices of degree `≥ 2`, and for each such `v` its neighborhood
`N v ⊆ C`, whose cardinality `d v = |N v|` is its degree.  For a pair `e = {x,y}` of clique
vertices the **co-neighborhood load** is
  `A e = ∑_{v ∈ I≥2, e ⊆ N v} 1 / (d v - 1)`,
and `b≥2 = ∑_{v ∈ I≥2} d v`.
**Lemma 1.**  `∑_{e ⊆ C, |e| = 2} A e = b≥2 / 2`.
The proof swaps the order of summation and uses, for each fixed `v`,
`∑_{e ⊆ N v, |e| = 2} 1/(d v - 1) = (d v choose 2)/(d v - 1) = d v / 2`.
-/
namespace ErdosSplit
open Finset
variable {V : Type*} [DecidableEq V]
/-- The co-neighborhood load of a clique pair `e`, summed over independent-side vertices
of degree `≥ 2` whose neighborhood contains `e`. -/
noncomputable def load (I₂ : Finset V) (N : V → Finset V) (e : Finset V) : ℝ :=
  ∑ v ∈ I₂.filter (fun v => e ⊆ N v), 1 / ((N v).card - 1 : ℝ)
/-
**Lemma 1 (Load identity).**  The total co-neighborhood load over all pairs of the
clique side `C` equals half of `b≥2 = ∑_{v ∈ I≥2} d v`.
-/
theorem load_identity (C I₂ : Finset V) (N : V → Finset V)
    (hN : ∀ v ∈ I₂, N v ⊆ C) (hd : ∀ v ∈ I₂, 2 ≤ (N v).card) :
    ∑ e ∈ C.powersetCard 2, load I₂ N e
      = (∑ v ∈ I₂, ((N v).card : ℝ)) / 2 := by
  -- For each fixed `v ∈ I₂`, the pairs of `C` contained in `N v` are exactly the pairs
  -- of `N v` (since `N v ⊆ C`), so the inner load evaluates to `d v / 2`.
  have step : ∀ v ∈ I₂,
      (∑ e ∈ powersetCard 2 C, if e ⊆ N v then (1 / ((N v).card - 1 : ℝ)) else 0)
        = ((N v).card : ℝ) / 2 := by
    intro v hv
    have h_filter : (C.powersetCard 2).filter (· ⊆ N v) = (N v).powersetCard 2 := by
      ext e
      simp only [mem_filter, mem_powersetCard]
      exact ⟨fun ⟨⟨_, hc⟩, hs⟩ => ⟨hs, hc⟩,
        fun ⟨hs, hc⟩ => ⟨⟨hs.trans (hN v hv), hc⟩, hs⟩⟩
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, h_filter,
      Finset.card_powersetCard, nsmul_eq_mul, Nat.cast_choose_two]
    have hpos : (2 : ℝ) ≤ ((N v).card : ℝ) := by exact_mod_cast hd v hv
    have hne : ((N v).card : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  -- Expand `load` into an indicator sum, swap the order of summation and apply `step`.
  have expand : ∀ e, load I₂ N e
      = ∑ v ∈ I₂, if e ⊆ N v then (1 / ((N v).card - 1 : ℝ)) else 0 := fun e => by
    rw [load, ← Finset.sum_filter]
  calc
    ∑ e ∈ C.powersetCard 2, load I₂ N e
        = ∑ e ∈ C.powersetCard 2, ∑ v ∈ I₂,
            if e ⊆ N v then (1 / ((N v).card - 1 : ℝ)) else 0 :=
          Finset.sum_congr rfl fun e _ => expand e
    _ = ∑ v ∈ I₂, ∑ e ∈ C.powersetCard 2,
            if e ⊆ N v then (1 / ((N v).card - 1 : ℝ)) else 0 := Finset.sum_comm
    _ = ∑ v ∈ I₂, ((N v).card : ℝ) / 2 := Finset.sum_congr rfl step
    _ = (∑ v ∈ I₂, ((N v).card : ℝ)) / 2 := by rw [Finset.sum_div]
end ErdosSplit
