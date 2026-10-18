/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
SPDX-License-Identifier: Apache-2.0

The Apache-2.0 grant applies to the author-written formalization in this file.
Existing mathematical attributions, author credits and provenance below are retained.
-/

/-
Author: Juan Pablo Traverso Gianini.
Existing third-party credits below are retained.
-/
/-
Paper VI — Section 7: fractional clique partitions with equality on every edge and uniform
cost; the zero-gap statement (22) and the support of optimal fractional partitions.
-/
module

public import PaperVI.Optimal

@[expose] public section

namespace PaperVI

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A fractional clique partition: nonnegative weights on vertex sets, supported on cliques of
order at least two, with total weight exactly one on every edge of `G`. -/
structure IsFracPartition (G : SimpleGraph V) (x : Finset V → ℝ) : Prop where
  nonneg : ∀ Q, 0 ≤ x Q
  support : ∀ Q, x Q ≠ 0 → 2 ≤ Q.card ∧ G.IsClique (Q : Set V)
  edge : ∀ u v, G.Adj u v → ∑ Q ∈ univ.filter (fun Q : Finset V => u ∈ Q ∧ v ∈ Q), x Q = 1

/-- A fractional clique partition whose blocks have order at most `r`. -/
def IsFracPartitionLe (r : ℕ) (G : SimpleGraph V) (x : Finset V → ℝ) : Prop :=
  IsFracPartition G x ∧ ∀ Q, x Q ≠ 0 → Q.card ≤ r

/-- The uniform cost `Σ_Q x_Q`. -/
def fracValue (x : Finset V → ℝ) : ℝ := ∑ Q, x Q

variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

/-- Double counting for a fractional partition: each edge of `K` is covered with total
weight one. -/
theorem frac_count {x : Finset V → ℝ} (hx : IsFracPartition G x) (K : Finset (Sym2 V))
    (hK : K ⊆ G.edgeFinset) :
    ∑ Q, x Q * ((insideFilter K Q).card : ℝ) = K.card := by
  have h1 : ∀ e ∈ K, ∑ Q, (if ∀ v ∈ e.toFinset, v ∈ Q then x Q else 0) = 1 := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      have hadj : G.Adj u v := by simpa using hK he
      rw [← hx.edge u v hadj, ← sum_filter]
      apply sum_congr _ (fun _ _ => rfl)
      ext Q
      simp only [mem_filter, mem_univ, true_and, Sym2.mem_toFinset, Sym2.mem_iff]
      constructor
      · intro h; exact ⟨h u (Or.inl rfl), h v (Or.inr rfl)⟩
      · rintro ⟨hu, hv⟩ w (rfl | rfl) <;> assumption
  calc ∑ Q, x Q * ((insideFilter K Q).card : ℝ)
      = ∑ Q, ∑ e ∈ K, (if ∀ v ∈ e.toFinset, v ∈ Q then x Q else 0) := by
        refine sum_congr rfl fun Q _ => ?_
        unfold insideFilter
        rw [card_filter, Nat.cast_sum, mul_sum]
        refine sum_congr rfl fun e _ => ?_
        split_ifs <;> simp
    _ = ∑ e ∈ K, ∑ Q, (if ∀ v ∈ e.toFinset, v ∈ Q then x Q else 0) := sum_comm
    _ = ∑ e ∈ K, (1 : ℝ) := sum_congr rfl h1
    _ = K.card := by simp

/-- The fractional slack identity: `Σ_Q x_Q - (s - u - 2m) = Σ_Q ℓ(a_Q, b_Q) x_Q`. -/
theorem frac_slack_identity {x : Finset V → ℝ} (hx : IsFracPartition G x) :
    fracValue x - ((sCount G P : ℝ) - uCount G P - 2 * mCount G P) =
      ∑ Q, (slack (coreSize P Q) (extSize P Q) : ℝ) * x Q := by
  have hcore := frac_count G hx (coreEdges G P) (coreEdges_subset G P)
  have hext := frac_count G hx (extEdges G P) (extEdges_subset' G P)
  have hcross := frac_count G hx (crossEdges G P) (crossEdges_subset G P)
  have ecore : ∀ Q, x Q * ((insideFilter (coreEdges G P) Q).card : ℝ)
      = x Q * ((coreSize P Q).choose 2 : ℝ) := by
    intro Q
    by_cases hQ : x Q = 0
    · simp [hQ]
    · rw [card_insideFilter_core G P Q (hx.support Q hQ).2]
  have eext : ∀ Q, x Q * ((insideFilter (extEdges G P) Q).card : ℝ)
      = x Q * ((extSize P Q).choose 2 : ℝ) := by
    intro Q
    by_cases hQ : x Q = 0
    · simp [hQ]
    · rw [card_insideFilter_ext G P Q (hx.support Q hQ).2]
  have ecross : ∀ Q, x Q * ((insideFilter (crossEdges G P) Q).card : ℝ)
      = x Q * ((coreSize P Q * extSize P Q : ℕ) : ℝ) := by
    intro Q
    by_cases hQ : x Q = 0
    · simp [hQ]
    · rw [card_insideFilter_cross G P Q (hx.support Q hQ).2]
  simp only [ecore] at hcore
  simp only [eext] at hext
  simp only [ecross] at hcross
  unfold fracValue uCount mCount sCount
  rw [← hcore, ← hext, ← hcross]
  have e1 : ∀ Q, (slack (coreSize P Q) (extSize P Q) : ℝ) * x Q =
      x Q - x Q * ((coreSize P Q * extSize P Q : ℕ) : ℝ) + x Q * ((coreSize P Q).choose 2 : ℝ) +
        2 * (x Q * ((extSize P Q).choose 2 : ℝ)) := by
    intro Q; simp only [slack]; push_cast; ring
  rw [sum_congr rfl (fun Q _ => e1 Q), sum_add_distrib, sum_add_distrib, sum_sub_distrib,
    ← mul_sum]
  ring

/-- Every fractional clique partition costs at least `s - u - 2m`. -/
theorem frac_lower_bound {x : Finset V → ℝ} (hx : IsFracPartition G x) :
    (sCount G P : ℝ) - uCount G P - 2 * mCount G P ≤ fracValue x := by
  have h := frac_slack_identity G P hx
  have : 0 ≤ ∑ Q, (slack (coreSize P Q) (extSize P Q) : ℝ) * x Q :=
    sum_nonneg fun Q _ => mul_nonneg (by exact_mod_cast slack_nonneg _ _) (hx.nonneg Q)
  linarith

omit [DecidableRel G.Adj] in
/-- The indicator of an integral clique partition is a fractional clique partition. -/
theorem isFracPartition_indicator {Bs : Finset (Finset V)} (hBs : IsCliquePartition G Bs) :
    IsFracPartition G (fun Q => if Q ∈ Bs then 1 else 0) ∧
      fracValue (fun Q => if Q ∈ Bs then (1 : ℝ) else 0) = Bs.card := by
  refine ⟨⟨fun Q => by split_ifs <;> norm_num, fun Q hQ => ?_, fun u v huv => ?_⟩, ?_⟩
  · have hQ' : Q ∈ Bs := by by_contra h; simp [h] at hQ
    exact ⟨hBs.two_le Q hQ', hBs.isClique Q hQ'⟩
  · obtain ⟨B, hB, hu⟩ := hBs.existsUnique u v huv
    rw [← sum_filter, filter_filter]
    have : univ.filter (fun Q : Finset V => (u ∈ Q ∧ v ∈ Q) ∧ Q ∈ Bs) = {B} := by
      ext Q
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact hu Q ⟨h3, h1, h2⟩
      · rintro rfl; exact ⟨⟨hB.2.1, hB.2.2⟩, hB.1⟩
    rw [this, sum_singleton]
  · unfold fracValue
    rw [← sum_filter, sum_const]
    simp

/-- **Zero LP gap (22).** Under the hypothesis of Theorem A, the minimum uniform cost of a
fractional clique partition (with equality on every edge), unrestricted or restricted to
blocks of order at most four, equals `cp_{≤4}(G) = cp(G)`. -/
theorem fractional_eq_cp (hn : 2 ≤ Fintype.card V) (hP : P.card = (Fintype.card V + 1) / 3)
    (hh : 18 * editDegree G P + 1 ≤ P.card) :
    IsLeast {v : ℝ | ∃ x, IsFracPartition G x ∧ fracValue x = v} (cp G : ℝ) ∧
    IsLeast {v : ℝ | ∃ x, IsFracPartitionLe 4 G x ∧ fracValue x = v} (cp G : ℝ) ∧
    cpLe 4 G = cp G := by
  obtain ⟨-, h4, hcp, Bs, hBs, hcard, hle, -⟩ := theoremA G P hn hP hh
  obtain ⟨hxf, hxv⟩ := isFracPartition_indicator G hBs
  have hcpQ : (cp G : ℝ) = (sCount G P : ℝ) - uCount G P - 2 * mCount G P := by
    exact_mod_cast hcp
  refine ⟨⟨⟨_, hxf, by rw [hxv, hcard]⟩, ?_⟩, ⟨⟨_, ⟨hxf, fun Q hQ => ?_⟩, by rw [hxv, hcard]⟩,
    ?_⟩, h4.symm⟩
  · rintro v ⟨x, hx, rfl⟩
    rw [hcpQ]; exact frac_lower_bound G P hx
  · have hQ' : Q ∈ Bs := by by_contra h; simp [h] at hQ
    exact hle Q hQ'
  · rintro v ⟨x, hx, rfl⟩
    rw [hcpQ]; exact frac_lower_bound G P hx.1

/-- **Support of optimal fractional partitions (Section 7).** Under the hypothesis of
Theorem A, every optimal fractional clique partition is supported on blocks of the four
zero-slack types `(1,1), (2,1), (2,2), (3,2)`. -/
theorem frac_optimal_support (hn : 2 ≤ Fintype.card V) (hP : P.card = (Fintype.card V + 1) / 3)
    (hh : 18 * editDegree G P + 1 ≤ P.card) {x : Finset V → ℝ} (hx : IsFracPartition G x)
    (hopt : fracValue x = cp G) :
    ∀ Q, x Q ≠ 0 → (coreSize P Q = 1 ∧ extSize P Q = 1) ∨ (coreSize P Q = 2 ∧ extSize P Q = 1) ∨
      (coreSize P Q = 2 ∧ extSize P Q = 2) ∨ (coreSize P Q = 3 ∧ extSize P Q = 2) := by
  have hcp := (theoremA G P hn hP hh).2.2.1
  have hcpQ : (cp G : ℝ) = (sCount G P : ℝ) - uCount G P - 2 * mCount G P := by
    exact_mod_cast hcp
  have hid := frac_slack_identity G P hx
  rw [hopt, hcpQ, sub_self] at hid
  have hz := (sum_eq_zero_iff_of_nonneg (fun Q _ => mul_nonneg
    (by exact_mod_cast slack_nonneg _ _) (hx.nonneg Q))).mp hid.symm
  intro Q hQ
  have := hz Q (mem_univ Q)
  rcases mul_eq_zero.mp this with h | h
  · exact (slack_eq_zero_iff _ _).mp (by exact_mod_cast h)
  · exact absurd h hQ

end PaperVI
