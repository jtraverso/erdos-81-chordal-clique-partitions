/-
Author: Juan Pablo Traverso Gianini.
Existing third-party credits below are retained.
-/
/-
Paper VI research round — Priority 2: the intrinsic formula and degree recognition of the core.

* (I1) For every vertex set `Q`, `cp(G) ≥ Φ_Q(G) = s_Q - u_Q - 2 m_Q` (no size restriction).
* (I2) Under the hypothesis of Theorem A, `cp(G) = max_Q Φ_Q(G) = Φ_P(G)`.
* (I3) Under the hypothesis of Theorem A and `n ≥ 3`, the core is recognised by degrees:
  `P = {v : 2 d(v) > n}`. Hence `cp(G) = Φ_{P_deg}(G)` is a function of `G` alone.

This is a statement about the VALUE `cp(G)`; no polynomial-time construction of an optimal
partition is claimed.
-/
module

public import PaperVI.TheoremA

@[expose] public section

namespace PaperVI

namespace Research

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The slack certificate value `Φ_Q(G) = s_Q - u_Q - 2 m_Q` of a vertex set `Q`. -/
def PhiQ (G : SimpleGraph V) [Fintype G.edgeSet] (Q : Finset V) : ℤ :=
  (sCount G Q : ℤ) - uCount G Q - 2 * mCount G Q

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **(I1)** The universal slack lower bound: `cp(G) ≥ Φ_Q(G)` for every `Q`. -/
theorem PhiQ_le_cp (Q : Finset V) : PhiQ G Q ≤ cp G := cp_ge G Q

/-- **(I2) Intrinsic formula.** Under the hypothesis of Theorem A (`p = ⌊(n+1)/3⌋`,
`p ≥ 18h + 1`), `cp(G)` is the maximum of `Φ_Q(G)` over all vertex sets `Q`, attained at the
core `P`. (Uniqueness of the maximiser is NOT claimed here.) -/
theorem cp_eq_max_PhiQ (P : Finset V) (hn : 2 ≤ Fintype.card V)
    (hP : P.card = (Fintype.card V + 1) / 3) (hh : 18 * editDegree G P + 1 ≤ P.card) :
    IsGreatest (Set.range (PhiQ G)) (cp G) ∧ (cp G : ℤ) = PhiQ G P := by
  have h := (theoremA G P hn hP hh).2.2.1
  refine ⟨⟨⟨P, h.symm⟩, ?_⟩, h⟩
  rintro v ⟨Q, rfl⟩
  exact PhiQ_le_cp G Q

/-- Degree of a core vertex: `d(a) ≥ n - 1 - h`. -/
theorem degree_core_ge (P : Finset V) {a : V} (ha : a ∈ P) :
    Fintype.card V ≤ G.degree a + 1 + editDegree G P := by
  have h := core_local_bound G P a ha
  have hsub : univ ⊆ insert a (G.neighborFinset a ∪
      (P.filter (fun b => b ≠ a ∧ ¬ G.Adj a b) ∪ Pᶜ.filter (fun x => ¬ G.Adj a x))) := by
    intro v _
    by_cases hva : v = a
    · exact mem_insert.mpr (Or.inl hva)
    · refine mem_insert.mpr (Or.inr ?_)
      by_cases hadj : G.Adj a v
      · exact mem_union_left _ ((G.mem_neighborFinset a v).mpr hadj)
      · refine mem_union_right _ ?_
        by_cases hvP : v ∈ P
        · exact mem_union_left _ (mem_filter.mpr ⟨hvP, hva, hadj⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨mem_compl.mpr hvP, hadj⟩)
  have h1 := card_le_card hsub
  rw [card_univ] at h1
  have h2 := card_insert_le a (G.neighborFinset a ∪
      (P.filter (fun b => b ≠ a ∧ ¬ G.Adj a b) ∪ Pᶜ.filter (fun x => ¬ G.Adj a x)))
  have h3 := card_union_le (G.neighborFinset a)
      (P.filter (fun b => b ≠ a ∧ ¬ G.Adj a b) ∪ Pᶜ.filter (fun x => ¬ G.Adj a x))
  have h4 := card_union_le (P.filter (fun b => b ≠ a ∧ ¬ G.Adj a b))
    (Pᶜ.filter (fun x => ¬ G.Adj a x))
  rw [SimpleGraph.card_neighborFinset_eq_degree] at h3
  omega

/-- Degree of an exterior vertex: `d(x) ≤ p + h`. -/
theorem degree_ext_le (P : Finset V) {x : V} (hx : x ∉ P) :
    G.degree x ≤ P.card + editDegree G P := by
  have h := ext_local_bound G P x hx
  have hsub : G.neighborFinset x ⊆ P ∪ Pᶜ.filter (fun y => G.Adj x y) := by
    intro v hv
    rw [SimpleGraph.mem_neighborFinset] at hv
    by_cases hvP : v ∈ P
    · exact mem_union_left _ hvP
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_compl.mpr hvP, hv⟩)
  have h1 := card_le_card hsub
  have h2 := card_union_le P (Pᶜ.filter (fun y => G.Adj x y))
  rw [SimpleGraph.card_neighborFinset_eq_degree] at h1
  omega

/-- **(I3) Degree recognition of the core.** Under the hypothesis of Theorem A and `n ≥ 3`,
the core is exactly the set of vertices of degree more than `n/2`. -/
theorem core_eq_highDegree (P : Finset V) (hn : 3 ≤ Fintype.card V)
    (hP : P.card = (Fintype.card V + 1) / 3) (hh : 18 * editDegree G P + 1 ≤ P.card) :
    P = univ.filter (fun v => Fintype.card V < 2 * G.degree v) := by
  ext v
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro hv
    have := degree_core_ge G P hv
    omega
  · intro hv
    by_contra hvP
    have := degree_ext_le G P hvP
    omega

/-- **Value recognition.** Under the hypothesis of Theorem A and `n ≥ 3`, `cp(G)` equals
`Φ_{P_deg}(G)` for the degree-defined set `P_deg = {v : 2 d(v) > n}`; no bipartition needs to
be supplied. -/
theorem cp_eq_PhiQ_highDegree (P : Finset V) (hn : 3 ≤ Fintype.card V)
    (hP : P.card = (Fintype.card V + 1) / 3) (hh : 18 * editDegree G P + 1 ≤ P.card) :
    (cp G : ℤ) = PhiQ G (univ.filter (fun v => Fintype.card V < 2 * G.degree v)) := by
  rw [← core_eq_highDegree G P hn hP hh]
  exact (cp_eq_max_PhiQ G P (by omega) hP hh).2

end Research

end PaperVI
