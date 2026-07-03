import Mathlib
/-!
# Edge clique partitions and the clique partition number
The paper studies the **edge clique partition number** `cp(G)`: the smallest number of
cliques whose edge sets partition `E(G)`.  Mathlib has `SimpleGraph.IsClique` but no notion
of clique partition, so we introduce it here.
We model an edge clique partition of `G` as a finite family `P` of vertex subsets
(the cliques) such that
* every member of `P` is a clique of `G`, and
* every edge of `G` (i.e. every adjacent pair) lies in a *unique* member of `P`.
`cliquePartitionNumber G` is the least cardinality of such a family.
-/
namespace ErdosSplit
open SimpleGraph Finset
variable {V : Type*} [DecidableEq V]
/-- `P` is an edge clique partition of `G`: each member is a clique, and every edge of `G`
lies in exactly one member. -/
def IsEdgeCliquePartition (G : SimpleGraph V) (P : Finset (Finset V)) : Prop :=
  (∀ K ∈ P, G.IsClique (K : Set V)) ∧
  (∀ ⦃x y⦄, G.Adj x y → ∃! K, K ∈ P ∧ x ∈ K ∧ y ∈ K)
/-- The clique partition number: the least size of an edge clique partition. -/
noncomputable def cliquePartitionNumber (G : SimpleGraph V) : ℕ :=
  sInf {m | ∃ P : Finset (Finset V), IsEdgeCliquePartition G P ∧ P.card = m}
/-- Every finite simple graph has an edge clique partition: cover each edge by the
2-element clique consisting of its endpoints. -/
theorem exists_edgeCliquePartition (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] :
    ∃ P : Finset (Finset V), IsEdgeCliquePartition G P := by
  classical
  refine ⟨(Finset.univ.powersetCard 2).filter (fun K => G.IsClique (K : Set V)), ?_, ?_⟩
  · intro K hK; exact (Finset.mem_filter.mp hK).2
  · intro x y hxy
    have hne : x ≠ y := hxy.ne
    have hcard : ({x, y} : Finset V).card = 2 := Finset.card_pair hne
    have hcl : G.IsClique (({x, y} : Finset V) : Set V) := by
      simp only [Finset.coe_insert, Finset.coe_singleton]
      intro a ha b hb hab
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        first | exact absurd rfl hab | exact hxy | exact hxy.symm
    refine ⟨{x, y}, ⟨?_, by simp, by simp⟩, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨⟨Finset.subset_univ _, hcard⟩, hcl⟩
    · rintro K ⟨hK, hxK, hyK⟩
      rw [Finset.mem_filter, Finset.mem_powersetCard] at hK
      have hsub : ({x, y} : Finset V) ⊆ K := by
        intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; omega)).symm
omit [DecidableEq V] in
/-- If every edge clique partition of `G` has at least `N` parts and at least one edge
clique partition exists, then `N ≤ cliquePartitionNumber G`. -/
theorem le_cliquePartitionNumber (G : SimpleGraph V) {N : ℕ}
    (hne : ∃ P : Finset (Finset V), IsEdgeCliquePartition G P)
    (hbound : ∀ P : Finset (Finset V), IsEdgeCliquePartition G P → N ≤ P.card) :
    N ≤ cliquePartitionNumber G := by
  apply le_csInf
  · obtain ⟨P, hP⟩ := hne; exact ⟨P.card, P, hP, rfl⟩
  · rintro m ⟨P, hP, rfl⟩; exact hbound P hP
end ErdosSplit
