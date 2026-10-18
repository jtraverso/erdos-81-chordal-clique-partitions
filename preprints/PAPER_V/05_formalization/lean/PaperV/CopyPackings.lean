/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini

Paper V, Theorem 6.2: the image multiset of the specified copied packings.
This strengthens the public interface, without changing the copy inequality.
-/
module

public import PaperV.CopyCore

@[expose] public section

namespace PaperV

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual multiset obtained by mapping the two specified triangle families. -/
def triangleImageMultiset (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V)
    (P' : Finset (triCS (copyGraph G v u)).O)
    (P'' : Finset (triCS (copyGraph G u v)).O) : (triCS G).O → ℕ :=
  fun t => (P'.filter (fun s => copyMap v u s.1 = t.1)).card +
    (P''.filter (fun s => copyMap u v s.1 = t.1)).card

theorem triangleImageMultiset_size (G : SimpleGraph V) [DecidableRel G.Adj]
    (v u : V) (huv : ¬ G.Adj u v)
    (P' : Finset (triCS (copyGraph G v u)).O)
    (P'' : Finset (triCS (copyGraph G u v)).O) :
    multSize (triCS G) (triangleImageMultiset G v u P' P'') = P'.card + P''.card := by
  classical
  simp only [multSize, triangleImageMultiset, Finset.sum_add_distrib]
  rw [← card_copyMap_fibers G v u huv P',
    ← card_copyMap_fibers G u v (fun h => huv h.symm) P'']

theorem triangleImageMultiset_isQMultiset (G : SimpleGraph V) [DecidableRel G.Adj]
    (v u : V) (huv : ¬ G.Adj u v)
    (P' : Finset (triCS (copyGraph G v u)).O)
    (P'' : Finset (triCS (copyGraph G u v)).O)
    (hP' : CSFeasible (triCS (copyGraph G v u)) P')
    (hP'' : CSFeasible (triCS (copyGraph G u v)) P'') :
    IsQMultiset (triCS G) (triangleImageMultiset G v u P' P'') 2 := by
  classical
  have hinj' := copyMap_injective_on_feasible G v u huv P' hP'
  have hinj'' := copyMap_injective_on_feasible G u v (fun h => huv h.symm) P'' hP''
  intro t
  have hleft : (P'.filter (fun s => copyMap v u s.1 = t.1)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    apply hinj' (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1
    exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
  have hright : (P''.filter (fun s => copyMap u v s.1 = t.1)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    apply hinj'' (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1
    exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
  exact Nat.add_le_add hleft hright

/-- Copy bound for the actual images of any specified feasible copied packings. -/
theorem copy_integral_for_packings (G : SimpleGraph V) [DecidableRel G.Adj]
    (v u : V) (huv : ¬ G.Adj u v)
    (P' : Finset (triCS (copyGraph G v u)).O)
    (P'' : Finset (triCS (copyGraph G u v)).O)
    (hP' : CSFeasible (triCS (copyGraph G v u)) P')
    (hP'' : CSFeasible (triCS (copyGraph G u v)) P'') :
    P'.card + P''.card ≤ 2 * nu3 G +
      oct (Hgraph (triCS G) (triangleImageMultiset G v u P' P'')) := by
  have h := transfer_half (triCS G) (triangleImageMultiset G v u P' P'')
    (triangleImageMultiset_isQMultiset G v u huv P' P'' hP' hP'')
  rw [triangleImageMultiset_size G v u huv P' P''] at h
  exact h

/-- Theorem 6.2 with the specified optimal packings and their actual image multiset. -/
theorem copy_integral_for_optimal_packings (G : SimpleGraph V) [DecidableRel G.Adj]
    (v u : V) (huv : ¬ G.Adj u v)
    (P' : Finset (triCS (copyGraph G v u)).O)
    (P'' : Finset (triCS (copyGraph G u v)).O)
    (hP' : CSFeasible (triCS (copyGraph G v u)) P')
    (hP'' : CSFeasible (triCS (copyGraph G u v)) P'')
    (hcard' : P'.card = nu3 (copyGraph G v u))
    (hcard'' : P''.card = nu3 (copyGraph G u v)) :
    nu3 (copyGraph G v u) + nu3 (copyGraph G u v) ≤ 2 * nu3 G +
      oct (Hgraph (triCS G) (triangleImageMultiset G v u P' P'')) := by
  have h := copy_integral_for_packings G v u huv P' P'' hP' hP''
  rwa [hcard', hcard''] at h

end PaperV
