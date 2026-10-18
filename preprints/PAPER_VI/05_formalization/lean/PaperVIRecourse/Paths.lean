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
/- Finite paths of actual block partitions, with a physical symmetric-difference
bound on every step and the stated graph property at every vertex. -/
module
public import PaperVIRecourse.PhysicalRecourse
@[expose] public section
namespace PaperVIRecourse
open Finset PaperVI
open scoped symmDiff
variable {V : Type*} [DecidableEq V]

inductive BlockPath (Good : Finset (Finset V) → Prop) (D : ℕ) :
    ℕ → Finset (Finset V) → Finset (Finset V) → Prop where
  | refl {A} (hA : Good A) : BlockPath Good D 0 A A
  | step {n A B C} (hA : Good A) (hD : (A ∆ B).card ≤ D)
      (tail : BlockPath Good D n B C) : BlockPath Good D (n+1) A C

theorem BlockPath.trans {Good : Finset (Finset V) → Prop} {D n m : ℕ}
    {A B C : Finset (Finset V)} (p : BlockPath Good D n A B)
    (q : BlockPath Good D m B C) : BlockPath Good D (n+m) A C := by
  induction p with
  | refl h => simpa using q
  | step h hd tail ih =>
    simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
      BlockPath.step h hd (ih q)

theorem BlockPath.widen {Good : Finset (Finset V) → Prop} {D D' n : ℕ}
    {A B : Finset (Finset V)} (p : BlockPath Good D n A B) (h : D ≤ D') :
    BlockPath Good D' n A B := by
  induction p with
  | refl hA => exact BlockPath.refl hA
  | step hA hd _ ih => exact BlockPath.step hA (hd.trans h) ih

variable [Fintype V]

/-- An actual optimal edge clique partition with a legal complete all-K5 lifting
whose core loads are bounded by r. -/
def BoundedAllK5Opt (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)
    (r : ℕ) (Bs : Finset (Finset V)) : Prop :=
  IsCliquePartition G Bs ∧ Bs.card = cp G ∧
    ∃ T : Sym2 V → Finset V, LiftInv G P (fun _ => 3) r (extEdges G P) T ∧
      ∀ e ∈ extEdges G P, T e ∪ e.toFinset ∈ Bs

end PaperVIRecourse
