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
Paper VI — Optimal clique partitions under local perturbations.
Basic definitions: the reference graph `K_P ∨ I_O`, the modification parameter `h`,
the edge counts `u, s, m`, the defects `C, A`, clique partitions and the clique
partition numbers `cp`, `cp_{≤ r}`.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Convert
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace PaperVI

open Finset

variable {V : Type*}

/-- The reference graph `S = K_P ∨ I_O`: two distinct vertices are adjacent iff at least one
of them lies in the core `P`. -/
def refGraph (P : Finset V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (u ∈ P ∨ v ∈ P)
  symm := ⟨fun _ _ ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The modification graph `G △ S`. -/
def editGraph (G : SimpleGraph V) (P : Finset V) : SimpleGraph V :=
  symmDiff G (refGraph P)

/-- The modification parameter `h = Δ(G △ S)`. -/
noncomputable def editDegree [Fintype V] (G : SimpleGraph V) (P : Finset V) : ℕ := by
  classical exact (editGraph G P).maxDegree

variable [DecidableEq V]

/-- Edges of `G` with both ends in the core `P` (`u = e(G[P])` is their number). -/
def coreEdges (G : SimpleGraph V) [Fintype G.edgeSet] (P : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∀ v ∈ e.toFinset, v ∈ P)

/-- Edges of `G` with both ends in the exterior `O = Pᶜ` (`m = e(G[O])`). -/
def extEdges (G : SimpleGraph V) [Fintype G.edgeSet] (P : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∀ v ∈ e.toFinset, v ∉ P)

/-- Crossing edges of `G`, with one end in `P` and one in `O` (`s = e_G(P,O)`). -/
def crossEdges (G : SimpleGraph V) [Fintype G.edgeSet] (P : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => (∃ v ∈ e.toFinset, v ∈ P) ∧ ∃ v ∈ e.toFinset, v ∉ P)

/-- `u = e(G[P])`. -/
def uCount (G : SimpleGraph V) [Fintype G.edgeSet] (P : Finset V) : ℕ := (coreEdges G P).card
/-- `s = e_G(P,O)`. -/
def sCount (G : SimpleGraph V) [Fintype G.edgeSet] (P : Finset V) : ℕ := (crossEdges G P).card
/-- `m = e(G[O])`. -/
def mCount (G : SimpleGraph V) [Fintype G.edgeSet] (P : Finset V) : ℕ := (extEdges G P).card

/-- The missing core edges `C = binom(p,2) - e(G[P])`, as an integer. -/
def Cdef (G : SimpleGraph V) [Fintype G.edgeSet] (P : Finset V) : ℤ :=
  (P.card.choose 2 : ℤ) - uCount G P

/-- The missing crossing edges `A = pq - e_G(P,O)`, as an integer (`q = |V| - p`). -/
def Adef [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet] (P : Finset V) : ℤ :=
  (P.card : ℤ) * ((Fintype.card V : ℤ) - P.card) - sCount G P

/-- `M(n) = ⌊n(n+1)/6⌋`. -/
def Mval (n : ℕ) : ℕ := n * (n + 1) / 6

/-- A clique partition of `G`: a finite family of vertex sets of size at least two, each a
clique of `G`, such that every edge of `G` lies in exactly one of them. Thus the edge sets of
the blocks partition `E(G)` exactly. -/
structure IsCliquePartition (G : SimpleGraph V) (Bs : Finset (Finset V)) : Prop where
  two_le : ∀ B ∈ Bs, 2 ≤ B.card
  isClique : ∀ B ∈ Bs, G.IsClique (B : Set V)
  existsUnique : ∀ u v, G.Adj u v → ∃! B, B ∈ Bs ∧ u ∈ B ∧ v ∈ B

/-- The clique partition number `cp(G)`. -/
noncomputable def cp (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ Bs.card = k}

/-- The restricted clique partition number `cp_{≤ r}(G)`: blocks of order at most `r`. -/
noncomputable def cpLe (r : ℕ) (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ (∀ B ∈ Bs, B.card ≤ r) ∧
    Bs.card = k}

/-- The slack `ℓ(a,b) = 1 - ab + binom(a,2) + 2 binom(b,2)` of a clique of type `(a,b)`. -/
def slack (a b : ℕ) : ℤ := 1 - (a : ℤ) * b + (a.choose 2 : ℤ) + 2 * (b.choose 2 : ℤ)

/-- Core size `a` of a block (number of core vertices). -/
def coreSize (P B : Finset V) : ℕ := (B ∩ P).card
/-- Exterior size `b` of a block (number of exterior vertices). -/
def extSize (P B : Finset V) : ℕ := (B \ P).card

end PaperVI
