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
/- Restricted physical connectivity for bounded-load complete all-K5 liftings. -/
module
public import PaperVIRecourse.LiftAlignment
public import PaperVIRecourse.TerminalAlignment
@[expose] public section
namespace PaperVIRecourse
open Finset PaperVI
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

/-- Two actual optimal partitions in the all-K5 bounded-load class are connected
inside that class, with at most u-2m steps and at most 884 changed blocks per step.
This makes no claim about mixed K4/K5 optimal partitions. -/
theorem restricted_allK5_connectivity
    (hjoin : ∀ a ∈ P, ∀ v, a ≠ v → G.Adj a v)
    (hq0 : 2 * P.card ≤ Pᶜ.card + 1) (hq1 : Pᶜ.card ≤ 2 * P.card + 1)
    (hh : 63 * editDegree G P ≤ P.card)
    {Bs₀ BsTarget : Finset (Finset V)}
    (h₀ : BoundedAllK5Opt G P (7 * editDegree G P) Bs₀)
    (hTarget : BoundedAllK5Opt G P (7 * editDegree G P) BsTarget) :
    ∃ n, n ≤ P.card.choose 2 - 2 * mCount G P ∧
      BlockPath (BoundedAllK5Opt G P (7 * editDegree G P)) 884 n Bs₀ BsTarget := by
  classical
  obtain ⟨hBs₀,hopt₀,T₀,hT₀,hlift₀⟩ := h₀
  obtain ⟨hBsTarget,hoptTarget,Tstar,hTstar,hliftTarget⟩ := hTarget
  obtain ⟨n₀,BsMid,hn₀,hpath₀,hMid,hMidOpt,hMidLift⟩ :=
    lift_alignment G P hjoin hq0 hq1 hh hTstar hT₀ hBs₀ hopt₀ hlift₀
  obtain ⟨n₁,hn₁,hpath₁⟩ := terminal_alignment G P hjoin hq0 hTstar
    hMid hMidOpt hMidLift hBsTarget hoptTarget hliftTarget
  have hn₀m : n₀ ≤ mCount G P :=
    hn₀.trans (card_le_card (filter_subset _ _))
  have hcount := (optimal_allK5_counts G P hjoin hq0 hTstar
    hBsTarget hoptTarget hliftTarget).1
  change (terminalBlocks P BsTarget).card + 3 * mCount G P = uCount G P at hcount
  rw [uCount_join G P hjoin] at hcount
  exact ⟨n₀+n₁,by omega,hpath₀.trans (hpath₁.widen (by decide))⟩

end PaperVIRecourse
