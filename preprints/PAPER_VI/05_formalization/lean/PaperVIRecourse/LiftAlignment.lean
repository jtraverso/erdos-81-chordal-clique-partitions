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
/- Align the exterior lifting to a bounded-load target while preserving every
already aligned assignment; lift each step to actual optimal block partitions. -/
module
public import PaperVIRecourse.ProtectedLifting
public import PaperVIRecourse.Paths
@[expose] public section
namespace PaperVIRecourse
open Finset PaperVI
open scoped symmDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

theorem protected_allK5_step
    (hq1 : Pᶜ.card ≤ 2 * P.card + 1) (hh : 63 * editDegree G P ≤ P.card)
    {T Tstar : Sym2 V → Finset V}
    (hT : LiftInv G P (fun _ => 3) (7 * editDegree G P) (extEdges G P) T)
    (hTstar : LiftInv G P (fun _ => 3) (7 * editDegree G P) (extEdges G P) Tstar)
    {Q : Finset (Sym2 V)} (hQsub : Q ⊆ extEdges G P)
    (hprotect : ∀ e ∈ Q, T e = Tstar e)
    {e0 : Sym2 V} (he0 : e0 ∈ extEdges G P) (he0Q : e0 ∉ Q) :
    ∃ T', LiftInv G P (fun _ => 3) (7 * editDegree G P) (extEdges G P) T' ∧
      T' e0 = Tstar e0 ∧ (∀ e ∈ Q, T' e = Tstar e) ∧
      (changedAssignments G P T T').card ≤ 13 := by
  classical
  have hhpos : 1 ≤ editDegree G P := by
    induction e0 using Sym2.ind with
    | h x y =>
      rw [mem_extEdges] at he0
      have hb := ext_local_bound G P x he0.2.1
      have hp : 0 < (Pᶜ.filter (fun y => G.Adj x y)).card :=
        card_pos.mpr ⟨y,mem_filter.mpr ⟨mem_compl.mpr he0.2.2,he0.1⟩⟩
      omega
  obtain ⟨T',hT',hnew,hret,hdiff⟩ := protected_recourse_lift G P
    (c := 3) (need := 30 * editDegree G P + 3) (by omega)
    hT hTstar hQsub hprotect he0 he0Q (by rw [hTstar.card e0 he0])
    (fun _ _ => by omega) (fun _ _ => by dsimp; omega)
    (fun k bx by_ dx dy sat nD h1 h2 h3 h4 h5 h6 =>
      arith_candidates_B hq1 hh h1 h2 h3 h4 h5 h6)
  refine ⟨T',hT',hnew,hret,?_⟩
  simpa only [changedAssignments,ne_comm] using hdiff

/-- Finite protected alignment of the lifting. Each move is a genuine full
partition reconstruction at distance at most 884. The final lifting is the
specified target, while the terminal triangles are allowed to differ. -/
theorem lift_alignment
    (hjoin : ∀ a ∈ P, ∀ v, a ≠ v → G.Adj a v)
    (hq0 : 2 * P.card ≤ Pᶜ.card + 1) (hq1 : Pᶜ.card ≤ 2 * P.card + 1)
    (hh : 63 * editDegree G P ≤ P.card)
    {Tstar : Sym2 V → Finset V}
    (hTstar : LiftInv G P (fun _ => 3) (7 * editDegree G P) (extEdges G P) Tstar)
    {T : Sym2 V → Finset V}
    (hT : LiftInv G P (fun _ => 3) (7 * editDegree G P) (extEdges G P) T)
    {Bs₀ : Finset (Finset V)} (hBs₀ : IsCliquePartition G Bs₀)
    (hopt₀ : Bs₀.card = cp G)
    (hlift₀ : ∀ e ∈ extEdges G P, T e ∪ e.toFinset ∈ Bs₀) :
    ∃ n BsEnd, n ≤ (changedAssignments G P T Tstar).card ∧
      BlockPath (BoundedAllK5Opt G P (7 * editDegree G P)) 884 n Bs₀ BsEnd ∧
      IsCliquePartition G BsEnd ∧ BsEnd.card = cp G ∧
      ∀ e ∈ extEdges G P, Tstar e ∪ e.toFinset ∈ BsEnd := by
  classical
  have key : ∀ d : ℕ, ∀ T : Sym2 V → Finset V,
      LiftInv G P (fun _ => 3) (7 * editDegree G P) (extEdges G P) T →
      ∀ Bs : Finset (Finset V), IsCliquePartition G Bs → Bs.card = cp G →
      (∀ e ∈ extEdges G P, T e ∪ e.toFinset ∈ Bs) →
      (changedAssignments G P T Tstar).card = d →
      ∃ n BsEnd, n ≤ d ∧
        BlockPath (BoundedAllK5Opt G P (7 * editDegree G P)) 884 n Bs BsEnd ∧
        IsCliquePartition G BsEnd ∧ BsEnd.card = cp G ∧
        ∀ e ∈ extEdges G P, Tstar e ∪ e.toFinset ∈ BsEnd := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro T hT Bs hBs hopt hlift hcard
      have hGood : BoundedAllK5Opt G P (7 * editDegree G P) Bs :=
        ⟨hBs,hopt,T,hT,hlift⟩
      by_cases hz : d = 0
      · have hzero : changedAssignments G P T Tstar = ∅ := card_eq_zero.mp (by omega)
        have hagree : ∀ e ∈ extEdges G P, T e = Tstar e := by
          intro e he
          by_contra hne
          have hm : e ∈ changedAssignments G P T Tstar := mem_filter.mpr ⟨he,hne⟩
          rw [hzero] at hm
          exact notMem_empty e hm
        refine ⟨0,Bs,by omega,BlockPath.refl hGood,hBs,hopt,?_⟩
        intro e he
        rw [← hagree e he]
        exact hlift e he
      · obtain ⟨e0,he0⟩ := card_pos.mp (show 0 < (changedAssignments G P T Tstar).card by omega)
        have he0E := (mem_filter.mp he0).1
        have he0ne := (mem_filter.mp he0).2
        let Q := (extEdges G P).filter (fun e => T e = Tstar e)
        have hQsub : Q ⊆ extEdges G P := filter_subset _ _
        have hprotect : ∀ e ∈ Q, T e = Tstar e := fun e he => (mem_filter.mp he).2
        have he0Q : e0 ∉ Q := fun he => he0ne ((mem_filter.mp he).2)
        obtain ⟨T',hT',hnew,hret,hd13⟩ := protected_allK5_step G P hq1 hh
          hT hTstar hQsub hprotect he0E he0Q
        have hsub : changedAssignments G P T' Tstar ⊆ changedAssignments G P T Tstar := by
          intro e he
          obtain ⟨heE,hne⟩ := mem_filter.mp he
          refine mem_filter.mpr ⟨heE,?_⟩
          intro heq
          exact hne (hret e (mem_filter.mpr ⟨heE,heq⟩))
        have hnnew : e0 ∉ changedAssignments G P T' Tstar := by
          intro he
          exact (mem_filter.mp he).2 hnew
        have hneSets : changedAssignments G P T' Tstar ≠ changedAssignments G P T Tstar := by
          intro heq
          exact hnnew (heq.symm ▸ he0)
        have hlt : (changedAssignments G P T' Tstar).card < d := by
          rw [← hcard]
          exact card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,hneSets⟩)
        obtain ⟨Bs',hBs',hopt',hlift',_,hd68,_⟩ :=
          exists_full_allK5_recourse G P hjoin hq0 hT hT' hBs hopt hlift
        have hd884 : (Bs ∆ Bs').card ≤ 884 :=
          allK5_distance_of_thirteen_changes Bs Bs' hd13 hd68
        obtain ⟨n,BsEnd,hn,hpath,hEnd,hEndOpt,hEndLift⟩ :=
          ih (changedAssignments G P T' Tstar).card hlt T' hT' Bs' hBs' hopt' hlift' rfl
        exact ⟨n+1,BsEnd,by omega,BlockPath.step hGood hd884 hpath,hEnd,hEndOpt,hEndLift⟩
  exact key _ T hT Bs₀ hBs₀ hopt₀ hlift₀ rfl

end PaperVIRecourse
