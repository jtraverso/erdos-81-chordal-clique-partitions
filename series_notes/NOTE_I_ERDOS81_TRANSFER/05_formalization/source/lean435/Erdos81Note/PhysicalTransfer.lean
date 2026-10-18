/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-
Author: Juan Pablo Traverso Gianini
This attribution identifies the author of this series formalization.
Existing mathematical, tool-assistance and third-party credits are retained below.
-/

/- Application of Paper V's actual realizable-class transfer to physical clique packings. -/
import PaperIV.FarRounding
import PaperV.Realizer

namespace Erdos81Note
open Finset PaperIV.FarRounding
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Objects are real K3/K4 copies; a conflict means a shared physical edge. -/
noncomputable abbrev physicalCS (G : SimpleGraph V) [DecidableRel G.Adj] : PaperV.ConflictSystem := by
  classical
  exact {
    O := {K : Finset V // IsItem G K}
    K := fun a b => a ≠ b ∧ ¬ Disjoint (pairs a.val) (pairs b.val)
    Ksymm := by
      rintro a b ⟨hne,h⟩
      exact ⟨hne.symm, fun hd => h hd.symm⟩
    Kirrefl := fun a h => h.1 rfl }

def physicalWeight (G : SimpleGraph V) [DecidableRel G.Adj] : (physicalCS G).O → ℕ :=
  fun K => gainOf K.val

/-- A feasible output of V is an actual edge-disjoint packing in IV's model. -/
noncomputable def toPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (physicalCS G).O) (hS : PaperV.CSFeasible (physicalCS G) S) : Packing G := by
  classical
  exact {
    pieces := S.image Subtype.val
    isItem := by
      intro K hK
      obtain ⟨a,_,rfl⟩ := mem_image.mp hK
      exact a.property
    edgeDisjoint := by
      intro K hK L hL hne
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hK
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hL
      by_contra hd
      exact hS ha hb ⟨fun h => hne (congrArg Subtype.val h),hd⟩ }

theorem toPacking_gain (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (physicalCS G).O) (hS : PaperV.CSFeasible (physicalCS G) S) :
    (toPacking G S hS).gain=∑ o ∈ S, physicalWeight G o := by
  classical
  unfold toPacking Packing.gain
  rw [sum_image]
  · rfl
  · intro a _ b _ hab
    exact Subtype.ext hab

/-- A physical packing can be supplied as the output of a realizability certificate. -/
noncomputable def liftPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Packing G) : Finset (physicalCS G).O := by
  classical
  exact P.pieces.attach.image (fun K => ⟨K.val,P.isItem K.val K.property⟩)

theorem liftPacking_feasible (G : SimpleGraph V) [DecidableRel G.Adj] (P : Packing G) :
    PaperV.CSFeasible (physicalCS G) (liftPacking G P) := by
  classical
  intro a ha b hb hconf
  obtain ⟨a',ha',rfl⟩ := mem_image.mp ha
  obtain ⟨b',hb',rfl⟩ := mem_image.mp hb
  exact hconf.2 (P.edgeDisjoint _ a'.property _ b'.property
    (fun h => hconf.1 (Subtype.ext h)))

theorem liftPacking_gain (G : SimpleGraph V) [DecidableRel G.Adj] (P : Packing G) :
    ∑ o ∈ liftPacking G P, physicalWeight G o=P.gain := by
  classical
  unfold liftPacking physicalWeight Packing.gain
  rw [sum_image]
  · exact sum_attach _ _
  · intro a _ b _ h
    exact Subtype.ext (congrArg (fun K : (physicalCS G).O => K.val) h)

/-- The integer form of the note's transfer-to-partition budget theorem.
The source may be auxiliary; the target always consists of real cliques of G. -/
theorem partition_of_certificate (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : PaperV.ConflictSystem) (w : C.O → ℕ) (X : C.O → ℕ) {q T : ℕ}
    (hq : 1 ≤ q)
    (cert : PaperV.RealCert C (physicalCS G) w (physicalWeight G) X q)
    (hbudget : q*G.edgeFinset.card+cert.cost ≤ q*T+PaperV.wMultSize C w X) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ T := by
  obtain ⟨i,hi⟩ := PaperV.realizable_class_transfer hq cert
  let P := toPacking G (cert.real i).out (cert.real i).feasible
  have hg : P.gain=∑ o ∈ (cert.real i).out, physicalWeight G o :=
    toPacking_gain G _ _
  obtain ⟨Q,hQ4,hQsum⟩ := exists_cliquePartition_of_packing P
  refine ⟨Q,hQ4,?_⟩
  have hprod : q*Q.size ≤ q*T := by rw [← hg] at hi; nlinarith
  exact Nat.le_of_mul_le_mul_left hprod hq

/-- A singleton auxiliary demand is used in the one-class specializations. -/
def oneDemand : PaperV.ConflictSystem where
  O := Unit
  K _ _ := False
  Ksymm := fun _ _ h => h.elim
  Kirrefl := fun _ h => h
  decK := fun _ _ => isFalse id

/-- Certificate for a packing relative to a reference gain L fixed before its construction.
The explicit residual L-gain is retained; no target partition bound is an input. -/
noncomputable def certificateOfPacking (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : ℕ) (P : Packing G) (hL : P.gain ≤ L) :
    PaperV.RealCert oneDemand (physicalCS G) (fun _ => L) (physicalWeight G) (fun _ => 1) 1 := by
  classical
  refine { Z := ∅, part := fun _ => 0, real := fun i => ?_ }
  refine { out := liftPacking G P
           feasible := liftPacking_feasible G P
           loss := L-P.gain
           bound := ?_ }
  rw [liftPacking_gain]
  have hc : (PaperV.classOf oneDemand (X := fun _ => 1) ∅ (fun _ => (0 : Fin 1)) i).card=1 := by
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    simp [PaperV.classOf]
    change Fintype.card (Σ _ : Unit, Fin 1) = 1
    simp
  simp only [PaperV.copyWeight]
  rw [sum_const,hc]
  simp
  omega

theorem certificateOfPacking_cost (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : ℕ) (P : Packing G) (hL : P.gain ≤ L) :
    (certificateOfPacking G L P hL).cost=L-P.gain := by
  simp [PaperV.RealCert.cost,certificateOfPacking]

theorem partition_of_reference_gain (G : SimpleGraph V) [DecidableRel G.Adj]
    (L T : ℕ) (P : Packing G) (hL : P.gain ≤ L)
    (hbudget : G.edgeFinset.card+(L-P.gain) ≤ T+L) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ T := by
  apply partition_of_certificate G oneDemand (fun _ => L) (fun _ => 1) (by omega)
    (certificateOfPacking G L P hL)
  rw [certificateOfPacking_cost]
  have htotal : PaperV.wMultSize oneDemand (fun _ => L) (fun _ => 1) = L := by
    change (∑ _ : Unit, L * 1) = L
    simp
  rw [htotal]
  simpa only [one_mul] using hbudget

end Erdos81Note
