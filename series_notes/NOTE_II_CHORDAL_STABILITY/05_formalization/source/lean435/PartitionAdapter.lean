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

import PaperIV.FarRounding
import PaperIV.Model
import PaperIV.RootVocabulary
import PaperIV.RD09SplitEditAccount
import PaperVI.Counting

namespace ChordalStabilityNote

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The physical IV partition is literally a partition for VI's optimum definition. -/
theorem physical_partition_to_VI {Bs : Finset (Finset V)}
    (h : PaperIV.Model.IsExactPartition G Bs) : PaperVI.IsCliquePartition G Bs := by
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨k, hk⟩ := (h.pieces B hB).kind
    rw [hk]
    cases k <;> norm_num [PaperIV.Model.PieceKind.size]
  · intro B hB
    exact (h.pieces B hB).clique
  · intro u v huv
    have hedge : s(u, v) ∈ PaperIV.Model.graphEdges G :=
      (PaperIV.Model.mem_graphEdges G).mpr (show s(u, v) ∈ G.edgeSet from huv)
    obtain ⟨B, ⟨hB, he⟩, hu⟩ := h.existsUnique_piece hedge
    have he' := PaperIV.Model.mem_pieceEdges_mk.mp he
    refine ⟨B, ⟨hB, he'.1, he'.2.1⟩, ?_⟩
    rintro B' ⟨hB', hu', hv'⟩
    exact hu B' ⟨hB', PaperIV.Model.mem_pieceEdges_mk.mpr ⟨hu', hv', huv.ne⟩⟩

theorem cp_le_physical_partition {Bs : Finset (Finset V)}
    (h : PaperIV.Model.IsExactPartition G Bs) : PaperVI.cp G ≤ Bs.card :=
  PaperVI.cp_le (physical_partition_to_VI h)

/-- The far-rounding partition interface also bounds VI's actual cp. -/
theorem far_partition_to_VI (Q : PaperIV.FarRounding.CliquePartition G) :
    PaperVI.IsCliquePartition G Q.pieces := by
  refine ⟨Q.two_le_card, ?_, ?_⟩
  · intro B hB u hu v hv huv
    exact Q.isClique B hB u hu v hv huv
  · intro u v huv
    have he : s(u, v) ∈ Q.pieces.biUnion PaperIV.FarRounding.pairs := by
      rw [Q.covers]
      exact SimpleGraph.mem_edgeFinset.mpr huv
    obtain ⟨B, hB, heB⟩ := mem_biUnion.mp he
    obtain ⟨huB, hvB, -⟩ := PaperIV.FarRounding.mk_mem_pairs.mp heB
    refine ⟨B, ⟨hB, huB, hvB⟩, ?_⟩
    rintro B' ⟨hB', huB', hvB'⟩
    by_contra hne
    have hd := Q.edgeDisjoint B' hB' B hB hne
    exact (disjoint_left.mp hd)
      (PaperIV.FarRounding.mk_mem_pairs.mpr ⟨huB', hvB', huv.ne⟩) heB

theorem cp_le_far_partition (Q : PaperIV.FarRounding.CliquePartition G) :
    PaperVI.cp G ≤ Q.size :=
  PaperVI.cp_le (far_partition_to_VI Q)

/-- IV's literal exterior-edge family equals VI's exterior-edge family. -/
theorem outsideEdges_eq_extEdges (P : Finset V) :
    PaperIV.RootVocab.outsideEdges G P = PaperVI.extEdges G P := by
  classical
  ext e
  simp only [PaperIV.RootVocab.outsideEdges, PaperVI.extEdges, mem_filter]
  constructor
  · rintro ⟨he, hs⟩
    exact ⟨he, fun v hv => PaperIV.RootVocab.mem_outsideVertices.mp (hs hv)⟩
  · rintro ⟨he, hs⟩
    exact ⟨he, fun v hv => PaperIV.RootVocab.mem_outsideVertices.mpr (hs v hv)⟩

theorem rootEdges_eq_coreEdges (P : Finset V) :
    PaperIV.RootVocab.rootEdges G P = PaperVI.coreEdges G P := by
  classical
  rfl

/-- The root-loss account counts exactly the missing spokes used by VI. -/
theorem missingSpoke_card_eq_Adef (P : Finset V) :
    ((PaperIV.RD09SplitEditAccount.missingSpokeEdges G P).card : ℤ) =
      PaperVI.Adef G P := by
  classical
  rw [PaperIV.RD09SplitEditAccount.card_missingSpokeEdges]
  have hIV := PaperIV.RootVocab.card_edgeFinset_add_missingIncidences G P
  rw [rootEdges_eq_coreEdges P, outsideEdges_eq_extEdges P] at hIV
  have hVI := PaperVI.card_kinds P G.edgeFinset
  change (PaperVI.coreEdges G P).card + (PaperVI.extEdges G P).card +
    (PaperVI.crossEdges G P).card = G.edgeFinset.card at hVI
  have ho : (PaperIV.RootVocab.outsideVertices P).card = Fintype.card V - P.card := by
    rw [PaperIV.RootVocab.outsideVertices, Finset.card_sdiff_of_subset (Finset.subset_univ P),
      Finset.card_univ]
  rw [ho] at hIV
  have hA : (PaperVI.crossEdges G P).card + PaperIV.RootVocab.missingIncidences G P =
      P.card * (Fintype.card V - P.card) := by omega
  have hp := Finset.card_le_univ P
  have hAZ : ((PaperVI.crossEdges G P).card : ℤ) +
      PaperIV.RootVocab.missingIncidences G P =
      (P.card : ℤ) * ((Fintype.card V : ℤ) - P.card) := by
    exact_mod_cast hA
  unfold PaperVI.Adef PaperVI.sCount
  omega

theorem Cdef_eq_zero_of_clique (P : Finset V) (hP : G.IsClique (P : Set V)) :
    PaperVI.Cdef G P = 0 := by
  have h := PaperIV.RootVocab.card_rootEdges G P hP
  rw [rootEdges_eq_coreEdges P] at h
  simp [PaperVI.Cdef, PaperVI.uCount, h]

end ChordalStabilityNote

#print axioms ChordalStabilityNote.cp_le_physical_partition
#print axioms ChordalStabilityNote.cp_le_far_partition
#print axioms ChordalStabilityNote.outsideEdges_eq_extEdges
#print axioms ChordalStabilityNote.missingSpoke_card_eq_Adef
#print axioms ChordalStabilityNote.Cdef_eq_zero_of_clique
