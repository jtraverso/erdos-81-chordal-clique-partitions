/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Original mathematical attributions and third-party notices are retained below.
-/

/-
Paper V formalization and integration.
Authors: Juan Pablo Traverso Gianini

Original mathematical attributions and existing source/port provenance are
retained below; this author credit does not reattribute those prior results.
-/

/-
Paper V — Preprint 1.0 canonical Lean/Mathlib 4.35 development.
Colorability and Realizability Defects in Resource-Dominated Packing Relaxations.

The public root exports the finite transfer, realization, copy, host, resource-LP
and supporting mathematical results. Exact source closure, signatures, axiom
footprints and reproduction commands are documented in the formal companion.
Historical development records are separate from this public interface.
-/

module

public import PaperV.Defs
public import PaperV.Core
public import PaperV.ConflictGraph
public import PaperV.PackingCert
public import PaperV.Parity
public import PaperV.Copy
public import PaperV.CopyPackings
public import PaperV.CopyFrac
public import PaperV.Seal
public import PaperV.Clon2
public import PaperV.Tightness
public import PaperV.StarT2
public import PaperV.BK
public import PaperV.Certificates
public import PaperV.PureProfile
public import PaperV.N2
public import PaperV.N2Gap
-- Brooks-independent fully-proved extension modules (Layer-E):
public import PaperV.CoverDefect
public import PaperV.SplittingQ
public import PaperV.DqBasic
public import PaperV.OddCycle
public import PaperV.TransferCorollaries
public import PaperV.LineGraph
public import PaperV.Extremal
public import PaperV.ChromaticIndex
public import PaperV.DefectApps
public import PaperV.SumDefect
-- Brooks-dependent corollaries now discharged by the closed Brooks chain:
public import PaperV.BrooksMain
public import PaperV.BrooksOct
public import PaperV.C1
public import PaperV.N1
-- Exact cycle-defect examples:
public import PaperV.CycleDefect
-- Mathlib-absent classical tools + P4-133 (Aug 2026):
public import PaperV.Vizing
public import PaperV.BeckFiala
public import PaperV.TerminalPairRounding
public import PaperV.TerminalPairAssembly
-- v0.9.19 additions (Sep 2026): DV26 / DV27 / AV5441 / edge-defect profile:
public import PaperV.WeightedTransfer
public import PaperV.LoadTwoK4
public import PaperV.UnitBoundaryCompletion
public import PaperV.EdgeDefectProfile
public import PaperV.UnitBoundaryWitnesses
public import PaperV.SealTermination
public import PaperV.CoverWitness
public import PaperV.SteinerK4
public import PaperV.SteinerK4Oct
public import PaperV.AffineK4
public import PaperV.SteinerFrac
-- Paper V wave 1 (Sep 2026): D_1 identity, rational LP certificate contract, cleanup/owned union, weighted Appendix A, mixed copies:
public import PaperV.DefectOne
public import PaperV.RationalLP
public import PaperV.CleanupTransfer
public import PaperV.UnitBoundaryWeighted
public import PaperV.MixedCopy
-- Paper V wave 2a (Sep 2026): realizers, RCT/RDT, realizability defect, host realizer soundness, strict separation:
public import PaperV.Realizer
public import PaperV.RealizabilityDefect
public import PaperV.HostRealizer
public import PaperV.StrictnessExample
-- Paper V wave 2a' + 2b (Sep 2026): realizer combinators/optimality, rational weights, LP bridge,
-- Galvin list edge colouring (port of Paper III Appendix D), Galvin/Konig host adapters:
public import PaperV.RealizerCombinators
public import PaperV.RationalWeights
public import PaperV.LPBridge
public import PaperV.Galvin
public import PaperV.GalvinRealizer
public import PaperV.GalvinClass
-- wave 2c: Farkas (Fourier-Motzkin, port L23) and strong duality for the rational packing LP (port L24)
public import PaperV.RationalFarkas
public import PaperV.StrongDuality
-- Theorem A1: fractional weighted copy inequality for the mixed {K3,K4} family
public import PaperV.MixedCopyFrac
-- GALVIN-BKW-LOCAL (Aristotle return c2f11738, re-gated): multigraph vocabulary, stable matchings, Konig,
-- rank orderings, Galvin engine + Theorems A (multigraph, lists >= Delta) and B (BKW local lists); host adapter
public import PaperV.MultiGalvinBase
public import PaperV.MultiStable
public import PaperV.MultiKonig
public import PaperV.MultiRanks
public import PaperV.GalvinMultigraph
public import PaperV.GalvinLocal
-- Theorem D (S8 §6): weighted completion by paired factors, finite averaging core (Aristotle return 547578ca, re-gated)
public import PaperV.PairedFactors
-- Konig corollary for the edge-defect profile (bipartite => Class 1, exact zero set) and the intermediate-defect example
public import PaperV.KonigProfile
public import PaperV.StrictnessIntermediate
-- sharp division-free constant for P4-133 (17|X| -> 10|X|)
public import PaperV.TerminalPairSharp
-- refactor 2026-09-14: shared generic core of the fractional copy inequalities (Thm 4.1 and A1)
public import PaperV.FracCopyGeneric
-- SEAL bridge: host realizers => SEAL-feasible packings (exact Galvin/BKW regime, Konig guarantee)
public import PaperV.SealHost
public import PaperV.PureProfileGap
-- Exact host completion on the restricted target system (Corollary 5.3, equality form)
public import PaperV.HostCompletion
-- Corollary to Theorem 7.3: integral mixed copy inequality up to the rounding gap
public import PaperV.MixedCopyAsymptotic
-- Audit finding: the degree-only relaxation is exact on even palettes
public import PaperV.PureProfileSharp
-- Audit finding: the degree-only optimum exactly, and tightness for every odd palette
public import PaperV.PureProfileExact

-- Paper V v1.8 manuscript interfaces and two-error certification.
public import PaperV.TwoErrorCertificate
public import PaperV.ResourceOptimum
public import PaperV.ManuscriptEndpoints

-- Checked interfaces added for the complete F1-F8 improvement ledger.
public import PaperV.GreedyLists
public import PaperV.ResourceComposition
public import PaperV.HostConstructionAdapters
public import PaperV.MixedGapBudget
public import PaperV.MixedPromotion
public import PaperV.MixedNormalization
public import PaperV.MixedRationalNormalization

-- F5: rational/real fractional elimination, explicit dual lifting, conserved gap.
public import PaperV.FractionalIntegral

public import PaperV.FiniteValueStability

public import PaperV.UnitBoundaryEndpoints

public import PaperV.BKExact

@[expose] public section
