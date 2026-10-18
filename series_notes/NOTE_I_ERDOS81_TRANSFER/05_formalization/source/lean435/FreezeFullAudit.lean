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

import Erdos81Note
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command

namespace FreezeAudit
def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
def projectModules : List Name := [
  `Erdos81Note,
  `Erdos81Note.Assembly,
  `Erdos81Note.PhysicalTransfer,
  `MixedRounding.Cleanup,
  `MixedRounding.Defs,
  `MixedRounding.Lift,
  `MixedRounding.Producer,
  `Nibble.AdaptiveAssembly,
  `Nibble.AdaptiveRounds,
  `Nibble.Assemble,
  `Nibble.Assembly,
  `Nibble.Basic,
  `Nibble.BeckFiala,
  `Nibble.BeckFialaPairs,
  `Nibble.BernoulliSpace,
  `Nibble.Conflict,
  `Nibble.Convergence,
  `Nibble.Covered,
  `Nibble.CoveredExpectation,
  `Nibble.DischargeSeq,
  `Nibble.FracMatchingBound,
  `Nibble.FracNibbleLE,
  `Nibble.FracNibbleRepaired,
  `Nibble.FracNibbleSlack,
  `Nibble.FracNibbleSlackR,
  `Nibble.Greedy,
  `Nibble.Interface,
  `Nibble.Iteration,
  `Nibble.IterationSeq,
  `Nibble.Measurable,
  `Nibble.Prelude,
  `Nibble.Regular,
  `Nibble.RegularMost,
  `Nibble.Round,
  `Nibble.RoundConflict,
  `Nibble.Survival,
  `Nibble.Tight.ConflictCount,
  `Nibble.Tight.CoverProb,
  `Nibble.Tight.CoverVariance,
  `Nibble.Tight.CoverWeight,
  `Nibble.Tight.CoverWeightMoments,
  `Nibble.Tight.CubeRetention,
  `Nibble.Tight.CubeVariance,
  `Nibble.Tight.FlipStability,
  `Nibble.Tight.LossVariance,
  `Nibble.Tight.PairExcessCodegree,
  `Nibble.Tight.PairWeightMean,
  `Nibble.Tight.Pruning,
  `Nibble.Tight.ResidualBand,
  `Nibble.Tight.ResidualBandCheb,
  `Nibble.Tight.RoundExplicit,
  `Nibble.Tight.SafeDegree,
  `Nibble.Tight.SafeDegreeVariance,
  `Nibble.Tight.SafeRoundCheb,
  `Nibble.Tight.Selection,
  `Nibble.Tight.SharpRound,
  `Nibble.Tight.SharpRoundAssembly,
  `Nibble.Tight.SharpRoundProof,
  `Nibble.Tight.SharpVariance,
  `Nibble.Tight.TightRound,
  `Nibble.Tight.TightRoundCheb,
  `Nibble.Tight.TightRoundConcrete,
  `Nibble.Tight.TwoEdgeMatch,
  `Nibble.TightAssembly,
  `Nibble.TightNibble,
  `Nibble.TightSchedule,
  `Nibble.WeightedSpreadNibble,
  `PaperI.FiniteLP,
  `PaperI.FiniteLPDuality,
  `PaperI.RationalFarkas,
  `PaperIV.AssignmentEquivalence,
  `PaperIV.AssignmentLemma,
  `PaperIV.CanonicalBudget,
  `PaperIV.CenteredMoments,
  `PaperIV.CertifiedF4Bridge,
  `PaperIV.CertifiedOptimumExistence,
  `PaperIV.ChordalBasics,
  `PaperIV.ChordalBridge,
  `PaperIV.ChordalC4,
  `PaperIV.ChordalCopy,
  `PaperIV.ChordalCoreMissing,
  `PaperIV.ChordalStructure,
  `PaperIV.ClassCopy,
  `PaperIV.ClassCopyEdit,
  `PaperIV.CleanedLowTriangleBridge,
  `PaperIV.CleanedTriangleMass,
  `PaperIV.CliqueBagNibble,
  `PaperIV.CloneMeasure,
  `PaperIV.ColourClasses,
  `PaperIV.CopyCleanup,
  `PaperIV.CopyPathNearEntry,
  `PaperIV.CopyPathWindow,
  `PaperIV.CopySelector,
  `PaperIV.Corollary73Assembly,
  `PaperIV.CountingTelescope,
  `PaperIV.CriticalBranch,
  `PaperIV.CriticalResidual,
  `PaperIV.CyclicLayering,
  `PaperIV.DeficitAlongPath,
  `PaperIV.DegreeConcentration,
  `PaperIV.DenseBagClosure,
  `PaperIV.Dirac1,
  `PaperIV.DiracEngine,
  `PaperIV.DiscardCounts,
  `PaperIV.DonationBudget,
  `PaperIV.DoubledPattern,
  `PaperIV.E01Ledger,
  `PaperIV.EditFirstEntry,
  `PaperIV.EditMetric,
  `PaperIV.EighthMoment,
  `PaperIV.EpsilonBudgetFull,
  `PaperIV.EquitableEdgeColouring,
  `PaperIV.EquitableKempe,
  `PaperIV.ExteriorTriangleLift,
  `PaperIV.F4EditRobustness,
  `PaperIV.FarRounding,
  `PaperIV.FarRoundingBatchBridge,
  `PaperIV.FarRoundingFromAssignment,
  `PaperIV.FarRoundingRealLP,
  `PaperIV.FarRoundingToPhysical,
  `PaperIV.FiniteHeavySelection,
  `PaperIV.FiniteLPDuality,
  `PaperIV.FirstEntryWindow,
  `PaperIV.GatedSplitTargetBridge,
  `PaperIV.GatedTerminalSplit,
  `PaperIV.GraphFamilyDistance,
  `PaperIV.H1DescentBarrier,
  `PaperIV.H1ImprovedConstants,
  `PaperIV.H1LedgerArithmetic,
  `PaperIV.JointTwoQuotaPhysical,
  `PaperIV.JointTypedNibbleGate,
  `PaperIV.JointTypedQuota,
  `PaperIV.K4UniformNibbleCounts,
  `PaperIV.LineGraphColouring,
  `PaperIV.LocalStabilityS01S03,
  `PaperIV.LowTriangleReduction,
  `PaperIV.MarkedQuotaGate,
  `PaperIV.MarkedQuotaNibble,
  `PaperIV.MarkedQuotaPairing,
  `PaperIV.MarkedQuotaSlackGate,
  `PaperIV.MarkedQuotaTokens,
  `PaperIV.MarkedQuotaTypedGain,
  `PaperIV.MixedNibbleUnion,
  `PaperIV.MixedRoundingAdapter,
  `PaperIV.Model,
  `PaperIV.MultiHostTriangleLift,
  `PaperIV.NB08Interface,
  `PaperIV.NearH1CalibratedRoot,
  `PaperIV.NearH1Calibration,
  `PaperIV.NearH1FinalAssembly,
  `PaperIV.NearH1FinalScalars,
  `PaperIV.NearH1Localization,
  `PaperIV.NearH1PhaseI,
  `PaperIV.NearH1PromotionAccounts,
  `PaperIV.NearH1RootRegularization,
  `PaperIV.NearH1SplitComparator,
  `PaperIV.NearH1StructureWitness,
  `PaperIV.NearH1WindowAccounts,
  `PaperIV.NearTerminalSynthesis,
  `PaperIV.NibbleHypotheses,
  `PaperIV.NibblePort,
  `PaperIV.OneFactorization,
  `PaperIV.OneStepEstimate,
  `PaperIV.OutsideCounting,
  `PaperIV.OwnerCoinMoments,
  `PaperIV.OwnerCoins,
  `PaperIV.PackingUnion,
  `PaperIV.PaddedEquitableColouring,
  `PaperIV.PaperIIINibbleAdapter,
  `PaperIV.PaperIIISlackNibbleAdapter,
  `PaperIV.ParametricBudget,
  `PaperIV.PartitionBridge,
  `PaperIV.PathDescentBarrier,
  `PaperIV.PathDescentBridge,
  `PaperIV.PatternCoin,
  `PaperIV.PatternCounting,
  `PaperIV.PatternMass,
  `PaperIV.PatternPoolGeometry,
  `PaperIV.PatternTransfer,
  `PaperIV.PhysicalCompletion,
  `PaperIV.RC01CandidatePool,
  `PaperIV.RC01Candidates,
  `PaperIV.RC01CanonicalFiberProfile,
  `PaperIV.RC01CanonicalFractional,
  `PaperIV.RC01CanonicalNormalization,
  `PaperIV.RC01CanonicalProfile,
  `PaperIV.RC01CanonicalSlackBridge,
  `PaperIV.RC01CanonicalSlots,
  `PaperIV.RC01CanonicalSupports,
  `PaperIV.RC01CanonicalTransferBridge,
  `PaperIV.RC01CanonicalValueAccounting,
  `PaperIV.RC01CleanFiber,
  `PaperIV.RC01CleanedGate,
  `PaperIV.RC01CleanedMixedCodegree,
  `PaperIV.RC01CleanedSpreadPacking,
  `PaperIV.RC01DenseAssembly,
  `PaperIV.RC01DensePhysicalGate,
  `PaperIV.RC01DenseRootwiseRetention,
  `PaperIV.RC01DeviationCleanup,
  `PaperIV.RC01FarAssembly,
  `PaperIV.RC01Final,
  `PaperIV.RC01GlobalBudget,
  `PaperIV.RC01GlobalSchedule,
  `PaperIV.RC01K3Pool,
  `PaperIV.RC01MarkedRounding,
  `PaperIV.RC01MixedPatterns,
  `PaperIV.RC01PatternCapacity,
  `PaperIV.RC01PatternCardinality,
  `PaperIV.RC01PatternMassScale,
  `PaperIV.RC01RegularVolume,
  `PaperIV.RC01ResidualCoverage,
  `PaperIV.RC01ResidualTransferClosure,
  `PaperIV.RC01RootedMomentAdapter,
  `PaperIV.RC01RootwiseCleanupBudget,
  `PaperIV.RC01RootwiseReference,
  `PaperIV.RC01RootwiseRetention,
  `PaperIV.RC01TriangleSchedule,
  `PaperIV.RC01TriangleTransfer,
  `PaperIV.RC01UniformDenseGate,
  `PaperIV.RD09CandidateCounting,
  `PaperIV.RD09CanonicalBadAccounts,
  `PaperIV.RD09CanonicalL2Assembly,
  `PaperIV.RD09CompleteFactorAdapter,
  `PaperIV.RD09FactorCandidateAverage,
  `PaperIV.RD09FactorCandidateMoments,
  `PaperIV.RD09FiniteAveraging,
  `PaperIV.RD09H1SpokeRealization,
  `PaperIV.RD09L1Adapter,
  `PaperIV.RD09LocalPhaseI,
  `PaperIV.RD09PaddedHostBase,
  `PaperIV.RD09PaddedL1Adapter,
  `PaperIV.RD09PaddedL1Mass,
  `PaperIV.RD09PhaseII,
  `PaperIV.RD09PhysicalLedger,
  `PaperIV.RD09RootExteriorAdapter,
  `PaperIV.RD09RootFactorPhase,
  `PaperIV.RD09RootSplitDistance,
  `PaperIV.RD09RootedOrderAdapter,
  `PaperIV.RD09SplitEditAccount,
  `PaperIV.RD09SpokeCompatibility,
  `PaperIV.RD09TerminalAssembly,
  `PaperIV.RegularityFormat,
  `PaperIV.Regularization,
  `PaperIV.RegularizationBounds,
  `PaperIV.RegularizedRootGoal,
  `PaperIV.ResourceSizes,
  `PaperIV.RootEdgeSplit,
  `PaperIV.RootRegularizationBridge,
  `PaperIV.RootVocabulary,
  `PaperIV.RootedCounting,
  `PaperIV.RootedCountingBridge,
  `PaperIV.RootedEliminationOrder,
  `PaperIV.RootedK3Counting,
  `PaperIV.RootedK3Pool,
  `PaperIV.RootedK4Counting,
  `PaperIV.RootedK4Degree,
  `PaperIV.RootedK4Pool,
  `PaperIV.RootedVariance,
  `PaperIV.RoundRobinPairs,
  `PaperIV.RoundingTrichotomy,
  `PaperIV.SharpEnvelope,
  `PaperIV.SimultaneousSelection,
  `PaperIV.SparseRegime,
  `PaperIV.SplitBaselineTarget,
  `PaperIV.SplitCanonicalSupportSum,
  `PaperIV.SplitCanonicalValue,
  `PaperIV.SplitCanonicalWeight,
  `PaperIV.SplitComparatorFamily,
  `PaperIV.SplitComparatorResidual,
  `PaperIV.SplitEdgeCount,
  `PaperIV.SplitFamilyDisjoint,
  `PaperIV.SplitFamilyNonempty,
  `PaperIV.SplitFarRounding,
  `PaperIV.SplitItems,
  `PaperIV.SplitLPToPhysicalLoads,
  `PaperIV.SplitPackingObstruction,
  `PaperIV.SplitTerminalLP,
  `PaperIV.SplitTriangleFactor,
  `PaperIV.SplitTriangleFactorHighHost,
  `PaperIV.SplitUniformIncidence,
  `PaperIV.SpreadPacking,
  `PaperIV.SpreadRestricted,
  `PaperIV.SpreadValueTransfer,
  `PaperIV.SymmetrizationBarrier,
  `PaperIV.SymmetrizationInvariantBarrier,
  `PaperIV.SymmetrizationMetricStep,
  `PaperIV.TargetEnvelope,
  `PaperIV.TelescopeK3,
  `PaperIV.TelescopeK3Full,
  `PaperIV.TelescopeK4,
  `PaperIV.TelescopeK4Full,
  `PaperIV.TelescopeK4Step2,
  `PaperIV.TerminalLedger,
  `PaperIV.TerminalSeparation,
  `PaperIV.TerminalSplit,
  `PaperIV.TerminalSplitAdapter,
  `PaperIV.TransportedMatchings,
  `PaperIV.TriangleCover,
  `PaperIV.TriangleNibblePort,
  `PaperIV.TrianglePairingDefs,
  `PaperIV.TrianglePairingSplit,
  `PaperIV.TrianglePairingSums,
  `PaperIV.TriangleSwap,
  `PaperIV.TwoRegimeAccounting,
  `PaperIV.UniformDual,
  `PaperIV.UniformSplitLoads,
  `PaperIV.UniformWeightValue,
  `PaperIV.VertexCopy,
  `PaperIV.VertexCopyGate,
  `PaperIV.VertexCopyItems,
  `PaperIV.VertexCopyMonotone,
  `PaperIV.VertexCopyRank,
  `PaperIV.VertexCopySelector,
  `PaperIV.VertexCopyTransport,
  `PaperIV.VertexCopyWBridge,
  `PaperIV.Vizing,
  `PaperIV.WeightedCodegree,
  `PaperIV.WeightedCoin,
  `PaperIV.WeightedMoments,
  `PaperIV.WeightedPatternCoins,
  `PaperV.ConflictGraph,
  `PaperV.Core,
  `PaperV.Realizer,
  `PaperV.WeightedTransfer]

def isProject (modules : NameSet) (moduleNames : Array Name) (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => modules.contains moduleNames[idx.toNat]!
  | none => false

structure AuditState where
  seen : NameSet := {}
  axioms : NameSet := {}

-- Walk every local declaration once, including unused private helpers. For
-- external dependencies use Lean's exported axiom footprints. A shared visited
-- set avoids repeatedly re-reading large private project proofs.
partial def visit (modules : NameSet) (moduleNames : Array Name) (n : Name) : StateT AuditState CommandElabM Unit := do
  if (← get).seen.contains n then return
  modify fun s => { s with seen := s.seen.insert n }
  let env ← getEnv
  if !isProject modules moduleNames env n then
    let axs ← collectAxioms n
    modify fun s => { s with axioms := axs.foldl (fun a x => a.insert x) s.axioms }
    return
  let visitExpr (e : Expr) := e.getUsedConstants.forM (visit modules moduleNames)
  match env.checked.get.find? n with
  | some (.axiomInfo v) =>
      modify fun s => { s with axioms := s.axioms.insert n }
      visitExpr v.type
  | some (.defnInfo v) => visitExpr v.type *> visitExpr v.value
  | some (.thmInfo v) => visitExpr v.type *> visitExpr v.value
  | some (.opaqueInfo v) => visitExpr v.type *> visitExpr v.value
  | some (.quotInfo _) => pure ()
  | some (.ctorInfo v) => visitExpr v.type
  | some (.recInfo v) => visitExpr v.type
  | some (.inductInfo v) => visitExpr v.type *> v.ctors.forM (visit modules moduleNames)
  | none => throwError "Missing kernel declaration during audit: {n}"

elab "#audit_project_modules" : command => do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let loaded : NameSet := moduleNames.foldl (fun s n => s.insert n) {}
  let missing := projectModules.filter (fun m => !loaded.contains m)
  unless missing.isEmpty do
    throwError "Source-manifest modules absent from imported environment: {missing}"
  logInfo m!"MODULE_PRESENCE_PASS expected={projectModules.length} missing=0"
  let modules : NameSet := projectModules.foldl (fun s n => s.insert n) {}
  unless modules.toArray.size == projectModules.length do
    throwError "Duplicate project module in source manifest"
  let mut roots : Array Name := #[]
  for (n, _) in env.checked.get.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let modName := moduleNames[idx.toNat]!
      if modules.contains modName then
        roots := roots.push n
  liftIO <| IO.eprintln s!"AUDIT_START declarations={roots.size}"
  let (_, st) ← (roots.forM (visit modules moduleNames)).run {}
  let extra := st.axioms.toArray.filter fun a => !(allowed.contains a)
  logInfo m!"FREEZE_FULL_AUDIT declarations={roots.size} nonstandard={extra.size} modules={projectModules.length} visited={st.seen.toArray.size}"
  logInfo m!"AXIOM_UNION {st.axioms.toArray}"
  if !extra.isEmpty then
    logInfo m!"NONSTANDARD_AXIOMS {extra}"
    throwError "Project audit rejected non-standard axioms"
end FreezeAudit

#audit_project_modules
