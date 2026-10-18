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

import PaperV

import Lean.Elab.Command

import Lean.Util.CollectAxioms



open Lean Elab Command



namespace FreezeAudit

def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def projectModules : List Name := [

  `PaperV,

  `PaperV.AffineK4,

  `PaperV.BK,

  `PaperV.BKExact,

  `PaperV.BeckFiala,

  `PaperV.BrooksB4,

  `PaperV.BrooksBlock,

  `PaperV.BrooksCut,

  `PaperV.BrooksCutExists,

  `PaperV.BrooksGlue,

  `PaperV.BrooksGreedyCtrl,

  `PaperV.BrooksHub,

  `PaperV.BrooksK4,

  `PaperV.BrooksLovasz,

  `PaperV.BrooksLovaszCore,

  `PaperV.BrooksLovaszCut,

  `PaperV.BrooksLovaszEndblock,

  `PaperV.BrooksMain,

  `PaperV.BrooksNonRegular,

  `PaperV.BrooksOct,

  `PaperV.BrooksReg,

  `PaperV.C1,

  `PaperV.Certificates,

  `PaperV.ChromaticIndex,

  `PaperV.CleanupTransfer,

  `PaperV.Clon2,

  `PaperV.ConflictGraph,

  `PaperV.Copy,

  `PaperV.CopyCore,

  `PaperV.CopyPackings,

  `PaperV.CopyFrac,

  `PaperV.CopyN1Degree,

  `PaperV.CopyN1K4,

  `PaperV.Core,

  `PaperV.CoverDefect,

  `PaperV.CoverWitness,

  `PaperV.CycleDefect,

  `PaperV.DefectApps,

  `PaperV.DefectOne,

  `PaperV.Defs,

  `PaperV.DqBasic,

  `PaperV.EdgeDefectProfile,

  `PaperV.Extremal,

  `PaperV.FiniteValueStability,

  `PaperV.FracCopyGeneric,

  `PaperV.FractionalIntegral,

  `PaperV.FractionalOptimum,

  `PaperV.FractionalUnitBoundary,

  `PaperV.Galvin,

  `PaperV.GalvinClass,

  `PaperV.GalvinLocal,

  `PaperV.GalvinMultigraph,

  `PaperV.GalvinRealizer,

  `PaperV.GreedyLists,

  `PaperV.HostCompletion,

  `PaperV.HostConstructionAdapters,

  `PaperV.HostRealizer,

  `PaperV.KonigProfile,

  `PaperV.LPBridge,

  `PaperV.LineGraph,

  `PaperV.LoadTwoK4,

  `PaperV.ManuscriptEndpoints,

  `PaperV.MixedCopy,

  `PaperV.MixedCopyAsymptotic,

  `PaperV.MixedCopyFrac,

  `PaperV.MixedGapBudget,

  `PaperV.MixedNormalization,

  `PaperV.MixedPromotion,

  `PaperV.MixedRationalNormalization,

  `PaperV.MultiGalvinBase,

  `PaperV.MultiKonig,

  `PaperV.MultiRanks,

  `PaperV.MultiStable,

  `PaperV.N1,

  `PaperV.N2,

  `PaperV.N2Gap,

  `PaperV.OddCycle,

  `PaperV.PackingCert,

  `PaperV.PairedFactors,

  `PaperV.Parity,

  `PaperV.PureProfile,

  `PaperV.PureProfileExact,

  `PaperV.PureProfileGap,

  `PaperV.PureProfileSharp,

  `PaperV.RationalFarkas,

  `PaperV.RationalLP,

  `PaperV.RationalWeights,

  `PaperV.RealizabilityDefect,

  `PaperV.Realizer,

  `PaperV.RealizerCombinators,

  `PaperV.ResourceComposition,

  `PaperV.ResourceOptimum,

  `PaperV.Seal,

  `PaperV.SealHost,

  `PaperV.SealTermination,

  `PaperV.SplittingQ,

  `PaperV.StarT2,

  `PaperV.SteinerFrac,

  `PaperV.SteinerK4,

  `PaperV.SteinerK4Oct,

  `PaperV.StrictnessExample,

  `PaperV.StrictnessIntermediate,

  `PaperV.StrongDuality,

  `PaperV.SumDefect,

  `PaperV.TerminalPairAssembly,

  `PaperV.TerminalPairRounding,

  `PaperV.TerminalPairSharp,

  `PaperV.Tightness,

  `PaperV.TransferCorollaries,

  `PaperV.TwoErrorCertificate,

  `PaperV.UnitBoundaryCompletion,

  `PaperV.UnitBoundaryEndpoints,

  `PaperV.UnitBoundaryWeighted,

  `PaperV.UnitBoundaryWitnesses,

  `PaperV.Vizing,

  `PaperV.Vizing.Basic,

  `PaperV.Vizing.Endpoints,

  `PaperV.Vizing.Fan,

  `PaperV.Vizing.Kempe,

  `PaperV.Vizing.Main,

  `PaperV.Vizing.Step,

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
  let modules : NameSet := projectModules.foldl (fun s n => s.insert n) {}
  unless modules.toArray.size == projectModules.length do
    throwError "Duplicate project module in source manifest"
  for modName in projectModules do
    unless moduleNames.contains modName do
      throwError "Listed project module is absent from public root environment: {modName}"
  logInfo m!"MODULE_COVERAGE checked={projectModules.length} all_imported=true"
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
