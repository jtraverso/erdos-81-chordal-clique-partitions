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
import PaperVIRelease
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command

namespace FreezeAudit
def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
def projectModules : List Name := [
  `LeanPool.ListEdgeColoringComplete,
  `LeanPool.ListEdgeColoringComplete.Basic,
  `LeanPool.ListEdgeColoringComplete.Certificate,
  `LeanPool.ListEdgeColoringComplete.Main,
  `LeanPool.ListEdgeColoringComplete.Polynomial,
  `PaperV.Vizing.Basic,
  `PaperV.Vizing.Endpoints,
  `PaperV.Vizing.Fan,
  `PaperV.Vizing.Kempe,
  `PaperV.Vizing.Main,
  `PaperV.Vizing.Step,
  `PaperVI,
  `PaperVI.Assembly,
  `PaperVI.Concentrated,
  `PaperVI.Counting,
  `PaperVI.Defs,
  `PaperVI.Engine,
  `PaperVI.Examples,
  `PaperVI.Fractional,
  `PaperVI.GainPacking,
  `PaperVI.JoinVariant,
  `PaperVI.Lifting,
  `PaperVI.ListColoring,
  `PaperVI.Local,
  `PaperVI.Optimal,
  `PaperVI.Rigidity,
  `PaperVI.StarDegree,
  `PaperVI.TheoremA,
  `PaperVI.TheoremB,
  `PaperVI.TheoremC,
  `PaperVI.TrianglePacking,
  `PaperVIExtended,
  `PaperVIOpt,
  `PaperVIOpt.Budgets,
  `PaperVIOpt.FracFace,
  `PaperVIOpt.InducedC4,
  `PaperVIOpt.Parametric,
  `PaperVIOpt.Secondary,
  `PaperVIRecourse,
  `PaperVIRecourse.BlockDistance,
  `PaperVIRecourse.CompatiblePrefix,
  `PaperVIRecourse.Compensation,
  `PaperVIRecourse.Connectivity,
  `PaperVIRecourse.Counts,
  `PaperVIRecourse.CrossCharges,
  `PaperVIRecourse.JoinPrefix,
  `PaperVIRecourse.LiftAlignment,
  `PaperVIRecourse.OptimalAdapter,
  `PaperVIRecourse.PartitionIdentity,
  `PaperVIRecourse.Paths,
  `PaperVIRecourse.PhysicalPrefix,
  `PaperVIRecourse.PhysicalRecourse,
  `PaperVIRecourse.Prefix,
  `PaperVIRecourse.ProtectedLifting,
  `PaperVIRecourse.ProtectedOwners,
  `PaperVIRecourse.ResourceHits,
  `PaperVIRecourse.RetainedConstruction,
  `PaperVIRecourse.TerminalAlignment,
  `PaperVIRecourse.TerminalStep,
  `PaperVIRelease,
  `PaperVIResearch,
  `PaperVIResearch.Duals,
  `PaperVIResearch.ExceptionalCleanup,
  `PaperVIResearch.ExceptionalConstruction,
  `PaperVIResearch.ExceptionalExamples,
  `PaperVIResearch.ExceptionalIntrinsic,
  `PaperVIResearch.ExceptionalModel,
  `PaperVIResearch.ExceptionalSetup,
  `PaperVIResearch.ExceptionalTheorem,
  `PaperVIResearch.ExceptionalTriangles,
  `PaperVIResearch.GreedyCount,
  `PaperVIResearch.Intrinsic,
  `PaperVIResearch.PhysicalExtension,
  `PaperVIResearch.PhysicalRecourse,
  `PaperVIResearch.PrescribedCount,
  `PaperVIResearch.ResidualCount,
  `PaperVIResearch.SecondExtremal,
  `PaperVIResearch.VizingExtraction,
  `Solution]

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
      throwError "Project source module absent from imported environment: {modName}"
  liftIO <| IO.eprintln s!"AUDIT_MODULE_COVERAGE present={projectModules.length} expected={projectModules.length}"
  let mut roots : Array Name := #[]
  for (n, _) in env.checked.get.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let modName := moduleNames[idx.toNat]!
      if modules.contains modName then
        roots := roots.push n
  liftIO <| IO.eprintln s!"AUDIT_START declarations={roots.size}"
  for modName in projectModules do
    let num : Nat := roots.foldl (fun (total : Nat) n =>
      match env.getModuleIdxFor? n with
      | some idx => if moduleNames[idx.toNat]! == modName then total + 1 else total
      | none => total) 0
    logInfo m!"AUDIT_MODULE declarations={num} module={modName}"
  let (_, st) ← (roots.forM (visit modules moduleNames)).run {}
  let extra := st.axioms.toArray.filter fun a => !(allowed.contains a)
  logInfo m!"FREEZE_FULL_AUDIT declarations={roots.size} nonstandard={extra.size} modules={projectModules.length} visited={st.seen.toArray.size}"
  logInfo m!"AXIOM_UNION {st.axioms.toArray}"
  if !extra.isEmpty then
    logInfo m!"NONSTANDARD_AXIOMS {extra}"
    throwError "Project audit rejected non-standard axioms"
end FreezeAudit

#audit_project_modules
