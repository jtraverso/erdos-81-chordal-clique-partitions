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

import GlobalAssembly
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command

namespace ChordalStabilityNoteAudit

structure AuditState where
  seen : NameSet := {}

def isLocalSource (env : Environment) (n : Name) : Bool :=
  let origin := match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!.toString
    | none => n.toString
  ["ChordalStabilityNote", "GlobalAssembly", "NearAssembly", "FarGap",
   "PaidRootAssembly", "GraphWindow", "PartitionAdapter", "WindowArithmetic",
   "PaperIV", "PaperV", "PaperVI", "PaperVIOpt", "PaperVIResearch", "PaperVIExtended",
   "PaperI", "LeanPool", "Solution", "HaggkvistJanssen", "MixedRounding", "Nibble"].any
    (fun p => origin == p || origin.startsWith (p ++ "."))

partial def visit (n : Name) : StateT AuditState CommandElabM Unit := do
  if (← get).seen.contains n then return
  modify fun s => {s with seen := s.seen.insert n}
  let env ← getEnv
  if !isLocalSource env n then return
  let some info := env.checked.get.find? n | throwError "Missing declaration {n}"
  info.type.getUsedConstants.forM visit
  if let some value := info.value? (allowOpaque := true) then
    value.getUsedConstants.forM visit

elab "#audit_stability_note" : command => do
  let root := ``ChordalStabilityNote.eventual_root_stability
  let (_, st) ← (visit root).run {}
  let env ← getEnv
  let names := st.seen.toArray
  for n in names do
    if let some idx := env.getModuleIdxFor? n then
      if env.header.moduleNames[idx.toNat]! == `PaperIV.Erdos81Unconditional then
        throwError "Forbidden final IV theorem entered dependency graph: {n}"
  let required := [``PaperIV.RC01FarAssembly.uniformTransferAt,
    ``PaperIV.NearH1Localization.exists_nearStructureWitness_of_nearRegime,
    ``PaperIV.LocalStability.localize_original_of_windowed_accounts_descent,
    ``PaperVI.cp_window_K4,
    ``ChordalStabilityNote.cp_le_physical_partition,
    ``ChordalStabilityNote.cp_le_far_partition]
  for n in required do
    unless st.seen.contains n do throwError "Required actual input absent from proof graph: {n}"
  let axioms ← collectAxioms root
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let extra := axioms.filter (fun a => !allowed.contains a)
  logInfo m!"NOTE_II_AXIOMS {root} {axioms}"
  unless extra.isEmpty do throwError "Nonstandard axioms: {extra}"
  let outputDir := (← liftIO <| IO.getEnv "NOTE_II_AUDIT_OUTPUT").getD "."
  liftIO <| IO.FS.writeFile ((System.FilePath.mk outputDir) / "DECLARATION_DEPENDENCIES_II.txt")
    (String.intercalate "\n" (names.toList.map Name.toString))
  logInfo m!"NOTE_II_AUDIT_PASS visited={names.size} actual_far_rounding=true actual_descent=true actual_VI_parametric=true final_IV_theorem=false"

end ChordalStabilityNoteAudit

#audit_stability_note
