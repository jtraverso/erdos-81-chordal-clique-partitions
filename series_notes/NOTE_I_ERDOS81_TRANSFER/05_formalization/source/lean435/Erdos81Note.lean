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

import Erdos81Note.Assembly
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command

namespace Erdos81NoteAudit

structure AuditState where
  seen : NameSet := {}

def isSeries (env : Environment) (n : Name) : Bool :=
  let origin := match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!.toString
    | none => n.toString
  ["Erdos81Note", "PaperIV", "PaperV", "PaperI", "MixedRounding", "Nibble"].any
    (fun p => origin == p || origin.startsWith (p++"."))

partial def visit (n : Name) : StateT AuditState CommandElabM Unit := do
  if (← get).seen.contains n then return
  modify fun s => {s with seen := s.seen.insert n}
  let env ← getEnv
  if !isSeries env n then return
  let some info := env.checked.get.find? n | throwError "Missing dependency {n}"
  info.type.getUsedConstants.forM visit
  if let some value := info.value? (allowOpaque := true) then
    value.getUsedConstants.forM visit

elab "#audit_note" : command => do
  let roots := [``Erdos81Note.partition_of_certificate,
    ``Erdos81Note.erdos81_eventual, ``Erdos81Note.erdos81_all_orders]
  let (_, st) ← (roots.forM visit).run {}
  let names := st.seen.toArray
  let env ← getEnv
  let mut forbidden : Array Name := #[]
  for n in names do
    if let some idx := env.getModuleIdxFor? n then
      if env.header.moduleNames[idx.toNat]! == `PaperIV.Erdos81Unconditional then
        forbidden := forbidden.push n
  unless forbidden.isEmpty do
    throwError "Final IV theorem entered proof chain: {forbidden}"
  unless st.seen.contains ``PaperV.realizable_class_transfer do
    throwError "Actual Paper V transfer theorem missing from proof chain"
  unless st.seen.contains
      ``PaperIV.LocalStability.localize_original_of_windowed_accounts_descent do
    throwError "Selected descent-localization theorem missing from proof chain"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for n in roots do
    let axioms ← collectAxioms n
    let extra := axioms.filter (fun a => !allowed.contains a)
    logInfo m!"NOTE_AXIOMS {n} {axioms}"
    unless extra.isEmpty do throwError "Nonstandard axioms {extra}"
  liftIO <| IO.FS.writeFile "DECLARATION_DEPENDENCIES.txt"
    (String.intercalate "\n" (names.toList.map Name.toString))
  logInfo m!"NOTE_AUDIT_PASS visited={names.size} forbidden_final_module=0 actual_transfer=true descent=true"

end Erdos81NoteAudit

#audit_note
