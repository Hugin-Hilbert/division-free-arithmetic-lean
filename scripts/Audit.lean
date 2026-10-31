import DivisionFree
import Lean.Util.CollectAxioms

/-! Check every exported project declaration, including definitions and generated auxiliaries. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut seen : Array Name := #[]
  let mut projectModules : Array ModuleIdx := #[]
  for moduleName in env.header.moduleNames do
    if (`DivisionFree).isPrefixOf moduleName then
      if let some idx := env.getModuleIdx? moduleName then
        projectModules := projectModules.push idx
  for (name, info) in env.constants.toList do
    let isProject := match env.getModuleIdxFor? name with
      | some idx => projectModules.contains idx
      | none => false
    if isProject then
      declarations := declarations + 1
      if info matches .thmInfo _ then
        theorems := theorems + 1
      for ax in ← collectAxioms name do
        unless allowed.contains ax do
          throwError "Unapproved axiom {ax} in {name}"
        unless seen.contains ax do
          seen := seen.push ax
  if declarations == 0 then
    throwError "No project declarations were audited"
  logInfo m!"Axiom audit passed: {declarations} declarations, {theorems} theorems."
  logInfo m!"Axioms used: {seen.toList}"
