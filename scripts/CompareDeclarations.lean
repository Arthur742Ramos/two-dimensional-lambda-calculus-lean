import Lean

/-! Fast local declaration-identity preflight. This does not replace the
independent exporter, sandbox, or NanoDa replay in CI. -/

deriving instance BEq for Lean.QuotKind
deriving instance BEq for Lean.QuotVal
deriving instance BEq for Lean.InductiveVal
deriving instance BEq for Lean.ConstantInfo

structure Config where
  challenge_module : String
  solution_module : String
  theorem_names : Array String
  definition_names : Array String
  deriving Lean.FromJson

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected a comparator JSON path")
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile path))
  let cfg : Config ← IO.ofExcept (Lean.fromJson? json)
  Lean.initSearchPath (← Lean.findSysroot)
  let challenge ← Lean.importModules #[{module := cfg.challenge_module.toName}] {}
  let solution ← Lean.importModules #[{module := cfg.solution_module.toName}] {}
  let targets := (cfg.theorem_names ++ cfg.definition_names).map String.toName
  let mut pending := targets
  let mut checked : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if checked.contains name then continue
    checked := checked.insert name
    let some cc := challenge.find? name | throw (IO.userError s!"missing in challenge: {name}")
    let some sc := solution.find? name | throw (IO.userError s!"missing in solution: {name}")
    if targets.contains name then
      unless cc.type == sc.type && cc.levelParams == sc.levelParams do
        throw (IO.userError s!"target type differs: {name}")
      pending := pending ++ sc.type.getUsedConstants
    else
      unless cc == sc do
        throw (IO.userError s!"dependency differs: {name}")
      pending := pending ++ sc.type.getUsedConstants
      if let some value := sc.value? then
        pending := pending ++ value.getUsedConstants
  IO.println s!"Declaration preflight passed: {targets.size} targets, {checked.size} declarations"
