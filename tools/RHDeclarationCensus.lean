/-
Declaration-level census for the five final RH Lean theorems.
Run after lake build Main:
  lake env lean tools/RHDeclarationCensus.lean

The expression closure walks types and bodies (including opaque values).
The block closure also retains whole mutual declaration groups.
Neither identifies elaborator-only dependencies or certifies source deletion.
-/
import Main
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

open Lean Elab Command

private def targets : Array Name :=
  #[\`\`riemannHypothesis, \`\`riemannZeta_eq_zero_re,
    \`\`LFunction_ne_zero_of_half_lt_re, \`\`LFunction_eq_zero_re,
    \`\`LFunction_eq_zero_re_of_isPrimitive]

private def projectPrefixes : Array String :=
  #["BuildAid", "CompanionTheory", "Development", "Formalism", "GroundTheory",
    "Lemmata", "PositivityTheory", "ReciprocityTheory", "Supplements"]

private def isProjectModule (n : Name) : Bool :=
  let s := n.toString
  s == "Main" || s == "Statements" ||
    projectPrefixes.any (fun p => s == p || s.startsWith (p ++ "."))

private def dependencies (ci : ConstantInfo) (keepBlocks : Bool) : NameSet := Id.run do
  let mut refs := ci.getUsedConstantsAsSet
  if keepBlocks then
    match ci with
    | .inductInfo v => for n in v.all do refs := refs.insert n
    | .defnInfo v => for n in v.all do refs := refs.insert n
    | .thmInfo v => for n in v.all do refs := refs.insert n
    | .opaqueInfo v => for n in v.all do refs := refs.insert n
    | .recInfo v => for n in v.all do refs := refs.insert n
    | _ => pure ()
  return refs

private def closure (env : Environment) (keepBlocks : Bool) : NameSet × Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut queue : Array Name := #[]
  let mut missing : Array Name := #[]
  for name in targets do
    unless seen.contains name do
      seen := seen.insert name
      queue := queue.push name
  let mut i := 0
  while i < queue.size do
    let name := queue[i]!
    i := i + 1
    match env.find? name with
    | none => missing := missing.push name
    | some ci =>
      for dep in dependencies ci keepBlocks do
        unless seen.contains dep do
          seen := seen.insert dep
          queue := queue.push dep
  return (seen, missing)

private structure ModuleStats where
  total : Nat := 0
  expressionReachable : Nat := 0
  blockReachable : Nat := 0
  deriving Inhabited

elab "#rh_decl_census" : command => do
  let env ← getEnv
  let (exprClosure, exprMissing) := closure env false
  let (blockClosure, blockMissing) := closure env true
  let mut stats : Std.HashMap Name ModuleStats := {}
  let mods := env.allImportedModuleNames
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := mods[idx.toNat]!
      if isProjectModule modName then
        let prior := stats[modName]?.getD {}
        stats := stats.insert modName {
          total := prior.total + 1
          expressionReachable := prior.expressionReachable +
            (if exprClosure.contains name then 1 else 0)
          blockReachable := prior.blockReachable +
            (if blockClosure.contains name then 1 else 0)
        }
  let mut rows := #["module\ttotal\texpression_reachable\tblock_reachable\tblock_unreachable"]
  let sorted := stats.toList.toArray.qsort (fun a b => Name.quickLt a.1 b.1)
  let mut total := 0
  let mut er := 0
  let mut br := 0
  for (name, s) in sorted do
    total := total + s.total
    er := er + s.expressionReachable
    br := br + s.blockReachable
    rows := rows.push s!"{name}\t{s.total}\t{s.expressionReachable}\t{s.blockReachable}\t{s.total - s.blockReachable}"
  let mut targetRows := #["name\tlevel_parameters\tchecked_type\taxioms"]
  for name in targets do
    match env.find? name with
    | none => throwError "Census target missing: {name}"
    | some ci =>
      let axioms ← collectAxioms name
      let axiomNames := String.intercalate "," (axioms.toList.map toString)
      targetRows := targetRows.push s!"{name}\t{repr ci.levelParams}\t{repr ci.type}\t{axiomNames}"
  liftIO <| IO.FS.createDirAll "analysis"
  liftIO <| IO.FS.writeFile "analysis/rh-declaration-modules.tsv"
    (String.intercalate "\n" rows.toList ++ "\n")
  liftIO <| IO.FS.writeFile "analysis/rh-targets.tsv"
    (String.intercalate "\n" targetRows.toList ++ "\n")
  logInfo m!"Project declarations: {total}; expression-reachable: {er}; block-reachable: {br}; block-unreachable: {total - br}"
  logInfo m!"Missing dependencies: expression {exprMissing.size}, block {blockMissing.size}"
  unless exprMissing.isEmpty && blockMissing.isEmpty do
    throwError "Missing dependencies; do not use this census for pruning."

#rh_decl_census
