/-
Stock Lake completion recovery for already-elaborated Lean modules.

This is a bounded, local recovery *candidate* tool, not an independent
proof checker. Lake's own noBuild/trustHash checks decide which previously
completed outputs can be repacked. Partially generated or stale outputs are
refused, not accepted by their mere presence on disk.

API study: leanprover-community/riemann-hypothesis
scripts/cache-bootstrap/RecoverCompleted.lean at 8ec38f92ac54b5c91bc07f4f6f88ea61691b7975.
-/
module

import Lake
import all Lake.CLI.Main
import all Lake.Load.Workspace
import all Lake.Build.Module
import all Lake.Build.Run

open Lake Lean System

private def verifiedPack
    (ws : Workspace) (modName : String) : FetchM (Lake.Job Json) := do
  let some leanModule := ws.findModule? modName.toName
    | error s!"unknown Lean module {modName}"
  -- Lake validates the current source/imports and actual output descriptors.
  -- No missing Lean outputs may be generated in this FetchM scope.
  let existing ← leanModule.leanArts.fetch
  let validated ← Job.async do
    let arts ← existing.await
    let trace ← IO.FS.readFile leanModule.traceFile
    let .ok traceMeta := BuildMetadata.parse trace
      | error "missing or invalid Lake build trace"
    let some outputHashes := traceMeta.outputs?
      | error "Lake build trace has no output descriptors"
    let .ok (saved : ModuleOutputDescrs) := fromJson? outputHashes
      | error "invalid Lake output descriptors"
    let actual := toJson arts.descrs
    let expected := toJson saved
    for field in #["m", "o", "i", "rs", "r", "c", "b"] do
      if let .ok value := expected.getObjVal? field then
        let .ok observed := actual.getObjVal? field
          | error s!"missing validated output {field}"
        unless observed == value do
          error s!"output changed after the saved trace: {field}"
    -- A killed leantar may have left arbitrary partial bytes: discard its
    -- output and ask *stock Lake* to pack the validated raw artifacts.
    if ← leanModule.ltarFile.pathExists then
      IO.FS.removeFile leanModule.ltarFile
    let packed ← leanModule.packLtar {arts with ltar? := none}
    let stored ← ws.lakeCache.saveArtifact packed.path "ltar"
    return Json.mkObj [
      ("module", toJson modName),
      ("accepted", toJson true),
      ("input_hash", toJson traceMeta.depHash.toString),
      ("archive", toJson stored.descr.relPath.toString)]
  return validated

public def main (args : List String) : IO Unit := do
  let [root, candidatesPath, resultPath, widthArg] := args
    | throw <| IO.userError
        "expected workspace candidates.json report.jsonl concurrency"
  let some width := widthArg.toNat?
    | throw <| IO.userError "invalid recovery worker count"
  unless width ≥ 1 ∧ width ≤ 16 do
    throw <| IO.userError "recovery workers must be in [1,16]"
  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let opts : LakeOptions := {
    rootDir := root
    configFile := "lakefile.toml"
    updateToolchain := false
    elanInstall?
    leanInstall?
    lakeInstall?
  }
  let config ← opts.mkLoadConfig.toIO (IO.userError ∘ toString)
  let some ws ← (loadWorkspace config).toBaseIO
    | throw <| IO.userError "could not load pinned Lake workspace"
  let .ok parsed := Json.parse (← IO.FS.readFile candidatesPath)
    | throw <| IO.userError "invalid candidates JSON"
  let .ok (names : Array String) := fromJson? parsed
    | throw <| IO.userError "expected JSON array of module names"
  let output ← IO.FS.Handle.mk resultPath .write
  let work : FetchM Unit := do
    let mut index := 0
    while index < names.size do
      let mut running : Array (String × Lake.Job Json) := #[]
      for name in names.extract index (index + width) do
        try
          let task ← verifiedPack ws name
          running := running.push (name, task)
        catch _ =>
          output.putStrLn ((Json.mkObj [
            ("module", toJson name), ("accepted", toJson false)]).compress)
          output.flush
      for (name, task) in running do
        try
          output.putStrLn (← task.await).compress
        catch _ =>
          output.putStrLn ((Json.mkObj [
            ("module", toJson name), ("accepted", toJson false)]).compress)
        output.flush
      index := index + width
  ws.runFetchM work {verbosity := .quiet, noBuild := true, trustHash := false}
