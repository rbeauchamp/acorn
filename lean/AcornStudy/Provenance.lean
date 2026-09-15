/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornStudy.GitEvidence

/-! # Study-owned historical provenance

A historical association is supported by preserved commit/tree/blob bytes.
Workflow transcripts and current-package receipts have no role in admission.
-/
namespace AcornStudy

/-- Read and decode a complete confined manifest. -/
def decodeDocument {α : Type} (path : LocalPath) (body : Acorn.Json.Decoder α) : IO α := do
  checked (Acorn.Json.decode (← document path) body)

/-- Complete disjoint roots make a source snapshot's retained scope explicit. -/
def sourceRoots (values : List String) : Except String (List LocalPath) := do
  let mut roots := []
  for value in values do
    let path ← localPath value
    if roots.any (fun r : LocalPath => beneath r.val path.val || beneath path.val r.val) then
      throw "overlapping or duplicate source roots"
    roots := roots ++ [path]
  if roots.isEmpty then throw "source snapshot has no retained roots"
  return roots

/-- Original-path associations established from retained historical source objects. -/
abbrev ProtocolHistory := List (String × String)

/-- Validate every retained historical protocol occurrence and its exact original path. -/
def verifyHistory (path : LocalPath) (owner : String) (integrity : Integrity) : IO ProtocolHistory := do
  let (objectValues, versions) ← decodeDocument path do
    Acorn.Json.version 1
    let _ ← Acorn.Json.text "scope"
    let objects ← (← Acorn.Json.take "objects").list
    let versions ← (← Acorn.Json.take "versions").list
    return (objects, versions)
  let objects ← loadObjects objectValues owner integrity
  let mut occurrences : List (String × String) := []
  let mut relations := []
  for v in versions do
    let (original, commit, raw, rawHash, protocol, hash, length) ← checked (Acorn.Json.decode v do
      let original ← pathField "original_path"
      let commit ← hex 40 (← Acorn.Json.text "commit")
      let raw ← pathField "commit_object"
      owned raw owner
      let rawHash ← hex 64 (← Acorn.Json.text "commit_object_sha256")
      let protocol ← pathField "protocol"
      owned protocol owner
      let hash ← hex 64 (← Acorn.Json.text "sha256")
      let length ← (← Acorn.Json.take "bytes").natural
      return (original, commit, raw, rawHash, protocol, hash, length))
    if occurrences.contains (original.val, commit.val) then throw (IO.userError "duplicate protocol history occurrence")
    occurrences := occurrences ++ [(original.val, commit.val)]
    let bytes ← verifyCommit raw commit rawHash integrity
    let root ← checked (gitHeaders bytes >>= fun h => header h "tree")
    integrity.file protocol hash
    unless (← readBytes protocol).size == length do throw (IO.userError "protocol history byte length mismatch")
    verifyProtocolPath objects root original protocol
    relations := relations ++ [(original.val, protocol.val)]
  if occurrences.isEmpty then throw (IO.userError "empty protocol history")
  return relations

/-- Source aliases resolve only to verified original archive members. -/
abbrev ArchiveRefs := List (String × List String)

/-- Validate the complete historical source catalog against archive bytes and trees. -/
def loadSources (path : LocalPath) (owner : String) (integrity : Integrity)
    (archives : ArchiveCache) : IO ArchiveRefs := do
  let (objectValues, snapshots) ← decodeDocument path do
    Acorn.Json.version 1
    let objects ← (← Acorn.Json.take "objects").list
    let snapshots ← (← Acorn.Json.take "snapshots").list
    return (objects, snapshots)
  let objects ← loadObjects objectValues owner integrity
  let mut members : ArchiveRefs := []
  let mut commits : List String := []
  for v in snapshots do
    let (aliases, commit, raw, rawHash, archive, hash, roots, files) ← checked (Acorn.Json.decode v do
      let aliases ← Acorn.Json.texts "aliases"
      if aliases.isEmpty then throw "source snapshot has no aliases"
      let commit ← hex 40 (← Acorn.Json.text "commit")
      let raw ← pathField "commit_object"
      owned raw owner
      let rawHash ← hex 64 (← Acorn.Json.text "commit_object_sha256")
      let archive ← pathField "archive"
      owned archive owner
      let hash ← hex 64 (← Acorn.Json.text "sha256")
      let roots ← sourceRoots (← Acorn.Json.texts "roots")
      let files ← (← Acorn.Json.take "files").list
      return (aliases, commit, raw, rawHash, archive, hash, roots, files))
    if commits.contains commit.val then throw (IO.userError "duplicate source snapshot commit")
    commits := commits ++ [commit.val]
    let raw ← verifyCommit raw commit rawHash integrity
    let files ← archives.verify archive hash files integrity
    verifySourceTrees objects raw files roots
    for alias in aliases do
      if members.any (fun p => p.1 == alias) then throw (IO.userError "duplicate source alias")
      members := members ++ [(alias, files.toList.map (·.1))]
  if commits.isEmpty then throw (IO.userError "empty historical source catalog")
  return members

/-- Validated historical provenance and the metadata that owns its inventory. -/
structure Provenance where
  /-- Verified original protocol path associations. -/
  history : ProtocolHistory := []
  /-- Verified archived path/reference aliases. -/
  sources : ArchiveRefs := []
  /-- Selected provenance manifest, if any. -/
  manifest : Option LocalPath := none
  /-- Metadata files are inventoried separately from hash-bound evidence. -/
  metadata : List String := []

/-- Load only the selected study-owned provenance package. -/
def loadProvenance (path : Option LocalPath) (base : String) (integrity : Integrity)
    (archives : ArchiveCache) : IO Provenance := do
  let some path := path | return {}
  unless path.val == base ++ "/provenance/manifest.json" do
    throw (IO.userError "provenance manifest must belong to its study")
  let (sourcesPath, historyPath) ← decodeDocument path do
    Acorn.Json.version 1
    let sources ← pathField "sources"
    let history ← optionalPath "protocol_history"
    return (sources, history)
  unless sourcesPath.val == base ++ "/provenance/sources.json" do
    throw (IO.userError "source catalog must belong to its study")
  let sources ← loadSources sourcesPath base integrity archives
  let mut history := []
  let mut metadata := [path.val, sourcesPath.val]
  if let some historyPath := historyPath then
    unless historyPath.val == base ++ "/provenance/protocol-history.json" do
      throw (IO.userError "protocol history must belong to its study")
    history ← verifyHistory historyPath base integrity
    metadata := metadata ++ [historyPath.val]
  return { history := history, sources := sources, manifest := some path, metadata := metadata }

/-- Missing paths are distinguished from all other host failures. -/
def pathExists (path : System.FilePath) : IO Bool := do
  try
    let _ ← path.symlinkMetadata
    return true
  catch error =>
    match error with
    | .noFileOrDirectory .. => return false
    | _ => throw error

/-- Reject unselected provenance and every unreferenced or missing file. -/
def Provenance.validateInventory (self : Provenance) (base : String) (integrity : Integrity) : IO Unit := do
  let root ← checked (localPath (base ++ "/provenance"))
  if self.manifest.isNone then
    if ← pathExists root.val then throw (IO.userError "unselected study provenance directory")
    return
  let allowed := ((← integrity.paths).toList ++ self.metadata).filter (fun p => beneath p root.val)
  let actual := (← inventory root).toList.map (·.val)
  unless actual.all allowed.contains && allowed.all actual.contains do
    throw (IO.userError "study provenance contains unreferenced files or missing material")

end AcornStudy
