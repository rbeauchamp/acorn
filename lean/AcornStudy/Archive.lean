/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornStudy.Files

/-! # Lossless archive membership

Tar supplies decompression and extraction only after every reported member has
been admitted as a distinct canonical regular file. Extraction uses private
scratch storage, removed on success and failure. Preserved member bytes, rather
than a listing's claimed hashes, determine both retained identities.
-/
namespace AcornStudy

/-- Git object identity hashes the raw-byte envelope, including byte length. -/
def objectDigest (kind : String) (bytes : ByteArray) : IO String :=
  digest false ((s!"{kind} {bytes.size}" ++ String.singleton (Char.ofNat 0)).toUTF8 ++ bytes)

/-- Original raw and Git blob identities of a regular archive member. -/
structure MemberIdentity where
  /-- SHA256 of the original bytes. -/
  sha256 : String
  /-- Git blob envelope SHA1. -/
  blob : String
  deriving BEq

/-- Sanitized tar invocation; inherited option variables cannot change semantics. -/
def tar (args : Array String) : IO String := do
  IO.Process.run {
    cmd := "tar", args := args,
    env := #[("TAR_OPTIONS", none), ("TAR_READER_OPTIONS", none), ("LC_ALL", some "C")] }

/-- Validate names and types before extraction. -/
def archiveNames (archive : LocalPath) : IO (Array LocalPath) := do
  checkPath archive
  let listing ← tar #["-tvf", archive.val]
  unless ((if listing.endsWith "\n" then (listing.dropEnd 1).toString else listing).splitOn "\n").all (·.startsWith "-") do
    throw (IO.userError "archive admits only regular file members")
  let listing ← tar #["-tf", archive.val]
  let mut names := #[]
  for name in (if listing.endsWith "\n" then (listing.dropEnd 1).toString else listing).splitOn "\n" do
    let path ← checked (localPath name)
    if names.any (fun p : LocalPath => p.val == path.val) then
      throw (IO.userError "duplicate archive member")
    names := names.push path
  if names.isEmpty then throw (IO.userError "empty archive")
  return names.qsort (fun a b => a.val < b.val)

/-- Actual regular-file identities from a confined, fresh extraction. -/
def archiveContents (archive : LocalPath) : IO (Array (String × MemberIdentity)) := do
  let names ← archiveNames archive
  IO.FS.withTempDir fun scratch => do
    let _ ← tar #["-xf", archive.val, "-C", scratch.toString,
      "--no-same-owner", "--no-same-permissions"]
    let mut result := #[]
    for name in names do
      let path := scratch / name.val
      unless (← path.symlinkMetadata).type == .file do
        throw (IO.userError "extracted member is not a regular file")
      let bytes ← IO.FS.readBinFile path
      result := result.push (name.val, ⟨← digest true bytes, ← objectDigest "blob" bytes⟩)
    return result

/-- Source member declarations retain both original identities. -/
def declaredMembers (values : List Acorn.Json.Value) : Except String (Array (String × MemberIdentity)) := do
  let mut result := #[]
  for v in values do
    let entry ← Acorn.Json.decode v do
      let path ← localPath (← Acorn.Json.text "path")
      let sha256 ← hex 64 (← Acorn.Json.text "sha256")
      let blob ← hex 40 (← Acorn.Json.text "git_blob")
      return (path.val, MemberIdentity.mk sha256.val blob.val)
    if result.any (fun p => p.1 == entry.1) then throw "duplicate source member"
    result := result.push entry
  return result.qsort (fun a b => a.1 < b.1)

/-- Actual member identities cached by verified container hash within one invocation. -/
structure ArchiveCache where
  private mk ::
  /-- Retained contents, never caller-specific declarations. -/
  private entries : IO.Ref (Array (String × Array (String × MemberIdentity)))

/-- Start a fresh archive cache. -/
def ArchiveCache.create : IO ArchiveCache := return ⟨← IO.mkRef #[]⟩

/-- Every physical copy is hash-verified even when content decoding is shared. -/
def ArchiveCache.contents (self : ArchiveCache) (archive : LocalPath)
    (hash : Hex 64) (integrity : Integrity) : IO (Array (String × MemberIdentity)) := do
  integrity.file archive hash
  let entries ← self.entries.get
  if let some (_, members) := entries.find? (fun p => p.1 == hash.val) then return members
  let members ← archiveContents archive
  self.entries.set (entries.push (hash.val, members))
  return members

/-- Compare every source declaration against actual member bytes, even on cache hits. -/
def ArchiveCache.verify (self : ArchiveCache) (archive : LocalPath) (hash : Hex 64)
    (values : List Acorn.Json.Value) (integrity : Integrity) : IO (Array (String × MemberIdentity)) := do
  let expected ← checked (declaredMembers values)
  let actual ← self.contents archive hash integrity
  unless actual == expected do throw (IO.userError "archive member inventory or SHA256/Git blob mismatch")
  return actual

/-- A trace archive declares run-owned raw observations only. -/
structure TraceArchive where
  /-- Run-owned container. -/
  path : LocalPath
  /-- Container's retained digest. -/
  sha256 : Hex 64
  /-- Distinct member paths, validated at decoding. -/
  members : List LocalPath

/-- Decode a run-owned trace archive with exact field ownership. -/
def traceArchive (dir : LocalPath) (v : Acorn.Json.Value) : Except String TraceArchive := Acorn.Json.decode v do
  let path ← localPath (← Acorn.Json.text "path")
  unless beneath path.val dir.val && path.val.endsWith ".tar.gz" do
    throw "trace archive must be a run-owned .tar.gz file"
  let sha256 ← hex 64 (← Acorn.Json.text "sha256")
  let mut members := []
  for name in ← Acorn.Json.texts "members" do
    let member ← localPath name
    unless member.val != path.val && beneath member.val dir.val &&
        !members.any (fun p : LocalPath => p.val == member.val) do
      throw "trace members must be distinct run-owned paths outside their container"
    members := members ++ [member]
  if members.isEmpty then throw "trace archive has no declared members"
  return ⟨path, sha256, members⟩

/-- Check exact original raw-material ownership and member bytes. -/
def TraceArchive.verify (archive : TraceArchive) (materials : List Material)
    (integrity : Integrity) (archives : ArchiveCache) : IO Unit := do
  unless materials.any (fun m => m.path.val == archive.path.val && m.role == "trace-archive" &&
      m.sha256.val == archive.sha256.val) do
    throw (IO.userError "trace archive is not hash-bound as a trace-archive material")
  let mut expected := #[]
  for member in archive.members do
    let [m] := materials.filter (fun m => m.path.val == member.val)
      | throw (IO.userError "trace member must have exactly one original raw-material entry")
    unless m.role == "raw" do throw (IO.userError "trace archives may contain only raw observations")
    expected := expected.push (member.val, m.sha256.val)
  let actual := (← archives.contents archive.path archive.sha256 integrity).map (fun p => (p.1, p.2.sha256))
  unless actual == expected.qsort (fun a b => a.1 < b.1) do
    throw (IO.userError "trace archive member inventory or raw SHA256 mismatch")

end AcornStudy
