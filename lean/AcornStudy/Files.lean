/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Json
import AcornStudy.Admission
import Init.System.IO

/-! # Confined preserved-byte IO

The filesystem, process runner and provisioned OpenSSL are explicit trusted host
boundaries. Every path component is checked without following symlinks. Digest
agreement establishes integrity, never independent timing or authenticity.
-/
namespace AcornStudy

/-- Lift a pure admission failure to the command boundary. -/
def checked {α : Type} (value : Except String α) : IO α :=
  IO.ofExcept value

/-- Inspect every component, rejecting symlinks and special files before access. -/
def checkPath (path : LocalPath) (directory : Bool := false) : IO Unit := do
  let mut componentPath : System.FilePath := ""
  let parts := path.val.splitOn "/"
  for part in parts do
    componentPath := if componentPath.toString.isEmpty then part else componentPath / part
    let kind := (← componentPath.symlinkMetadata).type
    unless kind == .file || kind == .dir do
      throw (IO.userError s!"{componentPath}: not a regular archive path")
    if componentPath.toString == path.val then
      unless (kind == .dir) == directory do
        throw (IO.userError s!"{componentPath}: wrong file kind")
    else unless kind == .dir do throw (IO.userError s!"{componentPath}: not a directory")

/-- Read raw bytes only after confined regular-file admission. -/
def readBytes (path : LocalPath) : IO ByteArray := do
  checkPath path
  IO.FS.readBinFile path.val

/-- Hash raw bytes with the provisioned cryptographic backend and require its
algorithm-specific output width. No text transcoding touches the input. -/
def digest (sha256 : Bool) (bytes : ByteArray) : IO String := do
  let child ← do
    let (stdin, child) ← (← IO.Process.spawn {
      cmd := "openssl", args := #["dgst", if sha256 then "-sha256" else "-sha1", "-binary"],
      stdin := .piped, stdout := .piped, stderr := .piped }).takeStdin
    stdin.write bytes
    stdin.flush
    pure child
  let output ← child.stdout.readBinToEnd
  let errors ← child.stderr.readToEnd
  let status ← child.wait
  unless status == 0 && output.size == (if sha256 then 32 else 20) do
    throw (IO.userError s!"OpenSSL digest failed: {errors}")
  let digit := fun n => Char.ofNat (if n < 10 then 48 + n else 87 + n)
  return output.data.foldl (fun s b =>
    s.push (digit (b.toNat / 16)) |>.push (digit (b.toNat % 16))) ""

/-- Verify a retained raw-file identity; computed identity alone is no comparison. -/
def verifyFile (path : LocalPath) (expected : Hex 64) : IO Unit := do
  unless (← digest true (← readBytes path)) == expected.val do
    throw (IO.userError s!"{path.val}: raw SHA256 mismatch")

/-- Per-invocation hash cache; the flag distinguishes computation from comparison. -/
structure Integrity where
  private mk ::
  /-- Only this invocation's immutable observations are cached. -/
  private entries : IO.Ref (Array (String × String × Bool))

/-- Start a fresh integrity invocation; no persistent cache can stand in for a read. -/
def Integrity.create : IO Integrity := return ⟨← IO.mkRef #[]⟩

/-- Hash a confined raw file once in this invocation. -/
def Integrity.sha256 (self : Integrity) (path : LocalPath) : IO String := do
  let entries ← self.entries.get
  if let some (_, hash, _) := entries.find? (fun p => p.1 == path.val) then return hash
  let hash ← digest true (← readBytes path)
  self.entries.set (entries.push (path.val, hash, false))
  return hash

/-- Verify a retained identity and record that an actual comparison succeeded. -/
def Integrity.file (self : Integrity) (path : LocalPath) (expected : Hex 64) : IO Unit := do
  unless (← self.sha256 path) == expected.val do
    throw (IO.userError s!"{path.val}: raw SHA256 mismatch")
  self.entries.modify (·.map fun p => if p.1 == path.val then (p.1, p.2.1, true) else p)

/-- Every visited material path, whether shared by multiple declarations or not. -/
def Integrity.paths (self : Integrity) : IO (Array String) := do
  return (← self.entries.get).map (·.1)

/-- Timing-input association requires a retained hash comparison, not just hashing. -/
def Integrity.requireVerified (self : Integrity) (path : LocalPath) : IO Unit := do
  unless (← self.entries.get).any (fun p => p.1 == path.val && p.2.2) do
    throw (IO.userError s!"{path.val}: retained timestamp input has no verified material hash")

/-- JSON manifests are size bounded and require valid UTF-8 before pure parsing. -/
def document (path : LocalPath) : IO Acorn.Json.Value := do
  checkPath path
  if (← (System.FilePath.mk path.val).metadata).byteSize > 64 * 1024 * 1024 then
    throw (IO.userError "JSON manifest exceeds 64 MiB")
  let bytes ← IO.FS.readBinFile path.val
  let some text := String.fromUTF8? bytes | throw (IO.userError "invalid manifest UTF-8")
  checked (Acorn.Json.parse text)

/-- Complete regular-file inventory; Finder metadata is the sole exclusion. -/
def inventory (root : LocalPath) : IO (Array LocalPath) := do
  checkPath root true
  let mut pending := #[root]
  let mut result := #[]
  while !pending.isEmpty do
    let some dir := pending.back? | throw (IO.userError "inventory lost pending directory")
    pending := pending.pop
    checkPath dir true
    for entry in ← (System.FilePath.mk dir.val).readDir do
      unless entry.fileName == ".DS_Store" do
        let path ← checked (localPath entry.path.toString)
        match (← entry.path.symlinkMetadata).type with
        | .dir => pending := pending.push path
        | .file => result := result.push path
        | _ => throw (IO.userError s!"{path.val}: symlink or special file in archive")
  return result.qsort (fun a b => a.val < b.val)

/-- Sorted child directories; even empty undeclared runs remain visible. -/
def directories (root : LocalPath) : IO (Array String) := do
  checkPath root true
  let mut result := #[]
  for entry in ← (System.FilePath.mk root.val).readDir do
    unless entry.fileName == ".DS_Store" do
      unless (← entry.path.symlinkMetadata).type == .dir do
        throw (IO.userError s!"{root.val}: non-directory {entry.fileName}")
      result := result.push entry.fileName
  return result.qsort (· < ·)

/-- Path-componentPath membership compares a complete component boundary. -/
def beneath (path root : String) : Bool := path == root || path.startsWith (root ++ "/")

/-- One original material with a role and canonical digest spelling. -/
structure Material where
  /-- Confined path. -/
  path : LocalPath
  /-- Retained SHA256 identity. -/
  sha256 : Hex 64
  /-- The declaration's scientific role, not an inferred claim. -/
  role : String

/-- Decode a material with exact field ownership. -/
def material (v : Acorn.Json.Value) : Except String Material := Acorn.Json.decode v do
  let path ← localPath (← Acorn.Json.text "path")
  let sha256 ← hex 64 (← Acorn.Json.text "sha256")
  let role ← Acorn.Json.text "role"
  return ⟨path, sha256, role⟩

end AcornStudy
