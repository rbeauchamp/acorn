/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornStudy.Files

/-! # Current native source-package framing

The live producer shares the native build inventory domain. Retained v1 packages
keep their original bytes and are read by the scientific archive owners. This
producer computes an identity on demand; it creates no archive or receipt.
Git owns maintained source history. OpenSSL and filesystem IO remain trusted.
-/
namespace AcornStudy

private def collectSources (root : System.FilePath) (start : String) (lean : Bool) :
    IO (Array String) := do
  let mut pending := #[start]
  let mut paths := #[]
  while !pending.isEmpty do
    let some relative := pending.back? | throw (IO.userError "source inventory lost directory")
    pending := pending.pop
    unless (← (root / relative).symlinkMetadata).type == .dir do
      throw (IO.userError s!"source directory is not a real directory: {relative}")
    for entry in ← (root / relative).readDir do
      let name := entry.fileName
      unless name == ".DS_Store" || (lean && (name == ".lake" || name == "lake-packages")) do
        let path := relative ++ "/" ++ name
        match (← entry.path.symlinkMetadata).type with
        | .dir => pending := pending.push path
        | .file =>
          if !lean || entry.path.extension == some "lean" || entry.path.extension == some "c" ||
              name == "lean-toolchain" || name == "lake-manifest.json" then
            paths := paths.push path
        | _ => throw (IO.userError s!"source package rejects non-regular entry: {path}")
  return paths

/-- Current native source membership, matching the native build discovery domain.
This includes every newly added file before execution admission; generated caches
are the only excluded source subtrees. Audit pins are owned by their included native leaf. -/
def nativeCodePaths (root : System.FilePath) : IO (Array String) := do
  let mut paths ← collectSources root "lean" true
  paths := paths ++ #["viewer/static/index.html", "verification-profile"]
  for path in paths do
    unless (← (root / path).symlinkMetadata).type == .file do
      throw (IO.userError s!"source is not regular: {path}")
  return paths.qsort (· < ·)

/-- Private scientific source membership adds compile-bound protocols to current code. -/
def nativeSourcePaths (root : System.FilePath) : IO (Array String) := do
  let mut paths ← nativeCodePaths root
  unless (← (root / "studies").symlinkMetadata).type == .dir do
    throw (IO.userError "studies is not a real directory")
  for entry in ← (root / "studies").readDir do
    let kind := (← entry.path.symlinkMetadata).type
    if kind == .symlink then throw (IO.userError "source package rejects study symlinks")
    if kind == .dir then
      let protocols := "studies/" ++ entry.fileName ++ "/protocols"
      let present ← try
        let _ ← (root / protocols).symlinkMetadata
        pure true
      catch error =>
        match error with
        | .noFileOrDirectory .. => pure false
        | _ => throw error
      if present then paths := paths ++ (← collectSources root protocols false)
  for path in paths do
    unless (← (root / path).symlinkMetadata).type == .file do
      throw (IO.userError s!"source is not regular: {path}")
  return paths.qsort (· < ·)

/-- Current native source inventory uses the same path domain and v2 framing as
build provenance. Retained v1 packages are consumed as original evidence by the
archive/identity readers; the live producer never reconstructs a Rust package. -/
def sourceInventory (root : System.FilePath) : IO String := do
  let mut result := "acorn-lean-source-v2\n"
  for path in ← nativeSourcePaths root do
    unless path.toList.all (fun c => c.toNat < 128 &&
        (c.isAlphanum || "/_-+.".contains c)) do
      throw (IO.userError s!"nonportable source path: {path}")
    let hash ← digest true (← IO.FS.readBinFile (root / path))
    result := result ++ hash ++ "  " ++ path ++ "\n"
  return result

end AcornStudy
