/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornStudy.Archive

/-! # Preserved Git object identities

Raw object envelopes, not the current Git checkout or human-readable tree
listings, establish historical membership. This establishes content agreement;
no independent timestamp or experiment/source correspondence follows from it.
-/
namespace AcornStudy

/-- One hash-verified raw Git object. -/
structure GitObject where
  private mk ::
  /-- Canonical object id. -/
  oid : String
  /-- Admitted Git object kind. -/
  kind : String
  /-- Original unmodified bytes. -/
  bytes : ByteArray

/-- A path must be contained by the scientific owner that declares it. -/
def owned (path : LocalPath) (owner : String) : Except String Unit :=
  if beneath path.val owner then .ok () else .error s!"{path.val}: evidence must belong to {owner}"

/-- Decode a required confined path. -/
def pathField (key : String) : Acorn.Json.Decoder LocalPath := do localPath (← Acorn.Json.text key)

/-- Decode a required nullable path field. -/
def optionalPath (key : String) : Acorn.Json.Decoder (Option LocalPath) := do
  match (← Acorn.Json.take key).optional with
  | none => pure none
  | some v => return some (← localPath (← v.text))

/-- Load exact object bytes, checking SHA256, Git envelope and unique object ids. -/
def loadObjects (values : List Acorn.Json.Value) (owner : String) (integrity : Integrity) : IO (Array GitObject) := do
  let mut objects := #[]
  for v in values do
    let (kind, oid, path, hash) ← checked (Acorn.Json.decode v do
      let kind ← Acorn.Json.text "kind"
      unless ["tag", "commit", "tree", "blob"].contains kind do throw "unknown archived object kind"
      let oid ← hex 40 (← Acorn.Json.text "oid")
      let path ← pathField "path"
      owned path owner
      let hash ← hex 64 (← Acorn.Json.text "sha256")
      return (kind, oid.val, path, hash))
    integrity.file path hash
    let bytes ← readBytes path
    unless (← objectDigest kind bytes) == oid do throw (IO.userError "Git object SHA1 mismatch")
    if objects.any (fun o : GitObject => o.oid == oid) then throw (IO.userError "duplicate archived object id")
    objects := objects.push ⟨oid, kind, bytes⟩
  return objects

/-- Resolve an archived object with an exact kind, failing closed on missing bytes. -/
def getObject (objects : Array GitObject) (oid kind : String) : Except String ByteArray := do
  let some obj := objects.find? (fun o => o.oid == oid)
    | throw s!"missing raw archived {kind} object {oid}"
  unless obj.kind == kind do throw "archived object has wrong kind"
  return obj.bytes

/-- Decode only identity-selecting headers, rejecting ambiguous duplicate selectors. -/
def gitHeaders (bytes : ByteArray) : Except String (List (String × String)) := do
  let some text := String.fromUTF8? bytes | throw "invalid Git header UTF-8"
  let head :: _ :: _ := text.splitOn "\n\n" | throw "Git object has no header terminator"
  let mut headers := []
  for line in head.splitOn "\n" do
    unless line.startsWith " " do
      let key :: rest := line.splitOn " " | throw "malformed Git object header"
      if rest.isEmpty then throw "malformed Git object header"
      if ["object", "type", "tag", "tree"].contains key then
        if headers.any (fun p : String × String => p.1 == key) then throw "duplicate Git identity header"
        headers := headers ++ [(key, String.intercalate " " rest)]
  return headers

/-- Require a unique identity header established by the decoder. -/
def header (headers : List (String × String)) (key : String) : Except String String :=
  match headers.find? (fun p => p.1 == key) with
  | some p => .ok p.2
  | none => .error s!"Git object has no {key} header"

/-- Raw-byte lowercase hexadecimal rendering. -/
def hexBytes (bytes : ByteArray) : String :=
  let digit := fun n => Char.ofNat (if n < 10 then 48 + n else 87 + n)
  bytes.data.foldl (fun s b => s.push (digit (b.toNat / 16)) |>.push (digit (b.toNat % 16))) ""

/-- Raw Git tree member. -/
structure TreeEntry where
  /-- One path component. -/
  name : String
  /-- Git mode retains symlink/submodule distinctions until the consuming boundary. -/
  mode : String
  /-- Raw 20-byte child identity rendered canonically. -/
  oid : String

private def treeEntriesLoop : Nat → List UInt8 → List TreeEntry → Except String (List TreeEntry)
  | 0, [], entries => .ok entries
  | 0, _ :: _, _ => .error "Git tree input exhausted"
  | fuel + 1, bytes, entries => do
    if bytes.isEmpty then return entries
    let rawHeader := bytes.takeWhile (· != 0)
    let 0 :: tail := bytes.drop rawHeader.length | throw "unterminated Git tree entry"
    let some text := String.fromUTF8? ⟨rawHeader.toArray⟩ | throw "invalid tree header UTF-8"
    let mode :: nameParts := text.splitOn " " | throw "invalid tree header"
    let name := String.intercalate " " nameParts
    unless ["40000", "040000", "100644", "100755", "120000", "160000"].contains mode &&
        !name.isEmpty && !name.contains '/' && name != "." && name != ".." do
      throw "invalid Git tree mode/name"
    unless tail.length ≥ 20 do throw "truncated Git tree object id"
    if entries.any (fun e => e.name == name) then throw "duplicate Git tree name"
    let oid := hexBytes ⟨(tail.take 20).toArray⟩
    treeEntriesLoop fuel (tail.drop 20) (entries ++ [⟨name, mode, oid⟩])

/-- Total parser for raw Git tree records and their 20-byte object ids. -/
def treeEntries (bytes : ByteArray) : Except String (List TreeEntry) :=
  treeEntriesLoop bytes.size bytes.data.toList []

/-- Resolve path components through preserved trees without consulting live Git. -/
def treePath (objects : Array GitObject) (root path : String) : Except String (Option String) := do
  let mut oid := root
  let components := path.splitOn "/"
  for i in [:components.length] do
    let entries ← treeEntries (← getObject objects oid "tree")
    let some component := components[i]? | throw "missing path component"
    let some entry := entries.find? (fun e => e.name == component) | return none
    if i + 1 < components.length && !["40000", "040000"].contains entry.mode then
      throw "non-directory in archived path"
    if i + 1 == components.length && ["120000", "160000"].contains entry.mode then
      throw "symlink/submodule is not preserved file evidence"
    oid := entry.oid
  return some oid

/-- Bind a raw commit to both its retained digest and Git envelope identity. -/
def verifyCommit (path : LocalPath) (oid : Hex 40) (hash : Hex 64) (integrity : Integrity) : IO ByteArray := do
  integrity.file path hash
  let bytes ← readBytes path
  unless (← objectDigest "commit" bytes) == oid.val do throw (IO.userError "raw commit identity mismatch")
  return bytes

/-- Bind exact protocol bytes to their original path in a preserved commit tree. -/
def verifyProtocolPath (objects : Array GitObject) (root : String)
    (original protocol : LocalPath) : IO Unit := do
  let some oid ← checked (treePath objects root original.val)
    | throw (IO.userError "protocol absent from archived commit tree")
  unless (← objectDigest "blob" (← readBytes protocol)) == oid do
    throw (IO.userError "registered protocol bytes differ from archived commit tree")

/-- Verify complete disjoint retained roots against all admitted source-tree entries. -/
def verifySourceTrees (objects : Array GitObject) (commit : ByteArray)
    (members : Array (String × MemberIdentity)) (roots : List LocalPath) : IO Unit := do
  let root ← checked (gitHeaders commit >>= fun h => header h "tree")
  let mut pending := #[("", root, ([] : List String))]
  let mut expected : Array (String × String) := #[]
  while !pending.isEmpty do
    let some (parent, oid, ancestors) := pending.back?
      | throw (IO.userError "source tree lost pending entry")
    if ancestors.contains oid then throw (IO.userError "cyclic archived source tree")
    pending := pending.pop
    let entries ← checked (getObject objects oid "tree" >>= treeEntries)
    for entry in entries do
      let path := parent ++ entry.name
      if roots.any (fun r => beneath path r.val || beneath r.val path) then
        match entry.mode with
        | "40000" | "040000" => pending := pending.push (path ++ "/", entry.oid, oid :: ancestors)
        | "100644" | "100755" => expected := expected.push (path, entry.oid)
        | _ => throw (IO.userError "source archive cannot claim symlink/submodule tree entries")
  unless expected.qsort (fun a b => a.1 < b.1) == members.map (fun p => (p.1, p.2.blob)) &&
      roots.all (fun r => expected.any (fun p => beneath p.1 r.val)) do
    throw (IO.userError "source archive differs from complete roots in originating commit tree")

end AcornStudy
