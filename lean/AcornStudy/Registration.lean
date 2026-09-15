/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornStudy.Provenance

/-! # Registration integrity and separate timing authentication

Ordinary inspection never consults a live tag, network service, or archived CA as
a trust anchor. Historical Git bytes establish integrity only. RFC3161 timing is
an optional host operation with separately supplied external trust policy.
-/
namespace AcornStudy

/-- Structurally inspected timestamp inputs, without an authentication claim. -/
structure TimestampEvidence where
  private mk ::
  /-- Original registered package. -/
  package : LocalPath
  /-- Retained timestamp response. -/
  reply : LocalPath
  /-- Retained untrusted certificate chain. -/
  certificates : LocalPath
  /-- Required external authority selector. -/
  trustId : String

/-- Historical tag/commit/tree association and explicit original-protocol binding. -/
def inspectHistorical (v : Acorn.Json.Value) (original : LocalPath) (owner : String)
    (history : ProtocolHistory) (integrity : Integrity) : IO Unit := do
  let (tag, tagOid, commitOid, objectValues, protocolPath, protocol, results, publication) ←
    checked (Acorn.Json.decode v do
      Acorn.Json.version 1
      unless (← Acorn.Json.text "kind") == "historical-git" do throw "wrong registration kind"
      let tag ← Acorn.Json.text "tag"
      let tagOid ← hex 40 (← Acorn.Json.text "tag_oid")
      let commitOid ← hex 40 (← Acorn.Json.text "commit_oid")
      let objects ← (← Acorn.Json.take "objects").list
      let protocolPath ← pathField "protocol_path"
      let protocol ← pathField "protocol"
      owned protocol owner
      let results ← optionalPath "results_path"
      let publication ← optionalPath "publication"
      if (← Acorn.Json.texts "limitations").isEmpty then throw "historical registration requires explicit limitations"
      return (tag, tagOid, commitOid, objects, protocolPath, protocol, results, publication))
  unless history.contains (protocolPath.val, original.val) do
    throw (IO.userError "historical protocol path does not bind preserved original in verified history")
  let objects ← loadObjects objectValues owner integrity
  let headers ← checked (getObject objects tagOid.val "tag" >>= gitHeaders)
  unless (← checked (header headers "object")) == commitOid.val &&
      (← checked (header headers "type")) == "commit" &&
      (← checked (header headers "tag")) == tag do
    throw (IO.userError "annotated tag does not bind named commit/tag")
  let root ← checked (getObject objects commitOid.val "commit" >>= gitHeaders >>= fun h => header h "tree")
  let _ ← checked (hex 40 root)
  verifyProtocolPath objects root protocolPath protocol
  if let some results := results then
    if (← checked (treePath objects root results.val)).isSome then
      throw (IO.userError "registration commit contains declared results path")
  if let some publication := publication then
    checked (owned publication owner)
    let bytes ← readBytes publication
    let some text := String.fromUTF8? bytes | throw (IO.userError "invalid publication UTF-8")
    let tagRef := "refs/tags/" ++ tag
    let peelRef := tagRef ++ "^{}"
    let mut named : List (String × String) := []
    for line in text.splitOn "\n" do
      let parts := ((line.toList.map (fun c => if Acorn.Json.unicodeWhitespace c then ' ' else c) |> String.ofList).splitOn " ").filter (· != "")
      if let [oid, name] := parts then
        if name == tagRef || name == peelRef then
          if named.any (fun p => p.1 == name) then throw (IO.userError "duplicate publication observation")
          named := named ++ [(name, oid)]
    unless named.contains (tagRef, tagOid.val) && named.contains (peelRef, commitOid.val) do
      throw (IO.userError "publication observation does not match tag object and commit peel")

/-- Retained timestamp packages admit protocol inputs only, never outcome roles. -/
def inspectTimestamp (v : Acorn.Json.Value) (original : LocalPath) (owner : String)
    (integrity : Integrity) : IO TimestampEvidence := do
  let timestamp ← checked (Acorn.Json.decode v do
    Acorn.Json.version 1
    unless (← Acorn.Json.text "kind") == "rfc3161" do throw "wrong registration kind"
    let package ← pathField "package"
    let reply ← pathField "reply"
    let certificates ← pathField "certificates"
    for path in [package, reply, certificates] do owned path owner
    let trustId ← Acorn.Json.text "trust_id"
    let _ ← Acorn.Json.text "prior_data_access"
    let _ ← Acorn.Json.texts "limitations"
    return TimestampEvidence.mk package reply certificates trustId)
  let materials ← decodeDocument timestamp.package do
    Acorn.Json.version 1
    (← (← Acorn.Json.take "materials").list).mapM (fun v => material v)
  let mut paths : List (String × String) := []
  for m in materials do
    if beneath m.path.val "studies" then checked (owned m.path owner)
    unless ["protocol", "population", "arms", "analysis", "exclusions", "stopping", "source", "build"].contains m.role do
      throw (IO.userError "registration package contains outcome or unknown material role")
    if m.path.val == timestamp.package.val || paths.contains (m.path.val, m.role) then
      throw (IO.userError "registration package self-reference or duplicate material")
    paths := paths ++ [(m.path.val, m.role)]
    integrity.file m.path m.sha256
  for role in ["protocol", "population", "arms", "analysis", "exclusions", "stopping"] do
    unless materials.any (fun m => m.role == role) do throw (IO.userError s!"registration package lacks {role}")
  unless paths.contains (original.val, "protocol") do
    throw (IO.userError "timestamp package does not bind declared original protocol")
  for path in [timestamp.package, timestamp.reply, timestamp.certificates] do
    integrity.requireVerified path
  return timestamp

/-- Inspect only a study-owned registration and its explicit original binding. -/
def inspectRegistration (path original : LocalPath) (owner : String)
    (history : ProtocolHistory) (integrity : Integrity) : IO (Option TimestampEvidence) := do
  checked (owned path owner)
  checked (owned original owner)
  let value ← document path
  let fields ← checked value.fields
  let some (_, kind) := fields.find? (fun p => p.1 == "kind") | throw (IO.userError "missing registration kind")
  match ← checked kind.text with
  | "historical-git" => inspectHistorical value original owner history integrity; return none
  | "rfc3161" => return some (← inspectTimestamp value original owner integrity)
  | _ => throw (IO.userError "unknown registration kind")

private def externalFile (path : System.FilePath) : IO System.FilePath := do
  unless path.isAbsolute do throw (IO.userError "registration trust path must be absolute")
  let canonical ← IO.FS.realPath path
  let repository ← IO.FS.realPath (← IO.currentDir)
  if beneath canonical.toString repository.toString || (← canonical.metadata).type != .file then
    throw (IO.userError "registration trust must be a regular file outside this repository")
  return canonical

private def trustedAuthority (id : String) : IO System.FilePath := do
  let some configured ← IO.getEnv "ACORN_REGISTRATION_TRUST"
    | throw (IO.userError "RFC3161 requires external ACORN_REGISTRATION_TRUST configuration")
  let path ← externalFile configured
  let bytes ← IO.FS.readBinFile path
  let some text := String.fromUTF8? bytes | throw (IO.userError "invalid trust configuration UTF-8")
  let authorities ← checked (Acorn.Json.parse text >>= fun v => Acorn.Json.decode v do
    Acorn.Json.version 1
    (← Acorn.Json.take "authorities").list)
  let mut found : List (String × System.FilePath) := []
  for value in authorities do
    let (key, caPath, expected) ← checked (Acorn.Json.decode value do
      let key ← Acorn.Json.text "id"
      let ca ← Acorn.Json.text "ca_file"
      let expected ← hex 64 (← Acorn.Json.text "sha256")
      return (key, ca, expected))
    let ca ← externalFile caPath
    unless (← digest true (← IO.FS.readBinFile ca)) == expected.val do
      throw (IO.userError "external trust anchor SHA256 mismatch")
    if found.any (fun p => p.1 == key) then throw (IO.userError "duplicate external authority id")
    found := found ++ [(key, ca)]
  let some (_, ca) := found.find? (fun p => p.1 == id)
    | throw (IO.userError "trust_id is not authorized by external trust configuration")
  return ca

/-- Optional message-imprint and chain authentication under external trust.
The provisioned OpenSSL timestamp verifier receives only the selected CAfile;
retained certificates remain untrusted intermediates. This does not prove blindness. -/
def TimestampEvidence.authenticate (self : TimestampEvidence) : IO Unit := do
  let ca ← trustedAuthority self.trustId
  let _ ← IO.Process.run {
    cmd := "openssl", args := #["ts", "-verify", "-data", self.package.val,
      "-in", self.reply.val, "-CAfile", ca.toString, "-untrusted", self.certificates.val] }

end AcornStudy
