/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import NativeApp.MutationAudit
import AcornTools.VerificationProfile

/-! # Published mutation-pin consistency

The current pin leaf and actual audit command admission own every live printed
expectation. Historical movements remain historical; matching a digest is never
interpreted as correctness, qualification or universal conformance.
-/
namespace AcornPinAudit

private def hexWords (text : String) : List String :=
  ((String.ofList (text.toList.map fun c =>
    if c.isDigit || ('a' ≤ c && c ≤ 'f') then c else ' ')).splitOn " ").filter
      (fun word => word.length == 16)

private def after (text lead : String) : List String :=
  (text.splitOn lead).drop 1 |>.filterMap fun rest => (hexWords rest).head?

private def require (legal : Bool) (message : String) : IO Unit :=
  unless legal do throw (IO.userError message)

private def current : List NativeApp.AuditArm := [.derived, .annealed, .differential]

private def commands (line : String) : Except String (List (NativeApp.AuditArm × Bool)) := do
  let mut result := []
  for rest in ((line.replace "acorn-core audit" "acorn audit").splitOn "acorn audit").drop 1 do
    let rest := (rest.splitOn "`").headD rest
    let rest := (rest.splitOn "#").headD rest
    let words := (rest.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
    if words.contains "…" || words.contains "..." then continue
    match NativeApp.auditOptions words with
    | .ok arm => result := result ++ [(arm, words.contains "--expect")]
    | .error _ => throw "printed audit command is not admitted"
  return result

/-- Check all published command/pin/checksum pairs and the explicit movement row. -/
def checkTexts (documents : Array (String × String)) (verification readiness : String)
    (studyPage : Option String := none) (historicalMovement : Bool := true) : IO Unit := do
  let pinned := NativeApp.hexWord NativeApp.AuditArm.derived.receipt.digest
  require (after verification "**Pinned digest: `" == [pinned]) "verification pinned digest differs"
  if let some page := studyPage then
    require (after page "LIVE_AGENT_PIN=\"" == [pinned]) "study viewer live pin differs"
  let rows := (readiness.splitOn "\n").filter (·.startsWith "| C-AC5 ")
  let [row] := rows | throw (IO.userError "readiness requires one C-AC5 movement row")
  let segments := (row.splitOn "moved").drop 1
  let mut chain := []
  for segment in segments do
    let some digest := (after segment "to `").head? | continue
    chain := (digest, (after segment "checksum `").head?) :: chain
  for arm in current do
    let digest := NativeApp.hexWord arm.receipt.digest
    let checksum := NativeApp.hexWord arm.receipt.checksum
    require (if historicalMovement then chain.contains (digest, some checksum) else
      row.contains s!"`{digest}`, checksum `{checksum}`") s!"C-AC5 omits current pair {digest}/{checksum}"
  let superseded := chain.map Prod.fst |>.filter fun word =>
    !current.any (fun arm => NativeApp.hexWord arm.receipt.digest == word)
  let mut expectations := 0
  for (path, text) in documents do
    let lines := text.splitOn "\n"
    for index in [:lines.length] do
      let line := lines[index]?.getD ""
      let admitted ← match commands line with
        | .ok admitted => pure admitted
        | .error message => throw (IO.userError s!"{path}:{index+1}: {message}")
      for (arm, expected) in admitted do
        unless expected do continue
        expectations := expectations + 1
        let window := String.intercalate " " ((lines.drop (index+1)).take 8)
        let sums := after window "checksum"
        require (sums.head? == some (NativeApp.hexWord arm.receipt.checksum))
          s!"{path}:{index+1}: audit lacks its paired checksum within eight lines"
    let words := (String.ofList (text.toList.map fun c => if c.isWhitespace then ' ' else c)).splitOn " "
      |>.filter (!·.isEmpty)
    for index in [:words.length] do
      let left := (words[index]?.getD "").toLower
      let right := (words[index+1]?.getD "").toLower
      if ["current", "live"].contains left && ["pin", "pins", "digest", "digests"].contains right then
        let subject := String.intercalate " " ((((words.take index).reverse.take 3).takeWhile
          (fun w => !w.endsWith "." && !w.endsWith ";" && !w.contains '|')).reverse)
        let claim := String.intercalate " " (((words.drop (index+2)).take 12).takeWhile fun w =>
          !w.endsWith "." && !w.endsWith ";" && !w.contains '|')
        require (!(hexWords (subject ++ " " ++ claim)).any superseded.contains)
          s!"{path}: superseded digest described as current"
  require (expectations > 0) "no concrete audit expectation with checksum is published"

/-- Installed corpus admission uses the explicitly selected historical page obligation. -/
def check (documents : Array (String × String)) : IO Unit := do
  let page ← if AcornVerificationProfile.privateEvidence then
    some <$> IO.FS.readFile "viewer/static/study.html" else pure none
  let readinessPath := if AcornVerificationProfile.privateEvidence then
    "docs/production-readiness.md" else "docs/frontier.md"
  checkTexts documents (← IO.FS.readFile "docs/verification.md")
    (← IO.FS.readFile readinessPath) page AcornVerificationProfile.privateEvidence

end AcornPinAudit
