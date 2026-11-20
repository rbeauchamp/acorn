/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornTools.Subjects

/-! # Published mutation-pin consistency

The current pin leaf and actual audit command admission own every live printed
expectation. A digest difference detects a change in the audit stream; matching
digests do not establish correctness or transition equivalence.
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

/-- What the pin audit reads of the program, as subjects of the finished build. -/
structure Program where
  /-- Each audit arm, the declared arm first: its pinned digest as the audit prints it, the
  same digest as sixteen bare hexadecimal digits, and its pinned checksum. -/
  arms : List (String × String × String)
  /-- The pinned checksum of the arm that the program's own parser of audit options selects for
  the words of a command, or nothing when the parser refuses them. -/
  options : List String → Option String

/-- Read the audit arms' pins and the program's option parser from the finished build `env`. -/
unsafe def program (env : Lean.Environment) : IO Program := do
  let arms ← AcornSubjects.read (List (String × String × String)) env
    "List (String × String × String)"
    "[NativeApp.AuditArm.declared, NativeApp.AuditArm.annealed, \
      NativeApp.AuditArm.differential].map (fun arm => \
      (NativeApp.auditWord arm.receipt.digest, NativeApp.hexWord arm.receipt.digest, \
        NativeApp.hexWord arm.receipt.checksum))"
  let options ← AcornSubjects.read (List String → Option String) env
    "List String → Option String"
    "fun words => (NativeApp.auditOptions words).toOption.map \
      (fun arm => NativeApp.hexWord arm.receipt.checksum)"
  return { arms, options }

/-- The audit commands a line prints, each as the pinned checksum of its arm and whether it
carries `--expect`. A command the program's parser refuses is an error. -/
private def commands (program : Program) (line : String) :
    Except String (List (String × Bool)) := do
  let mut result := []
  for rest in ((line.replace "acorn-core audit" "acorn audit").splitOn "acorn audit").drop 1 do
    let rest := (rest.splitOn "`").headD rest
    let rest := (rest.splitOn "#").headD rest
    let words := (rest.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
    if words.contains "…" || words.contains "..." then continue
    match program.options words with
    | some checksum => result := result ++ [(checksum, words.contains "--expect")]
    | none => throw "printed audit command is not admitted"
  return result

/-- Check published command/pin/checksum pairs and the current register row. -/
def checkTexts (program : Program) (documents : Array (String × String))
    (verification readiness : String) : IO Unit := do
  let some (_, pinned, _) := program.arms.head? | throw (IO.userError "no audit arm is pinned")
  require (after verification "**Pinned digest: `" == [pinned]) "verification pinned digest differs"
  let rows := (readiness.splitOn "\n").filter (·.startsWith "| C-AC5 ")
  let [row] := rows | throw (IO.userError "readiness requires one C-AC5 row")
  for (digest, _, checksum) in program.arms do
    require (row.contains s!"`{digest}`, checksum `{checksum}`") s!"C-AC5 omits current pair {digest}/{checksum}"
  let mut expectations := 0
  for (path, text) in documents do
    let lines := text.splitOn "\n"
    for index in [:lines.length] do
      let line := lines[index]?.getD ""
      let admitted ← match commands program line with
        | .ok admitted => pure admitted
        | .error message => throw (IO.userError s!"{path}:{index+1}: {message}")
      for (checksum, expected) in admitted do
        unless expected do continue
        expectations := expectations + 1
        let window := String.intercalate " " ((lines.drop (index+1)).take 8)
        let sums := after window "checksum"
        require (sums.head? == some checksum)
          s!"{path}:{index+1}: audit lacks its paired checksum within eight lines"
  require (expectations > 0) "no concrete audit expectation with checksum is published"

/-- The maintained documentation binds every current audit arm to its pin, in the finished
build `env`. -/
unsafe def check (env : Lean.Environment) (documents : Array (String × String)) : IO Unit := do
  checkTexts (← program env) documents (← IO.FS.readFile "docs/verification.md")
    (← IO.FS.readFile "docs/frontier.md")

end AcornPinAudit
