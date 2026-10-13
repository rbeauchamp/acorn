/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Digits
import Acorn.Host.Viewer.Buffer
import Acorn.Host.Viewer.Retry
import Acorn.Host.Viewer.SupervisedProcess
import Acorn.Host.Viewer.WorldMemory

/-! # Browser execution wiring admission

The generated kernel owns the page's constants, frame store and its ring binding,
whole-frame admission, record conversion, validation and numeric programs; their
agreement with the schema is proved beside their definitions. This lexical gate
holds only what stays handwritten: the call sites that route the observer through
those owners, and its request/timer inventory. Rendered browser behavior is
inspected separately.
-/
namespace AcornBrowserAudit
open Acorn.Host.Viewer

private def require (legal : Bool) (message : String) : IO Unit :=
  unless legal do throw (IO.userError s!"browser wiring: {message}")

private def compact (text : String) : String :=
  String.ofList (text.toList.filter (!·.isWhitespace))

/-- One pass over a script that finds its comments and its string, template and regex literals.
The first result is the executable code with comments and literals removed, which the wiring
checks read. The second is the script with each comment replaced by one space and each literal
kept, each character marked when it belongs to a literal, delimiters included. This conservative
scanner follows the maintained page syntax; unterminated constructs fail admission rather than
contributing apparent executable tokens. -/
private def scan (text : String) : IO (String × List (Char × Bool)) := do
  let mut rest := text.toList
  let mut out := []
  let mut kept := []
  let mut quote : Option Char := none
  let mut block := false
  let mut line := false
  let mut regex := false
  let mut bracket := false
  let mut escaped := false
  for _ in [:rest.length] do
    let some c := rest.head? | break
    let next := rest[1]?
    rest := rest.drop 1
    if line then
      if c == '\n' then line := false
    else if block then
      if c == '*' && next == some '/' then block := false; rest := rest.drop 1
    else if let some endQuote := quote then
      kept := (c, true) :: kept
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == endQuote then quote := none
    else if regex then
      kept := (c, true) :: kept
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == '[' then bracket := true
      else if c == ']' then bracket := false
      else if c == '/' && !bracket then regex := false
    else if c == '/' && next == some '/' then
      line := true; rest := rest.drop 1; kept := (' ', false) :: kept
    else if c == '/' && next == some '*' then
      block := true; rest := rest.drop 1; kept := (' ', false) :: kept
    else if c == '"' || c == '\'' || c == '`' then quote := some c; kept := (c, true) :: kept
    else if c == '/' && ((out.find? (!·.isWhitespace)).isNone || (out.find? (!·.isWhitespace)).any ("(,=:[!&|?{};".contains ·)) then
      regex := true; kept := (c, true) :: kept
    else out := c :: out; kept := (c, false) :: kept
  require (!block && quote.isNone && !regex) "unterminated JavaScript construct"
  return (String.ofList out.reverse, kept.reverse)

/-- Remove JavaScript comments, strings and regex literals before wiring checks (`scan`). -/
def code (text : String) : IO String := return (← scan text).1

private def body (script function : String) : IO String := do
  let [_, rest] := script.splitOn ("function" ++ function ++ "{")
    | throw (IO.userError s!"browser function missing or duplicated: {function}")
  let mut depth := 1
  let mut out := []
  for c in rest.toList do
    if c == '{' then depth := depth + 1
    else if c == '}' then depth := depth - 1
    if depth == 0 then return String.ofList out.reverse
    out := c :: out
  throw (IO.userError s!"browser function is unclosed: {function}")

/-- The source of each inline script of a page. -/
private def sources (page : String) : IO (List String) := do
  let mut result := []
  for part in (page.splitOn "<script").drop 1 do
    let some rest := (part.splitOn ">").tail? | throw (IO.userError "unclosed script start")
    let content := String.intercalate ">" rest
    let [source, _] := content.splitOn "</script>"
      | throw (IO.userError "unclosed script body")
    result := source :: result
  return result.reverse

/-- All inline browser source after lexical comment/literal removal. -/
def scripts (page : String) : IO String := do
  let mut result := ""
  for source in ← sources page do
    result := result ++ (← code source)
  return result

/-- Whether a character can continue an ASCII identifier: an ASCII letter or digit, `_` or `$`. -/
private def wordChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '$'

/-- `text` after `start`, when it begins with `start`. -/
private def after (start text : List Char) : Option (List Char) :=
  if start.isPrefixOf text then some (text.drop start.length) else none

/-- The initializer of the statement `const NAME = …;` that `text` begins with: `const`, white
space, `NAME`, optional white space, `=`, and everything up to the next `;`, which must follow. -/
private def initializer (name text : List Char) : Option (List Char) := do
  let rest ← after "const".toList text
  let gap := rest.takeWhile Char.isWhitespace
  if gap.isEmpty then none
  let rest ← after name (rest.drop gap.length)
  let '=' :: rest := rest.dropWhile Char.isWhitespace | none
  let value := rest.takeWhile (· != ';')
  if (rest.drop value.length).isEmpty then none else some value

/-- The initializers of the statements `const NAME = …;` that begin a statement of `code`: at its
start, or after `;`, `{` or `}` and white space. -/
private def initializers (name code : List Char) : List (List Char) :=
  go none code
where
  /-- The initializers from `text` on, after the last character `last` other than white space. -/
  go (last : Option Char) : List Char → List (List Char)
    | [] => []
    | text@(c :: rest) =>
      let here := if last.all (";{}".contains ·) then (initializer name text).toList else []
      here ++ go (if c.isWhitespace then last else some c) rest

/-- Whether `text` begins with the keyword `keyword`, then at least one character that cannot
continue an ASCII identifier (`wordChar`), then `name` with no such character after it. -/
private def binds (name text keyword : List Char) : Bool :=
  match after keyword text with
  | none => false
  | some rest =>
    let gap := rest.takeWhile (!wordChar ·)
    match after name (rest.drop gap.length) with
    | none => false
    | some tail => !gap.isEmpty && !(tail.head?.any wordChar)

/-- The places in `text` where one of the keywords `const`, `let`, `var`, `function` and `class`,
not preceded by a character that can continue an ASCII identifier, binds `name` (`binds`). -/
private def bindings (name text : List Char) : Nat :=
  go none text
where
  /-- The places from `text` on, after the character `previous`. -/
  go (previous : Option Char) : List Char → Nat
    | [] => 0
    | text@(c :: rest) =>
      let here := if previous.any wordChar then 0 else
        (["const", "let", "var", "function", "class"].filter (binds name text ·.toList)).length
      here + go (some c) rest

/-- The value of a canonical JavaScript decimal integer literal, the initializer without the
white space around it: `0`, or a digit from `1` to `9` followed by digits (`Acorn.Digits.read`),
of at most `2 ^ 53 - 1`, so that a double holds it exactly. -/
private def literal (initializer : List Char) : Option Nat :=
  let trimmed := (initializer.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace
  match trimmed.reverse with
  | ['0'] => some 0
  | '0' :: _ => none
  | digits => (Acorn.Digits.read (String.ofList digits)).filter (· ≤ 2 ^ 53 - 1)

/-- Each inline script of a page, with each comment replaced by one space: the script with each
literal kept and the script with each character of a literal replaced by `#`. -/
private def declarations (page : String) : IO (List (List Char × List Char)) := do
  let mut result := []
  for source in ← sources page do
    let kept := (← scan source).2
    result := (kept.map (·.1), kept.map fun (c, literal) => if literal then '#' else c) :: result
  return result.reverse

/-- The value of a page constant. The audit admits a page constant exactly when the page's
executable code, with comments removed and string, template and regex literals kept as opaque
tokens so that nothing after the initializer is hidden (`scan`), declares `NAME` exactly once, as
the statement `const NAME = LITERAL;`. `const` is a whole keyword at a statement start: at the
start of a script, or after `;`, `{` or `}` and white space (a space, tab, carriage return or
line feed). `NAME` is the complete identifier, followed by white space or `=`. No other whole
word `const`, `let`, `var`, `function` or `class` anywhere in the page's scripts, literals
included, binds `NAME` lexically: is followed by characters that cannot continue an ASCII
identifier and then by `NAME` as a whole word. `LITERAL`, the whole initializer between `=` and
the next `;` of the executable code without the white space around it, is a canonical JavaScript
decimal integer literal: `0`, or a digit from `1` to `9` followed by digits, read by
`Acorn.Digits.read`, with a value of at most `2 ^ 53 - 1`. So the admitted value is the value
that JavaScript evaluates: a leading zero, which a page outside strict mode reads as octal, and
a value that a double rounds are refused. -/
private def number (scripts : List (List Char × List Char)) (name : String) : Option Nat := do
  let [value] := scripts.flatMap (initializers name.toList ·.2) | none
  if (scripts.map (bindings name.toList ·.1)).sum == 1 then literal value else none

/-- Pages that the audit refuses for the constant `WIN`, since none declares it as a canonical
literal whose digits are the value JavaScript evaluates: a declaration of a name that only ends in
`WIN`, beside a `let` of `WIN` with a digit separator; an initializer that a tagged template
follows; a leading zero, which the page reads as octal; and a value that a double rounds. -/
private def refusedControls : List String :=
  ["<script>const constWIN = 1000; let WIN = 1000_000;</script>",
    "<script>const WIN = 1000`x`;</script>", "<script>const WIN = 01000;</script>",
    "<script>const WIN = 9007199254740993;</script>"]

/-- Check the documented constants against their sources: each row whose source is the page names
a constant that the page admits (`number`) with the documented value, and there is at least one
such row; each native row names the constant of its module with the documented value. -/
private def documentConstants (scripts : List (List Char × List Char)) : IO Unit := do
  let text ← IO.FS.readFile "docs/viewer-ux.md"
  let [_, appendix] := text.splitOn "## Appendix A"
    | throw (IO.userError "missing/duplicate viewer constants appendix")
  let native := [("replayCapacity", "Acorn.Host.Viewer.Buffer", replayCapacity),
    ("failureLimit", "Acorn.Host.Viewer.Retry", failureLimit),
    ("healthyRunMs", "Acorn.Host.Viewer.SupervisedProcess", healthyRunMs),
    ("mapSideCapacity", "Acorn.Host.Viewer.WorldMemory", mapSideCapacity)]
  let mut seen := []
  let mut pageRows := 0
  for line in appendix.splitOn "\n" do
    let cells := (line.splitOn "|").map (·.trimAscii.toString)
    match cells with
    | ["", name, value, source, ""] =>
      if name.startsWith "`" && source.startsWith "`" then
        let name := name.replace "`" ""
        let source := source.replace "`" ""
        require (!seen.contains name) s!"duplicate documented constant {name}"
        seen := name :: seen
        let page := source == "viewer/static/index.html"
        if page then pageRows := pageRows + 1
        let actual := if page then number scripts name else
          native.find? (fun row => row.1 == name && row.2.1 == source) |>.map (·.2.2)
        let documented := Acorn.Digits.read value
        require (documented.isSome && documented == actual) s!"documented constant differs: {name}"
    | _ => pure ()
  require (seen.length ≥ 2 && native.all (fun row => seen.contains row.1)) "missing native constant rows"
  require (pageRows > 0) "missing page constant rows"

/-- Check the generated-program call sites and the request/timer inventory. -/
def check : IO Unit := do
  let page ← IO.FS.readFile "viewer/static/index.html"
  let script := compact (← scripts page)
  for (token, count) in [("setInterval(", 3), ("setTimeout(", 1), ("fetch(", 1)] do
    require ((script.splitOn token).length == count + 1) s!"request/timer inventory differs: {token}"
  require (page.contains "fetch(\"/control\"") "request target differs from /control"
  require ((page.splitOn "/* LEAN_BROWSER_KERNEL */").length == 2) "kernel insertion must be unique"
  let part ← body script "admitEnvelope(f)"
  require (part.contains "if(!observerEnvelope(f)||!ctlState||f.run_id!==ctlState.runId||f.agent_epoch!==ctlState.agentEpoch)returnfalse;") "admitEnvelope(f) bypasses its admitted wiring"
  require (part.contains "constnext=[f.timestamp_ms,f.lifetime_step,f.world_step];") "admitEnvelope(f) bypasses its admitted wiring"
  require (part.contains "captureWatermark&&captureWatermark.runId===f.run_id&&captureWatermark.epoch===f.agent_epoch") "admitEnvelope(f) bypasses its admitted wiring"
  require (part.contains "if(!observerAfter(...next,...previous))returnfalse;") "admitEnvelope(f) bypasses its admitted wiring"
  require (part.contains "captureWatermark={runId:f.run_id,epoch:f.agent_epoch,at:next};returntrue;") "admitEnvelope(f) bypasses its admitted wiring"
  let part ← body script "connect()"
  require (part.contains "constfreshCapture=admitEnvelope(f);letoutcome=Intake.skipped;try{outcome=pushFrame(f);}") "connect() bypasses its admitted wiring"
  require (part.contains "if(!freshCapture)return;if(outcome===Intake.stored||outcome===Intake.rewound){identity.at=Date.now();identity.origin=f.origin;}lastFrameAt=Date.now();received++;streamStale=false;") "connect() bypasses its admitted wiring"
  let part ← body script "windowStats(id)"
  require (part.contains "aCtl:meanPositive(values()),aDem:meanPositive(values())") "windowStats(id) bypasses its admitted wiring"
  require (part.contains "aMeta:familyRate(,N_META),aOpt:familyRate(,N_CTL*N_SKILL)") "windowStats(id) bypasses its admitted wiring"
  require (part.contains "constfamilyRate=(field,width)=>meanPositive(indices.map(i=>meanPositive(S[field].subarray(i*width,(i+1)*width))))") "windowStats(id) bypasses its admitted wiring"
  let part ← body script "resetAgentBuffer()"
  require (part.contains "resetReadouts();") "resetAgentBuffer() bypasses its admitted wiring"
  let part ← body script "resetReadouts()"
  require (part.contains "$().title=WORLD_TILE_NOTE;") "resetReadouts() bypasses its admitted wiring"
  let part ← body script "meanPositive(values)"
  require (part.contains "returnObserverMath.meanPositive([],observerRows(values));") "meanPositive(values) bypasses its admitted wiring"
  let part ← body script "admitAgreement(next)"
  require (part.contains "if(!observerSnapshotFollows(next.process,next.clock,Number(next.stopped),n.cycle,n.resolved,n.attempt,Number(n.invalid),previous.process,previous.clock,Number(previous.stopped),p.cycle,p.resolved,p.attempt,Number(p.invalid)))returnfalse;")
    "agreement replacement bypasses generated process/clock admission"
  require (part.contains "A.latestAgreement=next;") "agreement must retain the authoritative snapshot"
  require (!script.contains "ObserverMath.finiteReturn(" && !script.contains "functionverify()")
    "browser must not reconstruct primary evaluation returns"
  let goalText ← body script "goalText(gkind,gitem,gx,gy,gn)"
  require (goalText == "returnobserverGoalText(gkind,gitem,gx,gy,gn);")
    "goal presentation must use the exhaustive semantic vocabulary"
  let connect ← body script "connect()"
  require ((connect.splitOn "received++").length == 2) "capture counter must have one guarded increment"
  require (page.contains "$(\"t_world\").title = WORLD_TILE_NOTE;") "readout reset omits world-tile title"
  for control in refusedControls do
    require (number (← declarations control) "WIN").isNone
      s!"page constant reader admits a refused control: {control}"
  documentConstants (← declarations page)
  IO.println "browser: generated program wiring and request/timer inventory admitted"

end AcornBrowserAudit
