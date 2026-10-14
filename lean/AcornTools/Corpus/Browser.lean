/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.BrowserStore
import Acorn.Host.Viewer.Buffer
import Acorn.Host.Viewer.Retry
import Acorn.Host.Viewer.SupervisedProcess
import Acorn.Host.Viewer.WorldMemory

/-! # Browser execution wiring admission

The generated kernel owns the page constants that `BrowserConstant` represents, the
frame store and its ring binding, whole-frame admission, record conversion, validation
and numeric programs; their agreement with the schema is proved beside their
definitions. This lexical gate
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

/-- Remove JavaScript comments, strings and regex literals before wiring checks.
This conservative scanner follows the maintained page syntax; unterminated
constructs fail admission rather than contributing apparent executable tokens. -/
def code (text : String) : IO String := do
  let mut rest := text.toList
  let mut out := []
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
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == endQuote then quote := none
    else if regex then
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == '[' then bracket := true
      else if c == ']' then bracket := false
      else if c == '/' && !bracket then regex := false
    else if c == '/' && next == some '/' then line := true; rest := rest.drop 1
    else if c == '/' && next == some '*' then block := true; rest := rest.drop 1
    else if c == '"' || c == '\'' || c == '`' then quote := some c
    else if c == '/' && ((out.find? (!·.isWhitespace)).isNone || (out.find? (!·.isWhitespace)).any ("(,=:[!&|?{};".contains ·)) then regex := true
    else out := c :: out
  require (!block && quote.isNone && !regex) "unterminated JavaScript construct"
  return String.ofList out.reverse

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

/-- All inline browser source after lexical comment/literal removal. -/
def scripts (page : String) : IO String := do
  let mut result := ""
  for part in (page.splitOn "<script").drop 1 do
    let some rest := (part.splitOn ">").tail? | throw (IO.userError "unclosed script start")
    let content := String.intercalate ">" rest
    let [source, _] := content.splitOn "</script>"
      | throw (IO.userError "unclosed script body")
    result := result ++ (← code source)
  return result

/-- The constants that Appendix A of the viewer specification quotes, in the order of its table,
each with the module that declares it and the value the viewer uses: the page's own constants,
which the generated kernel declares (`BrowserConstant`), then the server's. -/
private def ownedConstants : List (String × String × Nat) :=
  (([.readPace, .statsWindow, .frameCapacity, .ribbonSpan, .staleAfter, .tilePixels] :
      List BrowserConstant).map fun constant =>
    (constant.name, "Acorn.Host.Viewer.BrowserStore", constant.value)) ++
  [("replayCapacity", "Acorn.Host.Viewer.Buffer", replayCapacity),
    ("failureLimit", "Acorn.Host.Viewer.Retry", failureLimit),
    ("healthyRunMs", "Acorn.Host.Viewer.SupervisedProcess", healthyRunMs),
    ("mapSideCapacity", "Acorn.Host.Viewer.WorldMemory", mapSideCapacity)]

/-- The constants table of Appendix A rendered from the Lean owners: its header, its separator
and one row per constant of `ownedConstants`, each line ending in a line feed. -/
private def constantsTable : String :=
  "| constant | value | declared in |\n|---|---|---|\n" ++
    String.join (ownedConstants.map fun (name, source, value) =>
      s!"| `{name}` | {value} | `{source}` |\n")

/-- The title of Appendix A of the viewer specification. -/
private def appendixTitle : String := "Appendix A · Constants this document quotes"

/-- The number of places in `lines` where the lines of `block` occur one after another. -/
private def occurrences (block : List String) (lines : List String) : Nat :=
  match lines with
  | [] => if block.isEmpty then 1 else 0
  | _ :: rest => (if block.isPrefixOf lines then 1 else 0) + occurrences block rest

/-- Check the constants table of the viewer specification against the Lean owners. The
specification is read as lines, split at each line feed. Exactly one line holds the title of
Appendix A, and it is the whole heading `## Appendix A · Constants this document quotes`. Among
the lines after it, to the end of the file, the lines of `constantsTable` occur one after another
exactly once, and no other line contains `|`, so no second table, extra row or row in another
spelling can stand beside it. The lines run to the end of the file rather than to the next
heading of the same level, which Appendix A, the last such section, does not have, so finding
that heading needs no reading of code blocks or HTML. -/
private def documentConstants (text : String) : Except String Unit := do
  let lines := text.splitOn "\n"
  let table := (constantsTable.splitOn "\n").dropLast
  let [heading] := lines.filter fun line => (line.splitOn appendixTitle).length > 1
    | throw "missing/duplicate viewer constants appendix"
  unless heading == "## " ++ appendixTitle do throw "malformed viewer constants appendix heading"
  let appendix := (lines.dropWhile (· != heading)).drop 1
  unless occurrences table appendix == 1 do
    throw "the constants table differs from its Lean owners or occurs twice"
  unless appendix.filter (·.contains '|') == table do
    throw "a table line in Appendix A outside the constants table"

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
  match documentConstants (← IO.FS.readFile "docs/viewer-ux.md") with
  | .ok () => pure ()
  | .error message => require false message
  IO.println "browser: generated program wiring and request/timer inventory admitted"

end AcornBrowserAudit
