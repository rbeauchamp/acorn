import Acorn.Host.Viewer.BrowserStore
import Acorn.Host.Viewer.Buffer
import Acorn.Host.Viewer.Retry
import Acorn.Host.Viewer.Supervision
import Acorn.Host.Viewer.WorldMemory
import AcornTools.TrackedFiles

namespace AcornBrowserAudit
open Acorn.Host.Viewer

private def require (legal : Bool) (message : String) : IO Unit :=
  unless legal do throw (IO.userError s!"viewer constants: {message}")

private def ownedConstants : List (String × String × Nat) :=
  (([.readPace, .statsWindow, .frameCapacity, .ribbonSpan, .staleAfter, .tilePixels] :
      List BrowserConstant).map fun constant =>
    (constant.name, "Acorn.Host.Viewer.BrowserStore", constant.value)) ++
  [("replayCapacity", "Acorn.Host.Viewer.Buffer", replayCapacity),
    ("failureLimit", "Acorn.Host.Viewer.Retry", failureLimit),
    ("healthyRunMs", "Acorn.Host.Viewer.Supervision", healthyRunMs),
    ("mapSideCapacity", "Acorn.Host.Viewer.WorldMemory", mapSideCapacity)]

private def constantsTable : String :=
  "| constant | value | declared in |\n|---|---|---|\n" ++
    String.join (ownedConstants.map fun (name, source, value) =>
      s!"| `{name}` | {value} | `{source}` |\n")

private def appendixTitle : String := "Appendix A · Constants this document quotes"

private def occurrences (block : List String) (lines : List String) : Nat :=
  match lines with
  | [] => if block.isEmpty then 1 else 0
  | _ :: rest => (if block.isPrefixOf lines then 1 else 0) + occurrences block rest

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

def check : IO Unit := do
  AcornTrackedFiles.ensureTrackedRegular "." "" "docs/viewer-ux.md"
  match documentConstants (← IO.FS.readFile "docs/viewer-ux.md") with
  | .ok () => pure ()
  | .error message => require false message
  IO.println "viewer: document constants match their Lean owners"

end AcornBrowserAudit
