import AcornTools.ModuleInventory
import AcornTools.Native.Routes
import AcornTools.Native.Resources
import AcornTools.TrackedFiles

namespace AcornNativeAudit
open Lean

def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError s!"native boundary: {message}")

def read (path : System.FilePath) : IO String := do
  AcornTrackedFiles.ensureRegular "." path.toString
  IO.FS.readFile path

def functionBody (source symbol : String) : Option String := do
  let marker := if symbol.startsWith "_init_" then "static " else "LEAN_EXPORT "
  let start ← (source.splitOn "\n").find? fun line =>
    line.startsWith marker && (line.splitOn (symbol ++ "(")).length > 1 && line.endsWith "{"
  let after : String ← (source.splitOn start)[1]?
  let mut depth := 1
  let mut body := ""
  for c in after.toList do
    if c == '{' then depth := depth + 1
    else if c == '}' then
      depth := depth - 1
      if depth == 0 then return body
    body := body.push c
  none

def orderedCalls (source symbol : String) (calls : Array String) : IO Unit := do
  let some body := functionBody source symbol
    | throw (IO.userError s!"missing compiled definition {symbol}")
  let mut remaining := body
  for call in calls do
    let parts := remaining.splitOn (call ++ "(")
    require (parts.length > 1) s!"{symbol} lacks ordered call {call}"
    remaining := String.intercalate (call ++ "(") parts.tail

def orderedClosures (source symbol : String) (closures : Array String) : IO Unit := do
  let some body := functionBody source symbol
    | throw (IO.userError s!"missing compiled definition {symbol}")
  let mut remaining := body
  for closure in closures do
    let token := "lean_alloc_closure((void*)(" ++ closure ++ "),"
    let parts := remaining.splitOn token
    require (parts.length > 1) s!"{symbol} lacks ordered closure {closure}"
    remaining := String.intercalate token parts.tail

def primitiveAllowed (owner : Name) (token : String) : Bool :=
  #["lean_float_of_bits", "lean_float_to_bits", "lean_float_add", "lean_float_sub",
    "lean_float_mul", "lean_float_div", "lean_float_once", "lean_float32_of_bits",
    "lean_float32_to_bits", "lean_float32_add", "lean_float32_sub", "lean_float32_mul",
    "lean_float32_div", "lean_float32_once", "lean_float32_to_float", "lean_float32_to_uint8",
    "lean_float_to_float32", "lean_uint64_to_float", "lean_uint64_to_float32"].contains token ||
  (owner == `Acorn.Host.Endurance &&
    #["lean_float_decLt", "lean_float_decLe", "lean_float32_isnan", "lean_float32_isinf",
      "lean_float32_of_nat", "lean_float_of_nat"].contains token) ||
  (owner == `Acorn.Host.Viewer.BrowserMath &&
    #["lean_float_of_nat", "lean_float_isnan", "lean_float_isinf", "lean_float_decLt",
      "lean_float_negate", "lean_float_beq"].contains token)

def primitives (owner : Name) (source : String) : IO Unit := do
  let tokens := source.splitToList fun c => !c.isAlphanum && c != '_'
  for token in tokens do
    if token.startsWith "lean_float" || (token.splitOn "_to_float").length > 1 then
      require (primitiveAllowed owner token) s!"{owner}: unreviewed native primitive {token}"

def allowedArgument (argument : String) : Bool :=
  !argument.toList.any (fun c => c == '\'' || c == '"' || c == '\\') &&
  (argument.startsWith "/" || #["-c", "-o", "-I", "-isystem", "--sysroot",
    "-fstack-clash-protection", "-fPIC", "-ffp-contract=off", "-fno-fast-math",
    "-fdata-sections", "-ffunction-sections", "-fvisibility=hidden",
    "-Wno-unused-command-line-argument", "-nostdinc", "-O3", "-DNDEBUG",
    "-DLEAN_EXPORTING"].contains argument)

def compileFlags (text : String) : IO Unit := do
  let trace ← IO.ofExcept (Json.parse text)
  let log ← IO.ofExcept (trace.getObjValAs? (Array Json) "log")
  let mut commands := 0
  for entry in log do
    let message ← IO.ofExcept (entry.getObjValAs? String "message")
    if message.startsWith ".> " then
      let args := (String.ofList (message.toList.drop 3)).splitToList Char.isWhitespace |>.filter (!·.isEmpty)
      let compiler :: arguments := args
        | throw (IO.userError "empty native compiler command")
      require (compiler.endsWith "/clang") s!"unreviewed native compiler {compiler}"
      for argument in arguments do
        require (allowedArgument argument) s!"unreviewed native argument {argument}"
      for required in #["-c", "-ffp-contract=off", "-fno-fast-math"] do
        require (arguments.contains required) s!"native command lacks {required}"
      commands := commands + 1
  require (commands == 1) s!"expected one compilation command, found {commands}"

private def irCPath (owner : Name) : System.FilePath :=
  System.FilePath.mk (".lake/build/ir/" ++ owner.toString.replace "." "/" ++ ".c")

private def routeModule (owner : String) : Name :=
  (("Acorn/" ++ owner).splitOn "/").foldl Name.str .anonymous

unsafe def audit : IO Unit := do
  let modules ← AcornModuleInventory.projectModules
  let nativeModules := modules.filter AcornModuleInventory.nativeModule
  for owner in nativeModules do
    let path := irCPath owner
    primitives owner (← read path)
    compileFlags (← read (path.toString ++ ".o.export.trace"))
  for (owner, symbol, calls) in AcornNativeRoutes.routes do
    let mod := routeModule owner
    require (nativeModules.contains mod) s!"route owner {mod} is not an admitted native module"
    orderedCalls (← read (irCPath mod)) symbol calls
  for (owner, symbol, closures) in AcornNativeRoutes.closures do
    let mod := routeModule owner
    require (nativeModules.contains mod) s!"closure owner {mod} is not an admitted native module"
    orderedClosures (← read (irCPath mod)) symbol closures
  AcornNativeResourceAudit.audit nativeModules
  IO.println s!"native boundary: {AcornNativeRoutes.routes.size} reviewed call routes; flags and primitives admitted"

end AcornNativeAudit

unsafe def main (args : List String) : IO UInt32 := do
  unless args.isEmpty do
    IO.eprintln "usage: native-audit"
    return 1
  try
    AcornNativeAudit.audit
    return 0
  catch error =>
    IO.eprintln s!"native-audit: {error}"
    return 1
