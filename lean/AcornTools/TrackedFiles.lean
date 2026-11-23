import Std.Data.HashSet.Basic

namespace AcornTrackedFiles

private def stripNewline (text : String) : String :=
  (text.dropEndWhile fun c => c == '\n' || c == '\r').toString

def checkComponents (rel : String) : IO (List String) := do
  if rel.isEmpty || rel.startsWith "/" || rel.endsWith "/" ||
      rel.contains '\n' || rel.contains '\r' || rel.contains (Char.ofNat 0) then
    throw (IO.userError s!"unsupported tracked path: {rel}")
  let parts := rel.splitOn "/"
  for part in parts do
    if part.isEmpty || part == "." || part == ".." then
      throw (IO.userError s!"unsupported path component in {rel}")
  return parts

private def ensureAncestors (root : System.FilePath)
    (seenDirs : IO.Ref (Std.HashSet String)) (parts : List String) : IO Unit := do
  let mut curRel := ""
  for part in parts.dropLast do
    curRel := if curRel.isEmpty then part else curRel ++ "/" ++ part
    if !(← seenDirs.get).contains curRel then
      let entryMeta ← (root / curRel).symlinkMetadata
      unless entryMeta.type == .dir do
        throw (IO.userError s!"non-directory ancestor {curRel}")
      seenDirs.modify (·.insert curRel)

def ensureRegular (root : System.FilePath) (rel : String) : IO Unit := do
  let parts ← checkComponents rel
  let seenDirs ← IO.mkRef ({} : Std.HashSet String)
  ensureAncestors root seenDirs parts
  let entryMeta ← (root / rel).symlinkMetadata
  unless entryMeta.type == .file do
    throw (IO.userError s!"non-regular tracked entry {rel}")

def ensureRegularDir (root : System.FilePath) (rel : String) : IO Unit := do
  let parts ← checkComponents rel
  let seenDirs ← IO.mkRef ({} : Std.HashSet String)
  ensureAncestors root seenDirs parts
  let entryMeta ← (root / rel).symlinkMetadata
  unless entryMeta.type == .dir do
    throw (IO.userError s!"non-directory tracked directory {rel}")

def verifyGitRoot (dir : System.FilePath) (expectedPrefix : Option String := none) : IO Unit := do
  let dirMeta ← dir.symlinkMetadata
  unless dirMeta.type == .dir do
    throw (IO.userError s!"expected directory for Git root: {dir}")
  let topOut ← IO.Process.output {
    cmd := "git", args := #["-C", dir.toString, "rev-parse", "--show-toplevel"], stdin := .null }
  unless topOut.exitCode == 0 do
    throw (IO.userError s!"git rev-parse --show-toplevel failed in {dir}: {topOut.stderr}")
  let prefixOut ← IO.Process.output {
    cmd := "git", args := #["-C", dir.toString, "rev-parse", "--show-prefix"], stdin := .null }
  unless prefixOut.exitCode == 0 do
    throw (IO.userError s!"git rev-parse --show-prefix failed in {dir}: {prefixOut.stderr}")
  let topStr := stripNewline topOut.stdout
  let prefixStr := stripNewline prefixOut.stdout
  if let some expected := expectedPrefix then
    unless prefixStr == expected do
      throw (IO.userError s!"unexpected git prefix {prefixStr} in {dir}, expected {expected}")
  let target := if prefixStr.isEmpty then System.FilePath.mk topStr
    else System.FilePath.mk topStr / (prefixStr.dropEndWhile (· == '/')).toString
  unless (← IO.FS.realPath target) == (← IO.FS.realPath dir) do
    throw (IO.userError s!"git root mismatch for {dir}")

private def parseStageRecords (stdout : String) : IO (Array String) := do
  let records := (stdout.splitOn (String.singleton (Char.ofNat 0))).filter (!·.isEmpty)
  if records.isEmpty then
    throw (IO.userError "git ls-files returned no tracked entries")
  let mut paths := #[]
  for record in records do
    let [metaPart, path] := record.splitOn "\t"
      | throw (IO.userError s!"malformed git ls-files record: {record}")
    let [mode, _, stage] := metaPart.splitOn " "
      | throw (IO.userError s!"malformed git ls-files metadata: {metaPart}")
    unless (mode == "100644" || mode == "100755") && stage == "0" do
      throw (IO.userError s!"unsupported tracked entry mode or stage for {path}")
    discard (checkComponents path)
    paths := paths.push path
  return paths.qsort (· < ·)

def listTracked (dir : System.FilePath) (expectedPrefix : Option String := none) :
    IO (Array String) := do
  verifyGitRoot dir expectedPrefix
  let out ← IO.Process.output {
    cmd := "git",
    args := #["-C", dir.toString, "-c", "core.quotePath=false", "ls-files", "--stage", "-z"],
    stdin := .null }
  unless out.exitCode == 0 do
    throw (IO.userError s!"git ls-files failed in {dir}: {out.stderr}")
  let paths ← parseStageRecords out.stdout
  let seenDirs ← IO.mkRef ({} : Std.HashSet String)
  for path in paths do
    let parts := path.splitOn "/"
    ensureAncestors dir seenDirs parts
    let entryMeta ← (dir / path).symlinkMetadata
    unless entryMeta.type == .file do
      throw (IO.userError s!"non-regular tracked entry {path}")
  return paths

def ensureTrackedRegular (dir : System.FilePath) (expectedPrefix : Option String)
    (rel : String) : IO Unit := do
  discard (checkComponents rel)
  if rel.startsWith ":" || rel.startsWith "-" then
    throw (IO.userError s!"unsupported tracked path prefix: {rel}")
  verifyGitRoot dir expectedPrefix
  let out ← IO.Process.output {
    cmd := "git",
    args := #["-C", dir.toString, "-c", "core.quotePath=false", "ls-files", "--stage", "-z",
      "--", rel],
    stdin := .null }
  unless out.exitCode == 0 do
    throw (IO.userError s!"git ls-files failed for {rel} in {dir}: {out.stderr}")
  let paths ← parseStageRecords out.stdout
  unless paths == #[rel] do
    throw (IO.userError s!"path is not a tracked regular file: {rel}")
  ensureRegular dir rel

private def removeRegularIfExists (path : System.FilePath) : IO Unit := do
  let meta? ← try some <$> path.symlinkMetadata catch error =>
    if error matches .noFileOrDirectory .. then pure none else throw error
  if let some m := meta? then
    unless m.type == .file do
      throw (IO.userError s!"non-regular cached config entry: {path}")
    try IO.FS.removeFile path catch error =>
      if error matches .noFileOrDirectory .. then pure () else throw error

private def clearLakeConfigCache (lakeDir : System.FilePath) : IO Unit := do
  let configDir := lakeDir / "config"
  let meta? ← try some <$> configDir.symlinkMetadata catch error =>
    if error matches .noFileOrDirectory .. then pure none else throw error
  let some m := meta? | return
  unless m.type == .dir do
    throw (IO.userError s!"non-directory Lake config cache: {configDir}")
  removeRegularIfExists (configDir / "lakefile.olean")
  removeRegularIfExists (configDir / "lakefile.olean.trace")
  for entry in ← configDir.readDir do
    let entryMeta ← try some <$> entry.path.symlinkMetadata catch error =>
      if error matches .noFileOrDirectory .. then pure none else throw error
    if let some em := entryMeta then
      if em.type == .dir then
        removeRegularIfExists (entry.path / "lakefile.olean")
        removeRegularIfExists (entry.path / "lakefile.olean.trace")

def syncTrackedConfigTrace (dir : System.FilePath) (expectedPrefix : Option String)
    (stampLakeDir : System.FilePath) (extraLakeDirs : Array System.FilePath := #[]) : IO Unit := do
  verifyGitRoot dir expectedPrefix
  let out ← IO.Process.output {
    cmd := "git",
    args := #["-C", dir.toString, "-c", "core.quotePath=false", "ls-files", "--stage", "-z",
      "--", "*.lean"],
    stdin := .null }
  unless out.exitCode == 0 do
    throw (IO.userError s!"git ls-files *.lean failed in {dir}: {out.stderr}")
  if out.stdout.isEmpty then
    throw (IO.userError s!"git ls-files *.lean returned no tracked modules in {dir}")
  let desired := out.stdout.toUTF8
  let stampPath := stampLakeDir / "acorn-tracked-modules.z"
  let current? ← try some <$> IO.FS.readBinFile stampPath catch error =>
    if error matches .noFileOrDirectory .. then pure none else throw error
  unless current? == some desired do
    clearLakeConfigCache stampLakeDir
    for extra in extraLakeDirs do
      clearLakeConfigCache extra
    IO.FS.createDirAll stampLakeDir
    let tmp : System.FilePath := s!"{stampPath}.{← IO.Process.getPID}.tmp"
    try
      IO.FS.writeBinFile tmp desired
      IO.FS.rename tmp stampPath
    catch error =>
      try IO.FS.removeFile tmp catch _ => pure ()
      throw error

end AcornTrackedFiles
