import Std.Data.HashSet.Basic

namespace AcornTrackedFiles

private def stripNewline (text : String) : String :=
  (text.dropEndWhile fun c => c == '\n' || c == '\r').toString

private def isHexOid (value : String) : Bool :=
  (value.length == 40 || value.length == 64) &&
    value.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))

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

private def verifyCleanHead (repoTop : String) : IO Unit := do
  let headOut ← IO.Process.output {
    cmd := "git", args := #["--no-optional-locks", "-C", repoTop, "rev-parse", "--verify", "-q", "HEAD"],
    stdin := .null }
  unless headOut.exitCode == 0 do
    throw (IO.userError s!"HEAD commit is unavailable in {repoTop}")
  let cachedOut ← IO.Process.output {
    cmd := "git", args := #["--no-optional-locks", "-C", repoTop,
      "diff-index", "--cached", "--quiet", "--ignore-submodules=none", "HEAD", "--"],
    stdin := .null }
  unless cachedOut.exitCode == 0 do
    throw (IO.userError "staged changes differ from HEAD; commit or revert tracked changes before verdict checks")
  let wtOut ← IO.Process.output {
    cmd := "git", args := #["--no-optional-locks", "-C", repoTop,
      "-c", "core.symlinks=true", "-c", "core.fsmonitor=false",
      "diff", "--no-ext-diff", "--no-textconv", "--quiet", "--ignore-submodules=none", "HEAD", "--"],
    stdin := .null }
  unless wtOut.exitCode == 0 do
    throw (IO.userError "working-copy tracked files differ from HEAD; commit or revert tracked changes before verdict checks")
  let flagOut ← IO.Process.output {
    cmd := "git", args := #["--no-optional-locks", "-C", repoTop,
      "-c", "core.quotePath=false", "ls-files", "-v", "-z"],
    stdin := .null }
  unless flagOut.exitCode == 0 do
    throw (IO.userError s!"git ls-files -v failed in {repoTop}: {flagOut.stderr}")
  let records := (flagOut.stdout.splitOn (String.singleton (Char.ofNat 0))).filter (!·.isEmpty)
  if records.isEmpty then
    throw (IO.userError s!"git ls-files -v returned no tracked files in {repoTop}")
  for record in records do
    unless record.startsWith "H " do
      throw (IO.userError s!"tracked entry has non-clean Git index flag: {record}")

def verifyGitRoot (dir : System.FilePath) (expectedPrefix : String)
    (requireClean : Bool := true) : IO Unit := do
  let dirMeta ← dir.symlinkMetadata
  unless dirMeta.type == .dir do
    throw (IO.userError s!"expected directory for Git root: {dir}")
  let topOut ← IO.Process.output {
    cmd := "git", args := #["--no-optional-locks", "-C", dir.toString, "rev-parse", "--show-toplevel"],
    stdin := .null }
  unless topOut.exitCode == 0 do
    throw (IO.userError s!"git rev-parse --show-toplevel failed in {dir}: {topOut.stderr}")
  let prefixOut ← IO.Process.output {
    cmd := "git", args := #["--no-optional-locks", "-C", dir.toString, "rev-parse", "--show-prefix"],
    stdin := .null }
  unless prefixOut.exitCode == 0 do
    throw (IO.userError s!"git rev-parse --show-prefix failed in {dir}: {prefixOut.stderr}")
  let topStr := stripNewline topOut.stdout
  let prefixStr := stripNewline prefixOut.stdout
  unless prefixStr == expectedPrefix do
    throw (IO.userError s!"unexpected git prefix {prefixStr} in {dir}, expected {expectedPrefix}")
  let target := if prefixStr.isEmpty then System.FilePath.mk topStr
    else System.FilePath.mk topStr / (prefixStr.dropEndWhile (· == '/')).toString
  unless (← IO.FS.realPath target) == (← IO.FS.realPath dir) do
    throw (IO.userError s!"git root mismatch for {dir}")
  if requireClean then
    verifyCleanHead topStr

private def parseStageRecords (stdout : String) : IO (Array String) := do
  let records := (stdout.splitOn (String.singleton (Char.ofNat 0))).filter (!·.isEmpty)
  if records.isEmpty then
    throw (IO.userError "git ls-files returned no tracked entries")
  let mut paths := #[]
  for record in records do
    let [metaPart, path] := record.splitOn "\t"
      | throw (IO.userError s!"malformed git ls-files record: {record}")
    let [mode, oid, stage] := metaPart.splitOn " "
      | throw (IO.userError s!"malformed git ls-files metadata: {metaPart}")
    unless (mode == "100644" || mode == "100755") && stage == "0" && isHexOid oid do
      throw (IO.userError s!"unsupported tracked entry mode or stage for {path}")
    discard (checkComponents path)
    paths := paths.push path
  return paths.qsort (· < ·)

def listTracked (dir : System.FilePath) (expectedPrefix : String)
    (requireClean : Bool := true) : IO (Array String) := do
  verifyGitRoot dir expectedPrefix requireClean
  let out ← IO.Process.output {
    cmd := "git",
    args := #["--no-optional-locks", "-C", dir.toString, "-c", "core.quotePath=false",
      "ls-files", "--stage", "-z"],
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

def ensureTrackedRegular (dir : System.FilePath) (expectedPrefix : String)
    (rel : String) (requireClean : Bool := true) : IO Unit := do
  discard (checkComponents rel)
  if rel.startsWith ":" || rel.startsWith "-" then
    throw (IO.userError s!"unsupported tracked path prefix: {rel}")
  verifyGitRoot dir expectedPrefix requireClean
  let out ← IO.Process.output {
    cmd := "git",
    args := #["--no-optional-locks", "--literal-pathspecs", "-C", dir.toString,
      "-c", "core.quotePath=false", "ls-files", "--stage", "-z", "--", rel],
    stdin := .null }
  unless out.exitCode == 0 do
    throw (IO.userError s!"git ls-files failed for {rel} in {dir}: {out.stderr}")
  let paths ← parseStageRecords out.stdout
  unless paths == #[rel] do
    throw (IO.userError s!"path is not a tracked regular file: {rel}")
  ensureRegular dir rel

def runTrackedHelperStdout (repoRoot : System.FilePath) (args : Array String)
    (requireClean : Bool := true) : IO String := do
  ensureTrackedRegular repoRoot "" "scripts/tracked-files.sh" requireClean
  let helper := repoRoot / "scripts/tracked-files.sh"
  let out ← IO.Process.output { cmd := helper.toString, args, stdin := .null }
  unless out.exitCode == 0 do
    throw (IO.userError (out.stderr ++ out.stdout).trimAscii.toString)
  return out.stdout

def runTrackedHelper (repoRoot : System.FilePath) (args : Array String)
    (requireClean : Bool := true) : IO Unit :=
  discard (runTrackedHelperStdout repoRoot args requireClean)

private def byteHex (b : UInt8) : String :=
  let digits := "0123456789abcdef".toList
  let hi := digits[(b >>> 4).toNat]?.getD '0'
  let lo := digits[(b &&& 0x0f).toNat]?.getD '0'
  String.ofList [hi, lo]

private def randomHex8 : IO String := do
  let bytes ← IO.getRandomBytes 8
  let mut out := ""
  for b in bytes.data do
    out := out ++ byteHex b
  return out

def writeFileAtomicExclusive (path : System.FilePath) (text : String) : IO Unit := do
  let pid ← IO.Process.getPID
  for _ in [:16] do
    let suffix ← randomHex8
    let tmp : System.FilePath := s!"{path}.{pid}.{suffix}.tmp"
    let handle? ← try some <$> IO.FS.Handle.mk tmp .writeNew catch error =>
      if error matches .alreadyExists .. then pure none else throw error
    if let some h := handle? then
      try
        h.putStr text
        h.flush
        IO.FS.rename tmp path
      catch error =>
        try IO.FS.removeFile tmp catch _ => pure ()
        throw error
      return
  throw (IO.userError s!"unable to allocate exclusive temporary file for {path}")

end AcornTrackedFiles
