import Lean
import AcornTools.ModuleInventory
import AcornTools.TrackedFiles

namespace AcornFrameCheck

open Lean

def roundConstants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def initialHash : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

def rotateRight (word : UInt32) (count : UInt32) : UInt32 :=
  (word >>> count) ||| (word <<< (32 - count))

def padded (message : ByteArray) : ByteArray := Id.run do
  let mut out := message.push 0x80
  while out.size % 64 != 56 do
    out := out.push 0
  let bits : UInt64 := message.size.toUInt64 * 8
  for shift in [56, 48, 40, 32, 24, 16, 8, 0] do
    out := out.push (bits >>> shift.toUInt64).toUInt8
  return out

def compress (hash : Array UInt32) (data : ByteArray) (offset : Nat) : Array UInt32 := Id.run do
  let mut schedule : Array UInt32 := Array.replicate 64 0
  for index in [0:16] do
    let at' := offset + 4 * index
    schedule := schedule.set! index
      ((data[at']!.toUInt32 <<< 24) ||| (data[at' + 1]!.toUInt32 <<< 16) |||
        (data[at' + 2]!.toUInt32 <<< 8) ||| data[at' + 3]!.toUInt32)
  for index in [16:64] do
    let fifteen := schedule[index - 15]!
    let two := schedule[index - 2]!
    let small0 := rotateRight fifteen 7 ^^^ rotateRight fifteen 18 ^^^ (fifteen >>> 3)
    let small1 := rotateRight two 17 ^^^ rotateRight two 19 ^^^ (two >>> 10)
    schedule := schedule.set! index
      (schedule[index - 16]! + small0 + schedule[index - 7]! + small1)
  let mut a := hash[0]!
  let mut b := hash[1]!
  let mut c := hash[2]!
  let mut d := hash[3]!
  let mut e := hash[4]!
  let mut f := hash[5]!
  let mut g := hash[6]!
  let mut h := hash[7]!
  for index in [0:64] do
    let big1 := rotateRight e 6 ^^^ rotateRight e 11 ^^^ rotateRight e 25
    let choice := (e &&& f) ^^^ ((~~~ e) &&& g)
    let first := h + big1 + choice + roundConstants[index]! + schedule[index]!
    let big0 := rotateRight a 2 ^^^ rotateRight a 13 ^^^ rotateRight a 22
    let majority := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let second := big0 + majority
    h := g
    g := f
    f := e
    e := d + first
    d := c
    c := b
    b := a
    a := first + second
  return #[hash[0]! + a, hash[1]! + b, hash[2]! + c, hash[3]! + d, hash[4]! + e, hash[5]! + f,
    hash[6]! + g, hash[7]! + h]

def hexWord (word : UInt32) : String :=
  let digits := (Nat.toDigits 16 word.toNat)
  String.ofList (List.replicate (8 - digits.length) '0' ++ digits)

def sha256 (text : String) : String := Id.run do
  let data := padded text.toUTF8
  let mut hash := initialHash
  for block in [0:data.size / 64] do
    hash := compress hash data (64 * block)
  return String.join (hash.toList.map hexWord)

def vectorsHold : Bool :=
  sha256 "" == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" &&
    sha256 "abc" == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" &&
    sha256 "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" ==
      "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"

def ownModule (module : Name) : Bool :=
  module.getRoot == `Acorn || module.getRoot == `AcornVerif

def owned (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | some index => ownModule env.header.moduleNames[index.toNat]!
  | none => false

def named (info : ConstantInfo) : Array Name :=
  let inType := info.type.getUsedConstants
  match info with
  | .defnInfo value => inType ++ value.value.getUsedConstants
  | .opaqueInfo value => inType ++ value.value.getUsedConstants
  | .inductInfo value => inType ++ value.ctors.toArray
  | _ => inType

def declText (info : ConstantInfo) : String :=
  let kind := match info with
    | .defnInfo _ => "def"
    | .thmInfo _ => "theorem"
    | .opaqueInfo _ => "opaque"
    | .axiomInfo _ => "axiom"
    | .inductInfo _ => "inductive"
    | .ctorInfo _ => "constructor"
    | .recInfo _ => "recursor"
    | .quotInfo _ => "quotient"
  let body := match info with
    | .defnInfo value => value.value.dbgToString
    | .opaqueInfo value => value.value.dbgToString
    | .inductInfo value => toString value.ctors
    | _ => ""
  s!"{kind}\n{info.levelParams}\n{info.type.dbgToString}\n{body}"

partial def frame (env : Environment) (free stop : NameSet) (target : Name) :
    Std.HashMap Name String := Id.run do
  let mut pinned : Std.HashMap Name String := {}
  let mut seen : NameSet := {}
  let mut work : Array Name := #[target]
  while h : 0 < work.size do
    let name := work[work.size - 1]
    work := work.pop
    if seen.contains name then continue
    seen := seen.insert name
    if free.contains name || !owned env name then continue
    let some info := env.find? name | continue
    pinned := pinned.insert name (sha256 (declText info))
    unless stop.contains name do
      work := work ++ named info
  return pinned

structure Pin where
  target : Name
  home : Name
  free : Array Name := #[]
  stop : Array Name := #[]
  pins : Array (Name × String) := #[]

def Pin.text (pin : Pin) : String :=
  let sorted := pin.pins.qsort fun left right => left.1.toString < right.1.toString
  String.intercalate "\n"
    ([s!"target {pin.target}", s!"module {pin.home}"] ++
      pin.free.toList.map (s!"free {·}") ++ pin.stop.toList.map (s!"stop {·}") ++
      sorted.toList.map (fun entry => s!"pin {entry.2} {entry.1}")) ++ "\n"

def Pin.parse (text : String) : Except String Pin := do
  let mut target : Option Name := none
  let mut home : Option Name := none
  let mut pin : Pin := { target := .anonymous, home := .anonymous }
  for line in (text.splitOn "\n").filter (!·.isEmpty) do
    match line.splitOn " " with
    | ["target", name] =>
      if target.isSome then throw "two target lines"
      target := some name.toName
    | ["module", name] =>
      if home.isSome then throw "two module lines"
      home := some name.toName
    | ["free", name] => pin := { pin with free := pin.free.push name.toName }
    | ["stop", name] => pin := { pin with stop := pin.stop.push name.toName }
    | ["pin", digest, name] => pin := { pin with pins := pin.pins.push (name.toName, digest) }
    | _ => throw s!"a line that is none of the five statements: {line}"
  match target, home with
  | some found, some declaring => return { pin with target := found, home := declaring }
  | _, _ => throw "no target line or no module line"

def moduleComponents? : Name → Option (List String)
  | .anonymous => some []
  | .str parent seg => do
    if seg.isEmpty || seg == "." || seg == ".." ||
        seg.contains '/' || seg.contains ':' || seg.contains '«' || seg.contains '»' ||
        seg.contains '\n' || seg.contains '\r' || seg.contains (Char.ofNat 0) then
      none
    let rest ← moduleComponents? parent
    return rest ++ [seg]
  | .num _ _ => none

def moduleRelPath (base : System.FilePath) (parts : List String) (ext : String) :
    System.FilePath :=
  base / s!"{String.intercalate "/" parts}.{ext}"

def requestText (module : Name) : Option String :=
  let text := module.toString
  if !module.isAnonymous && (moduleComponents? module).isSome &&
      !text.toList.any (fun c => c == ':' || c == '/') &&
      text.toName == module then some text
  else none

private def stripNewline (text : String) : String :=
  (text.dropEndWhile fun c => c == '\n' || c == '\r').toString

private def isSafeComponent (value : String) : Bool :=
  !value.isEmpty && value != "." && value != ".." &&
    value.toList.all (fun c => c.isAlphanum || c == '-' || c == '_' || c == '.')

private def isHex40 (value : String) : Bool :=
  value.length == 40 && value.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))

private def symlinkMetadata? (path : System.FilePath) : IO (Option IO.FS.Metadata) :=
  try some <$> path.symlinkMetadata catch error =>
    if error matches .noFileOrDirectory .. then pure none else throw error

private def ensureRegularDir (path : System.FilePath) : IO Unit := do
  let entryMeta ← path.symlinkMetadata
  unless entryMeta.type == .dir do
    throw (IO.userError s!"non-directory path: {path}")

private def ensureNoSymlinkChain (root : System.FilePath) (parts : List String)
    (isLeafDir : Bool := false) : IO System.FilePath := do
  ensureRegularDir root
  let mut cur := root
  for part in parts.dropLast do
    if part.isEmpty || part == "." || part == ".." then
      throw (IO.userError s!"unsupported path component in {root}/{part}")
    cur := cur / part
    ensureRegularDir cur
  let some leaf := parts.getLast?
    | throw (IO.userError s!"empty relative path under {root}")
  if leaf.isEmpty || leaf == "." || leaf == ".." then
    throw (IO.userError s!"unsupported path component in {root}/{leaf}")
  cur := cur / leaf
  let leafMeta ← cur.symlinkMetadata
  let expected := if isLeafDir then IO.FS.FileType.dir else .file
  unless leafMeta.type == expected do
    throw (IO.userError s!"non-regular path: {cur}")
  return cur

private def sameRealPath (one other : System.FilePath) : IO Bool :=
  try pure ((← IO.FS.realPath one) == (← IO.FS.realPath other)) catch _ => pure false

private def hasExactRelSuffix (candidate : System.FilePath) (relStr : String) : Bool :=
  candidate.toString == relStr || candidate.toString.endsWith ("/" ++ relStr)

private def ensureRegularFileWithin (root candidate : System.FilePath) : IO System.FilePath := do
  let realRoot ← IO.FS.realPath root
  let candMeta ← candidate.symlinkMetadata
  unless candMeta.type == .file do
    throw (IO.userError s!"non-regular file: {candidate}")
  let realCand ← IO.FS.realPath candidate
  let prefixStr := realRoot.toString ++ "/"
  unless realCand.toString.startsWith prefixStr do
    throw (IO.userError s!"path {candidate} resolves outside {root}")
  let relStr := (realCand.toString.drop prefixStr.length).toString
  unless hasExactRelSuffix candidate relStr do
    throw (IO.userError s!"path {candidate} disagrees in relative spelling with {relStr}")
  let parts := relStr.splitOn "/"
  let verified ← ensureNoSymlinkChain root parts false
  unless (← IO.FS.realPath verified) == realCand do
    throw (IO.userError s!"canonical path mismatch for {candidate}")
  return realCand

private def ensureRegularUnder (baseRoot : System.FilePath) (relParts : List String)
    (candidate : System.FilePath) : IO System.FilePath := do
  let realBase ← IO.FS.realPath baseRoot
  let verified ← ensureNoSymlinkChain baseRoot relParts false
  let relStr := String.intercalate "/" relParts
  let realVerified ← IO.FS.realPath verified
  unless realVerified.toString == realBase.toString ++ "/" ++ relStr do
    throw (IO.userError s!"canonical path {realVerified} disagrees with {baseRoot}/{relStr}")
  let candMeta ← candidate.symlinkMetadata
  unless candMeta.type == .file do
    throw (IO.userError s!"non-regular file: {candidate}")
  unless hasExactRelSuffix candidate relStr do
    throw (IO.userError s!"path {candidate} disagrees with exact suffix {relStr}")
  let realCand ← IO.FS.realPath candidate
  unless realVerified == realCand do
    throw (IO.userError s!"path mismatch for {candidate}: expected {verified}")
  return realVerified

private def moduleFileParts? (parts : List String) (ext : String) : Option (List String) := do
  let leaf ← parts.getLast?
  return parts.dropLast ++ [s!"{leaf}.{ext}"]

private def ensureRegularLibArtifact (pkgDir : System.FilePath) (parts : List String)
    (ext : String) (candidate : System.FilePath) : IO System.FilePath := do
  let some fileParts := moduleFileParts? parts ext
    | throw (IO.userError s!"empty module path under {pkgDir}")
  ensureRegularUnder pkgDir ([".lake", "build", "lib", "lean"] ++ fileParts) candidate

structure LockedDep where
  dirName : String
  pkgDir : System.FilePath

structure VerifiedMod where
  pkgDir : System.FilePath
  oleanPath : System.FilePath
  isModule : Bool

structure GuardContext where
  allModules : Array Name
  deps : Array LockedDep
  sysrootLib : System.FilePath
  requireClean : Bool
  verified : IO.Ref (NameMap VerifiedMod)
  envs : IO.Ref (NameMap Environment)

private def admitSysroot : IO System.FilePath := do
  let out ← IO.Process.output {
    cmd := "lean", args := #["--print-prefix"],
    env := #[("LEAN_SYSROOT", none)], stdin := .null }
  unless out.exitCode == 0 do
    throw (IO.userError s!"failed to resolve Lean toolchain prefix: {out.stderr}")
  let expectedPrefix : System.FilePath := stripNewline out.stdout
  let sysroot ← findSysroot
  unless ← sameRealPath sysroot expectedPrefix do
    throw (IO.userError s!"Lean sysroot {sysroot} differs from toolchain prefix {expectedPrefix}")
  getLibDir sysroot

private def admitManifest (requireClean : Bool) : IO (Array LockedDep) := do
  AcornTrackedFiles.ensureTrackedRegular "." "lean/" "lean-toolchain" requireClean
  AcornTrackedFiles.ensureTrackedRegular "." "lean/" "Bootstrap.lean" requireClean
  AcornTrackedFiles.ensureTrackedRegular "." "lean/" "lakefile.lean" requireClean
  AcornTrackedFiles.ensureTrackedRegular "." "lean/" "lake-manifest.json" requireClean
  ensureRegularDir ".lake"
  ensureRegularDir ".lake/packages"
  let realLake ← IO.FS.realPath ".lake"
  let realPkgs ← IO.FS.realPath ".lake/packages"
  unless realPkgs == realLake / "packages" do
    throw (IO.userError ".lake/packages resolves outside .lake")
  if (← symlinkMetadata? ".lake/package-overrides.json").isSome then
    throw (IO.userError "unbound .lake/package-overrides.json; remove the ambient override")
  let lock ← IO.ofExcept (Json.parse (← IO.FS.readFile "lake-manifest.json"))
  let version ← IO.ofExcept (lock.getObjValAs? String "version")
  let pkgName ← IO.ofExcept (lock.getObjValAs? String "name")
  let packagesDir ← IO.ofExcept (lock.getObjValAs? String "packagesDir")
  let lakeDir ← IO.ofExcept (lock.getObjValAs? String "lakeDir")
  unless version == "1.3.0" && pkgName == "acorn" &&
      packagesDir == ".lake/packages" && lakeDir == ".lake" do
    throw (IO.userError "unsupported Lake lock layout in lake-manifest.json")
  let packages ← IO.ofExcept (lock.getObjValAs? (Array Json) "packages")
  if packages.isEmpty then
    throw (IO.userError "empty locked dependency inventory in lake-manifest.json")
  let mut seenNames : Array Name := #[]
  let mut seenDirs : Array String := #[]
  let mut deps : Array LockedDep := #[]
  for entry in packages do
    let name ← IO.ofExcept (entry.getObjValAs? String "name")
    let decoded := name.toName
    let dirName := decoded.toString (escape := false)
    let entryType ← IO.ofExcept (entry.getObjValAs? String "type")
    unless isSafeComponent dirName && !seenNames.contains decoded &&
        !seenDirs.contains dirName && entryType == "git" do
      throw (IO.userError s!"duplicate or unsupported locked dependency: {name}")
    seenNames := seenNames.push decoded
    seenDirs := seenDirs.push dirName
    let configFile ← IO.ofExcept (entry.getObjValAs? String "configFile")
    let manifestFile ← IO.ofExcept (entry.getObjValAs? String "manifestFile")
    unless isSafeComponent configFile && isSafeComponent manifestFile do
      throw (IO.userError s!"unsafe manifest filename for locked dependency {name}")
    let url ← IO.ofExcept (entry.getObjValAs? String "url")
    unless !url.isEmpty do
      throw (IO.userError s!"empty locked URL for {name}")
    let rev ← IO.ofExcept (entry.getObjValAs? String "rev")
    unless isHex40 rev do
      throw (IO.userError s!"invalid locked revision for {name}")
    let subDir ← IO.ofExcept (entry.getObjVal? "subDir")
    unless subDir == Json.null do
      throw (IO.userError s!"unsupported subDir for locked dependency {name}")
    let depDir : System.FilePath := ".lake/packages" / dirName
    ensureRegularDir depDir
    let realDep ← IO.FS.realPath depDir
    unless realDep == realPkgs / dirName do
      throw (IO.userError s!"dependency checkout {depDir} resolves outside .lake/packages")
    if let some gm ← symlinkMetadata? (depDir / ".git") then
      unless gm.type == .dir || gm.type == .file do
        throw (IO.userError s!"non-regular .git in dependency checkout: {depDir}")
      let revOut ← IO.Process.output {
        cmd := "git",
        args := #["--no-optional-locks", "-C", depDir.toString, "rev-parse", "--verify", "-q", "HEAD"],
        stdin := .null }
      unless revOut.exitCode == 0 && stripNewline revOut.stdout == rev do
        throw (IO.userError s!"dependency checkout {depDir} HEAD does not match locked revision {rev}")
    discard (ensureNoSymlinkChain depDir [configFile] false)
    discard (ensureNoSymlinkChain depDir [manifestFile] false)
    deps := deps.push { dirName, pkgDir := depDir }
  return deps

private def newGuardContext (requireClean : Bool) : IO GuardContext := do
  let sysrootLib ← admitSysroot
  let deps ← admitManifest requireClean
  let allModules ← AcornModuleInventory.allModules (requireClean := requireClean)
  let verified ← IO.mkRef ({} : NameMap VerifiedMod)
  let envs ← IO.mkRef ({} : NameMap Environment)
  return { allModules, deps, sysrootLib, requireClean, verified, envs }

private def queryLakeBatch (contextLabel : String) (specs : Array String) :
    IO (Array Json) := do
  if specs.isEmpty then return #[]
  let mut results : Array Json := #[]
  let maxSpecs := 1600
  let maxBytes := 128000
  let mut start := 0
  while start < specs.size do
    let mut stop := start
    let mut totalBytes := 0
    while stop < specs.size && stop - start < maxSpecs do
      let nextBytes := totalBytes + specs[stop]!.utf8ByteSize + 1
      if stop > start && nextBytes > maxBytes then break
      totalBytes := nextBytes
      stop := stop + 1
    let chunk := specs.extract start stop
    let output ← IO.Process.output (← AcornTrackedFiles.bootstrapProcess
      (#["query", "-J", "--no-build"] ++ chunk))
    unless output.exitCode == 0 do
      throw (IO.userError s!"{contextLabel}: Lake does not report all required modules and \
        artifacts built from the present sources (status {output.exitCode}). Lake said:\n\
        {(output.stdout ++ output.stderr).trimAscii}")
    let lines := output.stdout.splitOn "\n"
    unless lines.length == chunk.size + 1 && lines.getLast? == some "" do
      throw (IO.userError s!"{contextLabel}: Lake query answer line count mismatch \
        (expected {chunk.size}, got {lines.length - 1}). Lake said:\n{output.stdout}")
    for line in lines.dropLast do
      if line.isEmpty then
        throw (IO.userError s!"{contextLabel}: empty JSON line from Lake query")
      let parsed ← IO.ofExcept (Json.parse line)
      results := results.push parsed
    start := stop
  return results

private def requireLakeString (label : String) (json : Json) : IO String :=
  IO.ofExcept ((json.getStr?).mapError fun e => s!"{label}: malformed Lake string answer: {e}")

private def requireHeaderIsModule (label : String) (json : Json) : IO Bool :=
  IO.ofExcept ((json.getObjValAs? Bool "isModule").mapError fun e =>
    s!"{label}: malformed Lake module header: {e}")

private def parseTransImports (label : String) (json : Json) : IO (Array Name) := do
  let arr ← IO.ofExcept ((json.getArr?).mapError fun e =>
    s!"{label}: malformed Lake transImports array: {e}")
  let mut mods := #[]
  for item in arr do
    let s ← IO.ofExcept ((item.getStr?).mapError fun e =>
      s!"{label}: malformed Lake transImports entry: {e}")
    let mod := s.toName
    unless requestText mod == some s do
      throw (IO.userError s!"{label}: unsupported transitive import name from Lake: {s}")
    mods := mods.push mod
  return mods

private def isRegularFile (path : System.FilePath) : IO Bool := do
  return (← symlinkMetadata? path).any (·.type == .file)

private def verifyRootFiles (mod : Name) (text : String)
    (sourcePath answeredPath : System.FilePath) : IO System.FilePath := do
  let some parts := moduleComponents? mod
    | throw (IO.userError s!"module {text}: invalid module path components")
  let some leanParts := moduleFileParts? parts "lean"
    | throw (IO.userError s!"module {text}: empty module path components")
  let listed := moduleRelPath "." parts "lean"
  unless ← isRegularFile sourcePath do
    throw (IO.userError s!"module {text}: Lake reads missing or non-regular source at {sourcePath}")
  let realVerifiedSrc ← try
    ensureRegularUnder "." leanParts sourcePath
  catch error =>
    throw (IO.userError s!"module {text}: not read, since Lake reads its source at {sourcePath}, \
      which does not match tree file {listed} ({error})")
  discard (ensureRegularFileWithin "." listed)
  unless realVerifiedSrc == (← IO.FS.realPath listed) do
    throw (IO.userError s!"module {text}: not read, since Lake reads its source at {sourcePath}, \
      which is not the tree's file {listed}")
  let found ← try findOLean mod catch error =>
    throw (IO.userError s!"module {text}: not read, since Lean finds no compiled file for it: \
      {error}")
  let realAnswered ← try
    ensureRegularLibArtifact "." parts "olean" answeredPath
  catch error =>
    throw (IO.userError s!"module {text}: compiled file {answeredPath} is invalid: {error}")
  unless ← isRegularFile found do
    throw (IO.userError s!"module {text}: Lean finds missing or non-regular compiled file at {found}")
  unless ← sameRealPath found answeredPath do
    throw (IO.userError s!"module {text}: not read, since Lean finds its compiled file at \
      {found} and Lake answered for {answeredPath}, which is not that file")
  let some oleanParts := moduleFileParts? parts "olean"
    | throw (IO.userError s!"module {text}: empty module path components")
  unless hasExactRelSuffix found (String.intercalate "/" ([".lake", "build", "lib", "lean"] ++ oleanParts)) do
    throw (IO.userError s!"module {text}: Lean resolved compiled file {found} with mismatched suffix")
  return realAnswered

private def verifyDepFiles (deps : Array LockedDep) (mod : Name) (text : String)
    (sourcePath answeredPath : System.FilePath) : IO (System.FilePath × System.FilePath) := do
  let some parts := moduleComponents? mod
    | throw (IO.userError s!"module {text}: invalid dependency module path components")
  let mut shadowCur : System.FilePath := ".lake/build/lib/lean"
  for part in parts.dropLast do
    shadowCur := shadowCur / part
    if let some metaData ← symlinkMetadata? shadowCur then
      unless metaData.type == .dir do
        throw (IO.userError s!"module {text}: non-directory root entry shadows dependency at {shadowCur}")
  let rootShadow := moduleRelPath ".lake/build/lib/lean" parts "olean"
  if (← symlinkMetadata? rootShadow).isSome then
    throw (IO.userError s!"module {text}: non-inventoried root artifact shadows dependency at {rootShadow}")
  let found ← try findOLean mod catch error =>
    throw (IO.userError s!"module {text}: not read, since Lean finds no compiled file for it: \
      {error}")
  unless ← isRegularFile found do
    throw (IO.userError s!"module {text}: Lean finds missing or non-regular compiled file at {found}")
  let mut matched? : Option (System.FilePath × System.FilePath) := none
  for dep in deps do
    let okSrc ← try
      discard (ensureRegularFileWithin dep.pkgDir sourcePath)
      pure true
    catch _ => pure false
    if okSrc then
      let okOLean ← try
        let realAns ← ensureRegularLibArtifact dep.pkgDir parts "olean" answeredPath
        pure (some (dep.pkgDir, realAns))
      catch _ => pure none
      if let some pair := okOLean then
        matched? := some pair
        break
  let some (matchedPkgDir, realAnswered) := matched?
    | throw (IO.userError s!"module {text}: not read, since Lake resolved source {sourcePath} or \
        compiled file {answeredPath} outside the locked dependency checkouts")
  unless ← sameRealPath found answeredPath do
    throw (IO.userError s!"module {text}: not read, since Lean finds its compiled file at \
      {found} and Lake answered for {answeredPath}, which is not that file")
  let some oleanParts := moduleFileParts? parts "olean"
    | throw (IO.userError s!"module {text}: empty dependency module path components")
  unless hasExactRelSuffix found (String.intercalate "/" ([".lake", "build", "lib", "lean"] ++ oleanParts)) do
    throw (IO.userError s!"module {text}: Lean resolved compiled file {found} with mismatched suffix")
  return (matchedPkgDir, realAnswered)

private def verifyCompanionArtifacts (pkgDir : System.FilePath)
    (mod : Name) (text : String) (answers : Array System.FilePath) : IO Unit := do
  let some parts := moduleComponents? mod
    | throw (IO.userError s!"module {text}: invalid module path components")
  let exts := #["olean.server", "olean.private", "ir.sig", "ir"]
  unless answers.size == exts.size do
    throw (IO.userError s!"module {text}: incomplete companion artifact answer count")
  let found ← try findOLean mod catch error =>
    throw (IO.userError s!"module {text}: Lean finds no compiled file for companion check: {error}")
  for h : i in [:exts.size] do
    let ext := exts[i]
    let answered := answers[i]!
    let realExpected ← try
      ensureRegularLibArtifact pkgDir parts ext answered
    catch error =>
      throw (IO.userError s!"module {text}: companion artifact {answered} is invalid: {error}")
    let sibling := found.withExtension ext
    unless ← isRegularFile sibling do
      throw (IO.userError s!"module {text}: missing or non-regular companion artifact {sibling}")
    let some sibParts := moduleFileParts? parts ext
      | throw (IO.userError s!"module {text}: empty module path components")
    let sibSuffix := String.intercalate "/" ([".lake", "build", "lib", "lean"] ++ sibParts)
    unless hasExactRelSuffix sibling sibSuffix &&
        (← sameRealPath sibling answered) && (← sameRealPath sibling realExpected) do
      throw (IO.userError s!"module {text}: companion artifact {sibling} differs from Lake's {answered}")

private def verifyClosure (ctx : GuardContext) (module : Name) : IO Unit := do
  unless ctx.allModules.contains module do
    throw (IO.userError s!"module {module}: not read, since the tree holds no source file of \
      exactly this name among the package's Lean sources")
  let some text := requestText module
    | throw (IO.userError s!"module {module}: not read, since Lake cannot be asked about this \
        name (it is empty, holds a colon or a slash, or does not read back from its printed \
        text)")
  let rootQuery := #[s!"@/+{text}:lean", s!"@/+{text}:olean",
    s!"@/+{text}:header", s!"@/+{text}:transImports"]
  let rootAnswers ← queryLakeBatch s!"module {text}" rootQuery
  let #[leanJson, oleanJson, headerJson, transJson] := rootAnswers
    | throw (IO.userError s!"module {text}: unexpected Lake query root response count")
  let rootSource ← requireLakeString s!"module {text}" leanJson
  let rootOLeanAns ← requireLakeString s!"module {text}" oleanJson
  let rootIsModule ← requireHeaderIsModule s!"module {text}" headerJson
  let transImports ← parseTransImports s!"module {text}" transJson
  let realRootOLean ← verifyRootFiles module text rootSource rootOLeanAns
  ctx.verified.modify (·.insert module { pkgDir := ".", oleanPath := realRootOLean, isModule := rootIsModule })

  let cache ← ctx.verified.get
  let mut seen : NameSet := ({} : NameSet).insert module
  let mut pending : Array (Name × String × Bool) := #[]
  for imp in transImports do
    if seen.contains imp then continue
    seen := seen.insert imp
    if cache.contains imp then continue
    let some impText := requestText imp
      | throw (IO.userError s!"module {text}: invalid transitive import {imp}")
    let isRoot := ctx.allModules.contains imp
    pending := pending.push (imp, impText, isRoot)

  let mut querySpecs : Array String := #[]
  for (_, impText, isRoot) in pending do
    let pfx := if isRoot then "@/+" else "+"
    querySpecs := querySpecs.push s!"{pfx}{impText}:lean"
    querySpecs := querySpecs.push s!"{pfx}{impText}:olean"
    querySpecs := querySpecs.push s!"{pfx}{impText}:header"
  let depAnswers ← queryLakeBatch s!"module {text} imports" querySpecs
  let mut moduleArtifactsCheck : Array (Name × String × Bool × System.FilePath) := #[]
  if rootIsModule then
    moduleArtifactsCheck := moduleArtifactsCheck.push (module, text, true, ".")
  for h : i in [:pending.size] do
    let (imp, impText, isRoot) := pending[i]
    let idx := 3 * i
    let impLean ← requireLakeString s!"module {impText}" depAnswers[idx]!
    let impOLean ← requireLakeString s!"module {impText}" depAnswers[idx + 1]!
    let impIsModule ← requireHeaderIsModule s!"module {impText}" depAnswers[idx + 2]!
    let (impPkgDir, realImpOLean) ← if isRoot then
      pure (System.FilePath.mk ".", ← verifyRootFiles imp impText impLean impOLean)
    else
      verifyDepFiles ctx.deps imp impText impLean impOLean
    ctx.verified.modify (·.insert imp { pkgDir := impPkgDir, oleanPath := realImpOLean, isModule := impIsModule })
    if impIsModule then
      moduleArtifactsCheck := moduleArtifactsCheck.push (imp, impText, isRoot, impPkgDir)

  if !moduleArtifactsCheck.isEmpty then
    let mut artSpecs : Array String := #[]
    for (_, mText, isRoot, _) in moduleArtifactsCheck do
      let pfx := if isRoot then "@/+" else "+"
      artSpecs := artSpecs.push s!"{pfx}{mText}:olean.server"
      artSpecs := artSpecs.push s!"{pfx}{mText}:olean.private"
      artSpecs := artSpecs.push s!"{pfx}{mText}:ir.sig"
      artSpecs := artSpecs.push s!"{pfx}{mText}:ir"
    let artAnswers ← queryLakeBatch s!"module {text} module artifacts" artSpecs
    for h : i in [:moduleArtifactsCheck.size] do
      let (mod, mText, _, impPkgDir) := moduleArtifactsCheck[i]
      let idx := 4 * i
      let sAns ← requireLakeString s!"module {mText}" artAnswers[idx]!
      let pAns ← requireLakeString s!"module {mText}" artAnswers[idx + 1]!
      let isAns ← requireLakeString s!"module {mText}" artAnswers[idx + 2]!
      let iAns ← requireLakeString s!"module {mText}" artAnswers[idx + 3]!
      verifyCompanionArtifacts impPkgDir mod mText #[sAns, pAns, isAns, iAns]

private def isToolchainPrefix (mod : Name) : Bool :=
  #[`Init, `Std, `Lean, `Lake].any (·.isPrefixOf mod)

private def verifyLoadedEnv (ctx : GuardContext) (root : Name) (env : Environment) : IO Unit := do
  unless env.header.modules.size == env.header.moduleData.size do
    throw (IO.userError s!"module {root}: module inventory and metadata differ")
  unless (env.getModuleIdx? root).isSome do
    throw (IO.userError s!"module {root}: compiled module did not enter the environment")
  let verified ← ctx.verified.get
  for h : i in [:env.header.modules.size] do
    let mod := env.header.modules[i].module
    let data := env.header.moduleData[i]!
    let some parts := moduleComponents? mod
      | throw (IO.userError s!"module {root}: invalid loaded module name {mod}")
    if let some info := verified.find? mod then
      unless data.isModule == info.isModule do
        throw (IO.userError s!"module {mod}: loaded module-ness disagrees with source header")
      let found ← try findOLean mod catch error =>
        throw (IO.userError s!"module {mod}: Lean finds no compiled file after import: {error}")
      let realLoaded ← try
        ensureRegularLibArtifact info.pkgDir parts "olean" found
      catch error =>
        throw (IO.userError s!"module {mod}: loaded artifact {found} is invalid ({error})")
      unless realLoaded == info.oleanPath do
        throw (IO.userError s!"module {mod}: loaded artifact {found} differs from verified {info.oleanPath}")
      if data.isModule then
        for ext in #["olean.server", "olean.private", "ir.sig", "ir"] do
          let sib := found.withExtension ext
          discard <| try
            ensureRegularLibArtifact info.pkgDir parts ext sib
          catch error =>
            throw (IO.userError s!"module {mod}: companion artifact {sib} is invalid ({error})")
    else
      unless isToolchainPrefix mod && !ctx.allModules.contains mod do
        throw (IO.userError s!"module {root}: loaded unverified module {mod}")
      let expected := moduleRelPath ctx.sysrootLib parts "olean"
      let found ← try findOLean mod catch error =>
        throw (IO.userError s!"module {mod}: Lean finds no toolchain compiled file: {error}")
      let some oleanParts := moduleFileParts? parts "olean"
        | throw (IO.userError s!"module {mod}: invalid toolchain module path")
      let relOlean := String.intercalate "/" oleanParts
      unless (← isRegularFile found) && (← isRegularFile expected) &&
          hasExactRelSuffix found relOlean && (← sameRealPath found expected) do
        throw (IO.userError s!"module {mod}: toolchain artifact {found} differs from sysroot {expected}")
      if data.isModule then
        for ext in #["olean.server", "olean.private", "ir.sig", "ir"] do
          let sib := found.withExtension ext
          let expSib := moduleRelPath ctx.sysrootLib parts ext
          let some sibParts := moduleFileParts? parts ext
            | throw (IO.userError s!"module {mod}: invalid toolchain companion path")
          let relSib := String.intercalate "/" sibParts
          unless (← isRegularFile sib) && (← isRegularFile expSib) &&
              hasExactRelSuffix sib relSib && (← sameRealPath sib expSib) do
            throw (IO.userError s!"module {mod}: toolchain companion artifact {sib} differs from {expSib}")

def current (module : Name) (requireClean : Bool := true) : IO Unit := do
  let ctx ← newGuardContext requireClean
  verifyClosure ctx module

private def importedWithContext (ctx : GuardContext) (module : Name) : IO Environment := do
  if let some env := (← ctx.envs.get).find? module then
    return env
  verifyClosure ctx module
  let env ← importModules #[{ module }] {}
  verifyLoadedEnv ctx module env
  ctx.envs.modify (·.insert module env)
  return env

def imported (module : Name) (requireClean : Bool := true) : IO Environment := do
  let ctx ← newGuardContext requireClean
  importedWithContext ctx module

def computedWithContext (ctx : GuardContext) (pin : Pin) : IO (Std.HashMap Name String) := do
  let env ← importedWithContext ctx pin.home
  unless (env.find? pin.target).isSome do
    throw (IO.userError s!"{pin.home} declares no {pin.target}")
  return frame env (pin.free.foldl (·.insert ·) {}) (pin.stop.foldl (·.insert ·) {}) pin.target

def computed (pin : Pin) (requireClean : Bool := true) : IO (Std.HashMap Name String) := do
  let ctx ← newGuardContext requireClean
  computedWithContext ctx pin

def verify (file : System.FilePath) (ctx? : Option GuardContext := none) : IO Bool := do
  let pin ← IO.ofExcept ((Pin.parse (← IO.FS.readFile file)).mapError
    fun error => IO.userError s!"{file}: {error}")
  let now ← match ctx? with
    | some ctx => computedWithContext ctx pin
    | none => computed pin
  let mut same := true
  let mut pinned : NameSet := {}
  for (name, digest) in pin.pins do
    pinned := pinned.insert name
    match now[name]? with
    | none =>
      same := false
      IO.println s!"frame: {pin.target}: {name} is pinned and no longer part of the frame"
    | some current =>
      unless current == digest do
        same := false
        IO.println s!"frame: {pin.target}: {name} has changed"
  for (name, _) in now.toArray.qsort (fun left right => left.1.toString < right.1.toString) do
    unless pinned.contains name do
      same := false
      IO.println s!"frame: {pin.target}: {name} is part of the frame and not pinned"
  let verdict := if same then "unchanged" else "CHANGED"
  IO.println s!"frame: {pin.target}: {pin.pins.size} declarations pinned by {file}, \
    {now.size} in the frame, {verdict}"
  return same

def pinFiles : IO (Array System.FilePath) := do
  let prefixPath := "AcornVerif/Targets/"
  let tracked ← AcornTrackedFiles.listTracked "." "lean/"
  let mut sawTarget := false
  let mut files : Array System.FilePath := #[]
  for rel in tracked do
    if rel.startsWith prefixPath then
      sawTarget := true
      let name := (rel.drop prefixPath.length).toString
      if name.isEmpty || name.contains '/' then
        throw (IO.userError s!"AcornVerif/Targets/{name} is neither a regular file ending in .lean \
          nor a regular file ending in .frame")
      if name.endsWith ".frame" then
        files := files.push ("AcornVerif" / "Targets" / name)
      else unless name.endsWith ".lean" do
        throw (IO.userError s!"AcornVerif/Targets/{name} is neither a regular file ending in .lean \
          nor a regular file ending in .frame")
  unless sawTarget do
    throw (IO.userError "no tracked files under AcornVerif/Targets")
  return files.qsort (·.toString < ·.toString)

def namesAfter (keyword : String) : List String → Array Name
  | key :: name :: rest =>
    (if key == keyword then #[name.toName] else #[]) ++ namesAfter keyword rest
  | _ => #[]

def run (args : List String) : IO UInt32 := do
  unless vectorsHold do
    IO.eprintln "frame-check: this program's SHA-256 does not meet its test vectors"
    return 1
  try
    AcornTrackedFiles.admitLeanToolchain
    initSearchPath (← findSysroot)
    match args with
    | [] =>
      let files ← pinFiles
      if files.isEmpty then
        IO.println "frame: no pin file under AcornVerif/Targets, so no target's frame is pinned"
        return 0
      let ctx ← newGuardContext true
      let mut same := true
      for file in files do
        unless ← verify file (some ctx) do same := false
      if same then
        IO.println s!"frame: every pinned frame is unchanged ({files.size} pin files)"
        return 0
      IO.println "frame: a pinned frame has changed"
      return 1
    | "print" :: declaring :: target :: rest =>
      unless rest.length % 2 == 0 && rest.zipIdx.all (fun (word, index) =>
          index % 2 == 1 || word == "free" || word == "stop") do
        IO.eprintln "usage: frame-check print <module> <target> [free <name>]... [stop <name>]..."
        return 2
      let pin : Pin :=
        ⟨target.toName, declaring.toName, namesAfter "free" rest, namesAfter "stop" rest, #[]⟩
      let now ← computed pin (requireClean := false)
      let filled : Pin := ⟨pin.target, pin.home, pin.free, pin.stop, now.toArray⟩
      IO.print filled.text
      return 0
    | _ =>
      IO.eprintln "usage: frame-check [print <module> <target> [free <name>]... [stop <name>]...]"
      return 2
  catch error =>
    IO.eprintln s!"frame-check: {error}"
    return 1

end AcornFrameCheck

def main (args : List String) : IO UInt32 :=
  AcornFrameCheck.run args
