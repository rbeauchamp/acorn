/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Lean
import AcornTools.ModuleInventory

/-! # `frame-check` executable

A target is a statement a mission is to prove, frozen under `lean/AcornVerif/Targets/`. Its text
is frozen with its file. Its meaning is not: the statement reads definitions elsewhere, and a
change to one of them changes what the statement says while its file stays the same. This
program lets a target pin those definitions, and the merge gate runs it on the finished build.

**The frame of a target.** Start from the target's constant and follow constants: a
definition's type and value, a theorem's or an axiom's type, an inductive type's type and
constructors, a constructor's or a recursor's type. Three kinds of name bound the walk.

- A *free* name is not followed and not part of the frame: a submission may change it.
- A *stop* name is part of the frame, and what it names is not followed.
- A name outside the project's own modules (`Acorn`, `AcornVerif`) is not followed and not part
  of the frame. The dependencies' commits are pinned by Lake's manifest, which this program does
  not read.

**A pin file** is a file `<name>.frame` under `lean/AcornVerif/Targets/`, so only a merge the
owner makes can add or change one. It names the target, its module, the free names, the stop
names, and for each declaration of the frame the SHA-256 digest of its printed kind, universe
parameters, type and value (`declText`). Lines are `target`, `module`, `free`, `stop` and `pin`
followed by their words; an empty line is skipped, and no other line is admitted.

**The check** (no argument). It lists `lean/AcornVerif/Targets/` and admits two kinds of entry:
a regular file whose name ends in `.lean` and a regular file whose name ends in `.frame`, which
is a pin file. Any other entry, a subdirectory or a symbolic link included, fails the check and
is named, so a pin file that is misplaced or misnamed is refused and not passed over. For each
pin file it imports the module, computes the frame and compares it with the pinned one as a set
of names with digests. A declaration pinned and no longer reached, reached and not pinned, or
with another digest fails the check, and each is printed. With no pin file it says so and
passes: a target without a pin file is not pinned.

**Printing a pin file** (`print <module> <target> [free <name>]... [stop <name>]...`) writes
the pin file's text for those names to standard output.

**Compiled modules and their sources.** The declarations are read from compiled modules, never
from sources, and running this program builds the program and no module it reads. So before it
imports a module, for the check and for printing alike, it requires four things (`current`),
and builds nothing itself. First, the module is, under exactly its name, one of the package's
Lean sources: a member of the inventory of regular source files that verification's build
requests from (`AcornModuleInventory.allModules`). Then Lake, asked about the root package
alone, reports that module built from the present sources and names the source file it read
and its compiled file. Next, that source file is the inventoried file. Last, the compiled file
Lean finds for the module is the file Lake named. A module that has no source file of exactly
its name in the tree, a name that differs from a source's only in the case of its letters
included, a module the root package does not hold, a module that is out of date or imports one
that is, a module whose source Lake reads from another place, and a module whose compiled file
Lean finds elsewhere are each refused by name, with status 1. So, under what `current` lists
as trusted, a compiled file left by an earlier build is not read in place of the tree's source.

Some refusals follow that are of no module a pin can usefully name. A module of a dependency
is no source of this package: no dependency imports the project, so the environment of such a
module declares nothing in `Acorn` or `AcornVerif` and its frame is empty. A source placed in
the tree under a dependency's module name is in the inventory, and is a module of the root
package only if one of its libraries holds it; otherwise Lake, asked about the root package
alone, does not know it. A module of the documentation package in `site/` is no source of this
package either, and its compiled files are not on this program's search path. And an entry
below the package directory that is neither a directory nor a regular file, the build and
dependency directories apart, makes the inventory fail and this program with it, as it fails
verification.

What a pass means: every declaration the walk reaches prints to the text it printed when the
file was made, read from compiled modules that Lake reports built from the sources present when
the program ran. It does not say what those declarations mean, that the free names were well
chosen, or that the dependencies are unchanged. The digest is a detector of change. It is taken
with this file's own SHA-256, which each run checks against three published test vectors before
it reads anything. The vectors show that the empty message, a message of one block and a
message of two blocks digest as published, and no more: they do not show that an implementation
meeting them is SHA-256, or that it detects every change.
-/

namespace AcornFrameCheck

open Lean

/-! ## SHA-256 (FIPS 180-4) -/

/-- The round constants. -/
def roundConstants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The initial hash value. -/
def initialHash : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- Rotate a word right. -/
def rotateRight (word : UInt32) (count : UInt32) : UInt32 :=
  (word >>> count) ||| (word <<< (32 - count))

/-- The message with its padding: a one bit, zero bits, and the bit length as 64 bits. -/
def padded (message : ByteArray) : ByteArray := Id.run do
  let mut out := message.push 0x80
  while out.size % 64 != 56 do
    out := out.push 0
  let bits : UInt64 := message.size.toUInt64 * 8
  for shift in [56, 48, 40, 32, 24, 16, 8, 0] do
    out := out.push (bits >>> shift.toUInt64).toUInt8
  return out

/-- One block's compression of the hash value. -/
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

/-- A word as eight lower-case hexadecimal digits. -/
def hexWord (word : UInt32) : String :=
  let digits := (Nat.toDigits 16 word.toNat)
  String.ofList (List.replicate (8 - digits.length) '0' ++ digits)

/-- The SHA-256 digest of a text's UTF-8 bytes, as 64 hexadecimal digits. -/
def sha256 (text : String) : String := Id.run do
  let data := padded text.toUTF8
  let mut hash := initialHash
  for block in [0:data.size / 64] do
    hash := compress hash data (64 * block)
  return String.join (hash.toList.map hexWord)

/-- The three published test vectors this file's SHA-256 must meet before it is used: the empty
message, `abc`, which pads to one block, and a message of 56 bytes, which pads to two (FIPS
180-4, and NIST's example values). -/
def vectorsHold : Bool :=
  sha256 "" == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" &&
    sha256 "abc" == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" &&
    sha256 "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" ==
      "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"

/-! ## The frame -/

/-- Whether a module is one of the project's own. -/
def ownModule (module : Name) : Bool :=
  module.getRoot == `Acorn || module.getRoot == `AcornVerif

/-- Whether a constant is declared in one of the project's own modules. -/
def owned (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | some index => ownModule env.header.moduleNames[index.toNat]!
  | none => false

/-- The constants a declaration names where the walk follows it: its type, and a definition's
value or an inductive type's constructors. A theorem's proof is not followed. -/
def named (info : ConstantInfo) : Array Name :=
  let inType := info.type.getUsedConstants
  match info with
  | .defnInfo value => inType ++ value.value.getUsedConstants
  | .opaqueInfo value => inType ++ value.value.getUsedConstants
  | .inductInfo value => inType ++ value.ctors.toArray
  | _ => inType

/-- The printed text of a declaration that its digest is taken of: its kind, its universe
parameters, its type, and a definition's value or an inductive type's constructors. -/
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

/-- The frame of a target: every owned constant the walk reaches, with its digest. A free name
is left out and not followed; a stop name is kept and not followed. -/
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

/-! ## Pin files -/

/-- A pin file's content. -/
structure Pin where
  /-- The target whose frame is pinned. -/
  target : Name
  /-- The module that declares the target. -/
  home : Name
  /-- Names a submission may change: left out of the frame and not followed. -/
  free : Array Name := #[]
  /-- Names kept in the frame and not followed. -/
  stop : Array Name := #[]
  /-- The frame: each declaration with its digest. -/
  pins : Array (Name × String) := #[]

/-- A pin file's text, one statement a line, the declarations in the order of their names. -/
def Pin.text (pin : Pin) : String :=
  let sorted := pin.pins.qsort fun left right => left.1.toString < right.1.toString
  String.intercalate "\n"
    ([s!"target {pin.target}", s!"module {pin.home}"] ++
      pin.free.toList.map (s!"free {·}") ++ pin.stop.toList.map (s!"stop {·}") ++
      sorted.toList.map (fun entry => s!"pin {entry.2} {entry.1}")) ++ "\n"

/-- Read a pin file's text. Every line must be one of the five statements; a file without
exactly one target and one module is refused. -/
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

/-! ## Compiled modules and their sources -/

/-- The text by which Lake is asked about `module`, or `none` when Lake would not read that
text back as `module`. The requests are `@/+<text>:lean` and `@/+<text>:olean`. Lake cuts a
request at `:`, takes what
follows `@` as explicit, cuts that at `/` into a package, the root package when the text before
`/` is empty, and a target, and reads what follows the `+` of a module target with
`String.toName` (`parseTargetSpec`, `resolveTargetBaseSpec`, `resolveTargetLikeSpec` and
`parsePackageSpec`, Lake of Lean v4.36.0, Lake/CLI/Build.lean). So the printed name is returned
only when it holds neither `:` nor `/` and `String.toName` reads `module` back from it, and
never for the anonymous name: the module Lake answers for is then the root package's module of
the name this program imports. -/
def requestText (module : Name) : Option String :=
  let text := module.toString
  if !module.isAnonymous && !text.toList.any (fun c => c == ':' || c == '/') &&
      text.toName == module then some text
  else none

/-- Refuse `module` unless the tree holds a source file of exactly that name, Lake reports the
root package's module of that name current with the sources, the source file Lake read is that
file of the tree, and the compiled file Lean finds for the module is the one Lake answered for.

The name is first sought in `AcornModuleInventory.allModules`, the Lean sources below the
package directory named as the directory lists them, from which verification's build takes the
modules it requests; Lake is asked only about a member. A file system that takes two spellings
for one file opens a source under a name the tree does not hold, and Lake then answers for that
name; the inventory does not hold it.

Lake is then asked, through the bootstrap as every build of the gate is, for the source file
and the compiled file of that module of the root package, with `--no-build`, under which Lake
builds nothing (`lake query`, which prints one line for each request it answers, in the order
of the requests: `query` in Lake/CLI/Main.lean, `parseTargetSpecs` and `querySpecs` in
Lake/CLI/Build.lean, `Job.collectArray` in Lake/Build/Job/Monad.lean).
The inventory holds every Lean source below the package directory, a source under a
dependency's module name included; asked about the workspace, Lake would answer such a name for
the dependency's module, so it is asked about the root package.

Lake reads the module's source file, so a module without one fails there, and a module that the
root package does not hold is unknown to it. Into the module's trace it mixes, with other
inputs, the text of that source, the options, the toolchain and the compiled files of the
workspace's modules it imports, each of which it answers for in the same way first. It takes the
module as current only when the trace it recorded for the compiled files has that trace's hash
and the files, or the archive it restores them from, exist. It exits 0 only when the module and
every module of the workspace it imports are current, and 3 when one needs a build
(`Module.recFetchInput`, `fetchImportInfo`, `Module.recFetchPreSetup`, `Module.buildLean`,
`Module.recBuildElabArts` and `Module.oleanFacetConfig` in Lake/Build/Module.lean,
`buildAction` in Lake/Build/Common.lean and `finalizeBuild` in Lake/Build/Run.lean,
Lake of Lean v4.36.0). Every status but 0, the
bootstrap's own refusals included, is refused, with the module, the status and what Lake said,
and so is an answer that is not exactly two lines, each holding a path and ending in a line
end, with nothing before, between or after them.

The source file Lake names must be the inventoried file: the file that Lean's own mapping of a
module name to a path gives below the package directory (`Lean.modToFilePath`), which is the
file the inventory listed under that name. Lake takes a module's source from the source
directory its configuration gives the library (`Module.leanFile`, Lake/Config/Module.lean), so
a configuration that points a library elsewhere would have Lake answer for a file the tree does
not hold. Last, the file `Lean.findOLean` gives for the module, which is the file
`importModules` reads, must be the compiled file Lake named. Each pair is compared as real
paths, so that a symbolic link does not make two files look like one or one like two, and a
path that cannot be resolved is refused as well.

A name for which `requestText` gives nothing is refused before Lake is asked. Trusted, and not
checked here: that Lake's recorded traces are right and that nothing but Lake has written the
compiled files since; that the tree does not change while this program runs; and that Lean's
search path, which the bootstrap's `lake exe` sets with the workspace's own library directories
first, finds the modules that `module` imports where Lake answered for them, since only the
file of `module` itself is compared. -/
def current (module : Name) : IO Unit := do
  unless (← AcornModuleInventory.allModules).contains module do
    throw (IO.userError s!"module {module}: not read, since the tree holds no source file of \
      exactly this name among the package's Lean sources")
  let some text := requestText module
    | throw (IO.userError s!"module {module}: not read, since Lake cannot be asked about this \
        name (it is empty, holds a colon or a slash, or does not read back from its printed \
        text)")
  let output ← IO.Process.output {
    cmd := "lean", args := #["-DwarningAsError=true", "-DautoImplicit=false", "--run",
      "Bootstrap.lean", "query", "--no-build", "@/+" ++ text ++ ":lean",
      "@/+" ++ text ++ ":olean"], stdin := .null }
  unless output.exitCode == 0 do
    throw (IO.userError s!"module {text}: not read, since Lake does not report the root \
      package's module of this name built from the present sources (status \
      {output.exitCode}). Lake said:\n{(output.stdout ++ output.stderr).trimAscii}")
  let unread := IO.userError s!"module {text}: not read, since Lake's answer is not exactly \
    two lines naming its source file and its compiled file. Lake said:\n{output.stdout}"
  let [source, answered, ""] := output.stdout.splitOn "\n" | throw unread
  if source.isEmpty || answered.isEmpty then throw unread
  let sameFile (one other : System.FilePath) : IO Bool :=
    try pure ((← IO.FS.realPath one) == (← IO.FS.realPath other)) catch _ => pure false
  let listed := modToFilePath "." module "lean"
  unless ← sameFile source listed do
    throw (IO.userError s!"module {text}: not read, since Lake reads its source at {source}, \
      which is not the tree's file {listed}")
  let found ← try findOLean module catch error =>
    throw (IO.userError s!"module {text}: not read, since Lean finds no compiled file for it: \
      {error}")
  unless ← sameFile found answered do
    throw (IO.userError s!"module {text}: not read, since Lean finds its compiled file at \
      {found} and Lake answered for {answered}, which is not that file")

/-- The environment of a compiled module, read only once `current` has admitted the module.
Every environment this program reads comes from here. -/
def imported (module : Name) : IO Environment := do
  current module
  importModules #[{ module }] {}

/-- The frame of a pin's target, in the environment of its module. A module that `current`
refuses and an unknown target are refused. -/
def computed (pin : Pin) : IO (Std.HashMap Name String) := do
  let env ← imported pin.home
  unless (env.find? pin.target).isSome do
    throw (IO.userError s!"{pin.home} declares no {pin.target}")
  return frame env (pin.free.foldl (·.insert ·) {}) (pin.stop.foldl (·.insert ·) {}) pin.target

/-- Compare a pin file with the frame the build has. Prints each difference and returns whether
there is none. -/
def verify (file : System.FilePath) : IO Bool := do
  let pin ← IO.ofExcept ((Pin.parse (← IO.FS.readFile file)).mapError
    fun error => IO.userError s!"{file}: {error}")
  let now ← computed pin
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

/-- The pin files: the regular files ending in `.frame` in `AcornVerif/Targets`, the directory
of the package that only the owner's merges change. The directory admits those and regular
files ending in `.lean`; any other entry is refused by name. -/
def pinFiles : IO (Array System.FilePath) := do
  let directory : System.FilePath := "AcornVerif" / "Targets"
  let mut files : Array System.FilePath := #[]
  for entry in ← directory.readDir do
    let regular := (← entry.path.symlinkMetadata).type == .file
    if regular && entry.fileName.endsWith ".frame" then
      files := files.push entry.path
    else unless regular && entry.fileName.endsWith ".lean" do
      throw (IO.userError s!"{entry.path} is neither a regular file ending in .lean nor a \
        regular file ending in .frame")
  return files.qsort (·.toString < ·.toString)

/-- The names that follow a keyword in the arguments of `print`. -/
def namesAfter (keyword : String) : List String → Array Name
  | key :: name :: rest =>
    (if key == keyword then #[name.toName] else #[]) ++ namesAfter keyword rest
  | _ => #[]

/-- Check every pin file against the finished build, or print a pin file. -/
def run (args : List String) : IO UInt32 := do
  unless vectorsHold do
    IO.eprintln "frame-check: this program's SHA-256 does not meet its test vectors"
    return 1
  try
    initSearchPath (← findSysroot)
    match args with
    | [] =>
      let files ← pinFiles
      if files.isEmpty then
        IO.println "frame: no pin file under AcornVerif/Targets, so no target's frame is pinned"
        return 0
      let mut same := true
      for file in files do
        unless ← verify file do same := false
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
      let now ← computed pin
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

/-- Check every pin file against the finished build, or print a pin file. -/
def main (args : List String) : IO UInt32 :=
  AcornFrameCheck.run args
