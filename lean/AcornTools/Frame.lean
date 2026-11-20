/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Lean

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
- The walk skips declarations outside the project's own modules (`Acorn`, `AcornVerif`).
  Lake's manifest pins the dependency commits. The check for landed statements compares the
  manifest's SHA-256 digest with the one in `Landed.registered`.

**A pin file** is a file `<name>.frame` under `lean/AcornVerif/Targets/`, so only a merge the
owner makes can add or change one. It names the target, its module, the free names, the stop
names, and for each declaration of the frame the SHA-256 digest of its printed kind, universe
parameters, type and value, followed by its string literals (`declText`). Lines are `target`, `module`, `free`, `stop` and `pin`
followed by their words; an empty line is skipped, and no other line is admitted.

**The registration of landed statements** is the file `Landed.registered` in the same
directory. A landing is an entry of `AcornVerif.landings`: a target with the theorem recorded as
proving it. The registration has a `landing` line for each landing, the target's name and the
theorem's, a `lock` line for each of the package's two lock files, `lean-toolchain` and
`lake-manifest.json`, with the digest of its content, and a `pin` line for each declaration of
one frame: the walk above from every landed target and every such theorem, with no free and no
stop name. The landings are read from the build, by reducing the value of `AcornVerif.landings`
to its entries, so no list of names is kept in this program, and an entry is refused whose
proof is not the constant it names or whose constant is no theorem. A theorem's proof is not followed. The walk stops at
declarations outside the project, and the lock lines stand for those: a change of toolchain or
of a dependency's commit changes a lock file, and so fails the check until the registration is
made again.

**The check** (no argument). It lists `lean/AcornVerif/Targets/` and admits three kinds of
entry: a regular file whose name ends in `.lean`, a regular file whose name ends in `.frame`,
which is a pin file, and the regular file `Landed.registered`. Any other entry, a subdirectory
or a symbolic link included, fails the check and is named, so a file that is misplaced or
misnamed is refused and not passed over.

- For the registration it imports the module of the record, reads the landings and computes
  their frame. It fails when the record holds no landing, when the file is missing, when a
  landing on record is not registered, when a registered landing is no longer on record, when
  a lock file's content is not the registered one, and when the frame differs from the pinned
  one. So a pass never comes from finding nothing to
  register.
- For each pin file it imports the module, computes the frame and compares it with the pinned
  one. With no pin file it says so: an open target without a pin file is not pinned.

Frames are compared as sets of printed names with digests. A declaration pinned and no longer
reached, reached and not pinned, or with another digest fails the check, and each is printed.

**Printing** (`print <module> <target> [free <name>]... [stop <name>]...`) writes a pin file's
text for those names to standard output, and `print-landed` writes the registration's text for
the landings the build has on record.

What a pass means: every declaration the walk reaches prints to the text it printed when the
file was made, the landings on record are the registered ones, each landing's proof is the
theorem it names, and the two lock files hold the registered content. It does not say what those
declarations mean or that the free names were well chosen. Reading the record trusts Lean's
elaborator to reduce the list to the names the kernel admitted. The digest is a detector of
change. It is taken with this file's own SHA-256, which each run checks against three published
test vectors before it reads anything. The vectors show that the empty message, a message of one
block and a message of two blocks digest as published, and no more: they do not show that an
implementation meeting them is SHA-256, or that it detects every change.
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

/-- The string literals an expression holds, in the order of a walk over its whole tree. -/
partial def literals (expr : Expr) (found : Array String) : Array String :=
  match expr with
  | .lit (.strVal text) => found.push text
  | .app function argument => literals argument (literals function found)
  | .lam _ domain body _ => literals body (literals domain found)
  | .forallE _ domain body _ => literals body (literals domain found)
  | .letE _ type value body _ => literals body (literals value (literals type found))
  | .mdata _ body => literals body found
  | .proj _ _ body => literals body found
  | _ => found

/-- String literals written so that the list can be read back: each as the number of bytes of
its UTF-8 form, a colon and the literal itself. -/
def literalText (found : Array String) : String :=
  String.join (found.toList.map fun text => s!"{text.utf8ByteSize}:{text}")

/-- The printed text of a declaration that its digest is taken of: its kind, its universe
parameters, its type, a definition's value or an inductive type's constructors, and then every
string literal of the type and the value in the order they occur. Lean's printer of
expressions, `Expr.dbgToString`, writes a string literal as a C string, which ends at the
literal's first zero byte (Lean v4.35.0, `src/library/print.cpp`, the case of a string
literal), so two literals that agree up to a zero byte print alike. The list of literals after
the printed text tells them apart. -/
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
  let inValue := match info with
    | .defnInfo value => literals value.value #[]
    | .opaqueInfo value => literals value.value #[]
    | _ => #[]
  s!"{kind}\n{info.levelParams}\n{info.type.dbgToString}\n{body}\n\
    {literalText (literals info.type #[] ++ inValue)}"

/-- The frame of some roots: every owned constant the walk reaches from any of them, with its
digest. A free name is left out and not followed; a stop name is kept and not followed. -/
partial def frame (env : Environment) (free stop : NameSet) (roots : Array Name) :
    Std.HashMap Name String := Id.run do
  let mut pinned : Std.HashMap Name String := {}
  let mut seen : NameSet := {}
  let mut work : Array Name := roots
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

/-- A frame as it is written and compared: each declaration's printed name with its digest, in
the order of the names. A pin holds printed names, and reading one back as a name would not
return every name (a private declaration's name has a numeric component), so frames are compared
as printed. Two declarations that print alike are refused, since one line could not pin both. -/
def printed (computed : Std.HashMap Name String) : Except String (Array (String × String)) := do
  let entries := (computed.toArray.map fun entry => (entry.1.toString, entry.2)).qsort
    fun left right => left.1 < right.1
  for index in [1:entries.size] do
    if entries[index - 1]!.1 == entries[index]!.1 then
      throw s!"two declarations of the frame print as {entries[index]!.1}"
  for (name, _) in entries do
    if name.any fun character => character == ' ' || character == '\n' then
      throw s!"a declaration of the frame prints with a space or a line break: {name}"
  return entries

/-- Compare pinned declarations with a frame the build has. Prints each difference under
`label` and returns whether there is none. -/
def compare (label : String) (pins now : Array (String × String)) : IO Bool := do
  let mut same := true
  let current : Std.HashMap String String :=
    now.foldl (fun map entry => map.insert entry.1 entry.2) {}
  let mut pinned : Std.HashSet String := {}
  for (name, digest) in pins do
    if pinned.contains name then
      same := false
      IO.println s!"frame: {label}: {name} is pinned twice"
    pinned := pinned.insert name
    match current[name]? with
    | none =>
      same := false
      IO.println s!"frame: {label}: {name} is pinned and no longer part of the frame"
    | some digestNow =>
      unless digestNow == digest do
        same := false
        IO.println s!"frame: {label}: {name} has changed"
  for (name, _) in now do
    unless pinned.contains name do
      same := false
      IO.println s!"frame: {label}: {name} is part of the frame and not pinned"
  return same

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
  /-- The frame: each declaration's printed name with its digest. -/
  pins : Array (String × String) := #[]

/-- A pin file's text, one statement a line, the declarations in the order of their names. -/
def Pin.text (pin : Pin) : String :=
  let sorted := pin.pins.qsort fun left right => left.1 < right.1
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
    | ["pin", digest, name] => pin := { pin with pins := pin.pins.push (name, digest) }
    | _ => throw s!"a line that is none of the five statements: {line}"
  match target, home with
  | some found, some declaring => return { pin with target := found, home := declaring }
  | _, _ => throw "no target line or no module line"

/-- The frame of a pin's target, in the environment of its module. An unknown target is
refused. -/
def computed (pin : Pin) : IO (Array (String × String)) := do
  let env ← importModules #[{ module := pin.home }] {}
  unless (env.find? pin.target).isSome do
    throw (IO.userError s!"{pin.home} declares no {pin.target}")
  IO.ofExcept ((printed (frame env (pin.free.foldl (·.insert ·) {})
    (pin.stop.foldl (·.insert ·) {}) #[pin.target])).mapError
      fun error => IO.userError s!"{pin.target}: {error}")

/-- Compare a pin file with the frame the build has. Prints each difference and returns whether
there is none. -/
def verify (file : System.FilePath) : IO Bool := do
  let pin ← IO.ofExcept ((Pin.parse (← IO.FS.readFile file)).mapError
    fun error => IO.userError s!"{file}: {error}")
  let now ← computed pin
  let same ← compare (toString pin.target) pin.pins now
  let verdict := if same then "unchanged" else "CHANGED"
  IO.println s!"frame: {pin.target}: {pin.pins.size} declarations pinned by {file}, \
    {now.size} in the frame, {verdict}"
  return same

/-! ## The statements of landed missions -/

/-- The module that holds the record of landings. -/
def landingsModule : Name := `AcornVerif.Landings

/-- The name of the registration file in `AcornVerif/Targets`. -/
def registrationName : String := "Landed.registered"

/-- The entries of a list of landings, each as its target's name and its theorem's name, read
from a term by reducing it: the list to its constructors, each entry to the constructor of
`AcornVerif.Targets.Landing`, and each name to a name. A term of any other shape is refused,
and so is an entry whose proof is not the constant its theorem's name names, at whatever
universes: the name a landing records is then the declaration that proves its target, which the
kernel checked against the target's statement when it admitted the entry. -/
partial def landingEntries (list : Expr) (found : Array (Name × Name)) :
    MetaM (Array (Name × Name)) := do
  let list ← Meta.whnf list
  match list.getAppFnArgs with
  | (``List.nil, _) => return found
  | (``List.cons, #[_, head, tail]) =>
    let head ← Meta.whnf head
    match head.getAppFnArgs with
    | (`AcornVerif.Targets.Landing.mk, #[target, proved, proof]) =>
      let target : Name ← Meta.reduceEval target
      let proved : Name ← Meta.reduceEval proved
      unless proof.consumeMData.isConstOf proved do
        throwError "the landing of {target} names {proved} as its theorem, and its proof is \
          another term: {proof}"
      landingEntries tail (found.push (target, proved))
    | _ => throwError "an entry of the record of landings is no application of Landing.mk: {head}"
  | _ => throwError "the record of landings does not reduce to a list: {list}"

/-- The landings on record: the entries of `AcornVerif.landings` as the build's environment
holds it. The definition's value is read, so no list of names is kept here. -/
def landedOnRecord (env : Environment) : IO (Array (Name × Name)) := do
  unless (env.find? `AcornVerif.landings).isSome do
    throw (IO.userError s!"{landingsModule} declares no AcornVerif.landings")
  let (found, _, _) ← (landingEntries (mkConst `AcornVerif.landings) #[]).toIO
    { fileName := "<frame-check>", fileMap := default } { env }
  return found

/-- The files whose content selects the toolchain and the dependencies' commits, relative to the
package directory. The frame stops at declarations outside the project, so the registration
binds these files instead: what a pinned declaration calls in Lean or a dependency can change
only with one of them. -/
def lockFiles : Array String := #["lean-toolchain", "lake-manifest.json"]

/-- The registration's content: the landings whose statements are registered, each a target's
printed name with its theorem's, the digests of the lock files, and the frame of all the
landings. -/
structure Registration where
  /-- Each registered landing: the target's printed name and the theorem's. -/
  landings : Array (String × String) := #[]
  /-- Each lock file's path with the SHA-256 digest of its content. -/
  locks : Array (String × String) := #[]
  /-- The frame: each declaration's printed name with its digest. -/
  pins : Array (String × String) := #[]

/-- The registration's text: a `landing` line for each landing in the order of the targets'
names, a `lock` line for each lock file in the order of their paths, then a `pin` line for each
declaration in the order of their names. -/
def Registration.text (registration : Registration) : String :=
  let landings := registration.landings.qsort fun left right => left.1 < right.1
  let locks := registration.locks.qsort fun left right => left.1 < right.1
  let pins := registration.pins.qsort fun left right => left.1 < right.1
  String.intercalate "\n"
    (landings.toList.map (fun entry => s!"landing {entry.1} {entry.2}") ++
      locks.toList.map (fun entry => s!"lock {entry.2} {entry.1}") ++
      pins.toList.map (fun entry => s!"pin {entry.2} {entry.1}")) ++ "\n"

/-- Read a registration's text. Every line must be a `landing`, a `lock` or a `pin`
statement. -/
def Registration.parse (text : String) : Except String Registration := do
  let mut registration : Registration := {}
  for line in (text.splitOn "\n").filter (!·.isEmpty) do
    match line.splitOn " " with
    | ["landing", target, proved] =>
      registration := { registration with landings := registration.landings.push (target, proved) }
    | ["lock", digest, path] =>
      registration := { registration with locks := registration.locks.push (path, digest) }
    | ["pin", digest, name] =>
      registration := { registration with pins := registration.pins.push (name, digest) }
    | _ => throw s!"a line that is neither a landing, a lock nor a pin: {line}"
  return registration

/-- What the build has to register: the landings on record, which must be some, and the frame
whose roots are every landed target and every theorem recorded as proving one, with no free and
no stop name. A target that the build does not declare is refused, and so is a name recorded as
proving one that the build does not declare as a theorem. -/
def landedNow : IO Registration := do
  let env ← importModules #[{ module := landingsModule }] {}
  let record ← landedOnRecord env
  if record.isEmpty then
    throw (IO.userError "AcornVerif.landings records no landing, so no statement of a landed \
      mission would be registered")
  let mut roots : Array Name := #[]
  for (target, proved) in record do
    unless (env.find? target).isSome do
      throw (IO.userError s!"the record of landings names {target}, which the build does not \
        declare")
    match env.find? proved with
    | some (.thmInfo _) => pure ()
    | some _ => throw (IO.userError s!"the landing of {target} names {proved}, which is no \
        theorem")
    | none => throw (IO.userError s!"the record of landings names {proved}, which the build \
        does not declare")
    roots := roots.push target
    roots := roots.push proved
  let pins ← IO.ofExcept ((printed (frame env {} {} roots)).mapError IO.userError)
  let mut locks : Array (String × String) := #[]
  for path in lockFiles do
    locks := locks.push (path, sha256 (← IO.FS.readFile path))
  return { landings := record.map fun entry => (entry.1.toString, entry.2.toString), locks, pins }

/-- Compare the registration with what the build has: the registered landings with the landings
on record, as sets, and the registered frame with the frame of those landings. Prints each
difference and returns whether there is none. -/
def verifyLanded (file : System.FilePath) : IO Bool := do
  let now ← landedNow
  let registered ← IO.ofExcept ((Registration.parse (← IO.FS.readFile file)).mapError
    fun error => IO.userError s!"{file}: {error}")
  let mut same := true
  for entry in now.landings do
    unless registered.landings.contains entry do
      same := false
      IO.println s!"frame: landed: {entry.1} is on record as proved by {entry.2} and that is \
        not registered"
  for entry in registered.landings do
    unless now.landings.contains entry do
      same := false
      IO.println s!"frame: landed: {entry.1} is registered as proved by {entry.2} and that is \
        no longer on record"
  unless registered.landings.size == now.landings.size do
    same := false
    IO.println s!"frame: landed: {registered.landings.size} landings are registered and \
      {now.landings.size} are on record"
  for entry in now.locks do
    unless registered.locks.contains entry do
      same := false
      IO.println s!"frame: landed: {entry.1} is not registered with its present content, so \
        the toolchain or a dependency may differ from the registered one"
  unless registered.locks.size == now.locks.size do
    same := false
    IO.println s!"frame: landed: {registered.locks.size} lock files are registered and \
      {now.locks.size} are read"
  unless ← compare "landed" registered.pins now.pins do same := false
  let verdict := if same then "unchanged" else "CHANGED"
  IO.println s!"frame: landed: {registered.landings.size} landings registered by {file}, \
    {now.landings.size} on record, {registered.locks.size} lock files, \
    {registered.pins.size} declarations pinned, {now.pins.size} in the frame, {verdict}"
  return same

/-- The pin files and the registration: the regular files ending in `.frame` in
`AcornVerif/Targets`, the directory of the package that only the owner's merges change, and
whether it holds the regular file `Landed.registered`. The directory admits those and regular
files ending in `.lean`; any other entry is refused by name. -/
def pinFiles : IO (Array System.FilePath × Option System.FilePath) := do
  let directory : System.FilePath := "AcornVerif" / "Targets"
  let mut files : Array System.FilePath := #[]
  let mut registration : Option System.FilePath := none
  for entry in ← directory.readDir do
    let regular := (← entry.path.symlinkMetadata).type == .file
    if regular && entry.fileName.endsWith ".frame" then
      files := files.push entry.path
    else if regular && entry.fileName == registrationName then
      registration := some entry.path
    else unless regular && entry.fileName.endsWith ".lean" do
      throw (IO.userError s!"{entry.path} is neither a regular file ending in .lean, a \
        regular file ending in .frame nor the regular file {registrationName}")
  return (files.qsort (·.toString < ·.toString), registration)

/-- The names that follow a keyword in the arguments of `print`. -/
def namesAfter (keyword : String) : List String → Array Name
  | key :: name :: rest =>
    (if key == keyword then #[name.toName] else #[]) ++ namesAfter keyword rest
  | _ => #[]

/-- Check the registration and every pin file against the finished build, or print one. -/
def run (args : List String) : IO UInt32 := do
  unless vectorsHold do
    IO.eprintln "frame-check: this program's SHA-256 does not meet its test vectors"
    return 1
  try
    initSearchPath (← findSysroot)
    match args with
    | [] =>
      let (files, registration) ← pinFiles
      let mut same := true
      match registration with
      | some file => unless ← verifyLanded file do same := false
      | none =>
        same := false
        IO.println s!"frame: landed: AcornVerif/Targets holds no {registrationName}, so the \
          statements of landed missions are not registered"
      if files.isEmpty then
        IO.println "frame: no pin file under AcornVerif/Targets, so no open target's frame is \
          pinned"
      for file in files do
        unless ← verify file do same := false
      if same then
        IO.println s!"frame: the registration of landed statements and every pinned frame are \
          unchanged ({files.size} pin files)"
        return 0
      IO.println "frame: a registered or pinned frame has changed"
      return 1
    | ["print-landed"] =>
      IO.print (← landedNow).text
      return 0
    | "print" :: declaring :: target :: rest =>
      unless rest.length % 2 == 0 && rest.zipIdx.all (fun (word, index) =>
          index % 2 == 1 || word == "free" || word == "stop") do
        IO.eprintln "usage: frame-check print <module> <target> [free <name>]... [stop <name>]..."
        return 2
      let pin : Pin :=
        ⟨target.toName, declaring.toName, namesAfter "free" rest, namesAfter "stop" rest, #[]⟩
      let now ← computed pin
      let filled : Pin := ⟨pin.target, pin.home, pin.free, pin.stop, now⟩
      IO.print filled.text
      return 0
    | _ =>
      IO.eprintln "usage: frame-check [print-landed | print <module> <target> [free <name>]... \
        [stop <name>]...]"
      return 2
  catch error =>
    IO.eprintln s!"frame-check: {error}"
    return 1

end AcornFrameCheck

/-- Check the registration and every pin file against the finished build, or print one. -/
def main (args : List String) : IO UInt32 :=
  AcornFrameCheck.run args
