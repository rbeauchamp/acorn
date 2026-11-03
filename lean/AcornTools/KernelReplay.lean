/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Lake.Check.Axioms
import Lean.Replay
import Lean.Util.FoldConsts
import Regula.Shell
import Regula.Workspace

/-! # The kernel replay of the Regula audit

The second step of the Regula audit (`scripts/regula.sh`), in the place of the release's
`lake check --inadvisably-no-sandbox`. That command exports every constant of the whole imported
environment, Mathlib's included, and replays the export in one process; on Acorn's claim it does
not fit the machines that run the gate. So the audit obtains Regula's rules under its profile and
this replay, not Regula v0.12.0's proof verdict as the release defines it.

The replay takes its claim from Regula itself. It runs the steps by which `lake lint` reads the
build (`Regula.Shell.loadPlain` and `Regula.Shell.inputOf` of Regula v0.12.0): Lake's load of the
workspace, the modules of the default targets, the import of them, and Regula's closed input of
that environment. Its seeds are that input's claimed constants (`Regula.Closed.Input.claimedDecls`),
the set every rule of `lake lint` reads, together with the constants each claimed module's own data
lists. It prints Regula's own line of what it read (`Regula.Shell.coverage`); the audit requires
that line to be the one `lake lint` prints after it, so a change of the build between the two
fails the audit.

Every seed and every constant it names, transitively, is replayed in Lean's kernel by
`Lean.Kernel.Environment.replay`, starting from an empty environment, so no claimed constant is
checked against one the kernel did not check. The quotient constants are then compared with the
kernel's, as `leanchecker --from-export` does, and every axiom a replayed constant names must be one
of the three that `lake check` admits, by Lake's own `usedAxioms`. An unsafe or partial claimed
constant is left out and counted, as `lake check` leaves it out: its export skips an unsafe constant
(`LeanExport/Basic.lean:255` at Lean v4.35.0) and Lean's replay skips both
(`Lean/Replay.lean:183-185`); RG1006 refuses each one except the helper Lean gives a terminating
recursive definition.

The replay leaves out the constants of the imported environment that no claimed constant depends
on. Lean's kernel looks a constant up only by a name that a term it checks contains, or by one of
its own built-in names, which are replayed (`kernelRoots`); a name absent from the replayed
environment makes it refuse, never accept. That is an assumption about Lean's kernel, which Lake's
comparator states for its own exports (`Lake/CLI/Check.lean:475-477`). The replay reads the build's
`.olean` files in this process, where `lake check` replays an export in a process that maps none.
-/

namespace AcornKernelReplay

open Lean

/-- The constants that Lean's kernel names by itself, so a replay holds them beside what the claim
needs: the list `lake comparator` roots for that reason (`primitiveTargets` and `builtinTargets`,
`Lake/CLI/Check.lean` of Lean v4.35.0), and the three axioms `lake check` admits. -/
def kernelRoots : Array Name := #[`Nat.add, `Nat.sub, `Nat.mul, `Nat.pow, `Nat.gcd, `Nat.div,
  `Nat.mod, `Nat.beq, `Nat.ble, `Nat.land, `Nat.lor, `Nat.xor, `Nat.shiftLeft, `Nat.shiftRight,
  `String.ofList, `Char.ofNat, `List, `eagerReduce, `Nat, `String, `String.mk, `Char, `optParam,
  `autoParam, `semiOutParam, `outParam, `Quot, `propext, `Classical.choice, `Quot.sound]

/-- The axioms `lake check` admits (`standardAxioms`, `Lake/CLI/Check.lean` of Lean v4.35.0). -/
def admittedAxioms : Array Name := #[`propext, `Classical.choice, `Quot.sound]

/-- The quotient constants the kernel adds itself when it adds `Quot`. The replay leaves them to it
and then compares them with the build's, as `leanchecker --from-export` does
(`LeanChecker.lean:68-90` of Lean v4.35.0). -/
def quotientParts : Array Name := #[`Quot.mk, `Quot.lift, `Quot.ind]

/-- What the kernel adds together with `n`: an inductive type with the other types of its block and
all their constructors, or `n` alone. -/
def replayUnit (map : Std.HashMap Name ConstantInfo) (n : Name) : Array Name := Id.run do
  let head := match map[n]? with
    | some (.ctorInfo v) => some v.induct
    | some (.inductInfo v) => some v.name
    | _ => none
  let some ind := head | return #[n]
  let some (.inductInfo v) := map[ind]? | return #[n]
  let mut out := #[]
  for t in v.all do
    out := out.push t
    if let some (.inductInfo w) := map[t]? then out := out ++ w.ctors.toArray
  return out

/-- What the kernel needs before `ci`: every constant its type or value names; for an inductive
type, a constructor or a recursor, the types and constructors of its block; and for `Quot`, `Eq`.
A name missing from the replayed environment makes the kernel refuse, never accept. -/
def replayNeeds (ci : ConstantInfo) : Array Name := Id.run do
  let mut out := ci.getUsedConstantsAsSet.foldl (·.push ·) #[]
  match ci with
  | .inductInfo v => out := out ++ v.ctors.toArray ++ v.all.toArray
  | .ctorInfo v => out := out.push v.induct
  | .recInfo v => out := out ++ v.all.toArray ++ (v.rules.map (·.ctor)).toArray
  -- `Quot.lift` and `Quot.ind` state `Eq`, which the kernel needs before `Quot`
  -- (`Lean/Replay.lean`).
  | .quotInfo _ => out := out.push `Eq
  | _ => pure ()
  return out

/-- Regula's closed input of the workspace in the current directory, with the environment it read:
the steps of `Regula.Shell.loadPlain` and `Regula.Shell.inputOf` (Regula v0.12.0), which `lake lint`
runs, with the environment kept. The profile does not change which modules and constants are
claimed; `standard-logical`, the weakest, refuses no input that a stronger profile admits. -/
def load : Regula.Reader.Attempt Lake.LeanLib Environment (Environment × Regula.Closed.Input) := do
  let sysroot ← Regula.Reader.requireEnv "LEAN_SYSROOT"
    "LEAN_SYSROOT is not set: run `lake exe kernel-replay`, which sets it"
  let dir ← Regula.Reader.realPath "."
  let root ← ExceptT.mk (Regula.Effect.Prog.bind
    (Regula.Effect.Prog.call (.loadWorkspace sysroot dir)) fun r =>
      pure (Regula.Reader.loaded "the workspace" r))
  let received ← Regula.Reader.requireEnv "LEAN_PATH"
    "LEAN_PATH is not set: run `lake exe kernel-replay`, which sets it"
  unless Regula.Load.startsSearchPath (root.leanPath.map toString)
      ((System.SearchPath.parse received).map toString) do
    throw "Lake's search path does not start with that of the workspace in the current directory"
  let modules ← Regula.Reader.defaultModules root root.defaultTargets
  let roots := modules.map (·.1)
  let env ← Regula.Reader.attempt
    (Regula.Effect.Prog.call (.importForRules root.leanPath roots.toArray))
  let facts ← Regula.Shell.factsOf env root.leanPath root.leanLib root.rootLib
  let input ← ExceptT.mk (pure (facts.input roots .standardLogical))
  return (env, input)

/-- The replay of the claim of `input` in the environment `env` it was read from. -/
def replay (env : Environment) (input : Regula.Closed.Input) : IO UInt32 := do
  let constants := env.constants.map₁
  let toReplay := quotientParts.foldl (init := constants) (·.erase ·)
  let claimedModules : NameSet := input.modules.foldl (·.insert ·) {}
  let mut named : NameSet := {}
  let mut claimed : Array Name := #[]
  for d in input.claimedDecls do
    unless named.contains d.name do
      named := named.insert d.name
      claimed := claimed.push d.name
  for h : i in [0:env.header.moduleNames.size] do
    if claimedModules.contains env.header.moduleNames[i] then
      for n in (env.header.moduleData[i]?.map (·.constNames)).getD #[] do
        unless named.contains n do
          named := named.insert n
          claimed := claimed.push n
  let mut kept : Array Name := #[]
  let mut unchecked := 0
  for n in claimed do
    let some ci := toReplay[n]?
      | IO.eprintln s!"kernel replay: the environment holds no claimed constant {n}"; return 1
    if ci.isUnsafe || ci.isPartial then unchecked := unchecked + 1 else kept := kept.push n
  let seeds := kernelRoots ++ kept
  let mut kenv := (← mkEmptyEnvironment).toKernelEnv
  let mut done : NameSet := quotientParts.foldl (·.insert ·) {}
  let mut expanding : NameSet := {}
  let mut stack : Array (Name × Bool) := seeds.reverse.map (·, false)
  let mut replayed := 0
  while !stack.isEmpty do
    let (n, ready) := stack.back!
    stack := stack.pop
    if done.contains n || (!ready && expanding.contains n) || !toReplay.contains n then continue
    let unit := replayUnit toReplay n
    if ready then
      let mut batch : Std.HashMap Name ConstantInfo := {}
      for x in unit do
        if let some c := toReplay[x]? then batch := batch.insert x c
      try
        kenv ← kenv.replay batch
      catch e =>
        IO.eprintln s!"kernel replay: Lean's kernel refuses {n}:\n{e}"
        return 1
      done := unit.foldl (·.insert ·) done
      replayed := replayed + batch.size
    else
      stack := stack.push (n, true)
      expanding := unit.foldl (·.insert ·) expanding
      for x in unit do
        if let some c := toReplay[x]? then
          for d in replayNeeds c do
            unless done.contains d || unit.contains d do stack := stack.push (d, false)
  for n in seeds do
    unless done.contains n do
      IO.eprintln s!"kernel replay: {n} was not replayed"
      return 1
  for q in #[`Quot] ++ quotientParts do
    if let some info := constants[q]? then
      unless kenv.find? q == some info do
        IO.eprintln s!"kernel replay: the kernel's {q} differs from the build's"
        return 1
  let checked := constants.filter fun n _ => done.contains n
  let used := Lake.Check.usedAxioms
    { constMap := checked, constOrder := checked.toArray.map (·.1) }
  let refused := used.filter fun (ax, _) => !admittedAxioms.contains ax
  unless refused.isEmpty do
    for (ax, ref) in refused do
      IO.eprintln s!"kernel replay: the axiom {ax}, which {ref} uses, is not admitted"
    return 1
  IO.println (Regula.Shell.coverage input)
  IO.println s!"kernel replay: Lean's kernel accepts {replayed} constants from an empty \
    environment, the {kept.size} safe constants that the claim of {input.modules.length} modules \
    names and every constant they depend on, leaving out {unchecked} unsafe or partial claimed \
    constants; they use the axioms {used.toList.map (·.1)}"
  return 0

end AcornKernelReplay

/-- The kernel replay of the Regula audit, from the package's directory through
`lake exe kernel-replay`. It is `unsafe` because Lean's `enableInitializersExecution` is, which
Lake's load of the workspace configuration needs, as in Regula's own `lint`. -/
unsafe def main (args : List String) : IO UInt32 := do
  unless args.isEmpty do
    IO.eprintln "usage: kernel-replay"
    return 2
  let result ← (Regula.Effect.Prog.interpret
    (Regula.Effect.table Lean.enableInitializersExecution Regula.Load.lakeCalls)
    AcornKernelReplay.load.run).toIO
  match result with
  | .error why =>
    IO.eprintln s!"kernel replay: Regula could not read the build: {why}"
    return 1
  | .ok (env, input) => AcornKernelReplay.replay env input
