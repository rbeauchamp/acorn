---
name: regula
description: Regula v0.12.0, the audit whose proof verdict Acorn's merge gate requires. Use before writing or changing Lean definitions, theorems, proofs or lean/lakefile.lean, and when `lake lint` reports an RG rule ID or a verdict other than pass.
---

# Regula in Acorn

[Regula](https://github.com/rbeauchamp/regula) v0.12.0 gives Acorn its proof verdict. Its README and `specification/README.md` at the tag `v0.12.0` are its documentation; this skill states how Acorn uses it.

## The proof verdict

The merge gate runs `./scripts/regula.sh`. Regula's release names three commands for the verdict, run in order on one build from the package's directory with no option of Lake's: `lake build --wfail`, `lake check --inadvisably-no-sandbox` and `lake lint`. The script runs them in `lean/`, with the package's script `kernelReplay` (`lean/lakefile.lean`) in the place of the second:

```sh
lake build --wfail
lake script run kernelReplay
lake lint
```

`lake build --wfail` fails on any warning, `sorry` among them. `kernelReplay` replays every constant of every claimed module, with every constant it depends on, in Lean's kernel from an empty environment, compares the quotient constants with the kernel's, and refuses an axiom outside `propext`, `Quot.sound` and `Classical.choice`, by Lake's own `usedAxioms`. `lake check` would replay the whole imported environment, Mathlib's included (about 496,000 constants), from an export it holds in memory, and on Acorn's claim it does not fit a 24 GiB machine; the replay leaves out only the constants that no claimed constant depends on (it checks about 87,000) and takes under 2 minutes and 4 GiB. `lake lint` runs Regula's rules. It exits 0 for `pass`, 1 for `fail` and 2 for `incomplete` (RG2001), and its last line names the verdict: a pass reads `regula: proof verdict: pass, which says nothing about what ran during the build, on <directory>`. The script passes only on exit 0 with that line naming `lean/`.

A pass means that the proofs of the claimed modules are sound and use only axioms that the profile admits. It says nothing about what a compiled program runs, and nothing about whether a theorem states what was meant: review still reads each statement.

## The claim and the profile

The claimed modules are the modules of the default targets of `lean/lakefile.lean` and every module of the package that their imports reach: the libraries `Acorn`, `AcornVerif`, `NativeApp`, `Bootstrap` and `AcornDocument`. Every Acorn theorem lives in one of them, and so does every definition such a theorem is about. A new source below `lean/Acorn`, `lean/AcornVerif` or `lean/NativeApp` is claimed by its library's glob.

`kernelReplay` and `lake lint` import the claimed modules into one environment, so only one of them can declare a top-level `main`: `Bootstrap`'s, which `lean --run` interprets. Each executable's root is a module of the library `Entry`, outside the claim, whose `main` applies the entry function of a claimed module (such as `Acorn.SwiftTdDriver.main`). Put an executable's logic in the claimed module and keep its `Entry` root to that one application. Tool code under `lean/AcornTools` and the documentation site are outside the claim, so neither holds a theorem.

The profile is `standard-logical`, the one argument in `lintDriverArgs`: `propext`, `Quot.sound` and `Classical.choice`. Lean core's binary32 and binary64 operations, which the executing library uses, depend on `Classical.choice`.

## The rules

Each rule reads the constants of the build as Lean loaded them, the claimed modules and the profile.

| Rule | What it refuses in a claimed module |
| --- | --- |
| RG1001 | An `axiom` declaration, even one nothing uses. |
| RG1002 | A constant that depends on `sorryAx`, directly or through an import. |
| RG1003 | A constant that depends on an axiom other than Lean's three, which RG1002 and RG1004 do not name. |
| RG1004 | A constant that depends on an axiom that `native_decide`, `decide +native` or `bv_decide` adds. |
| RG1005 | A constant that depends on an axiom the profile does not admit. |
| RG1006 | An `unsafe` or `partial` constant, a constant with a recursion helper's name (`f._unsafe_rec`) without the form Lean gives a terminating recursive definition, and a constant whose value mentions `Lean.Loop.mk` or `repeatM`, which `while` and `repeat` compile to. |
| RG2001 | Nothing: it is the `incomplete` verdict, for a build Regula cannot load, an input without the closed form, or arguments other than one profile. |

Write a loop with a known measure as well-founded recursion (`termination_by`) or as `for` over a finite collection, never `while`, `repeat` or `partial`. A host effect in `IO` or `BaseIO` that runs until something outside the program happens iterates with `for _ in forever do` (`lean/Acorn/Host/Forever.lean`), whose iteration is a `partial_fixpoint` definition with the unfolding of `repeat`; the body is written as it would be under `repeat`. In Std's `Async` monad, which runs a continuation in a task, no such fixed point exists: the viewer's live-frame loop calls Std's own loop there, `EAsync.forIn`, which is trusted toolchain code. Turn an assumption into a hypothesis of the theorems that need it, never an `axiom`.

## Decision contracts

`Regula.Contract` and `Regula.Decision`, in Regula's library `RegulaContract`, give no verdict: no rule of Regula reads them. `lean/Acorn/Decisions.lean` states each decision function's contract as a `Regula.ExecutableContract` with a kind (`Regula.Decides`, `Regula.DecidesSoundly` or `Regula.DecidesCompletely`) and registers the function with a declaration of type `Regula.RegisteredDecision`. The ownership audit requires a contract with a kind, in `Acorn.Decisions` or `AcornVerif.Decisions`, for each registered function whose result is not `Decidable`, and counts only a contract about the whole function: its subject is the function applied to nothing but the arguments its type takes implicitly, so a contract about one application such as `f x₀` does not count.
