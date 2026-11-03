---
name: regula
description: Regula v0.12.0 and the Regula audit of Acorn's merge gate, which runs Regula's rules and Acorn's kernel replay. Use before writing or changing Lean definitions, theorems, proofs or lean/lakefile.lean, and when `lake lint` reports an RG rule ID or a verdict other than pass, or the kernel replay refuses.
---

# Regula in Acorn

[Regula](https://github.com/rbeauchamp/regula) v0.12.0 is the audit of Lean builds that Acorn's merge gate runs. Its README and `specification/README.md` at the tag `v0.12.0` are its documentation; this skill states how Acorn uses it.

## The Regula audit

The merge gate runs `./scripts/regula.sh`. Regula's release names three commands for its proof verdict, run in order on one build from the package's directory with no option of Lake's: `lake build --wfail`, `lake check --inadvisably-no-sandbox` and `lake lint`. `lake check` replays the whole imported environment, Mathlib's included (496,347 constants here), from an export it holds in memory, and on Acorn's claim it does not fit a 24 GiB machine. So the script runs, in `lean/`:

```sh
lake build --wfail
lake exe kernel-replay
lake lint
```

and obtains Regula's rules under the profile and Acorn's kernel replay, not Regula v0.12.0's proof verdict as the release defines it. The departure is interim: when a Regula release makes its proof verdict obtainable for a project that imports Mathlib, the gate returns to Regula's own commands. `docs/verification.md` (section "Regula audit") states it for the documents.

`lake build --wfail` fails on any warning, `sorry` among them. `kernel-replay` (`lean/AcornTools/KernelReplay.lean`) reads the build once with Regula's own code, as `lake lint` reads it, under the profile of the package's `lintDriverArgs`, read by Regula's own parser of them. On that one input it runs Regula's rules, printing what Regula prints for a verdict other than pass, and refuses unless they pass; from the same input it replays every constant Regula's rules read as claimed, with every constant it depends on, in Lean's kernel from an empty environment (about 87,000 constants, under 2 minutes). It requires every constant of the environment the kernel returns to equal the build's, the quotient constants among them, and every claimed constant to be one of them, and refuses an axiom outside `propext`, `Quot.sound` and `Classical.choice` that one of them uses, by Lake's own `usedAxioms`. It prints Regula's line of what it read, and the script fails unless `lake lint` prints the same line: a consistency check that both runs read the same numbers of claimed modules and constants, not a check that the build did not change between them. `lake lint` runs Regula's rules. It exits 0 for `pass`, 1 for `fail` and 2 for `incomplete` (RG2001), and its last line names the verdict: a pass reads `regula: proof verdict: pass, which says nothing about what ran during the build, on <directory>`. The script passes only when the replay exits 0, the two lines agree, and `lake lint` exits 0 with that line naming `lean/`.

A pass of the audit means that Lean's kernel accepts the proofs of the claimed modules and that they use only axioms that the profile admits. It says nothing about what a compiled program runs, and nothing about whether a theorem states what was meant: review still reads each statement.

## The claim and the profile

The claimed modules are the modules of the default targets of `lean/lakefile.lean` and every module of the package that their imports reach: the libraries `Acorn`, `AcornVerif`, `NativeApp`, `Bootstrap` and `AcornDocument`. Every Acorn theorem lives in one of them, and so does every definition such a theorem is about. A new source below `lean/Acorn`, `lean/AcornVerif` or `lean/NativeApp` is claimed by its library's glob.

`kernel-replay` and `lake lint` import the claimed modules into one environment, so only one of them can declare a top-level `main`: `Bootstrap`'s, which `lean --run` interprets. Each executable's root is a module of the library `Entry`, outside the claim, whose `main` applies the entry function of a claimed module (such as `Acorn.SwiftTdDriver.main`). Put an executable's logic in the claimed module and keep its `Entry` root to that one application. Tool code under `lean/AcornTools` and the documentation site are outside the claim, so neither holds a theorem.

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

`Regula.Contract` and `Regula.Decision`, in Regula's library `RegulaContract`, give no verdict: no rule of Regula reads them. `lean/Acorn/Decisions.lean` states each decision function's contract as a `Regula.ExecutableContract` with a kind (`Regula.Decides`, `Regula.DecidesSoundly` or `Regula.DecidesCompletely`) and registers the function with a declaration of type `Regula.RegisteredDecision`. The ownership audit requires a contract with a kind, in `Acorn.Decisions` or `AcornVerif.Decisions`, for each registered function whose result is not `Decidable`, and counts only a contract about the whole function whose condition applies its kind to that function. Its subject is the function applied to nothing but the arguments its type takes implicitly, so a contract about one application such as `f x₀` does not count. Its condition is `K accepts spec`, which lacks the kind's last argument, so the contract applies it to the function, or `fun g => K accepts spec t`, where `t` contains `g`; any other form, such as `fun _ => Regula.Decides accepts spec id`, does not count.
