---
name: regula
description: Regula v0.13.0 and the Regula audit of Acorn's merge gate, which obtains Regula's proof verdict. Use before writing or changing Lean definitions, theorems, proofs or lean/lakefile.lean, and when `lake lint` reports an RG rule ID or a verdict other than pass.
---

# Regula in Acorn

[Regula](https://github.com/rbeauchamp/regula) v0.13.0 is the audit of Lean builds that Acorn's merge gate runs. Its README and `specification/README.md` at the tag `v0.13.0` are its documentation; this skill states how Acorn uses it.

## The Regula audit

The merge gate runs `./scripts/regula.sh`, which obtains Regula's proof verdict by the route the release publishes: two commands in order on one build, each in `lean/` with no option of Lake's and with `REGULA_FULL` unset.

```sh
lake build --wfail
lake lint
```

`lake build --wfail` fails on any warning, `sorry` among them. `lake lint` reads the build, replays the claim's cone in Lean's kernel into an empty environment, and runs Regula's rules under the profile of the package's `lintDriverArgs`. The cone is each constant of a claimed module, every constant that one of them reaches through what each mentions as the kernel checks it, and the constants that the kernel builds into a term, and nothing else; an unsound proof in a dependency that the claim reaches fails it. `lake lint` exits 0 for `pass`, 1 for `fail` and 2 for `incomplete` (RG2001), and its last line names the verdict: a pass reads `regula: proof verdict: pass, which says nothing about what ran during the build, on <directory>`. The script passes only when `lake lint` exits 0 with that line naming the real path of `lean/`.

A pass means, as Regula states, that the proofs of the claimed modules are sound and use only axioms that the profile admits, for a project that places no file or code aimed at the checker or the toolchain. Both commands run in Acorn's own Lake, so such a file or code could make them print a pass whatever the build holds. Acorn relies on that assumption about itself: it is part of Acorn's trusted base, and no check establishes it. Add no file or code meant to change what Lake, Lean's loader or Regula's checker does. A pass says nothing about what a compiled program runs, and nothing about whether a theorem states what was meant: review still reads each statement. Regula's full verdict needs no assumption about the project, and Acorn cannot get it: only a project with no dependency in its Lake configuration and no Mathlib in its imports can. `docs/verification.md` (section "Regula audit") states this for the documents.

## The claim and the profile

The claimed modules are the modules of the default targets of `lean/lakefile.lean` and every module of the package that their imports reach: the libraries `Acorn`, `AcornVerif`, `NativeApp`, `Bootstrap` and `AcornDocument`. Every Acorn theorem lives in one of them, and so does every definition such a theorem is about. A new source below `lean/Acorn`, `lean/AcornVerif` or `lean/NativeApp` is claimed by its library's glob.

`lake lint` imports the claimed modules into one environment, so only one of them can declare a top-level `main`: `Bootstrap`'s, which `lean --run` interprets. Each executable's root is a module of the library `Entry`, outside the claim, whose `main` applies the entry function of a claimed module (such as `Acorn.SwiftTdDriver.main`). Put an executable's logic in the claimed module and keep its `Entry` root to that one application. Tool code under `lean/AcornTools` and the documentation site are outside the claim, so neither holds a theorem.

The profile is `standard-logical`, the one argument in `lintDriverArgs`: `propext`, `Quot.sound` and `Classical.choice`. Lean core's binary32 and binary64 operations, which the executing library uses, depend on `Classical.choice`.

## The rules

Each rule reads the constants of the build as Lean loaded them, the claimed modules and the profile. RG1002 to RG1005 follow what each constant mentions as Lean's kernel checks it, the relation the replay follows: its type, the value of a definition, theorem or opaque constant, the constructors and other types of an inductive type's block, a constructor's inductive type, the types of a recursor's block, and `Eq` for a quotient.

| Rule | What it refuses in a claimed module |
| --- | --- |
| RG1001 | An `axiom` declaration, even one nothing uses. |
| RG1002 | A constant that depends on `sorryAx`, directly or through an import. |
| RG1003 | A constant that depends on an axiom other than Lean's three, which RG1002 and RG1004 do not name. |
| RG1004 | A constant that depends on an axiom that `native_decide`, `decide +native` or `bv_decide` adds. |
| RG1005 | A constant that depends on an axiom the profile does not admit. |
| RG1006 | An `unsafe` or `partial` constant, a constant with a recursion helper's name (`f._unsafe_rec`) without the form Lean gives a terminating recursive definition, and a constant whose value mentions `Lean.Loop.mk` or `repeatM`, which `while` and `repeat` compile to. |
| RG2001 | Nothing: it is the `incomplete` verdict, for a build Regula cannot load, an input without the closed form, arguments other than one profile, a claimed constant that Lean's import replaced and that is no theorem within the profile or has a recursion helper's name, or a replay of the claim's cone that Lean's kernel does not accept. |

Write a loop with a known measure as well-founded recursion (`termination_by`) or as `for` over a finite collection, never `while`, `repeat` or `partial`. A host effect in `IO` or `BaseIO` that runs until something outside the program happens iterates with `for _ in forever do` (`lean/Acorn/Host/Forever.lean`), whose iteration is a `partial_fixpoint` definition with the unfolding of `repeat`; the body is written as it would be under `repeat`. In Std's `Async` monad, which runs a continuation in a task, no such fixed point exists: the viewer's live-frame loop calls Std's own loop there, `EAsync.forIn`, which is trusted toolchain code. Turn an assumption into a hypothesis of the theorems that need it, never an `axiom`.

## Decision contracts

`Regula.Contract` and `Regula.Decision`, in Regula's library `RegulaContract`, give no verdict: no rule of Regula reads them. `lean/Acorn/Decisions.lean` states each decision function's contract as a `Regula.ExecutableContract` with a kind (`Regula.Decides`, `Regula.DecidesSoundly` or `Regula.DecidesCompletely`) and registers the function with a declaration of type `Regula.RegisteredDecision`. The ownership audit requires a contract with a kind, in `Acorn.Decisions` or `AcornVerif.Decisions`, for each registered function whose result is not `Decidable`, and counts only a contract about the whole function whose condition applies its kind to that function. Its subject is the function applied to nothing but the arguments its type takes implicitly, so a contract about one application such as `f x₀` does not count. Its condition is `K accepts spec`, which lacks the kind's last argument, so the contract applies it to the function, or `fun g => K accepts spec t`, where `t` contains `g`; any other form, such as `fun _ => Regula.Decides accepts spec id`, does not count.
