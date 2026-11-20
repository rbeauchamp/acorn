---
name: Mission
about: Propose or specify a self-contained mission with a frozen Lean theorem or Regula decision contract
title: ""
labels: ["mission"]
---

<!-- An Acorn mission is a self-contained unit of work whose acceptance is decided by an exact Lean theorem about an executable Acorn definition or a Regula decision contract passing `./scripts/gate.sh` (see CONTRIBUTING.md#missions-for-outside-contributors-and-agents). The owner adds the tier label (`mission:proof`, `mission:contract`, `mission:world`, or `mission:prior-art`) once the contract is exact. A theorem's statement is then held as a target: a Lean definition of type `Prop` under `lean/AcornVerif/Targets/`, where a change is the owner's to make, listed in `lean/AcornVerif/Targets/Registry.lean` under this issue's number. Write each paragraph and each list item on a single line. -->

## Problem and mission relevance

<!-- State what capability, proof gap, contract, world model, or prior-art step this mission addresses, how it serves Acorn's continual learning and planning goals, and the baseline commit and source modules inspected. -->

## Mission contract

<!-- Freeze the exact contract so that Lean's kernel and `./scripts/gate.sh` decide acceptance without weakening the statement. -->

- Targets: <!-- once the owner has registered them, the name of each target to prove, such as `AcornVerif.Targets.Json.parse_complete`, and its file. To propose a statement, write the exact Lean 4 theorem signature(s) over the executed definition here; a proposer does not add files under `lean/AcornVerif/Targets/`. To prove a target, state a theorem whose statement is the target, using the contract's definitions from the target's module, add its entry to the list in `lean/AcornVerif/Landings.lean` and register that entry in `lean/AcornVerif/Targets/Landed.registered` (see docs/missions.md, steps 3 and 5). Write "none" for a mission whose whole contract is the next line -->
- Decision contract or other part that is not a statement to prove: <!-- the exact Regula decision contract (`lean/Acorn/Decisions.lean`, `lean/AcornVerif/Decisions.lean`) or other change to establish, which stays frozen in this issue; write "none" where the targets are the whole contract -->
- Module touch-set: <!-- closed list of files the pull request may modify (such as the modules that hold the proofs in `lean/Acorn/` or `lean/AcornVerif/`, `lean/AcornVerif/Landings.lean` and the registration `lean/AcornVerif/Targets/Landed.registered` for a mission with targets, `lean/Acorn/Decisions.lean`, `lean/AcornVerif/Decisions.lean`, `docs/` or `site/`); exclude every other file under `lean/AcornVerif/Targets/` and the other trusted-base files in `.github/CODEOWNERS` unless explicitly required -->
- Audit-pin invariance: <!-- state whether the three `C-AC5` mutation-audit pins in `lean/Acorn/Host/AuditPins.lean` must remain unchanged -->
- Verification gate: `./scripts/gate.sh` passing on the exact pull request head (see the gate requirements in CONTRIBUTING.md).
