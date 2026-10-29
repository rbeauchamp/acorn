---
name: Mission
about: Propose or specify a self-contained mission with a frozen Lean theorem or Regula decision contract
title: ""
labels: ["mission"]
---

<!-- An Acorn mission is a self-contained unit of work whose acceptance is decided by an exact Lean theorem about an executable Acorn definition or a Regula decision contract passing `./scripts/gate.sh` (see CONTRIBUTING.md#missions-for-outside-contributors-and-agents). The owner adds the tier label (`mission:proof`, `mission:contract`, `mission:world`, or `mission:prior-art`) once the contract is exact. Write each paragraph and each list item on a single line. -->

## Problem and mission relevance

<!-- State what capability, proof gap, contract, world model, or prior-art step this mission addresses, how it serves Acorn's continual learning and planning goals, and the baseline commit and source modules inspected. -->

## Mission contract

<!-- Freeze the exact contract so that Lean's kernel and `./scripts/gate.sh` decide acceptance without weakening the statement. -->

- Target theorem or decision contract: <!-- exact Lean 4 theorem signature(s) over the executed definition or Regula decision contract (`lean/Acorn/Decisions.lean`, `lean/AcornVerif/Decisions.lean`) to establish -->
- Module touch-set: <!-- closed list of files the pull request may modify (such as target modules in `lean/Acorn/` or `lean/AcornVerif/`, `lean/Acorn/Decisions.lean`, `lean/AcornVerif/Decisions.lean`, `docs/` or `site/`); exclude trusted-base files in `.github/CODEOWNERS` unless explicitly required -->
- Audit-pin invariance: <!-- state whether the three `C-AC5` mutation-audit pins in `lean/Acorn/Host/AuditPins.lean` must remain unchanged -->
- Verification gate: `./scripts/gate.sh` passing on the exact pull request head (see the gate requirements in CONTRIBUTING.md).
