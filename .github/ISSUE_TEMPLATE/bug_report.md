---
name: Defect report
about: Report a soundness, contract, specification, runtime or viewer defect
title: ""
labels: ["bug"]
---

<!-- Use this template for concrete defects in code, proofs, specifications, gates, or documentation. Do not report security vulnerabilities or trusted-base gate bypasses here; use private vulnerability reporting (SECURITY.md). Write each paragraph and each list item on a single line. -->

## Problem and evidence

<!-- State the expected vs. actual behavior or contract gap, the baseline commit (`git rev-parse HEAD`), and the affected module, theorem, or document owners. -->

## Reproduction or structural argument

<!-- Give the smallest command, inspection step, or counterexample that demonstrates the defect. Counterexamples are diagnostics to close the whole defect class by type, proof, or gate check, never scenario tests. -->

## Retrospective

<!-- Every defect issue records how to close the whole class and why the system let it arise undetected. -->

- Failed mission-level property: <!-- which mission-level property or invariant failed -->
- Executable contract to close the class: <!-- the type, theorem, construction, or gate check that makes this defect class impossible -->
- Assumption that stood in for that contract: <!-- where the existing code or reasoning relied on an unproved assumption -->
- Root cause and link change: <!-- why the system let this class arise undetected, traced to a contract, check, document, or instruction that can be changed, with that change -->
- Class: <!-- external system behaviour | case coverage | prose nothing enforces | theorem misses executed path | plain logic | requirement gap | time budget | stale text | process -->
- External system (if any): <!-- none, or the tool/OS/service and version -->
- How found: <!-- inspection, proof attempt, gate run, or live run -->
- Earlier issue repeated (if any): <!-- none, or #<id> -->
