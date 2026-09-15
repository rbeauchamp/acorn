# Working on Acorn

Acorn is an independent research implementation inspired by Oak Lab's mission
and the Alberta Plan. [Design](docs/design.md) owns implementation coverage;
[prior-art review](docs/prior-art-review.md) owns technical admission and default
qualification; [learned-only binding](docs/learned-only-binding.md) owns departures.
No composition is qualified for implicit default use. Do not imply endorsement,
learning effectiveness or completion of the Alberta Plan.

## Correct by construction

An ounce of math is worth a pound of computation. Identify semantics, state
invariants, hypotheses and implementation linkage before choosing work.
Prefer types making illegal states unrepresentable, derivation, exhaustive
compiler checks over closed types, universal proofs, then derived guards.
Enforce the invariant at every construction, deserialization and update boundary.
Bounding an output alone does not bound stored state.

Proofs must concern the executed definitions or a checked correspondence.
Distinguish finite-word arithmetic from mathematical integers, rationals and reals.
State concurrency, serialization, native, compiler and OS assumptions explicitly.
No custom axiom, sorry, unsafe/partial application definition, panic or unchecked
native replacement enters governed code. Reviewed tooling and the narrow C fsync
primitive are explicit trust boundaries.

There are no scenario tests. Counterexamples diagnose missing invariants or
contracts; close the whole defect class. Prefer structural/analytic proofs to
reflection. Before certified re-execution, estimate initial and recurring proof
cost beside the proposed observation and obtain an owner decision if it does
not cost clearly less. Difficulty proving a property does not make it empirical.

Measure only irreducibly empirical claims with explicit scope, budget, uncertainty
and prospective decision criteria. A digest is a mutation detector, not correctness
or scientific evidence. Do not rerun learning or promote defaults during ordinary
engineering. Preserve original observations separately from presentations.

## Learned-only and research admission

Every hand-authored action-path bias requires its actual departure declaration.
A provenance witness is a declaration, not proof that it is honest. Source and
compiled ownership enforce the learned/host/handcrafted boundary and explicit
composition roots. The viewer observes telemetry and sends lifecycle stop only;
it cannot alter learning decisions.

Verify citations against the actual source before adding them. Paper-based code
and proofs must identify author, work, venue/year and exact equation, section or
theorem in source documentation. Reproduce derivations and explain material
adaptations, their rationale, semantic consequences and composition compatibility.
Fix defects found in prior art, with a characterization theorem or identity and
present-tense explanation. Do not replicate a known error for fidelity.

Technical admission requires soundness, fit to the continuing setting, semantic
compatibility/nondegeneracy, affordable work/storage and sufficient specification.
Promotion requires separate prospective evidence and an explicit decision. Keep
negative and inconclusive evidence honest; exclusion is not a positive result.

## Review and delivery

Use the shipped proof-review standard and pr-review-toolkit for review-and-fix.
One independent reviewer is the default; add a specialist only for a concrete
uncertainty. Use ux-review for viewer behavior or [viewer specification](docs/viewer-ux.md) changes, including
rendered-state inspection. The skills under .agents/skills are maintained
contributor interfaces.

Keep comments about current semantics and rationale; Git records chronology.
Fix authorized concrete defects, preserve unrelated work and ask before materially
broader scope or new follow-up issues. Prefer small coherent changes over rewrites.
Apply [performance engineering](docs/performance-engineering.md) to performance-sensitive work; preserve proofs and
admission predicates. Do not replace unresolved proof obligations with measurements.

Run the complete command in the actual Git checkout:

```sh
./scripts/verify.sh
```

Provision pinned Lean/Mathlib v4.33.0, OpenSSL 3, GNU coreutils, ShellCheck and a C
compiler first. Verification is bounded by a hard 300-second process-group SIGKILL
deadline, including cold project builds. No override, grace period, partial pass,
missing check or cached acceptance substitutes for a pass. Every discovered module
and native entry retains compilation and source/compiled/axiom/route admission.
Mathlib umbrella imports are forbidden; import specific dependencies.

CI runs the same command on the exact proposed head. Resolve required checks,
signature/PR protections and review conversations before merging; never bypass
protections. Record actual results and material limits in one concise PR.
Proof/module counts describe scope, not correctness. Successful raw logs need
no permanent receipt. Optional diagnostics are not ordinary acceptance substitutes.

Public source has an explicit profile and no historical studies, private capture
or calculator executables. Shared schema and analysis definitions remain where
proofs use them. Never select reduced verification because a file is absent.
No release, visibility change, external submission or scientific campaign follows
from permission to prepare or merge code. Keep local run state and credentials
out of commits. Use [SECURITY](SECURITY.md) for vulnerability reporting.
