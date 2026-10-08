# Working on Acorn

Acorn pursues Oak Lab's mission: agents that learn from experience to achieve
goals in big worlds. The Alberta Plan guides its work on continual learning and
planning in Lean. [Design](docs/design.md) owns implementation coverage;
[prior-art review](docs/prior-art-review.md) owns technical admission and default
qualification; [learned-only binding](docs/learned-only-binding.md) owns departures.
Core calls select an explicit research profile. The prior-art register records
current qualification decisions.

Describe implemented behavior, proof hypotheses and research questions directly;
use citations for attribution and concrete results for claims. Omit affiliation
disclaimers and repeated assurances about what the project is not. Write the
README and public docs for a first-time reader: define project terms such as
research profile in plain English before relying on them.

## Correct by construction

An ounce of math is worth a pound of computation. Identify semantics, state
invariants, hypotheses and implementation linkage before choosing work.
Prefer types making illegal states unrepresentable, derivation, exhaustive
compiler checks over closed types, universal proofs, then derived guards.
Enumerate every construction, deserialization (including checkpoint load), update
(including reset and retirement) and entry-point boundary; enforce the invariant
at each. Bounding an output alone does not bound stored state.

Proofs must concern the executed definitions or a checked correspondence.
Distinguish finite-word arithmetic from mathematical integers, rationals and reals.
State concurrency, serialization, native, compiler and OS assumptions explicitly.
No custom axiom, sorry, unsafe/partial application definition, panic or unchecked
native replacement enters governed code. Reviewed tooling and the narrow C fsync
primitive are explicit trust boundaries.

There are no scenario tests. Counterexamples diagnose missing invariants or
contracts; close the whole defect class with a gate or proof covering every
instance, not only those found. Prefer structural/analytic proofs to
reflection. Before certified re-execution, estimate initial and recurring proof
cost beside the proposed observation and obtain an owner decision if it does
not cost clearly less. Difficulty proving a property does not make it empirical.

- Measure only irreducibly empirical claims with explicit scope, budget,
  uncertainty and prospective decision criteria.
- Label an unresolved empirical quantity, including a gap between prediction and
  observation, UNKNOWN with the reason deduction cannot settle it. Report
  measurements as observed with their run and configuration, and estimates as
  estimates, not bounds.
- Follow [scientific evidence guidance](CONTRIBUTING.md#scientific-evidence) for
  protocols and recordkeeping.
- A digest is a mutation detector, not correctness or scientific evidence.
- Do not rerun learning or promote defaults during ordinary engineering.
- Preserve original observations separately from presentations.

## Learned-only and research admission

Every hand-authored action-path bias requires its actual departure declaration.
Review checks each provenance declaration against the producing code. Source and
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
Name files and modules for their current role; rename or remove artifacts named
for a retired implementation.
Fix authorized concrete defects, preserve unrelated work and ask before materially
broader scope or new follow-up issues. Prefer small coherent changes over rewrites.
Apply [performance engineering](docs/performance-engineering.md) to performance-sensitive work; preserve proofs and
admission predicates. Do not replace unresolved proof obligations with measurements.

Provision pinned Lean/Mathlib v4.34.1, FloatLib, Verso, OpenSSL 3, GNU coreutils, ShellCheck and a C
compiler first. A fresh worktree has no `lean/.lake` dependencies; run
`(cd lean && lake exe cache get && lake build Mathlib regula/lint regula/axiomGate floatlibBridge regulaInterface)` and then
`(cd site && lake build verso/VersoManual verso/VersoManual:shared)` there before verifying.
Then run the complete command in the actual Git checkout:

```sh
./scripts/verify.sh
```

- Each run is bounded by a hard 360-second process-group SIGKILL deadline,
  including the cold project build when outputs are cold. CI runs
  `./scripts/verify.sh build-executing` first, under its own deadline, so there
  the cold build and the checks no longer share one.
- No override, grace period, partial pass, missing check or cached acceptance
  substitutes for a pass.
- Every discovered module and native entry retains compilation and
  source/compiled/route admission.
- Mathlib and FloatLib umbrella imports are forbidden; import specific dependencies.
- FloatLib is a proof dependency: only the proof bridge imports it, and no
  executing module may.

Sign commits and preserve license notices. CI runs the same command on the exact
proposed head and, as a second required job outside that deadline, the Regula
audit `./scripts/lean.sh lint`. Resolve required checks,
signature/PR protections and review conversations before merging; never bypass
protections. Record actual results and material limits in one concise PR.
Proof/module counts describe scope, not correctness. Successful raw logs need
no permanent receipt. Optional diagnostics are not ordinary acceptance substitutes.

- Every maintained source belongs to a library that the Regula manifest claims
  or to one explicit ownership inventory.
- Shared specification and analysis definitions remain where proofs use them.
- A missing file fails verification; it never selects a smaller suite.
- No release, repository creation, visibility change, external submission or
  scientific campaign follows from permission to prepare or merge code. Before
  creating a public-bound repository or its first commit, show the owner the
  exact local tree and wait for explicit approval.
- Keep local run state and credentials and private or proprietary material out
  of commits.
- Use [SECURITY](SECURITY.md) for vulnerability reporting.
