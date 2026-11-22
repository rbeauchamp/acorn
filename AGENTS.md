# Working on Acorn

Acorn's mission is to discover and implement algorithms that enable agents to
achieve goals in big worlds. The Alberta Plan guides its work on continual learning and
planning in Lean. [Design](docs/design.md) owns implementation coverage;
[prior-art review](docs/prior-art-review.md) owns technical admission and default
qualification; [learned-only binding](docs/learned-only-binding.md) owns departures;
[architectural intent](docs/architectural-intent.md) and
[architectural foundation](docs/architecture-foundation.md) own the modular 4-layer
federated and always-on live-upgrade target architecture.
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
native replacement enters governed code. Reviewed tooling and the narrow C file-sync
primitive are explicit trust boundaries.

There are no scenario tests. Counterexamples diagnose missing invariants or
contracts; close the whole defect class with a gate or proof covering every
instance, not only those found. Prefer structural/analytic proofs to
reflection. Before certified re-execution, estimate initial and recurring proof
cost beside the proposed observation and obtain an owner decision if it does
not cost clearly less. Difficulty proving a property does not make it empirical.

Mathematics comes first. A run of the agent, a study or any other evaluation
taken as an answer is the last resort, whatever its name: a measurement, a smoke
test or a diagnostic that only chooses a direction. What deterministic code does
at a fixed seed is a mathematical question. Before proposing a run, state the
question and why derivation or proof cannot answer it effectively and
efficiently, with the cost of each, and obtain the owner's authorization.
Stepping the agent or one of its learners over a sequence of percepts by any
means, whether the binary, evaluation inside Lean or a re-implementation in any
language, is a run. Proof search is computing a value that a theorem in the
pull request then checks, and nothing else is.
[What counts as a run](CONTRIBUTING.md#what-counts-as-a-run) gives the cases
and what every pull request lists of the computations made on the agent.
No step of work on a change starts a program that steps the agent or one of its
learners over percepts, whatever the step is for, unless the owner's
authorization for that run is stated in the change's intent;
[running a program](CONTRIBUTING.md#running-a-program) says where the
invocations that may be driven without that authorization are listed, and where
to read which files that such a run produced no step opens.

The habit of evaluation returns through specifications. When a specification
seems to need a run to check it, treat that first as a defect in the
specification and restate it as what the algorithm must maintain, as
[proof-shaped specifications](CONTRIBUTING.md#proof-shaped-specifications) says.

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

Every hand-authored action-path bias requires its actual departure declaration,
except as [learned-only binding](docs/learned-only-binding.md) says of a state
mechanism submitted under the frame of a learned-state result.
Review checks each provenance declaration against the producing code. Source and
compiled ownership enforce the learned/host/handcrafted boundary and explicit
composition roots. The viewer observes telemetry and sends lifecycle stop only;
it cannot alter learning decisions.

Verify citations against the actual source before adding them. Paper-based code
and proofs must identify author, work, venue/year and exact equation, section or
theorem in Acorn's documentation (`docs/prior-art-review.md`, `docs/design.md`,
all checked by `corpus-audit` via `AcornCorpus.prose`, or
`site/AcornDocs/Verification.lean`, checked through `docs/verification.md`),
rather than adding comments in Lean files (while legacy in-source citations drain
via `comment-ratchet.json`). Reproduce derivations
and explain material adaptations, their rationale, semantic consequences and
composition compatibility there. Fix defects found in prior art, with a characterization theorem or identity and
present-tense explanation. Do not replicate a known error for fidelity.
Implementing a published algorithm is prior-art work and is never called or
counted as a discovery;
[prior art and discovery](docs/prior-art-review.md#prior-art-and-discovery)
states both terms and how work between them is judged.

Technical admission requires soundness, fit to the continuing setting, semantic
compatibility/nondegeneracy, affordable work/storage and sufficient specification.
Promotion requires separate prospective evidence and an explicit decision. Keep
negative and inconclusive evidence honest; exclusion is not a positive result.

## Review and delivery

Use the shipped proof-review standard and pr-review-toolkit for review-and-fix.
For that review, which the author runs, one independent reviewer is the
default; add a specialist only for a concrete uncertainty. It does not decide
when work is complete and discharges no review that Acorn requires. The
[review protocol](CONTRIBUTING.md#review-protocol) does, for every author:
every pull request requires an independent review, chosen by what it claims or
changes and by whether it passed the maintainers' validation pipeline, never by
who wrote it. A pull request that claims a result gets the referee's review; one
that claims no result counts the validation pipeline's review where it passed
that pipeline, and gets the referee's review or the short review where it did
not. Any model reviewer must belong to another model family than every model
that did or fixed the work, and the applicable assignment rule determines when
an uninvolved person is eligible. Every review is bounded by
[three rounds of review](CONTRIBUTING.md#three-rounds-of-review).
Use ux-review for viewer behavior or [viewer specification](docs/viewer-ux.md) changes, including
rendered-state inspection. The skills under .agents/skills are maintained
contributor interfaces.

Lean source files across `lean/` (including `lean/lakefile.lean`) and `site/`
code (`site/AcornSite.lean`, `site/AcornSite/`, and `site/Main.lean`, excluding
`site/AcornDocs.lean` and `site/AcornDocs/` Verso `#doc` prose) are governed by
the ratcheted `no-comments` ban
(`.no-comments.json`, `comment-ratchet.json`, pinned in `lean/no-comments.pin`):
do not add `--`, `/- -/`, `/-- -/`, or `/-! -/` comments to scoped `.lean`
files, and drain legacy comments monotonically toward `[]`. Record new and migrated semantics, decision records, and rationale in `docs/`
(`docs/design.md`, `docs/prior-art-review.md`, automatically
checked by `corpus-audit` via `AcornCorpus.prose`, or
`site/AcornDocs/Verification.lean`, checked via `docs/verification.md`) rather
than in Lean source comments; Git records chronology.
Name files and modules for their current role; rename or remove artifacts named
for a retired implementation.
Fix authorized concrete defects, preserve unrelated work and ask before materially
broader scope or new follow-up issues. Prefer small coherent changes over rewrites.
Apply [performance engineering](docs/performance-engineering.md) to performance-sensitive work; preserve proofs and
admission predicates. Do not replace unresolved proof obligations with measurements.

Provision pinned Lean/Mathlib v4.36.0, FloatLib, lean-intent, Verso, OpenSSL 3, GNU coreutils, ShellCheck and a C
compiler first. A fresh worktree has no `lean/.lake` dependencies; run
`(cd lean && lake exe cache get && lake build Mathlib regula/lint floatlibBridge regulaInterface leanIntentBridge leanIntentNative)` and then
`(cd site && lake build verso/VersoManual verso/VersoManual:shared)` there before verifying.
Then run the complete command in the actual Git checkout:

```sh
./scripts/verify.sh
```

- Each run is bounded by a hard 360-second process-group SIGKILL deadline,
  including the cold project build when outputs are cold. The merge gate runs
  `./scripts/verify.sh build-executing` first, under its own deadline, so there
  the cold build and the checks no longer share one.
- No override, grace period, partial pass, missing check or cached acceptance
  substitutes for a pass.
- Every discovered module and native entry retains compilation and
  source/compiled/route admission.
- Mathlib and FloatLib umbrella imports are forbidden; import specific dependencies.
- FloatLib is a proof dependency: only the proof bridge imports it, and no
  executing module may.

Sign commits and keep `LICENSE` as Acorn's copyright and license notice (do not
add per-file MIT headers to Lean sources under the `no-comments` policy;
existing non-Lean notices such as `lean/os/checkpoint-sync.c` stay). The merge
gate, `./scripts/gate.sh`, which the no-mistakes pipeline runs on the exact
proposed head before a pull request opens, runs the same command and, outside
that deadline, the Regula audit `./scripts/regula.sh`, lean-intent's
confirmation and implementation checks (`lean/AcornTools/Intent.lean`), the
check of each target's pinned frame (`lean/AcornTools/Frame.lean`), and the
pinned `no-comments` ratchet check (`.no-comments.json`,
`comment-ratchet.json`, `lean/no-comments.pin`); GitHub runs the same checks on
a pull request's
head commit when it is opened or reopened and at every push to it
(`.github/workflows/verify.yml`). Resolve required checks,
signature/PR protections and review conversations before merging; never bypass
protections. Record actual results and material limits in one concise PR.
Proof/module counts describe scope, not correctness. Successful raw logs need
no permanent receipt. Optional diagnostics are not ordinary acceptance substitutes.

- Every maintained source belongs to a library of `lean/lakefile.lean` or to one
  explicit ownership inventory.
- Shared specification and analysis definitions remain where proofs use them.
- A missing file fails verification; it never selects a smaller suite.
- No release, repository creation, visibility change, external submission or
  scientific campaign follows from permission to prepare or merge code. Before
  creating a public-bound repository or its first commit, show the owner the
  exact local tree and wait for explicit approval.
- Keep local run state and credentials and private or proprietary material out
  of commits.
- Use [SECURITY](SECURITY.md) for vulnerability reporting.
