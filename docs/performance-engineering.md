# Performance engineering in service of the mission

This is the durable policy for balancing execution efficiency with algorithmic
progress, correctness and scientific qualification. Apply it when selecting
work, designing shared abstractions and reviewing changes. The scoped work item
owns priorities and budgets.

## What performance is for

[Oak Lab's mission page, as archived](https://web.archive.org/web/20260909143403/https://oaklab.ai/mission), speaks of continual, batch-size-one
learning and planning in real time with low compute and energy use. Correctness,
useful learning and feasible resource consumption guide the requirements below.

Performance work is warranted when it enables an identified research or
operating requirement, prevents a material resource regression, or addresses an
explicitly prioritized performance contract. Prioritize costs that affect the
intended research or interaction.

## Select and bound the work

Set performance requirements from each research or operating milestone's
throughput, latency and memory needs. Each specified operating contract retains
its own acceptance criteria.

Before substantial optimization, state the decision in the active issue:

- **Need:** the research milestone or operating requirement affected, with the
  relevant workload, scale and host assumptions. Specify the needed experiment
  completion time or learning throughput, memory ceiling and interaction
  latency where applicable. Distinguish startup from steady execution and
  finite observations from lifetime requirements. Do not invent owner limits.
- **Evidence:** whether existing derivations and observations already answer
  the question. If adequacy is unknown, identify the smallest authorized check
  that can resolve it; do not presume either adequacy or a blocker. For an
  irreducibly empirical physical effect, name the platform-dependent `UNKNOWN`
  and why deduction cannot settle it.
- **Cost and decision:** the expected enabling benefit, competing algorithmic
  or qualification work, and a bounded budget for implementation, proofs,
  review and measurement. Include assistant compute cost and recurring
  maintenance, not only benchmark duration. Set acceptance, regression,
  uncertainty and stopping rules before collecting decision-bearing results.

When the required operating budget is met, prioritize the next authorized
algorithmic or qualification milestone. An explicit stronger performance
contract still requires its own resolution; operational adequacy does not
silently waive it. When performance blocks that milestone, prefer a reusable
numeric, storage, ownership or traversal improvement over repeated tuning of
individual algorithms. Routine implementation should follow the practices below
without requiring a new profiling campaign or separate approval for every edit.

Stop a bounded effort when its decision is resolved, its declared stopping rule
is reached or its budget expires. Reject candidates under the declared rules;
continue only within the remaining authorized scope and budget. Keep useful
results and limitations in the existing record.
Do not automatically renew the budget or replace rejected candidates with a
broader redesign. If recurring bespoke tuning makes the implementation strategy
too costly, present that architectural tradeoff to the owner before more work.
There is no fixed percentage of project effort reserved for optimization.

## Lean implementation practices

Check the pinned compiler and runtime when applying Lean's native execution
guidance. Inspect the generated behavior for the workload being optimized.

- **Ownership:** consume state so updated arrays can be uniquely owned. Avoid
  retaining an entire prior state through a closure or observer when only small
  metadata is needed. Sharing is legitimate when required by semantics; inspect
  generated reuse/copy paths before attributing a cost to source syntax.
  [Reference counting](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Reference-Counting/).
  In `lean/Acorn/FeatureConsumers.lean`, `Acorn.Features.takeOut` reads element
  `index` and overwrites slot `index` with its stand-in argument, and is marked
  `@[noinline]` so both operations precede caller use of the taken element. Both
  `Acorn.Features.detachedUpdate` (called by option-table updates in
  `Acorn.Handcrafted.TemporalControl` and `Acorn.Handcrafted.DrawFirst`, with
  value equality proved in `Acorn.Features.detachedUpdate_eq`) and
  `Acorn.Features.detachedUpdateCosted` (called by `Controller.creditStepCosted`
  in `lean/Acorn/Sarsa.lean`, whereas `Controller.stopStepCosted` and
  `Controller.terminalCosted` map all rows via `Costed.mapVector`) pass the next
  slot's element `(index.val + 1) % size` as the stand-in into slot `index`—for
  example, on `[a, b]` at index `0`, `takeOut` reads `a` and produces `[b, b]`—so
  slot `index` temporarily holds a second reference to the next element while
  the update runs before overwriting slot `index` with the updated element. The
  runtime can then reuse the taken element's storage in place only under three
  unchecked conditions: the vector is uniquely referenced by that call (`RC = 1`),
  the element appears in no other slot and has no other reference, and `size > 1`;
  where any fails, the update writes to copies with the same result. Likewise,
  `Acorn.Features.Skill.stepTemporal` destructures the policy step's result
  before crediting the model under the same unproved runtime-exclusivity
  expectation. `@[noinline]` on `Acorn.SwiftTdDriver.execute`,
  `Acorn.ControlDriver.execute`, `Acorn.FeatureDriver.execute`, and
  `Acorn.TemporalDriver.execute` keeps initial learner/consumer storage
  dynamically allocated instead of hoisted into shared process-global terms,
  whereas `@[noinline]` on `Acorn.TemporalDriver.diagnosticAssignment` keeps
  that entry's route linear.
- **Arithmetic:** favor native machine scalars through hot calculations when
  their correspondence with the admitted representation is established. Avoid
  repeated word/float conversions where a shared, proved implementation can
  preserve every required rounding boundary and exceptional-value behavior.
  Native arithmetic does not authorize reassociation, fast math, altered NaN
  semantics or replacing a specified numerical recipe with another function.
  [Floating-point numbers](https://lean-lang.org/doc/reference/latest/Basic-Types/Floating-Point-Numbers/).
  In `lean/Acorn/Encoding.lean`, raw `Binary32` and `Binary64` values stay as
  raw machine words without passing through Lean core's Float32.ofBits or
  Float.ofBits (whose logical models canonicalize NaNs), `Binary32.key` assigns
  both `±0` encodings key `0`, and `Binary32.Finite` and `Binary64.Finite`
  `Decidable` instances apply *UInt32.decLt* and *UInt64.decLt* directly rather
  than *inferInstanceAs* (which Lean v4.36.0 unfolds into `Nat` comparisons).
  In `lean/Acorn/Arithmetic.lean` and `lean/Acorn/Conversion.lean`, native
  hardware operations may choose NaN sign and payload unlike Lean's
  canonicalizing float model, no FMA or custom native override is used,
  `Conversion.ofInt` converts the integer's magnitude through `UInt64`
  (*natAbs.toUInt64*), so its magnitude wraps modulo `2^64` rather than at the
  signed 32-bit `Conversion.toI32` round-trip domain (`CurrentFloat.toI32_ofInt`;
  for example, `2^31` lies outside signed 32-bit range yet converts exactly, and
  `CurrentOrder.numerical64_ofInt` proves exactness for `|value| < 2^53`), while
  `Conversion.ofI64Word` avoids intermediate arbitrary-precision `Int`
  allocation, widening/narrowing aligns IEEE-754
  fields with exact bias/shift offsets (`874` subnormal bias, `896` normal
  exponent offset, `897` smallest normal biased exponent, `925`/`926` subnormal
  shifts, `1075` binary64 integer bias, and `1150` normal overflow bound), and
  `Rounding.nearestEven` / `Rounding.wordShift64` isolate nearest-even integer
  quotient rounding. In `lean/Acorn/Portable.lean`, `Portable.exp` keeps Int32
  range reduction via `Portable.expReduceWord` / `Portable.expScaleWord`
  (`Portable.exp_eq_spec`) to avoid `Int`, modulo, `Option`, and pair
  allocations while preserving input NaN words (`Portable.exp_nan_word`),
  `Portable.ln` maps NaN and negative inputs to positive quiet NaN
  `0x7fc00000`, and `Portable.powLoop` / `Portable.powLoopWord` multiply the
  accumulator before squaring (`Portable.powLoop_zero` returns without reading
  the base). `Word.multiplyHigh` (`lean/Acorn/Word.lean`) computes the unsigned
  128-bit high word from four 32-bit `UInt64` limb products (`Word.multiplyHigh_eq_spec`
  against `Word.multiplyHighSpec`).
- **Storage:** inspect element layout and boxing in large containers. A scalar's
  compact representation does not imply a generic array has that layout;
  boxing may use a tagged immediate rather than a separate allocation. Choose
  reusable storage with checked initialization/read/write/admission
  correspondence. Packed storage is a candidate with proof and measurement
  costs, not an automatic recommendation to redesign every array.
  [Boxing](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Boxing/).
  In `lean/Acorn/State.lean`, `ValueRule.domain90`, `ValueRule.domain95`,
  `ValueRule.domain99`, and `ValueRule.domainDifferential` pre-evaluate interval
  bounds once so `Weight.project` avoids recomputing horizons on every write,
  `LogStepSize.alphaAfter` reuses a memoized step size before falling back to
  `Portable.exp`, `NumericState.stepSize` is marked `@[inline]`, and
  `StepSizeRails.ofConfig` kernel-reduces over the three roles (`maxRecDepth 8192`).
  In `lean/Acorn/RankedFeatures.lean`, `RankedFeatures.position` reads the array
  size of `slots` directly instead of re-evaluating `Acorn.Features.rankWidth`.
- **Work and observation:** preserve required order while avoiding unnecessary
  intermediate collections, repeated invariant work and diagnostics with no
  consumer. Neither immutable code nor lists are inherently defects. Reuse
  shared folds and helpers when their semantics and lowering fit the need.
- **Execution evidence:** use the optimized native route and existing admitted
  flags. Inspect generated code for the specific unresolved cost; use bounded
  measurements for physical effects. A reduction in calls or instructions
  alone does not establish elapsed-time or peak-memory improvement.

Proof terms and subtype predicates are erased; required admission checks and
computational representations can still cost work. Keep refinements and prove
correspondence at reusable implementation boundaries. Do not weaken guarantees
to improve a benchmark. [Subtypes](https://lean-lang.org/doc/reference/latest/Basic-Types/Subtypes/).
Shorter elapsed time or lower RSS is not an energy proof.

## What our evidence supports

The current implementation uses optimized native execution and consuming runner
ownership, but shared arithmetic still crosses word/float representations and
many numeric fields use generic arrays. See [Arithmetic](../lean/Acorn/Arithmetic.lean),
[Conversion](../lean/Acorn/Conversion.lean),
[State](../lean/Acorn/State.lean) and
[Attempt](../lean/Acorn/Host/Attempt.lean).

Use workload-specific observations to identify infrastructure worth examining.
State the measured scope, unresolved costs and relevant implementation contracts.
Keep results with their owning work item. Scientific benefit follows the
[qualification and evidence requirements](prior-art-review.md#default-promotion-and-demotion).

Other explicit commitments remain binding until the owner changes them. Changes
to execution language or trusted boundaries require an owner decision and
correspondence arguments connecting the required guarantees to the new execution.

## Evidence for performance claims

Keep contributor verification economical within its full admission contract.
The merge gate reuses only pinned dependencies, as described in
[verification](verification.md#build-and-source-inventory): the no-mistakes
pipeline reuses provisioned outputs only while a run's toolchain, lock and pin
files match the base commit. A changed set of FloatLib modules that the proof bridge
imports keeps the same locked dependencies, and Lake builds only the added ones.
Provisioning is stored apart from every run's checks, so a project failure does
not discard useful provisioning work. On GitHub the verification workflow stores
nothing between runs: each run provisions the dependencies from their pinned
sources. Project outputs still build cold in every
gate run. One run of `./scripts/verify.sh` bounds the cold build and every check
with one fixed deadline. The gate runs the command twice, each run under its own
deadline: `./scripts/verify.sh build-executing` selects every module outside
`AcornVerif` except `AcornTools.AxiomPins`, and every executable. It builds these
targets and their dependencies, with native objects where applicable. The
complete command selects every tracked module, including the proof library
and axiom pins, and reuses outputs only where Lake's traces match. So in the gate
the cold build and the checks no longer share one deadline. Reuse Lake's
source/toolchain-validated configuration trace and batch independent source
hashes while checking every result's filename and digest. Neither mechanism
reuses a previous verification result or substitutes a digest for correctness.
Import only the mathematics and tooling a module uses. Order build requests so
that none delays the scheduling of independent work, as the gate's
[build request order](verification.md#build-and-source-inventory) does;
request order must retain the complete tracked module and target inventory.
Within one verification process, reuse imported compiler data across consumers
and isolated entry environments. Retain compiler ownership, duplicate-declaration
refusals and each entry's actual import closure. Shared memory must outlive every
consumer; never free one environment's regions while a sibling still uses them.
After ordinary verification passes in `scripts/gate.sh`, run the post-verification
checks (`lean-intent`, `frame-check` and the SHA-256-verified `no-comments`
check, after bounded upfront admission refusing Lake reconfiguring flags)
sequentially in a background subshell beside the Regula audit, sizing
`no-comments` worker concurrency (`clamp(cpus - 1, 1, 6)`) to leave a core for
Regula's single-threaded kernel replay and limit concurrent worker parallelism
(note this caps worker count rather than enforcing a hard combined-memory
bound). The pinned `lean-no-comments` v0.3.1 release reuses persistent worker
processes across files sharing an identical import header; exact inventory
parity with v0.2.0 is checked on the repository tree, while cross-file
independence from process-global mutable state within a batch remains an
explicit upstream trust assumption documented in
[verification](verification.md#build-and-source-inventory). Enforce explicit
hard ceilings on every check, step and job in `scripts/gate.sh` and
`.github/workflows/verify.yml`, and emit `$GITHUB_STEP_SUMMARY` phase timings
plus `::warning::` budget alerts so CI duration regressions surface immediately
without skipping, narrowing or weakening the checked properties.

Apply the [proof-first policy](../AGENTS.md#correct-by-construction) to correctness
and resource claims. Pure analysis definitions state contracts over explicit
inputs and hypotheses. Physical measurements name their workload, environment
and observations under the [scientific evidence guidance](../CONTRIBUTING.md#scientific-evidence).
