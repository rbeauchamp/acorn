# Performance engineering in service of the mission

This is the durable policy for balancing execution efficiency with algorithmic
progress, correctness and scientific qualification. Apply it when selecting
work, designing shared abstractions and reviewing changes. The scoped work item
owns priorities and budgets.

## What performance is for

[Oak Lab's mission](https://oaklab.ai/mission) includes continual, batch-size-one
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
- **Arithmetic:** favor native machine scalars through hot calculations when
  their correspondence with the admitted representation is established. Avoid
  repeated word/float conversions where a shared, proved implementation can
  preserve every required rounding boundary and exceptional-value behavior.
  Native arithmetic does not authorize reassociation, fast math, altered NaN
  semantics or replacing a specified numerical recipe with another function.
  [Floating-point numbers](https://lean-lang.org/doc/reference/latest/Basic-Types/Floating-Point-Numbers/).
- **Storage:** inspect element layout and boxing in large containers. A scalar's
  compact representation does not imply a generic array has that layout;
  boxing may use a tagged immediate rather than a separate allocation. Choose
  reusable storage with checked initialization/read/write/admission
  correspondence. Packed storage is a candidate with proof and measurement
  costs, not an automatic recommendation to redesign every array.
  [Boxing](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Boxing/).
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
CI caches only pinned dependencies, keyed by runner image family, architecture,
toolchain and dependency manifest; an exact hit avoids repeated provisioning.
Admit restored dependencies and save newly provisioned dependencies before the
project gate, so a project failure does not discard useful provisioning work.
Project outputs still build cold under the fixed deadline. Reuse Lake's
source/toolchain-validated configuration trace and batch independent source
hashes while checking every result's filename and digest. Neither mechanism
reuses a previous verification result or substitutes a digest for correctness.
Import only the mathematics and tooling a module uses. Request native targets
early enough that their compilation can overlap independent proof builds;
request order must retain the complete discovered module and target inventory.
Within one verification process, reuse imported compiler data across consumers
and isolated entry environments. Retain compiler ownership, duplicate-declaration
refusals and each entry's actual import closure. Shared memory must outlive every
consumer; never free one environment's regions while a sibling still uses them.

Apply the [proof-first policy](../AGENTS.md#correct-by-construction) to correctness
and resource claims. Pure analysis definitions state contracts over explicit
inputs and hypotheses. Physical measurements name their workload, environment
and observations under the [scientific evidence guidance](../CONTRIBUTING.md#scientific-evidence).
