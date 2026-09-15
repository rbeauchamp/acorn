# Performance engineering in service of the mission

This is the durable policy for balancing execution efficiency with algorithmic
progress, correctness and scientific qualification. Apply it when selecting
work, designing shared abstractions and reviewing changes. The explicitly scoped work item owns priorities and budgets; this document
is not another backlog.

## What performance is for

[Oak Lab's mission](https://oaklab.ai/mission) includes continual, batch-size-one
learning and planning in real time with low compute and energy use. Correctness,
useful learning and feasible resource consumption all matter. The mission's
efficiency aspirations are not demonstrated properties of Acorn. Language
choice, proof counts and isolated speedups are not measures of research success.

Performance work is warranted when it enables an identified research or
operating requirement, prevents a material resource regression, or addresses an
explicitly prioritized performance contract. A language-comparison ratio alone
does not determine which mission-critical work should happen next. Conversely,
a large slowdown must not be dismissed as premature optimization when it makes
the intended research or interaction impractical.

## Select and bound the work

Set performance requirements from each research or operating milestone's
throughput, latency and memory needs. No blanket cross-language ratio is a
current acceptance gate. This does not establish performance adequacy, parity
or a waiver of a separately specified operating contract.

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
  and why deduction cannot settle it. An unresolved proof obligation does not
  become empirical because its proof is difficult.
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

Lean provides documented techniques for efficient native execution. They do not
guarantee Rust parity for this agent or establish equal development cost for
dense numerical workloads. Check the pinned compiler/runtime when applying the
upstream guidance; an idiom's spelling does not prove its generated behavior.

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
The proof-first ordering, compiled-route checks and review requirements in
[AGENTS.md](../AGENTS.md) remain authoritative. Measurement is not a substitute
for correctness proofs; shorter elapsed time or lower RSS is not an energy proof.

## What our evidence supports

The current implementation uses optimized native execution and consuming runner
ownership, but shared arithmetic still crosses word/float representations and
many numeric fields use generic arrays. See [Arithmetic](../lean/Acorn/Arithmetic.lean),
[Conversion](../lean/Acorn/Conversion.lean),
[State](../lean/Acorn/State.lean) and
[Attempt](../lean/Acorn/Host/Attempt.lean).

An authorized observation may identify infrastructure to examine. Such observations neither establish an unavoidable Lean slowdown nor show that
the remaining gap has an easy remedy. Partial profiles do not fully attribute
the gap; finite comparisons do not prove whole-agent cross-language equivalence
or lifetime resource bounds. Do not duplicate benchmark tables here or create a
new study for ordinary engineering. Scientific benefit remains subject to its
own [qualification and evidence requirements](prior-art-review.md#default-promotion-and-demotion).

Other explicit commitments remain binding until the owner changes them. Pausing
their implementation is not completion. Changing execution language or trusted
boundaries requires an owner decision and accounting for the guarantees that must reach the new execution;
existing Lean proofs do not automatically verify a Rust replacement.

## Proof before performance claims

Use types, derivations and implementation-linked universal proofs for identities,
bounds and state legality. A sampled result or mutation digest cannot establish
them. Prefer structural arguments to certified re-execution; estimate the initial
and recurring cost before choosing reflection.

Measurements answer irreducibly empirical questions about a specified workload,
platform or regime. State why no derivation reaches the claim, define the smallest
informative design and fix acceptance rules, budgets and uncertainty handling
before execution. Difficulty proving a property does not make it empirical.

This source release includes no historical performance observations or certified
benchmark verdict. Retained pure analysis/proof definitions are contracts over
inputs and hypotheses, not evidence that those inputs were observed. No useful
learning, physical performance parity or current default qualification is claimed.
Follow the [scientific evidence guidance](../CONTRIBUTING.md#scientific-evidence).
