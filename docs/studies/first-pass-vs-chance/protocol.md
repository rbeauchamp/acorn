# First-pass achievement against a uniform-random policy: protocol

This is the protocol of study `first-pass-vs-chance`, the observation that
[U6](../../baseline-assessment.md#conformance-sequence) of the baseline
assessment asks for ([#12](https://github.com/rbeauchamp/acorn/issues/12)).
It fixes every choice below before any outcome exists.

**Protocol revision 1. Status: written, not authorized, not run.** Writing this
protocol does not authorize execution. The
[scientific evidence guidance](../../../CONTRIBUTING.md#scientific-evidence)
requires the owner's explicit authorization before the first run.

## Question

Does the `ranked` agent achieve more of the standard curriculum's goals than a
policy that chooses every action uniformly at random, when each makes one pass
through the curriculum from the same initial world?

Terms used below:

- A **seed** is the 64-bit number given to `--seed`. It fixes the generated
  world, the two reach targets and every pseudo-random stream of the world, the
  agent and the comparator.
- The **standard curriculum** is the 13 goals of `rawStandardCurriculum`, in
  order, numbered from 0: survive 200 steps, collect 2 wood, collect 2 stone,
  reach a near target, collect 4 wood, craft an axe, collect 3 food, reach a far
  target, collect 2 gold, craft a boat, collect 8 wood, survive 800 steps,
  collect 4 gold.
- An **attempt** installs one goal and runs until the goal is satisfied or a
  step cap is reached. A **pass** is one attempt at each goal in order. The
  world is not reset between attempts: position, inventory and energy carry on.
- An arm **achieves** a goal when the goal is satisfied within the attempt.

## What derivation settles

Claim labels follow the
[baseline assessment](../../baseline-assessment.md): machine-checked, argued,
assumed and UNKNOWN.

1. **The comparator's action law.** *Argued from a machine-checked identity.*
   `BaselineAttempt.tick` draws one `Xoshiro256.nextBelow` word with count 9 and
   maps it through `Action.fromIndex`; it reads no observation.
   `nextBelow_quotient` proves that the drawn index is ⌊9w / 2⁶⁴⌋ for the
   generator's output word w. Index a is drawn exactly when
   a·2⁶⁴/9 ≤ w < (a+1)·2⁶⁴/9, which holds for ⌈(a+1)·2⁶⁴/9⌉ − ⌈a·2⁶⁴/9⌉ words.
   Since 2⁶⁴ = 9c + 7 with c = 2 049 638 230 412 172 401, that count is c for
   wait and eat and c + 1 for the other seven actions. Under a uniform output
   word (assumed), every action has probability within 2⁻⁶⁴ of 1/9. Only the
   comparator's task outcomes need observing.
2. **The two survive goals are independent of the policy.** *Argued from
   machine-checked lemmas.* `World.setGoal` sets the goal's origin to the
   current time. Each successful step advances the clock by one
   (`World.step_clock`), leaves the goal and its origin unchanged
   (`World.step_goal`) and reports completion from the successor state
   (`World.step_completion`). `Goal.observe` gives a survive goal the remaining
   time, required minus elapsed. So every action sequence satisfies goal 0 at
   its step 200 and goal 11 at its step 800, whenever the cap is at least 800
   and no world step is refused. Both arms achieve both goals; they carry no
   information about the question.
3. **The arms are matched.** *Argued from the definitions.* Both start from
   `World.initial` of the same world configuration, take the same curriculum in
   the same order, install each goal with `World.setGoal`, make one attempt per
   goal under the same cap, stop an attempt at the first step whose successor
   satisfies the goal, and carry the physical world from goal to goal
   (`runRandomBaseline`; `atAttemptBoundary` with one attempt per goal). They
   differ in the policy and in the agent's learning.
4. **No task reward arrives before achievement.**
   `StepResult.reward_completion` (machine-checked) makes the reward 1 on the
   achieving step and 0 on every other. Within an attempt the task reward
   therefore says nothing about the installed goal until the attempt is over;
   the achieving reward is carried into the next attempt
   (`Attempt.start_carried`). What the agent can bring to a goal in its first
   pass is what it learned on earlier goals.
5. **A run is a function of its command and binary.** *Argued from the types;
   the compiled binary, the Lean runtime and the operating system are trusted
   boundaries.* The agent's step (`AgentCallbacks`), the world's step
   (`World.step`) and the comparator (`runRandomBaseline`) are pure functions,
   so they read no clock and no entropy. Observers receive values and return
   nothing to the agent. Clock readings reach only telemetry, the printed
   campaign summary and the CSV footer.
6. **Work.** *Argued from item 2.* Each arm takes at most
   11 × 3000 + 200 + 800 = 34 000 steps per seed.

**UNKNOWN: the frequency with which the agent out-achieves the comparator.**
For one seed the outcome is a fixed computation, but the only known way to
evaluate it is to execute it: up to 34 000 updates of about three million
learned parameters in binary32 arithmetic, each depending on the states the
agent's own earlier choices reached in a generated terrain. No invariant of the
definitions bounds achievement, and a kernel-checked evaluation would re-execute
the same stream at greater cost. Over the population of 2⁶⁴ seeds the frequency
cannot be enumerated. It is estimated from a random sample of seeds.

## Design

| | Agent arm | Comparator arm |
|---|---|---|
| Policy | `ranked` research profile, discounted criterion, expectation planning | Uniform over the nine actions to within 2⁻⁶⁴ (item 1) |
| Learning | Fresh agent at the first step; learns on every step; nothing is frozen | None |
| Owner | The full agent, through `acorn-core demo` | `runRandomBaseline`, selected by `--baseline` |
| World | Side 1024, from the seed | A second copy of the same initial world |
| Stream | One pass: 13 goals, one attempt each, cap 3000 steps | The same |

One process per seed runs the agent's pass and then the comparator's pass.

**Why these values.** The side and the cap are the core's defaults
([run controls](../../design.md#run-controls)); neither was chosen with an
outcome in view, and no outcome exists. One attempt per goal and one cycle are
forced by item 3: the comparator makes one attempt per goal in one pass.

**Horizon: one pass, at most 34 000 steps.** This is the longest horizon on
which the public core offers a matched comparator.

- Inventory and tools persist, so in a later curriculum cycle an attempt can be
  satisfied by what an earlier cycle left behind. A comparison over several
  cycles needs a comparator that follows the same campaign in one persistent
  world, and `runRandomBaseline` makes one pass only.
- A checkpointed resume is not used to give the agent more experience first. A
  restore starts the option models and the off-policy questions afresh and
  restarts the world
  ([checkpoint admission](../../verification.md#checkpoint-admission)), so it
  would evaluate a different composition.

By item 4, this horizon tests whether learning on earlier goals raises
achievement on later ones within the pass. It cannot show learning that needs
repeated visits to the same goal.

**Initialization.** Each run constructs the agent with
`AgentConstruction.standard` from the seed, loads no checkpoint and starts the
world at `World.initial`.

**Population, sample and prior access.** The population is the 2⁶⁴ seeds. The
sample is the 20 seeds of [seeds.txt](seeds.txt), drawn once, in the order
listed, with

```sh
od -An -N160 -v -tu8 /dev/urandom
```

when this revision was written. No seed was discarded or redrawn. No outcome of
any run at these seeds was observed: no agent run of any kind was made in
preparing this protocol. The draw itself cannot be audited afterwards; that is
an attestation, not a proof. There is no development set, selection step or
held-out set, because nothing is tuned.

## Estimand, margin and claims

For a seed, let a be the number of curriculum goals the agent achieves, k the
number the comparator achieves, and D = a − k. By item 2, D is the difference
over the eleven policy-dependent goals, an integer from −11 to 11. A seed is a
**win** when D ≥ 1, a **loss** when D ≤ −1 and a **tie** when D = 0. A seed on
which the world refuses either pass is not a win.

- **Estimand.** q, the fraction of the 2⁶⁴ seeds that are wins.
- **Meaningful margin.** One goal. A seed counts toward the claim only when the
  agent achieves at least one more goal than the comparator, the smallest unit
  of achievement the curriculum has: one eleventh of its policy-dependent goals.
- **Claim.** q > 1/2: in most worlds the agent achieves at least one more goal
  than chance. Equivalently, the median of D is at least 1.

The mean of D is reported but carries no decision. D is bounded only by ±11, so
an interval for its mean that is valid at every sample size is far wider than
one for q: Hoeffding's inequality needs 22² · ln(40) / 2 ≈ 893 seeds for a 95%
interval of half-width one goal, against 20 seeds here. An interval with
approximate coverage, such as a bootstrap, would rest on an unverified
large-sample argument.

## Uncertainty method

Let V be the number of wins among the 20 seeds, W the number of seeds whose
valid outcome is a win, and M the number of seeds with no valid outcome
([failed runs](#stopping-rule-exclusions-and-failed-runs)). A valid outcome
shows whether its seed is a win and a missing one does not, so W ≤ V ≤ W + M,
and V = W when no seed is missing.

**Sampling law.** By item 5, whether a seed is a win is a fixed property of the
seed. The 20 seeds are independent uniform draws from the population (assumed of
the operating system's entropy source), so V has the binomial distribution with
20 trials and probability q. This needs no assumption about the generator that
turns a seed into a world, and no independence between worlds.

**Interval.** For a count w, the exact binomial interval is the set of values
of q that neither one-sided exact binomial test rejects at 0.025: its lower end
is the largest q with P(Bin(20, q) ≥ w) ≤ 0.025, or 0 when w = 0, and its upper
end the smallest q with P(Bin(20, q) ≤ w) ≤ 0.025, or 1 when w = 20. The
reported 95% interval for q takes its lower end at W and its upper end at
W + M. With no missing seed it is the exact binomial interval at W.

Coverage is at least 95% for every q and holds at this sample size.
P(Bin(20, q) ≥ w) increases with q, so the lower end at V exceeds the true q
only when V reaches the smallest w whose upper tail under the true q is at most
0.025, an event of probability at most 0.025; the upper end is symmetric.
Neither end falls as the count rises, because P(Bin(20, q) ≥ w) falls and
P(Bin(20, q) ≤ w) rises with w. So the lower end at W is at most the lower end
at V, and the upper end at W + M is at least the upper end at V: the reported
interval contains the exact binomial interval at V, whatever caused the missing
outcomes.

Reporting an interval and not a point estimate follows the uncertainty-aware
evaluation cited by the
[promotion standard](../../prior-art-review.md#default-promotion-and-demotion).
That source's bootstrap is not used.

| Count | Interval for q | Count | Interval for q | Count | Interval for q |
|---|---|---|---|---|---|
| 0 | 0.000 to 0.169 | 7 | 0.153 to 0.593 | 14 | 0.457 to 0.882 |
| 1 | 0.001 to 0.249 | 8 | 0.191 to 0.640 | 15 | 0.508 to 0.914 |
| 2 | 0.012 to 0.317 | 9 | 0.230 to 0.685 | 16 | 0.563 to 0.943 |
| 3 | 0.032 to 0.379 | 10 | 0.271 to 0.729 | 17 | 0.621 to 0.968 |
| 4 | 0.057 to 0.437 | 11 | 0.315 to 0.770 | 18 | 0.683 to 0.988 |
| 5 | 0.086 to 0.492 | 12 | 0.360 to 0.809 | 19 | 0.751 to 0.999 |
| 6 | 0.118 to 0.543 | 13 | 0.407 to 0.847 | 20 | 0.831 to 1.000 |

Lower ends are rounded down and upper ends up. The reported interval takes its
lower end from the row of W and its upper end from the row of W + M.

## Decision rule

W and M are the counts defined under [uncertainty method](#uncertainty-method).

| Result | Condition | What is reported |
|---|---|---|
| **Accepted** | W ≥ 15 | In most worlds the agent achieves at least one more goal than chance in its first pass. |
| **Refuted** | W + M ≤ 5 | In most worlds the agent does not achieve more goals than chance in its first pass. |
| **Inconclusive** | otherwise | The sample does not settle whether q is above or below 1/2. |

The thresholds are exact: P(Bin(20, 1/2) ≥ 15) = 5425/262144 ≈ 0.0207, and
P(Bin(20, 1/2) ≥ 14) ≈ 0.0577 exceeds 0.025. The rule accepts with probability
at most 0.0207 when q ≤ 1/2 and refutes with probability at most 0.0207 when
q ≥ 1/2. A missing seed never counts as a win toward acceptance and always
counts as one against refutation, so both bounds hold whatever caused the
missing outcomes.

What the rule can detect, exactly, with no missing seed:

| True q | Accepted | Refuted | Inconclusive |
|---|---|---|---|
| 0.1 | 0.0000 | 0.9887 | 0.0113 |
| 0.2 | 0.0000 | 0.8042 | 0.1958 |
| 0.3 | 0.0000 | 0.4164 | 0.5836 |
| 0.5 | 0.0207 | 0.0207 | 0.9586 |
| 0.7 | 0.4164 | 0.0000 | 0.5836 |
| 0.8 | 0.8042 | 0.0000 | 0.1958 |
| 0.9 | 0.9887 | 0.0000 | 0.0113 |

**Why 20 seeds.** Twenty is the smallest sample for which this rule accepts with
probability at least 0.8 when q = 0.8 and refutes with probability at least 0.8
when q = 0.2; at every smaller sample that probability is below 0.76. The
value 0.8 is a planning choice, not an estimate of q. If q lies between about
0.3 and 0.7 the likely result is inconclusive.

**Negative and inconclusive results** are reported with the same prominence as
an accepted one: the result line, W, losses, ties, M and the interval, in the
baseline assessment's U6 row and in the issue. A refuted result is stated as
refuted at this horizon. An inconclusive result is stated as inconclusive; it
is neither evidence of learning nor evidence against it. Outside this study's
scope, learning stays UNKNOWN.

No result changes the
[qualification register](../../prior-art-review.md#current-default-qualification).
Promotion needs the separate decision and fresh evidence the promotion standard
describes.

## Stopping rule, exclusions and failed runs

- **Fixed sample.** Twenty seeds, one run each; the only further run is the
  rerun allowed below. There is no interim analysis, no extension and no
  replacement seed. A further study uses a new protocol revision and new seeds,
  and its sample is not pooled with this one.
- **No exclusions.** No seed is removed for its outcome.
- **Missing.** A seed has a valid outcome when its last run exits with status 0
  and reports a complete outcome CSV: the core prints `csv written successfully`
  on standard output exactly when no CSV creation or write failed, and a CSV
  failure does not change its exit status. Every other seed has no valid
  outcome, including one killed at the per-run deadline, and counts in M.
- **Reruns.** A run interrupted from outside the executed definitions (a machine
  restart, an operator's kill, a full disk) is rerun once with the same command.
  A run that exits with status 0 without a complete outcome CSV was interrupted
  in this sense: the operating system refused a file operation. The interrupted
  record is first moved, unedited, to the directory named interrupted beside
  the seed directories, so both records are kept and the seed's own directory
  holds the rerun alone. By item 5 a rerun cannot select among outcomes. A run
  killed by the per-run deadline is not rerun, and a rerun is not rerun: a seed
  whose rerun gives no valid outcome is missing.
- **Deadline kills.** The record decides whether the deadline ended a run. A
  run counts as killed by the deadline when its standard error holds the line
  "time: command terminated abnormally" and the resource report's real time is
  at least 3600 s. The same line with a shorter real time, or a record with no
  exit status, is an interruption from outside. The exit status does not
  separate the two: on 2026-10-03, with a stand-in for the core and a 2 s
  deadline, this host recorded status 1 and that line both for the deadline's
  kill (2.15 s real) and for a kill from outside (1.19 s real). A deadline kill
  cannot show less than 3600 s, because the report's clock starts before the
  deadline's and stops after it.
- **Derived checks.** The record behind a valid outcome must agree with items 2
  and 3: 13 outcome rows, one per goal in order; achievement of goals 0 and 11
  at 200 and 800 steps; a comparator count of at least 2; and the same agent
  count in the CSV and in the printed comparison. A violation means the
  executed binary is not the source this protocol analyses. The study stops,
  the violation is reported as a deviation and no decision is issued.

## Resource budget

The machine is the shared development host: an Apple M4 Pro with 14 cores (10
performance, 4 efficiency) and 24 GB of memory, running macOS 27.0.

| Quantity | Limit | Kind |
|---|---|---|
| Agent steps | At most 34 000 per run: 680 000 with no rerun | Derived (item 6) |
| Concurrent processes | 4; each run's loop is sequential and uses one core | Fixed |
| Per-run deadline | 3600 s, enforced by SIGKILL | Hard limit |
| Runs | 20, and at most one rerun per seed: at most 40 | Fixed ([reruns](#stopping-rule-exclusions-and-failed-runs)) |
| CPU time | At most 20 core-hours with no rerun, at most 40 in all | Hard limit: runs of at most 3600 s each |
| Wall time | At most 5 hours with no rerun | Hard limit: 20 runs on 4 workers. A rerun runs for at most 3600 s |
| Expected CPU time | About 3 to 7 core-hours | Estimate, not a bound |
| Expected wall time | About 1 to 2 hours | Estimate, not a bound |
| Memory per process | UNKNOWN | Recorded per run |

The estimate rests on one informal observation, not retained in this
repository: on 2026-10-02 the slowest mutation-audit arm took 241 and 259
CPU-seconds on this host, for a campaign of at most 15 200 steps on a 512 × 512
world. That is 16 to 17 ms per step if every capped attempt ran out, and more
if the campaign was shorter; its step count was not recorded. At 17 ms per step
a seed costs about 10 minutes, and at twice that about 20. The comparator's
pass adds world steps only. The deadline binds only above about 105 ms per
step. Peak memory cannot be derived from the definitions, because it depends on
the runtime's allocation; if four processes do not fit, concurrency is lowered,
which changes no outcome (item 5) and raises the wall-time limit in proportion.

The runs invoke no Lake command. The host's shared build slot is needed only
for the verification and build that precede them; four processes leave six
performance cores to other work. Other load changes wall time and no outcome.

## Execution

Preconditions: the owner's authorization names this protocol revision and the
commit to run. That commit contains this revision unchanged, and its Lean
sources are those of the commit that registered the revision; the first block
below refuses to continue otherwise. It takes the registering commit to be the
one that first added this file, which is so because pull requests are
squash-merged and revision 1 reaches the main branch in one commit. It compares
this file, the seed list and the Lean sources with that commit. The checkout
must have full history: a shallow checkout ends at a commit that then appears
to have added every file, so the block refuses one. Running any other Lean
sources needs a new revision first.

The commands are for this host (macOS, GNU coreutils installed). Each block
below is a complete bash script, run by bash from the root of the checkout. The
run script exports a shell function, which zsh, this host's default shell, does
not do. The scripts were written from the core's argument and output
definitions and have not been executed against the core; the extraction
commands were checked against text assembled by hand from those definitions.

Build and record the run identity, from a clean, full-history checkout of the
authorized commit:

```bash
set -euo pipefail
study=docs/studies/first-pass-vs-chance
out="$study/observations/r1"
test -z "$(git status --porcelain)"
test "$(git rev-parse --is-shallow-repository)" = false
registered=$(git log --diff-filter=A --format=%H -- "$study/protocol.md" | tail -n 1)
git diff --quiet "$registered" HEAD -- lean "$study/protocol.md" "$study/seeds.txt"
./scripts/verify.sh
./scripts/lean.sh build acorn-viewer
mkdir -p "$out"
{
  git rev-parse HEAD
  printf '%s\n' "$registered"
  shasum -a 256 lean/.lake/build/bin/acorn-core "$study/protocol.md" "$study/seeds.txt"
  cat lean/lean-toolchain
  sw_vers
  sysctl -n machdep.cpu.brand_string hw.ncpu hw.memsize
  date -u +%Y-%m-%dT%H:%M:%SZ
} > "$out/identity.txt"
```

Run the 20 seeds, four at a time. The script refuses a seed that already has a
directory, so it never overwrites a record:

```bash
set -euo pipefail
study=docs/studies/first-pass-vs-chance
out="$study/observations/r1"
run_seed() {
  dir="$out/seed-$1"
  mkdir "$dir" || return 1
  status=0
  /usr/bin/time -l gtimeout --signal=KILL 3600s \
    lean/.lake/build/bin/acorn-core demo --research-profile ranked \
      --criterion discounted --planning expectation --seed "$1" --side 1024 \
      --steps 3000 --attempts 1 --goals 13 --cycles 1 --baseline \
      --csv "$dir/outcomes.csv" > "$dir/stdout.txt" 2> "$dir/stderr.txt" || status=$?
  printf '%s\n' "$status" > "$dir/exit-status.txt"
}
export -f run_seed
export out
xargs -P 4 -n 1 "$BASH" -c 'run_seed "$1"' bash < "$study/seeds.txt"
```

Rerun an interrupted seed, written N here, under the
[reruns rule](#stopping-rule-exclusions-and-failed-runs), once the run script
has ended. First move its record aside, unedited. This script refuses a seed
that already has an interrupted record, so no seed is rerun twice:

```bash
set -euo pipefail
out=docs/studies/first-pass-vs-chance/observations/r1
mkdir -p "$out/interrupted"
test ! -e "$out/interrupted/seed-N"
mv "$out/seed-N" "$out/interrupted/seed-N"
```

Then run the run script again. It refuses every seed that still has a
directory, reports each refusal and exits with a nonzero status. It runs the
seeds that have none: those moved aside, and any that an interruption left
unstarted.

Extract one line per seed: the seed, the exit status, whether the core reported
a complete CSV, the derived check on the agent's rows, the agent's achieved
count from the CSV, and the comparator's and the agent's counts as the core
printed them:

```bash
set -euo pipefail
study=docs/studies/first-pass-vs-chance
out="$study/observations/r1"
for dir in "$out"/seed-*; do
  grep -Fqx 'csv written successfully' "$dir/stdout.txt" && csv=complete || csv=incomplete
  awk -F, 'NR > 1 && !/^#/ { rows++
      if ($1 != rows - 1 || $2 != 0) bad = 1
      if ($1 == 0 && !($4 == 200 && $5 == 1)) bad = 1
      if ($1 == 11 && !($4 == 800 && $5 == 1)) bad = 1 }
    END { exit !(rows == 13 && !bad) }' "$dir/outcomes.csv" && derived=ok || derived=violated
  printf '%s %s %s %s %s %s\n' "${dir##*seed-}" \
    "$(cat "$dir/exit-status.txt" 2> /dev/null || echo absent)" "$csv" "$derived" \
    "$(awk -F, 'NR > 1 && !/^#/ && $5 == 1 { n++ } END { print n + 0 }' "$dir/outcomes.csv")" \
    "$(sed -n 's/^distinct goals achieved .* random policy: \([0-9]*\)\/13; agent: \([0-9]*\)\/13 (agent used 13 attempts)$/\1 \2/p' "$dir/stdout.txt")"
done > "$study/results-r1.txt"
```

A line whose status is not 0, or whose CSV is incomplete, is a missing seed.
Every other line is valid and must read check ok, a sixth field of at least 2
and equal fifth and seventh fields; anything else is a derived-check violation.
For a valid line, D is the fifth field minus the sixth. W counts valid lines
with D ≥ 1, and M counts the seeds of the list without a valid line. The
[decision rule](#decision-rule) gives the result, and the interval table gives
the interval's lower end at W and its upper end at W + M.

## Records

- **Run identity.** Each run is `first-pass-vs-chance/r1/seed-N` for its seed N,
  and an interrupted run that was rerun is
  `first-pass-vs-chance/r1/interrupted/seed-N`. An empirical citation names the
  study, the revision, the run or runs and the comparison.
- **Original observations.** Each seed's directory holds the outcome CSV, the
  standard output, the standard error with the resource report, and the exit
  status, exactly as written. An interrupted run's directory holds whatever
  that run wrote. They are never edited. The extracted results file and any
  written summary are presentations, kept apart from them.
- **Source and environment.** The identity file records the commit run, the
  commit that registered the revision, the SHA-256 of the binary, of this
  protocol and of the seed list, the toolchain, the operating system, the
  processor and the start time.
- **Timing.** This revision reaches the main branch before the first run.
  GitHub's record of the merge is the independent time of registration; run
  start times come from the local clock, which nothing attests. A content hash
  shows that a file is unchanged, not when it was written.
- **Deviations.** Any departure from this protocol is recorded with the result,
  with its reason and its effect on the claim.

## Analysis

**Confirmatory.** One comparison, the decision rule above. There is no second
confirmatory test, so no multiplicity adjustment applies.

**Exploratory.** Reported as description, with no decision and no claim:

- the value of D for each seed with a valid outcome, their mean and range, and
  the counts of wins, losses and ties, with the exact binomial interval for the
  fraction of losses, its lower end at the count of losses and its upper end at
  that count plus M;
- for each goal, the number of seeds on which the agent achieved it and its
  steps to achievement. The core prints only the comparator's count, so no
  per-goal comparison is available;
- the learner columns of the outcome CSV and the campaign summary's replacement
  and ranking counts;
- observed steps per second, wall time and peak memory, as observations of this
  host and not as performance claims. Peak memory is read from the resource
  report's "maximum resident set size" line, for a run that ended on its own.
  On 2026-10-03, with a stand-in for the core that held 200 MiB, this host
  reported 214 MiB on that line and 1.4 MiB on the "peak memory footprint"
  line, which describes the timeout wrapper alone. After a deadline kill both
  lines described the wrapper alone, so a killed run has no memory observation.

## What a result will and will not establish

- **Adaptation.** The agent learns throughout the measured pass. The counts
  describe a learner in its first 34 000 steps, not a trained policy held fixed.
- **Attribution.** The comparator is not an ablation of the agent: it has no
  features, no memory and no temporally extended exploration. A win shows the
  whole `ranked` composition out-achieving chance. It does not separate learning
  from authored behavioural structure such as exploration duration
  ([D3](../../learned-only-binding.md#d3--exploration-duration--step-9)), and it
  credits no single mechanism.
- **Scope.** The result concerns worlds of side 1024, the standard curriculum,
  one pass with a 3000-step cap, and the source at the authorized commit. A
  material change to the learning equations, features, reward or selection rules
  needs a new observation.
- **Lifetime cost.** Memory and latency over a long lifetime are outside this
  study; one pass does not observe them.

## Revisions

A revision is this file and [seeds.txt](seeds.txt) as committed together. It is
registered when it reaches the main branch. From then until the run, any change
to either makes a new revision with a new number and a new observations
directory; its seeds are redrawn only if a run was made at the old ones. After
the run, the only edits are corrections that follow a renamed declaration or a
moved link. The identity file holds the hash of the
revision as run, and Git holds its text.
