# First-pass achievement against a uniform-random policy: result

This is the result of revision 1 of study `first-pass-vs-chance`, the
observation that [U6](../../baseline-assessment.md#conformance-sequence) of the
baseline assessment asks for
([#12](https://github.com/rbeauchamp/acorn/issues/12)). The
[protocol](protocol.md) defines every term used here and fixed every choice
before the run.

## Result

**Refuted at this horizon.** In most worlds the agent does not achieve more
goals than chance in its first pass.

| Quantity | Value |
|---|---|
| Seeds with a valid outcome | 20 of 20 |
| W, wins: the agent achieves at least one more goal than the comparator | 4 |
| Losses: the agent achieves at least one goal fewer | 9 |
| Ties | 7 |
| M, seeds with no valid outcome | 0 |
| Reported 95% interval for q, the fraction of all seeds that are wins | 0.057 to 0.437 |
| [Decision rule](protocol.md#decision-rule) | W + M = 4 ≤ 5: refuted |

The interval is the row for a count of 4 in the protocol's
[table](protocol.md#uncertainty-method), with both ends at that row because no
seed is missing. It lies below 1/2. The rule refutes with probability at most
0.0207 when q is 1/2 or more.

Citation: study first-pass-vs-chance, protocol revision 1, runs
first-pass-vs-chance/r1/seed-N for the 20 seeds of [seeds.txt](seeds.txt),
comparing the `ranked` agent with the uniform-random comparator.

**What is refuted.** The claim q > 1/2: that in most worlds the agent achieves
at least one more goal than a uniform-random policy, in one pass of the
standard curriculum from a fresh agent. The result concerns worlds of side
1024, a cap of 3000 steps and the source at the commit below.

**What is not shown.**

- That the agent does worse than chance in most worlds. Nine of 20 seeds are
  losses, and the interval for the fraction of losses, 0.230 to 0.685, contains
  1/2.
- Anything about learning over repeated visits to a goal, which stays UNKNOWN:
  the protocol's horizon is one pass
  ([what a result establishes](protocol.md#what-a-result-will-and-will-not-establish)).
- Which mechanism is responsible. The comparator is not an ablation of the
  agent.

No result here changes the
[qualification register](../../prior-art-review.md#current-default-qualification).

## Authorization and run identity

The owner authorized execution of revision 1 on 2026-10-03, delegating the
judgment of need. The run was judged needed for four reasons: the protocol
isolates the one quantity no derivation settles, how often the agent
out-achieves chance; U6 is the next step of the baseline assessment's
conformance sequence; issue 12 cannot close without it; and the cost is bounded
and local. The authorization named revision 1 and commit
6ac4eec84c9a65204262d460dad6f2f419552ad9, the commit that registered the
revision.

The run was made on 2026-10-03 from a clean, full-history checkout of that
commit. The protocol's first block passed its identity checks and
`./scripts/verify.sh` there before building, and wrote
[identity.txt](observations/r1/identity.txt):

| Item | Recorded value |
|---|---|
| Commit run, and commit that registered the revision | 6ac4eec84c9a65204262d460dad6f2f419552ad9 |
| SHA-256 of the core binary | f90c7495729a4d33cce77061dd52155bdf0894756e90e9665c691a251f539903 |
| SHA-256 of the protocol | bf92dacc28967c36e2fa590f401710b98b038ea5f31d2f90b1317f780232c85f |
| SHA-256 of the seed list | 2bb577cc5e7ad9813de9215cd4c7d160b77782540a6c2bcffe73d78257c976df |
| Toolchain | leanprover/lean4:v4.34.0 |
| Host | Apple M4 Pro, 14 cores, 24 GiB, macOS 27.0 (26A428) |
| Identity written | 2026-10-03T17:25:10Z |

The identity file's time is when the build block ended; the run block started
after it. A content hash shows that a file is unchanged, not when it was
written.

## Deviations

None. The protocol's build, run and extraction blocks were executed as written,
by bash from the root of the checkout. Every one of the 20 runs exited with
status 0 and reported a complete outcome CSV, so no seed is missing, no run was
interrupted or rerun, and no run reached the per-run deadline. Every record
passed the [derived checks](protocol.md#stopping-rule-exclusions-and-failed-runs):
13 outcome rows in order, goals 0 and 11 achieved at 200 and 800 steps, a
comparator count of at least 2, and the same agent count in the CSV and in the
printed comparison. No seed was added, removed or excluded.

## Records

- **Original observations.** [observations/r1](observations/r1) holds the
  identity file and one directory per seed with the outcome CSV, the standard
  output, the standard error with the resource report, and the exit status,
  exactly as written.
- **Extraction.** [results-r1.txt](results-r1.txt) is the output of the
  protocol's extraction block: per seed, the exit status, the CSV report, the
  derived check, the agent's count from the CSV, and the comparator's and the
  agent's counts as the core printed them.
- **This file** is a presentation. Every number in it is computed from those
  records; the commands are [below](#calculations).

## Outcome by seed

Seeds are in the order of the seed list. D is the agent's count minus the
comparator's. Both counts include the two survive goals, which every policy
achieves.

| # | Seed | Agent | Comparator | D | Outcome | Agent steps | Real time, s | Steps/s | Peak memory, MiB | Units replaced | Ranked positions |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | 16265277883658242538 | 2 | 6 | −4 | loss | 34000 | 547.9 | 62 | 148.0 | 1537 | 63/63/63 |
| 2 | 13880459309090878793 | 2 | 6 | −4 | loss | 34000 | 596.2 | 57 | 141.3 | 1537 | 63/63/63 |
| 3 | 1716393356351936839 | 2 | 2 | 0 | tie | 34000 | 578.8 | 59 | 155.7 | 1537 | 63/63/63 |
| 4 | 8789851314873071931 | 10 | 5 | +5 | win | 10563 | 199.1 | 54 | 139.4 | 444 | 63/63/63 |
| 5 | 13620147381080419094 | 6 | 6 | 0 | tie | 22257 | 389.7 | 57 | 145.0 | 985 | 63/63/63 |
| 6 | 4749189528387228772 | 2 | 7 | −5 | loss | 34000 | 569.2 | 60 | 144.5 | 1537 | 63/63/63 |
| 7 | 6635416297289148158 | 3 | 5 | −2 | loss | 31001 | 522.5 | 60 | 155.8 | 1396 | 63/63/63 |
| 8 | 7851395224514791152 | 3 | 5 | −2 | loss | 31001 | 551.5 | 56 | 156.4 | 1391 | 63/63/63 |
| 9 | 5962091343256219173 | 2 | 6 | −4 | loss | 34000 | 575.5 | 59 | 142.2 | 1537 | 63/63/63 |
| 10 | 9983648312904296248 | 2 | 3 | −1 | loss | 34000 | 588.7 | 58 | 141.1 | 1537 | 63/63/63 |
| 11 | 5492052231715161233 | 10 | 10 | 0 | tie | 10528 | 205.1 | 52 | 138.9 | 443 | 63/63/63 |
| 12 | 2322414581419455238 | 2 | 6 | −4 | loss | 34000 | 568.0 | 60 | 133.7 | 1537 | 63/63/63 |
| 13 | 11461955249533438688 | 10 | 6 | +4 | win | 12545 | 221.6 | 57 | 151.2 | 537 | 63/63/63 |
| 14 | 8131621970623044447 | 6 | 6 | 0 | tie | 24259 | 419.2 | 59 | 139.6 | 1078 | 63/63/63 |
| 15 | 14189236946719402793 | 5 | 9 | −4 | loss | 25003 | 473.1 | 53 | 142.4 | 1112 | 63/63/63 |
| 16 | 6989574669978301092 | 2 | 2 | 0 | tie | 34000 | 604.2 | 56 | 144.0 | 1537 | 63/63/63 |
| 17 | 16097639153899355059 | 10 | 10 | 0 | tie | 10008 | 214.0 | 47 | 150.2 | 419 | 63/63/63 |
| 18 | 536031971435615468 | 6 | 3 | +3 | win | 23918 | 426.5 | 56 | 142.7 | 1063 | 63/63/63 |
| 19 | 1306155069690187360 | 6 | 2 | +4 | win | 25541 | 439.2 | 59 | 140.7 | 1138 | 63/63/63 |
| 20 | 18322016315669325009 | 6 | 6 | 0 | tie | 22038 | 399.3 | 55 | 145.5 | 976 | 62/62/62 |

## Exploratory descriptions

These are the descriptions the protocol's [analysis](protocol.md#analysis)
lists. They carry no decision and no claim.

**The difference D.** Its mean over the 20 seeds is −0.70 and its range is −5
to +5. Its values are −5 once, −4 five times, −2 twice, −1 once, 0 seven times,
+3 once, +4 twice and +5 once. There are 4 wins, 9 losses and 7 ties. The exact
binomial interval for the fraction of losses is 0.230 to 0.685, the table row
for a count of 9. Over all 20 seeds the agent achieved 97 goals and the
comparator 111; without the two survive goals, 57 and 71.

**Achievement by goal.** The table gives the agent's steps to achievement for
each seed and goal, with a dash where the attempt reached the cap of 3000
steps. The core prints only the comparator's count, so there is no per-goal
comparison.

| # | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | 200 | – | – | – | – | – | – | – | – | – | – | 800 | – |
| 2 | 200 | – | – | – | – | – | – | – | – | – | – | 800 | – |
| 3 | 200 | – | – | – | – | – | – | – | – | – | – | 800 | – |
| 4 | 200 | 222 | 1 | – | 335 | 1 | – | – | 1 | 1 | 1 | 800 | 1 |
| 5 | 200 | 254 | – | – | 1 | – | – | – | – | 1 | 1 | 800 | – |
| 6 | 200 | – | – | – | – | – | – | – | – | – | – | 800 | – |
| 7 | 200 | – | – | – | – | – | – | – | – | 1 | – | 800 | – |
| 8 | 200 | – | 1 | – | – | – | – | – | – | – | – | 800 | – |
| 9 | 200 | – | – | – | – | – | – | – | – | – | – | 800 | – |
| 10 | 200 | – | – | – | – | – | – | – | – | – | – | 800 | – |
| 11 | 200 | 1 | 521 | – | 1 | 1 | – | – | 1 | 1 | 1 | 800 | 1 |
| 12 | 200 | – | – | – | – | – | – | – | – | – | – | 800 | – |
| 13 | 200 | 2538 | 1 | – | 1 | 1 | – | – | 1 | 1 | 1 | 800 | 1 |
| 14 | 200 | 1 | – | – | 2256 | – | – | – | – | 1 | 1 | 800 | – |
| 15 | 200 | 1 | – | – | – | – | – | – | – | 1 | 1 | 800 | – |
| 16 | 200 | – | – | – | – | – | – | – | – | – | – | 800 | – |
| 17 | 200 | 1 | 1 | – | 1 | 1 | – | – | 1 | 1 | 1 | 800 | 1 |
| 18 | 200 | 1915 | – | – | 1 | – | – | – | – | 1 | 1 | 800 | – |
| 19 | 200 | 2012 | – | – | 1527 | – | – | – | – | 1 | 1 | 800 | – |
| 20 | 200 | 35 | – | – | 1 | – | – | – | – | 1 | 1 | 800 | – |

| Goal | Seeds achieving it, of 20 | Of those, at the attempt's first step | Steps in the others |
|---|---|---|---|
| 0, survive 200 steps | 20 | 0 | 200 in each |
| 1, collect 2 wood | 10 | 4 | 35, 222, 254, 1915, 2012, 2538 |
| 2, collect 2 stone | 5 | 4 | 521 |
| 3, reach a near target | 0 | | |
| 4, collect 4 wood | 9 | 6 | 335, 1527, 2256 |
| 5, craft an axe | 4 | 4 | |
| 6, collect 3 food | 0 | | |
| 7, reach a far target | 0 | | |
| 8, collect 2 gold | 4 | 4 | |
| 9, craft a boat | 11 | 11 | |
| 10, collect 8 wood | 10 | 10 | |
| 11, survive 800 steps | 20 | 0 | 800 in each |
| 12, collect 4 gold | 4 | 4 | |

On eight seeds the agent achieved only the two survive goals. No seed achieved
either reach goal or the food goal. Of the agent's 57 achievements on the
eleven policy-dependent goals, 47 came at the attempt's first step. A collect
goal is satisfied when the inventory holds at least the requested quantity and
a craft goal when the tool is owned (`Goal.observe`), whenever they were
acquired, and the world is not reset between attempts. So an attempt that ends
at its first step is one whose condition held one step after the goal was
installed: what earlier attempts left behind met it, or that one step completed
it. The record does not separate the two cases. The same rule applies to the
comparator, whose steps the core does not print.

**Learner columns of the outcome CSV.** Each row carries three values read at
the end of its attempt. The exploration rate is the binary32 value nearest
0.01 in all 260 rows. The mean step size of the primitive controller lies
between 4.9915 × 10⁻⁵ and 5.0009 × 10⁻⁵ in every row. The mean absolute
temporal-difference error of the prediction demons ranges from 2.6 × 10⁻⁷ to
0.81 over the rows, and from 5.4 × 10⁻⁷ to 0.37 over the 20 final rows.

**Replacement and ranking counts of the campaign summary.** The feature tester
replaced between 419 and 1537 units per seed: 1537 on each of the eight seeds
that ran all 34 000 steps, and one unit per 22 to 24 agent steps on every seed.
At the end of the pass each of the three option models held 63 ranked
positions on 19 seeds and 62 on one.

**Resource use**, as observations of this host and not as performance claims.

| Quantity | Observed | Protocol |
|---|---|---|
| Agent steps | 520 662 in all; 10 008 to 34 000 per seed | At most 680 000; at most 34 000 per run |
| Steps per second, the core's figure for the agent's pass | 47 to 62 per seed; 58.0 over all seeds, about 17 ms per step | Estimate of 16 to 17 ms per step or more |
| Real time per run, agent and comparator | 199.1 to 604.2 s | Deadline 3600 s |
| CPU time, user plus system | 9064 s in all, 2.52 core-hours | Limit 20 core-hours; estimate 3 to 7 |
| Peak memory per process, maximum resident set size | 133.7 to 156.4 MiB | UNKNOWN before the run |
| Concurrent processes | 4 | 4 |
| Runs | 20, no rerun | 20, at most 40 |

The run block took 38 minutes 41 seconds, from 17:26:28Z to 18:05:09Z, against
an estimate of one to two hours and a limit of five. Those two times were read
from the local clock when the block was started and when it returned; they are
not part of the retained record, and nothing attests the local clock. The 20
real times in the record sum to 9089 s, which four workers cannot finish in
less than 37.9 minutes.

## Calculations

From the root of the checkout. The counts and the mean of D, from the
extraction:

```bash
awk '$2 == 0 && $3 == "complete" { d = $5 - $6; w += d >= 1; l += d <= -1; t += d == 0; s += d; v++ }
  END { print "W", w, "losses", l, "ties", t, "M", 20 - v, "mean D", s / v }' \
  docs/studies/first-pass-vs-chance/results-r1.txt
```

The agent's steps to achievement by seed and goal, from the outcome CSVs:

```bash
study=docs/studies/first-pass-vs-chance
while read -r seed; do
  awk -F, 'NR > 1 && !/^#/ { printf "%s ", ($5 == 1 ? $4 : "-") } END { print "" }' \
    "$study/observations/r1/seed-$seed/outcomes.csv"
done < "$study/seeds.txt"
```

Agent steps, steps per second and the replacement count are the fields
total_steps, steps_per_sec and retire_count of each CSV's last line. The ranked
positions are the ranked_slots line of the standard output. Real, user and
system time and the maximum resident set size are the resource report at the
end of the standard error. The learner columns are the last three fields of
each outcome row.
