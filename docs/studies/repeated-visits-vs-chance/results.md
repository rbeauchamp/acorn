# Improvement over repeated visits against a uniform-random policy: result

This is the result of revision 2 of study `repeated-visits-vs-chance`, the
observation that [U7](../../baseline-assessment.md#conformance-sequence) of the
baseline assessment asks for
([#61](https://github.com/rbeauchamp/acorn/issues/61)). The
[protocol](protocol.md) defines every term used here and fixed every choice
before the run.

## Result

**Refuted at this horizon.** In most worlds the agent's attempts to reach a
target do not shorten over repeated visits by at least 300 steps per attempt
and by at least 300 steps per attempt more than chance's do.

| Quantity | Value |
|---|---|
| Seeds with a valid outcome | 20 of 20 |
| W, wins: the agent's improvement A and its excess D over the comparator's are both at least 1200 steps | 0 |
| Losses: A and D are both at most −1200 steps | 1 |
| Ties | 19 |
| M, seeds with no valid outcome | 0 |
| Reported 95% interval for q, the fraction of all seeds that are wins | 0.000 to 0.169 |
| [Decision rule](protocol.md#decision-rule) | W + M = 0 ≤ 5: refuted |

The interval is the row for a count of 0 in the protocol's
[table](protocol.md#uncertainty-method), with both ends at that row because no
seed is missing. It lies below 1/2. The rule refutes with probability at most
0.0207 when q is 1/2 or more.

Citation: study repeated-visits-vs-chance, protocol revision 2, runs
repeated-visits-vs-chance/r2/seed-N for the 20 seeds of [seeds.txt](seeds.txt),
comparing the `ranked` agent with the uniform-random comparator.

**What is refuted.** The claim q > 1/2: that in most worlds the agent's reach
attempts shorten, between its first two visits and its last two, by at least
the margin and by at least the margin more than a uniform-random policy's. The
result concerns worlds of side 1024, the standard curriculum, four cycles with
a cap of 3000 steps, the two reach goals and the source at the commit below.

**How it came about.** Almost no reach attempt reached its target, in either
arm. Each arm made 160 visits to a reach goal: 20 seeds, two goals, four
cycles. The agent achieved one of them and the comparator none. On 19 seeds
every reach attempt of both arms ran to the cap, so every cost is 12 000 steps
and A and D are 0. On the other seed the agent reached the near target on its
first visit, after 1263 steps, and on no later visit, so its late cost exceeds
its early cost by 1737 steps and the seed is a loss. This is, but for that one
visit, the case the protocol names in advance: a refuted result in which
neither arm reaches a target on any visit.

**What is not shown.**

- That the agent cannot learn the reach goals. The agent is rewarded for a goal
  only when it achieves it. With one achievement in 160 visits it received
  almost nothing to learn those goals from, so the run does not observe what
  happens to its attempts once it is reaching targets
  ([what a result establishes](protocol.md#what-a-result-will-and-will-not-establish)).
- That the agent does worse than chance. One seed of 20 is a loss, and the
  interval for the fraction of losses is 0.001 to 0.249. The comparator reached
  no target at all.
- Anything about need. The result is a comparison with one named policy, the
  uniform-random comparator. It is not evidence that the reach goals need
  continual learning, and no such need is proved: `Goal.observe` gives the
  agent the exact displacement of the installed target, so a fixed rule that
  steps toward the target arrives wherever no water or mountain is in the way
  ([#69](https://github.com/rbeauchamp/acorn/issues/69)).
- Which mechanism is responsible. The comparator is not an ablation of the
  agent.
- Anything beyond this horizon. Whether the agent learns over a longer
  campaign, or on goals it does achieve, stays UNKNOWN.

No result here changes the
[qualification register](../../prior-art-review.md#current-default-qualification).

## Authorization and run identity

The owner authorized execution after issue 58 landed, as revision 2 at its
registering commit. Revision 2 was registered by
[#75](https://github.com/rbeauchamp/acorn/pull/75), which reached the main
branch as commit 96e3f6b0c0d456f8dddb5099a679564ed06297e8 at
2026-10-04T08:22:59Z by GitHub's record. Its `lean/` and `scripts/` trees equal
those of d3bc6e0a559a45047e4e666323621b4ca7650f0a, the commit by which
[#73](https://github.com/rbeauchamp/acorn/pull/73) landed the change for
[#58](https://github.com/rbeauchamp/acorn/issues/58).

The run was made on 2026-10-04 from a clean, full-history checkout of the
registering commit. The checkout had no Lean dependencies, so the pinned
dependencies were provisioned first with the commands the repository
prescribes for a fresh worktree. The protocol's first block then passed its
identity checks and `./scripts/verify.sh` there before building, and wrote
[identity.txt](observations/r2/identity.txt):

| Item | Recorded value |
|---|---|
| Commit run, which is the commit that registered the revision | 96e3f6b0c0d456f8dddb5099a679564ed06297e8 |
| SHA-256 of the core binary | d3634651365c557241e7dc8ba432a11fa1fc894dc4a8067e674120da2592470a |
| SHA-256 of the protocol | 2a6e9cc457563e68d4d0a720621e4252dbc896b107e314110c54ec750e3d3255 |
| SHA-256 of the seed list | c7cc8452dfd50dc95924b718aba2f44a5568a7f3d17f608d3044c5ddca048c85 |
| Toolchain | leanprover/lean4:v4.34.0 |
| Host | Apple M4 Pro, 14 cores, 24 GiB, macOS 27.0 (26A428) |
| Identity written | 2026-10-04T08:31:51Z |

The identity file's time is when the build block ended; the run block started
after it. A content hash shows that a file is unchanged, not when it was
written.

## Prior access

No outcome of the study was observed before the run. Three accesses to its
seeds or scripts came before or during it, and none ran an agent or a
comparator at a listed seed:

- **The design pass for [#69](https://github.com/rbeauchamp/acorn/issues/69)**,
  between the two registrations, as the protocol's
  [design](protocol.md#design) discloses. A generator-only tool evaluated
  terrain, spawn and both reach targets at each of the 20 seeds. It
  constructed no agent and no comparator and took no world step. It found
  both targets reachable within one attempt's cap on all 20 seeds by a body
  that holds a boat and on 17 by a body without one; on seeds
  18389388507701574072, 635693954212696868 and 5290812662085785406 one
  target's goal box is entirely water. Its search code is unverified.
- **The validation of [#74](https://github.com/rbeauchamp/acorn/pull/74)**,
  after revision 2 was registered. Its test step evaluated the generator only
  at all 20 seeds: the spawn position from `World.initial`, the spawn tile's
  kind, its tree and stone counts, and the two reach targets from
  `rawStandardCurriculum`. By that pull request's record it took no world
  step on those seeds, constructed no agent and no comparator on them and
  observed no outcome of either arm; the comparator campaigns it ran used
  seeds of study first-pass-vs-chance only. The file holding the listed seeds
  was written while this study's run block was already running, by another
  process on the host.
- **The validation of [#75](https://github.com/rbeauchamp/acorn/pull/75)**,
  which registered this revision. Its test step executed the protocol's
  scripts at seed 1, which is not a listed seed, and its body lists those
  executions.

Neither the seeds nor any command, margin or rule was changed after either
evaluation: they are those registered. A run is a function of its command and
binary ([item 7](protocol.md#what-derivation-settles)), so a process that
reads the generator at the same seeds changes no outcome.

## Deviations

None. The protocol's build, run, extraction and calculation blocks were
executed as written, by bash from the root of the checkout. Every one of the 20
runs exited with status 0 and reported a complete outcome CSV, so no seed is
missing, no run was interrupted or rerun, and no run reached the per-run
deadline. Every record passed the
[derived checks](protocol.md#stopping-rule-exclusions-and-failed-runs): 52
outcome rows and 52 comparator lines in order, goals 0 and 11 achieved at 200
and 800 steps in every cycle of both arms, and 52 attempts for each arm in the
printed comparison. No seed was added, removed or excluded.

Two things about how the run block was started are not in the protocol and
change none of its commands. The block was started in its own session, so that
the operator's tooling could not interrupt it, and a `caffeinate -i -w` on its
process kept the host from idle sleep until it ended.

## Records

- **Original observations.** [observations/r2](observations/r2) holds the
  identity file and one directory per seed with the outcome CSV, the standard
  output, the standard error with the resource report, and the exit status,
  exactly as written.
- **Extraction.** [results-r2.txt](results-r2.txt) is the output of the
  protocol's extraction block: per seed, the exit status, the CSV report, the
  derived check on the agent's rows with its early and late costs, the same
  for the comparator's lines, and each arm's attempt count as the core printed
  it.
- **This file** is a presentation. Every number in it is computed from those
  records; the commands are [below](#calculations).

## Outcome by seed

Seeds are in the order of the seed list. A cost is the steps of four reach
attempts, so 12000 means that all four ran to the cap. A is the agent's early
cost minus its late cost, the comparator's improvement is the same for the
comparator, and D is A minus the comparator's improvement.

| # | Seed | Agent early | Agent late | A | Comparator early | Comparator late | Comparator improvement | D | Outcome | Agent steps | Real time, s | Steps/s | Peak memory, MiB | Units replaced | Ranked positions |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | 4477596743101089616 | 12000 | 12000 | 0 | 12000 | 12000 | 0 | 0 | tie | 73427 | 1423.21 | 52 | 150.5 | 3354 | 63/63/63 |
| 2 | 15051658002046768980 | 12000 | 12000 | 0 | 12000 | 12000 | 0 | 0 | tie | 88016 | 1618.29 | 55 | 147.4 | 4029 | 63/63/63 |
| 3 | 15472145577556848196 | 10263 | 12000 | −1737 | 12000 | 12000 | 0 | −1737 | loss | 89474 | 1697.96 | 53 | 147.1 | 4096 | 63/63/63 |
| 4 | 18444144794871009966 | 12000 | 12000 | 0 | 12000 | 12000 | 0 | 0 | tie | 94014 | 1686.98 | 56 | 145.9 | 4307 | 63/63/63 |
| 5 | 14389056706724403837 | 12000 | 12000 | 0 | 12000 | 12000 | 0 | 0 | tie | 100012 | 1810.35 | 55 | 145.3 | 4584 | 63/63/63 |
| 6 | 15263872034031786306 | 12000 | 12000 | 0 | 12000 | 12000 | 0 | 0 | tie | 54426 | 1100.69 | 50 | 145.2 | 2475 | 63/63/63 |
| 7 | 6752030555784622456 | 12000 | 12000 | 0 | 12000 | 12000 | 0 | 0 | tie | 82368 | 1532.69 | 54 | 152.7 | 3768 | 63/63/63 |
| 8 | 10588601992970704341 | 12000 | 12000 | 0 | 12000 | 12000 | 0 | 0 | tie | 82018 | 1549.47 | 53 | 146.3 | 3751 | 63/63/63 |
| 9 | 18389388507701574072 | 12000 | 12000 | 0 | 12000 | 12000 | 0 | 0 | tie | 71654 | 1376.03 | 53 | 143.9 | 3272 | 63/63/63 |
| 10 | 5290812662085785406 | 12000 | 12000 | 0 | 12000 | 12000 | 0 | 0 | tie | 65248 | 1236.66 | 53 | 148.6 | 2975 | 63/63/63 |
| 11 | 7183679067753989937 | 12000 | 12000 | 0 | 12000 | 12000 | 0 | 0 | tie | 49029 | 995.81 | 50 | 145.3 | 2225 | 63/63/63 |
| 12 | 17103312333100815830 | 12000 | 12000 | 0 | 12000 | 12000 | 0 | 0 | tie | 112008 | 2154.51 | 52 | 143.8 | 5139 | 63/63/63 |
| 13 | 8475637654084313318 | 12000 | 12000 | 0 | 12000 | 12000 | 0 | 0 | tie | 57761 | 1123.65 | 51 | 144.8 | 2629 | 63/63/63 |
| 14 | 635693954212696868 | 12000 | 12000 | 0 | 12000 | 12000 | 0 | 0 | tie | 120466 | 2162.76 | 56 | 141.3 | 5530 | 63/63/63 |
| 15 | 5684715628158642161 | 12000 | 12000 | 0 | 12000 | 12000 | 0 | 0 | tie | 82133 | 1527.87 | 54 | 145.7 | 3756 | 63/63/63 |
| 16 | 9387623327148988313 | 12000 | 12000 | 0 | 12000 | 12000 | 0 | 0 | tie | 46596 | 894.10 | 53 | 146.6 | 2113 | 63/63/63 |
| 17 | 9459746653325513711 | 12000 | 12000 | 0 | 12000 | 12000 | 0 | 0 | tie | 97013 | 1794.65 | 54 | 142.5 | 4445 | 63/63/63 |
| 18 | 7275330315411389186 | 12000 | 12000 | 0 | 12000 | 12000 | 0 | 0 | tie | 94014 | 1749.15 | 54 | 144.7 | 4307 | 63/63/63 |
| 19 | 16962846302593851773 | 12000 | 12000 | 0 | 12000 | 12000 | 0 | 0 | tie | 88016 | 1630.48 | 54 | 159.0 | 4029 | 63/63/63 |
| 20 | 3516833798422133599 | 12000 | 12000 | 0 | 12000 | 12000 | 0 | 0 | tie | 82285 | 1533.71 | 54 | 144.5 | 3764 | 63/63/63 |

## Exploratory descriptions

These are the descriptions the protocol's [analysis](protocol.md#analysis)
lists. They carry no decision and no claim.

**The difference D.** Its mean over the 20 seeds is −86.85 and its range is
−1737 to 0: it is 0 on 19 seeds and −1737 on one. There are 0 wins, 1 loss and
19 ties. The exact binomial interval for the fraction of losses is 0.001 to
0.249, the table row for a count of 1.

**Each half of the win condition.** The agent's improvement A is at least 1200
on 0 seeds, D is at least 1200 on 0 seeds, and the comparator's improvement is
at least 1200 on 0 seeds. The exact binomial interval for each is 0.000 to
0.169. Each is at most one half of the win condition and none is the claim.

**Reach and food visits.** Seeds achieving the visit, of 20, by cycle:

| Arm | Goal | Cycle 0 | Cycle 1 | Cycle 2 | Cycle 3 |
|---|---|---|---|---|---|
| Agent | 3, reach a near target | 1 | 0 | 0 | 0 |
| Agent | 7, reach a far target | 0 | 0 | 0 | 0 |
| Agent | 6, collect 3 food | 0 | 0 | 0 | 0 |
| Comparator | 3, reach a near target | 0 | 0 | 0 | 0 |
| Comparator | 7, reach a far target | 0 | 0 | 0 | 0 |
| Comparator | 6, collect 3 food | 0 | 0 | 0 | 0 |

Every one of these 480 visits took 3000 steps, the cap, except the agent's
visit to goal 3 in cycle 0 on seed 15472145577556848196, which achieved the
goal after 1263 steps. The food goal was achieved on no visit by either arm,
so the caution about it under the protocol's [design](protocol.md#design) has
nothing to apply to.

**The other goals.** Seeds achieving the visit, of 20, by cycle, with the
number of those at the attempt's first step in parentheses. The two survive
goals were achieved at 200 and 800 steps on every visit of both arms and are
omitted.

| Goal | Agent, cycle 0 | 1 | 2 | 3 | Comparator, cycle 0 | 1 | 2 | 3 |
|---|---|---|---|---|---|---|---|---|
| 1, collect 2 wood | 12 (6) | 19 (19) | 20 (19) | 20 (20) | 14 (4) | 18 (18) | 19 (19) | 20 (20) |
| 2, collect 2 stone | 1 (0) | 3 (3) | 6 (6) | 8 (8) | 1 (0) | 5 (3) | 5 (5) | 5 (5) |
| 4, collect 4 wood | 11 (8) | 17 (17) | 20 (20) | 20 (20) | 12 (11) | 17 (17) | 19 (19) | 19 (19) |
| 5, craft an axe | 2 (2) | 5 (3) | 6 (6) | 9 (9) | 2 (1) | 5 (5) | 5 (5) | 5 (5) |
| 8, collect 2 gold | 2 (2) | 4 (4) | 8 (6) | 11 (11) | 2 (2) | 4 (4) | 4 (4) | 6 (6) |
| 9, craft a boat | 18 (18) | 18 (18) | 20 (20) | 20 (20) | 17 (17) | 19 (18) | 20 (20) | 20 (20) |
| 10, collect 8 wood | 13 (12) | 17 (17) | 17 (17) | 17 (17) | 15 (14) | 17 (16) | 18 (18) | 18 (18) |
| 12, collect 4 gold | 2 (2) | 4 (4) | 7 (7) | 10 (10) | 1 (1) | 3 (3) | 3 (3) | 5 (5) |

Over its 1040 attempts the agent achieved 528 and the comparator 503. Without
the two survive goals the counts are 368 and 343, of which 351 and 325 came at
the attempt's first step. This is what each arm retained, as
[item 4](protocol.md#what-derivation-settles) describes: a goal whose condition
the inventory already meets is satisfied one step after it is installed. The
counts rise from cycle to cycle in both arms, which is why the protocol does
not use a count of goals achieved as its outcome.

**Position at the end of each reach visit**, as x, y. The record does not hold
the targets' positions, so these tables do not show how far from a target a
visit ended. The agent's end positions range over the whole world, with a
coordinate on its edge (0 or 1023) on 5 of its 160 visits; the comparator's
lie between 270 and 771 in x and between 199 and 645 in y.

Agent:

| # | Cycle 0, goal 3 | Cycle 0, goal 7 | Cycle 1, goal 3 | Cycle 1, goal 7 | Cycle 2, goal 3 | Cycle 2, goal 7 | Cycle 3, goal 3 | Cycle 3, goal 7 |
|---|---|---|---|---|---|---|---|---|
| 1 | 433, 612 | 300, 656 | 189, 725 | 563, 560 | 716, 477 | 647, 392 | 380, 532 | 291, 697 |
| 2 | 445, 730 | 423, 748 | 621, 794 | 544, 712 | 633, 807 | 691, 893 | 547, 1023 | 615, 884 |
| 3 | 484, 532 | 369, 538 | 565, 900 | 679, 920 | 737, 1017 | 705, 1014 | 954, 928 | 555, 515 |
| 4 | 497, 27 | 297, 253 | 362, 509 | 689, 179 | 729, 22 | 424, 0 | 56, 35 | 242, 294 |
| 5 | 686, 569 | 562, 567 | 179, 368 | 125, 236 | 85, 192 | 297, 116 | 925, 78 | 529, 170 |
| 6 | 626, 630 | 616, 624 | 604, 504 | 488, 400 | 615, 659 | 544, 659 | 385, 685 | 449, 955 |
| 7 | 590, 314 | 1001, 483 | 949, 76 | 682, 19 | 639, 370 | 334, 497 | 140, 342 | 88, 223 |
| 8 | 586, 344 | 672, 181 | 717, 61 | 575, 36 | 171, 154 | 185, 168 | 294, 391 | 263, 396 |
| 9 | 413, 537 | 391, 539 | 151, 460 | 50, 577 | 168, 479 | 2, 681 | 88, 626 | 140, 643 |
| 10 | 408, 476 | 674, 188 | 722, 189 | 948, 558 | 934, 504 | 919, 516 | 945, 464 | 1017, 542 |
| 11 | 738, 273 | 741, 473 | 758, 513 | 625, 430 | 625, 378 | 670, 259 | 689, 59 | 722, 113 |
| 12 | 348, 355 | 182, 360 | 26, 355 | 8, 454 | 190, 465 | 314, 587 | 329, 594 | 162, 531 |
| 13 | 620, 726 | 574, 348 | 593, 175 | 602, 110 | 840, 108 | 852, 39 | 935, 377 | 933, 349 |
| 14 | 449, 272 | 287, 657 | 836, 879 | 886, 814 | 1023, 582 | 1001, 564 | 931, 814 | 847, 677 |
| 15 | 392, 659 | 0, 763 | 92, 1017 | 419, 966 | 136, 974 | 228, 884 | 48, 186 | 88, 0 |
| 16 | 332, 619 | 196, 725 | 25, 950 | 102, 1011 | 9, 981 | 3, 730 | 59, 643 | 7, 899 |
| 17 | 426, 651 | 422, 437 | 580, 448 | 824, 469 | 1022, 273 | 993, 52 | 882, 43 | 884, 151 |
| 18 | 577, 497 | 514, 1021 | 855, 611 | 831, 697 | 663, 609 | 583, 134 | 718, 19 | 662, 109 |
| 19 | 449, 493 | 302, 640 | 250, 747 | 445, 711 | 667, 526 | 721, 499 | 631, 529 | 857, 554 |
| 20 | 443, 630 | 242, 592 | 311, 239 | 223, 339 | 441, 459 | 337, 3 | 425, 3 | 701, 56 |

Comparator:

| # | Cycle 0, goal 3 | Cycle 0, goal 7 | Cycle 1, goal 3 | Cycle 1, goal 7 | Cycle 2, goal 3 | Cycle 2, goal 7 | Cycle 3, goal 3 | Cycle 3, goal 7 |
|---|---|---|---|---|---|---|---|---|
| 1 | 393, 506 | 453, 551 | 377, 547 | 406, 518 | 327, 571 | 391, 580 | 361, 551 | 337, 530 |
| 2 | 491, 532 | 426, 511 | 435, 489 | 351, 509 | 371, 504 | 402, 516 | 365, 547 | 324, 533 |
| 3 | 616, 602 | 623, 614 | 602, 509 | 529, 536 | 563, 480 | 548, 484 | 547, 491 | 504, 472 |
| 4 | 537, 533 | 531, 517 | 565, 585 | 509, 534 | 479, 546 | 404, 627 | 392, 613 | 375, 645 |
| 5 | 567, 481 | 539, 502 | 565, 448 | 566, 488 | 514, 463 | 469, 420 | 490, 362 | 507, 361 |
| 6 | 456, 513 | 529, 396 | 593, 371 | 561, 355 | 555, 373 | 600, 376 | 488, 363 | 580, 380 |
| 7 | 476, 460 | 437, 547 | 529, 594 | 627, 561 | 689, 551 | 670, 569 | 706, 635 | 670, 638 |
| 8 | 547, 461 | 510, 499 | 553, 514 | 520, 482 | 499, 515 | 572, 565 | 518, 580 | 541, 589 |
| 9 | 394, 546 | 270, 509 | 328, 506 | 386, 538 | 375, 493 | 347, 433 | 330, 465 | 333, 484 |
| 10 | 422, 566 | 401, 579 | 282, 603 | 314, 640 | 311, 640 | 325, 630 | 339, 641 | 376, 644 |
| 11 | 575, 489 | 581, 453 | 588, 374 | 585, 393 | 596, 360 | 593, 231 | 573, 227 | 590, 199 |
| 12 | 465, 527 | 531, 529 | 434, 545 | 418, 539 | 368, 458 | 453, 509 | 510, 578 | 526, 495 |
| 13 | 562, 574 | 538, 598 | 544, 545 | 624, 533 | 584, 463 | 597, 503 | 636, 490 | 599, 470 |
| 14 | 487, 465 | 465, 448 | 428, 496 | 373, 508 | 423, 396 | 345, 385 | 349, 394 | 332, 371 |
| 15 | 571, 485 | 590, 539 | 592, 528 | 557, 615 | 593, 595 | 611, 645 | 621, 589 | 613, 508 |
| 16 | 589, 500 | 666, 515 | 736, 413 | 637, 417 | 596, 442 | 671, 452 | 648, 476 | 665, 512 |
| 17 | 463, 527 | 508, 486 | 599, 544 | 610, 543 | 666, 472 | 709, 384 | 665, 386 | 720, 405 |
| 18 | 539, 422 | 535, 459 | 554, 437 | 570, 416 | 693, 521 | 732, 524 | 747, 509 | 771, 511 |
| 19 | 579, 463 | 529, 443 | 495, 331 | 522, 305 | 570, 221 | 528, 281 | 429, 323 | 401, 356 |
| 20 | 452, 528 | 503, 487 | 407, 609 | 373, 627 | 385, 513 | 432, 551 | 387, 587 | 351, 579 |

**Learner columns of the outcome CSV.** Each row carries three values read at
the end of its attempt. The exploration rate is the binary32 value nearest
0.01 in all 1040 rows. The mean step size of the primitive controller lies
between 4.9168 × 10⁻⁵ and 5.0048 × 10⁻⁵ in every row. The mean absolute
temporal-difference error of the prediction demons lies between 5.2 × 10⁻⁸ and
0.86 in every row, and between 1.2 × 10⁻⁵ and 0.47 in the 20 final rows.

**Replacement and ranking counts of the campaign summary.** The feature tester
replaced between 2113 and 5530 units per seed, one unit per 21.8 to 22.1 agent
steps on every seed. At the end of the campaign each of the three option
models held 63 ranked positions on all 20 seeds.

**Resource use**, as observations of this host and not as performance claims.

| Quantity | Observed | Protocol |
|---|---|---|
| Agent steps | 1 629 978 in all; 46 596 to 120 466 per seed | At most 2 720 000; at most 136 000 per run |
| Comparator steps | 1 706 272 in all | The same bound |
| Steps per second, the core's figure for the agent's campaign | 50 to 56 per seed; 53.9 over all seeds, about 18.6 ms per step | Estimate of about 17 ms per step |
| Real time per run, agent and comparator | Between 894.1 and 2162.8 s | Deadline 14 400 s |
| CPU time, user plus system | 30 425 s in all, 8.45 core-hours | Limit 80 core-hours; estimate 6 to 14 |
| Peak memory per process, maximum resident set size | Between 141.3 and 159.0 MiB | UNKNOWN before the run |
| Concurrent processes | 4 | 4 |
| Runs | 20, no rerun | 20, at most 40 |

The run block took 2 hours 12 minutes 6 seconds, from 08:33:42Z to 10:45:48Z,
against an estimate of two to four hours and a limit of 20. Those two times
were read from the local clock when the block was started and when it
returned; they are not part of the retained record, and nothing attests the
local clock. The 20 real times in the record sum to 30 599 s, which four
workers cannot finish in less than 127.5 minutes. Other work ran on the host
during the block, which changes wall time and no outcome.

The protocol left open whether the step rate and the memory of study
first-pass-vs-chance hold beyond 34 000 steps. In this run, over campaigns of
46 596 to 120 466 agent steps, the rate was 50 to 56 steps per second where
that study observed 47 to 62, and peak memory was 141.3 to 159.0 MiB where it
observed 134 to 157. These are observations of one run on one host.

## Calculations

By bash from the root of the checkout. The counts are the output of the
protocol's calculation block on the extraction. Each seed's costs,
improvements and D, in the order of the seed list, and the summary of D:

```bash
study=docs/studies/repeated-visits-vs-chance
while read -r seed; do
  awk -v s="$seed" '$1 == s { a = $5 - $6; c = $8 - $9; print s, $5, $6, a, $8, $9, c, a - c }' \
    "$study/results-r2.txt"
done < "$study/seeds.txt"
awk '$2 == 0 && $3 == "complete" { a = $5 - $6; c = $8 - $9; d = a - c; s += d; v++
    if (v == 1 || d < lo) lo = d
    if (v == 1 || d > hi) hi = d
    na += (a >= 1200); nd += (d >= 1200); nc += (c >= 1200) }
  END { print "mean D", s / v, "least", lo, "greatest", hi
    print "A >= 1200:", na + 0, "D >= 1200:", nd + 0, "comparator improvement >= 1200:", nc + 0 }' \
  "$study/results-r2.txt"
```

One line per attempt, written outside the checkout: the arm, the seed's number
in the list, the cycle, the goal, the steps, whether it was achieved, and the
position at its end:

```bash
study=docs/studies/repeated-visits-vs-chance
attempts="${TMPDIR:-/tmp}/repeated-visits-r2-attempts.txt"
n=0
while read -r seed; do
  n=$((n + 1))
  awk -F, -v n="$n" 'NR > 1 && !/^#/ { print "agent", n, int(r++ / 13), $1, $4, $5, $10, $11 }' \
    "$study/observations/r2/seed-$seed/outcomes.csv"
  awk -v n="$n" '$1 == "#" && $2 == "baseline" { for (i = 3; i <= 9; i++) { split($i, f, "="); v[i] = f[2] }
      print "comparator", n, v[3], v[4], v[6], v[7], v[8], v[9] }' \
    "$study/observations/r2/seed-$seed/outcomes.csv"
done < "$study/seeds.txt" > "$attempts"
```

From those lines: the seeds achieving each visit and how many at the first
step, by arm, goal and cycle; the reach and food visits achieved; each arm's
totals; and the positions at the end of the reach visits:

```bash
attempts="${TMPDIR:-/tmp}/repeated-visits-r2-attempts.txt"
awk '{ k = $1 " " $4 " " $3; a[k] += $6; f[k] += ($6 == 1 && $5 == 1) }
  END { for (k in a) print k, a[k], f[k] }' "$attempts" | sort -k1,1 -k2,2n -k3,3n
awk '($4 == 3 || $4 == 6 || $4 == 7) && $6 == 1' "$attempts"
awk '{ t[$1]++; a[$1] += $6; s[$1] += $5
    if ($4 != 0 && $4 != 11) { p[$1] += $6; f[$1] += ($6 == 1 && $5 == 1) } }
  END { for (k in t) print k, t[k], a[k], s[k], p[k], f[k] }' "$attempts" | sort
awk '$4 == 3 || $4 == 7 { k = $1 " " $2; p[k] = p[k] " " $7 "," $8 }
  END { for (k in p) print k p[k] }' "$attempts" | sort -k1,1 -k2,2n
```

The learner columns are the fields demon_error, epsilon and mean_alpha of each
outcome row:

```bash
study=docs/studies/repeated-visits-vs-chance
cat "$study"/observations/r2/seed-*/outcomes.csv | awk -F, '!/^#/ && $1 != "index" { r++
    e[$8]++
    if (r == 1 || $9 + 0 < al) al = $9 + 0
    if (r == 1 || $9 + 0 > ah) ah = $9 + 0
    if (r == 1 || $7 + 0 < dl) dl = $7 + 0
    if (r == 1 || $7 + 0 > dh) dh = $7 + 0 }
  END { for (k in e) print "epsilon", k, e[k], "rows"
    printf "mean_alpha %.5g to %.5g; demon_error %.3g to %.3g; rows %d\n", al, ah, dl, dh, r }'
```

Agent steps, steps per second and the replacement count are the fields
total_steps, steps_per_sec and retire_count of each CSV's last line, and the
rate over all seeds is the sum of total_steps over the sum of wall_ms. The
ranked positions are the ranked_slots line of the standard output. Real, user
and system time and the maximum resident set size are the resource report at
the end of the standard error:

```bash
study=docs/studies/repeated-visits-vs-chance
while read -r seed; do
  d="$study/observations/r2/seed-$seed"
  printf '%s %s%s %s\n' "$seed" \
    "$(tail -n 1 "$d/outcomes.csv" | tr ' ' '\n' | awk -F= '$1 == "total_steps" || $1 == "steps_per_sec" || $1 == "retire_count" { printf "%s ", $2 }')" \
    "$(awk '$2 == "real" { printf "%s %s %s ", $1, $3, $5 } /maximum resident set size/ { printf "%.1f", $1 / 1048576 }' "$d/stderr.txt")" \
    "$(sed -n 's/^  ranked_slots: //p' "$d/stdout.txt" | tr ' ' '/')"
done < "$study/seeds.txt"
```
