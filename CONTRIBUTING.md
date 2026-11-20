# Contributing

Questions, research criticism, documentation improvements and code contributions
are welcome, including from AI agents directed by contributors. Open an
[issue](https://github.com/rbeauchamp/acorn/issues) using the
[issue templates](.github/ISSUE_TEMPLATE) (or a blank issue for a question) with
the question or problem and links to the relevant text, equation or source; see
[SUPPORT](SUPPORT.md) for where to ask questions and what to include. You do
not need a proposed fix or Lean expertise to report something unclear.

For a substantial implementation or empirical study, discuss the research need
and scope before starting. For a focused code change, explain its intended
semantics, assumptions and implementation owner in the pull request. Participation
is governed by the [Code of Conduct](CODE_OF_CONDUCT.md); use
[SECURITY](SECURITY.md) for private vulnerability reports.

## Working on code and proofs

[AGENTS](AGENTS.md) is the engineering and review policy: proof-first correctness,
learned-only boundaries, prior-art admission, and delivery requirements. Follow
its [review and delivery](AGENTS.md#review-and-delivery) section for checks,
signed commits and the review an author runs; the
[review protocol](#review-protocol) below says which review decides when work
is complete. The shipped skills under .agents/skills
provide the review workflow, proof-specific questions and how the
[Regula audit](docs/verification.md#regula-audit) applies to writing Lean.

Claude Code reads AGENTS.md by itself only when no CLAUDE.md or CLAUDE.local.md
applies to the checkout, including a CLAUDE.md in a parent directory. If one
does, add `@AGENTS.md` to a personal, uncommitted CLAUDE.local.md at the
checkout root.

For each change, explain the intended behavior, its implementation and proof
owners, and any assumptions in the PR, whose description keeps the sections of
the [pull request template](.github/pull_request_template.md). Run
`./scripts/verify.sh` from the checkout and report its actual result and
material limits. The merge gate,
`./scripts/gate.sh`, which the no-mistakes pipeline runs before a pull request
opens, also requires the [Regula audit](docs/verification.md#regula-audit),
lean-intent's confirmation and implementation checks of Acorn's intent records, and
the check that the declarations a pinned target reads are unchanged.

Pull requests are squash-merged: the PR title becomes the commit header on main
and the PR body its message. Title each PR as a
[Conventional Commits](https://www.conventionalcommits.org/en/v1.0.0/) header,
`type(scope)!: summary`, with the type one of feat, fix, docs, refactor, perf,
test, build, ci, chore or revert. The scope is optional text without parentheses;
the optional `!` marks a breaking change, which also carries a
`BREAKING CHANGE:` footer in the body. The no-mistakes pipeline drafts each
title in this form, and the [PR title check](.github/workflows/pr-title.yml),
started by hand, rejects any other title.
Releases follow [Semantic Versioning](https://semver.org/): fix implies a patch
release, feat a minor release and a breaking change a major release, or a minor
release before 1.0.

## Review protocol

One protocol governs every pull request, whoever wrote it: an outside
contributor, an agent they direct, the owner or one of the organization's
agents. It decides when work is complete. No statement by an author decides
that, and neither does a passing gate or the verdict of a reviewer the author
chose.

The maintainers are the owner and the organization's agents
([triage and response](#triage-and-response)). A model family is the models of
one developer.

### Which review a pull request gets

A pull request gets the referee's review when it does any of these:

- it claims to complete or advance a mission, or an issue that asks for a
  proof or a discovery;
- it adds or changes the statement of a theorem about the agent, which is a
  theorem that says what the executed agent or one of its learners does, or
  it adds or changes a specification, which is a statement of what is to be
  established: a target, an intent record, a decision contract, the
  [mission contract](docs/mission-contract.md) or an issue's contract;
- it claims learning or discovery.

Every other pull request is an ordinary change. The line is drawn by what a
pull request claims or changes, never by who wrote it or by how its author
describes it. The maintainers decide it at triage, from the pull request's
head, and decide it again when a push changes what the pull request claims or
changes. In doubt, a pull request gets the referee's review.

An ordinary change is reviewed by its author, with one independent reviewer,
as [AGENTS](AGENTS.md#review-and-delivery) and the review skills under
.agents/skills describe. An author may run that review on any pull request.
For a pull request under the referee's review it helps the work and discharges
nothing of this protocol.

### The gate on the exact head

GitHub runs the gate on a pull request's head commit and shows the result on
the pull request, where the contributor and the maintainers see the same
result. A head on which GitHub shows no run of the gate has not been checked
there, which is neither a pass nor a failure. Before a merge, the maintainers
confirm the gate's pass on that exact head commit, by running
`./scripts/gate.sh` on it ([merge authority](#triage-and-response)). A result
on an earlier head counts for nothing.

### The referee's review

**Who the referee is.** The maintainers assign the referee. The author never
does, and an author's request for a referee or against one, in the pull request
or anywhere else, has no weight: the maintainers neither take nor pass over a
referee because of it. The rule of assignment is this:

- the referee is of another model family than every model that did the work,
  or is a person. Whom this admits for work a person did with no model is the
  maintainers' call;
- the referee took no part in the work: it did not write it, advise on it or
  review it for the author;
- where the author is one of the maintainers, another of them assigns: an
  agent other than the one that did the work, or the owner;
- the assignment is written on the pull request: who assigned, and the
  referee's model family or that the referee is a person.

A review by anyone who was not assigned in this way, from any account, is an
ordinary comment. It is welcome as criticism and discharges nothing.

**What the referee reads, and against what.** The maintainers give the referee
the pull request at its head commit, the issue it names and Acorn's tracked
text. The author addresses the referee only on the pull request. The review is
adversarial: for each claim the referee looks for the cheapest way it could be
false, or weaker than the pull request says, while every check passes. It reads
the claims against the issue's contract, against Acorn's
[proof standard](.agents/skills/proof-review/references/proof-standard.md),
which includes its two questions on credit to learning, and against
[AGENTS](AGENTS.md). It reads the Lean statements themselves, not their names
or the description. The referee does not repair the work.

**The report.** The referee's report is a comment on the pull request, and
stays there. It names the head commit it read and has four parts:

- what is claimed: each claim of the pull request, with the theorem,
  definition or text that is to carry it;
- what is established: for each claim, whether it is established, established
  under hypotheses that the report names, or not established, and which
  statement was read to say so;
- what must change: the findings, each with its place, its reason and what
  would correct it;
- a verdict: accept, revise or reject.

A report that restates the gate's result is no report. The gate shows that
proofs are sound; it does not show that they are proofs of what is claimed.

**Findings and revision.** The findings go back to the author on the pull
request. The author answers each one there, by a change to the work or by a
reasoned objection. A finding stays open until the referee withdraws it or the
maintainers rule on it in writing on the pull request. After a push, the new
head has no report until the referee has read it and reported again. This
repeats until the report is clean or the author withdraws. A report is clean
when its verdict is accept and no finding is open. An author may withdraw at
any time; the pull request is then closed. A verdict of reject says that no
revision can make the claim good: the pull request is closed, and new work is
a new pull request.

**A claim of discovery.** A pull request that claims a discovery, in the sense
of [prior art and discovery](docs/prior-art-review.md#prior-art-and-discovery),
has two referees, each assigned by the rule above. Neither sees the other's
report before filing its own: each files with the maintainers, who post both on
the pull request once they hold both. Whether the two are also of different
model families from each other is the maintainers' choice. Both reports must
be clean.

### When work is complete

Work under the referee's review is complete when its pull request has merged
and, on the head commit that merged, each referee's report is clean and the
gate has passed. An ordinary change is complete when its pull request has
merged with the gate's pass on its head commit.

Until then the work is submitted, under review or accepted by its referees,
and nothing calls it complete: not its description, a commit message, a
comment, or its author's last message. A description says what the work
claims. An issue's own section on completion or acceptance says what is to be
established, and its line on the gate names one check; whether a pull request
has established it is decided here.

The owner's merge and the owner's review of changes to the trusted base are as
[triage and response](#triage-and-response) states them; this protocol changes
neither. A pull request under the referee's review does not merge before its
report is clean.

### What the protocol does not promise

No date is promised for an assignment, a report or a merge; the target for a
first response is in [triage and response](#triage-and-response). The protocol
is a written rule that no check of the gate executes, and a referee can be
wrong ([verification](docs/verification.md#review-protocol-and-the-rule-on-runs)).

## Missions for outside contributors and agents

[Missions](docs/missions.md) is the way in: what a mission costs and pays, step-by-step
instructions an agent can follow, and how the [mission board](docs/mission-board.md)
credits what has landed. This section states the rules those instructions rest on.

Acorn's missions serve [Oak Lab's mission](https://web.archive.org/web/20260909143403/https://oaklab.ai/mission):
discovering and implementing algorithms that allow agents to achieve goals in
big worlds, and formally proving that they work—that the agent achieves goals
over a formally modelled class of big worlds. In Acorn, missions are the work
that serves it, and each mission
states the theorem or contract to establish, which Lean's kernel and the
repository gate (`./scripts/gate.sh`) check; the
[review protocol](#review-protocol) decides when a mission's pull request is
accepted. Landing a mission is not
by that fact a discovery: a discovery is an algorithm nobody has published, and
a mission that implements or proves a published algorithm is prior-art work.
[Prior art and discovery](docs/prior-art-review.md#prior-art-and-discovery)
states both terms and how work between them is judged.

An Acorn mission is accepted by a proof rather than a benchmark score because a
score measures a finite set of cases, while a theorem covers every world in the
class it states. A score on a fixed evaluation suite can be high without
showing that the agent learns or achieves goals in general; for example, an
audit of [ARC-AGI-3](https://docs.arcprize.org/)'s 25 public games found that
all 25 are reachable by non-intelligent strategies and 10 are solvable in a
single blind step (Liew, 2026,
[arXiv:2605.25931](https://arxiv.org/abs/2605.25931)). Running the agent in its
worlds ([ARC-AGI-3](https://docs.arcprize.org/) games or
[Microduck](https://github.com/pollen-robotics/microduck)) still
matters as a smoke test and demonstration, never acceptance evidence.

Because the mission is to discover and implement algorithms, a mission's
theorem is about an executable Acorn definition—the algorithm itself. A proof
that some algorithm merely exists, without exhibiting an executable definition,
is not a mission result, though it may serve as a lemma. Proofs about that
executable definition may use Lean's standard classical axioms (propext,
Quot.sound and Classical.choice, the standard-logical profile enforced by the
[Regula audit](docs/verification.md#regula-audit), whose profile `lean/lakefile.lean`
states, and pinned for selected theorems by `lean/AcornTools/AxiomPins.lean`), since
the algorithm is explicit in the running code (Lean's compiler refuses compiled
code that reaches a noncomputable declaration, and mission
[#132](https://github.com/rbeauchamp/acorn/issues/132) adds a source-admission
check refusing noncomputable in executing modules).

- **What a mission is:** a GitHub issue labelled mission whose contract, the
  exact Lean theorem statement or decision contract to establish, is frozen and
  may not be weakened. Each mission states the theorem or contract
  that its pull request must establish, checked by Lean's kernel and
  `./scripts/gate.sh` and read by a referee under the
  [review protocol](#review-protocol);
  runs of the agent in its worlds are demonstrations, not acceptance evidence.
- **Where a contract is frozen:** a theorem's statement is frozen as a *target*,
  a Lean definition whose value is the statement, in a module under
  `lean/AcornVerif/Targets/`. Every build elaborates each target against the
  current definitions, so a statement cannot stop type-checking unnoticed.
  [CODEOWNERS](.github/CODEOWNERS) names the directory, which requests the
  owner's review on every pull request that changes it, and only the owner
  merges, so a change to a target is the owner's to make. A target fixes its
  own text: the definitions it names are outside the directory, and a mission
  does not change them either. `lean/AcornVerif/Targets/Registry.lean` lists the
  targets under each mission's issue number. A part of a contract that is not a statement
  to prove, such as a change to a decision's kind or the list of files a pull
  request may change, is frozen in the issue, and so is the whole contract of a
  mission with no target: there it is frozen while nobody but the owner has
  edited the issue last.
- **What a mission's kind is:** category labels mark the kind of work:
  `mission:proof` for proofs over
  executing definitions or mathematical models in `lean/AcornVerif/`,
  `mission:contract` for Regula decision contracts (`lean/Acorn/Decisions.lean`,
  `lean/AcornVerif/Decisions.lean`) and bounded host or gate checks,
  `mission:world` for spatial, kinematic and world-class specifications and
  proofs, and `mission:prior-art` for prior-art design passes, implementations
  and proofs. The first three issues labelled mission
  ([#163](https://github.com/rbeauchamp/acorn/issues/163),
  [#174](https://github.com/rbeauchamp/acorn/issues/174) and
  [#132](https://github.com/rbeauchamp/acorn/issues/132)) are starter missions
  of the proof and contract kind (`mission:proof` and `mission:contract`).
  [#135](https://github.com/rbeauchamp/acorn/issues/135) and
  [#134](https://github.com/rbeauchamp/acorn/issues/134) were checked and left
  unlabelled, with the reason recorded on each issue, until their contracts are
  exact: #135 must fix its slow-variation threshold and #134 its key matrix and
  feature-rank assumptions. Missions that prove learning and goal-achievement
  results come with Acorn's research agenda, with no dates promised.
- **How to find one:** browse
  [open missions](https://github.com/rbeauchamp/acorn/issues?q=is%3Aopen+label%3Amission),
  which are always current, or the [mission board](docs/mission-board.md), a dated
  copy; or run
  `gh issue list -R rbeauchamp/acorn --label mission --state open --limit 1000`
  (the command stops silently at its limit, 30 if none is given; if it returns as
  many results as the limit, run it again with a larger one until it returns fewer).
- **How to prove a target:** write a theorem whose statement is the target, in a
  file the mission names, and add an entry for it to the list in
  `lean/AcornVerif/Landings.lean`: the target's name, the theorem's name and the
  theorem. The entry compiles only when the theorem proves the statement the
  registry holds under that name (`statementOf`), so Lean's kernel, not a reader,
  decides that the target is proved. [Missions](docs/missions.md#step-5-do-the-work)
  shows both steps.
- **How to claim it:** open a pull request that closes the issue (`Closes #<id>.`
  in the description), or comment claim on the issue; a claim comment lapses
  after seven days without a pull request that passes the gate.
- **Files a mission may touch:** modify only the modules and documents the
  mission names (such as the modules that hold its proofs in `lean/Acorn/` or
  `lean/AcornVerif/`, the decision registries `lean/Acorn/Decisions.lean` and
  `lean/AcornVerif/Decisions.lean`, `docs/` or `site/`). A mission with targets
  also adds its entries to `lean/AcornVerif/Landings.lean`, and changes nothing
  under `lean/AcornVerif/Targets/` and no definition that a target names, which
  together are its contract. Files that make up
  Acorn's trusted base (`scripts/`, `lean/lakefile.lean`, `site/lakefile.toml`,
  `lean/AcornTools/`, `lean/AcornTools.lean`, `lean/Bootstrap.lean`, `lean/os/`
  and `.github/`) are listed in [CODEOWNERS](.github/CODEOWNERS), which requests
  the owner's review on every pull request that changes them, and only the
  owner's account, the one with write access, merges outside pull requests; do
  not touch them unless the mission contract explicitly requires it.
- **Gate to pass:** every mission pull request must pass `./scripts/gate.sh`
  (which provisions dependencies, runs `./scripts/verify.sh build-executing` and
  `./scripts/verify.sh` each under its 360-second deadline, and runs the Regula
  audit `./scripts/regula.sh`), keep the sections of the
  [pull request template](.github/pull_request_template.md), name its mission
  with `Closes #<id>.` in the description, and paste the output of
  `./scripts/gate.sh` from the exact pull request head.

### AI-generated contributions

Contributions written with or by AI agents and models are welcome across
missions, proofs, contracts, code and documentation. Pointing an agent at
[AGENTS](AGENTS.md), this guide and an open mission issue is an intended way to
contribute.

- **Responsibility:** the person directing the agent and submitting the issue or
  pull request is responsible for the contribution: confirming they have the
  right to submit it under the [MIT License](LICENSE), verifying citations and
  external claims against primary sources rather than submitting unverified
  model output, keeping within the mission's frozen contract and touched files,
  and running `./scripts/gate.sh` locally before opening or updating a pull
  request.
- **Credit:** squash merges keep the human contributor's Git authorship on main,
  and the pull request description credits both the human contributor and the AI
  agent or model, the agent or model on a line of the form `Agent: <name>`. The
  [mission board](docs/mission-board.md) counts a landed mission for the account
  that opened its pull request and for the name on that line
  ([what the board counts](docs/missions.md#what-the-board-counts)); it counts
  nothing else and grants no repository privilege.
- **Acceptance:** every contribution is judged by Lean's kernel, the frozen
  theorem or decision contract, `./scripts/gate.sh` and the
  [review protocol](#review-protocol), never by trust in the author or the
  model. That protocol, and no statement of the author or the model, says when
  it is complete.

### Triage and response

Acorn is maintained by one owner ([@rbeauchamp](https://github.com/rbeauchamp))
and the organization's autonomous review and verification agents. To make sure
every promise is one that an organization of one owner and its agents can keep:

- **Who looks at new issues and pull requests, and how soon:** the organization's
  agents and the owner triage new issues and gate-passing pull requests with a
  target initial response within seven days, without promising 24/7 coverage or
  a fixed merge date. Pull requests that do not name an issue or mission, omit
  the sections of the [pull request template](.github/pull_request_template.md),
  omit a passing `./scripts/gate.sh` result, or weaken a frozen mission contract
  may be closed on triage with a note explaining what is needed to reopen.
- **How a mission claim lapses:** as stated above under claiming, a contributor
  claims a mission by opening a pull request with `Closes #<id>.` or by
  commenting claim on the issue; a claim comment lapses after seven days without
  an open pull request that passes `./scripts/gate.sh`, freeing the mission for
  others. Multiple contributors or agents may work on an open mission
  concurrently; the first pull request that preserves the frozen contract and
  passes `./scripts/gate.sh` and review merges.
- **Merge authority and trusted-base review:** outside pull requests are merged
  only on the owner's word. Only the owner's account has write access to merge,
  after running `./scripts/gate.sh` on the exact pull request head (and a blind
  specification read-back when a pull request introduces or edits a
  specification), and for a pull request under the referee's review of the
  [review protocol](#review-protocol), only once each referee's report on that
  head is clean. Changes to the trusted-base files listed in
  [CODEOWNERS](.github/CODEOWNERS) are reviewed by the owner.
- **Keeping the board current:** whoever files or merges a mission may
  [regenerate the board](docs/missions.md#regenerating-the-board) in a pull request,
  and the organization's agents do so when they triage, with no schedule promised.
  The board states when it was derived; GitHub stays the record. A pull request that
  changes how the board is derived regenerates it in that same pull request, from
  GitHub's own pages, and its author reads the result against GitHub before it merges.

## Scientific evidence

Ordinary engineering needs implementation, proofs, useful documentation and a
concise PR, not a scientific dossier. Do not run a study to replace an unresolved
proof obligation. Scientific execution requires explicitly authorized scope.
A run is the last resort, a smoke test or a diagnostic that only chooses a
direction included: [AGENTS](AGENTS.md#correct-by-construction) says what must be
shown before one is proposed.

### What counts as a run

Stepping the agent, or one of its learners, over a sequence of percepts of any
length is a run, by whatever means: the compiled binary, evaluation inside
Lean, or a re-implementation in any language. The tool does not decide it. A
learner stepped alone is a run, and so is a copy of the agent's arithmetic in
another language.

Inside Lean, what makes a computation a run is that the step of the agent or
of a learner is evaluated or reduced on given percepts to see what it yields,
and no theorem of the pull request checks what it yielded. The command does
not decide it: an evaluation command, a reduction command, a tactic, and an
example stated to print or inspect a value all count.

Three things are not runs. Proof search is computing a value that a theorem in
the pull request then checks: the theorem states the value and Lean's kernel
checks it, so nothing rests on the computation having been right. Lean's
kernel checking a theorem of the pull request is never a run, whatever its
proof evaluates: the gate does that for every theorem. And trying to prove a
stated proposition and failing is proof work: a tactic that fails on a lemma
about every percept has evaluated no step on given percepts. Stating
propositions about what the step yields on given percepts and discarding them
is different. Each is an evaluation of the step, and it is a run unless a
theorem kept in the pull request checks the value.

[AGENTS](AGENTS.md#correct-by-construction) says what a run needs before it is
made. Every pull request lists, on the line the
[pull request template](.github/pull_request_template.md) gives it, every
computation made on the agent or on one of its learners in preparing the
change, every evaluation of the step on given percepts included, whether or
not anything of it was kept: what was computed and by what means, what it
showed, and either the theorem of the pull request that checks its value, or
that it was a run and under what authorization. Where none was made, it says
so. No check can see an
evaluation made on a contributor's machine, so this is a written rule and the
list is its trace
([verification](docs/verification.md#review-protocol-and-the-rule-on-runs)).

### Proof-shaped specifications

On 2026-11-19 the owner of the project stated where the habit of evaluation
comes back into work on Acorn and how it is stopped. This subsection is that
statement as the agents that maintain Acorn restate it: the substance is the
owner's and the wording is theirs.

AI agents trained on ordinary machine-learning practice rarely propose to skip
a proof. The habit returns through the way a task is specified: a
definition of done written as a number of tries or a success rate, with numbers
picked from a run; generalisation tested on held-out cases; a baseline
established by running the old agent; and then the observation that such a
statement is too hard to prove, so part of it may rest on a run. Recognise this
and stop it at the specification, in this order:

1. When a specification seems to need a run to check it, treat that first as a
   defect in the specification, and restate it as what the algorithm must
   maintain.
2. A proof-shaped specification of a learning algorithm has the parts a
   verified program has: an invariant true of every state the agent can reach;
   a condition under which, having nothing left to correct, its choice is the
   right one; and a measure that every mistake strictly lowers. Each is a
   statement about one arbitrary step. None names a horizon, a rate or a
   probability. A count of tries is then a bound that a result derives, never a
   threshold someone picked.

   The measure as just described does not by itself give a bound: one that a
   step which is not a mistake may raise, or whose values can fall without
   end, allows mistakes without limit. What the derivation needs is the
   mathematics of the agents that maintain Acorn and no part of the owner's
   statement. These conditions are sufficient: the measure takes its values
   in the natural numbers, every mistake strictly lowers it, and no other
   step raises it. Each of the last two is still a statement about one
   arbitrary step. Under them the mistakes of every run number at most the
   measure's value where the run starts. Where a count of tries also counts
   steps that are not mistakes, a bound on it does not follow from the
   measure alone: it needs its own argument that the algorithm makes
   progress.
3. Each device of evaluation has a mathematical counterpart, listed in the
   table below.
4. Difficulty of proof is an unresolved obligation and never a reason to lower
   the bar quietly. Lowering it is a trade of quality for cost and is the
   owner's decision.
5. A computed value is labelled computed, sets no threshold and completes
   nothing.

| Device of evaluation | Its mathematical counterpart |
|---|---|
| A success rate | A derived bound on mistakes that holds in every run |
| A held-out case | The scope of a quantifier over a family of problems |
| A baseline run of the old agent | A theorem that the old agent fails the same statement |
| Averaging over random draws | A statement for every sequence of draws |
| Noise | The worst case over what is irrelevant |
| A check that the agent took no shortcut | The family of problems excludes the shortcut; no statement about behaviour at one place can exclude it |

### Deliverable placement

Shared algorithms and proofs belong in maintained modules. A study owns its
protocol, original observations, canonical results and necessary source
identity. Preserve original bytes separately from semantic presentations. Never
rewrite an original observation to improve a claim or replay archived experience
into an agent. This source release's study data is under
[docs/studies](docs/studies).

### Protocol and evidence

Before observation, specify the semantic question, estimands, accepted/refuted
claims, initialization, stream, held-out population and prior access, comparisons,
exclusions, missing/failed-run treatment, stopping rules, resource budget and
uncertainty method. Distinguish confirmatory from exploratory analysis and report
negative and inconclusive results. For continual learning, account for adaptation,
lifetime memory/latency and the actual meaning of each ablation.

Use immutable protocol revisions and distinct run identities. Record exact source,
configuration and environment with each run. A content hash establishes integrity,
not preregistration, independent timing or scientific truth. Additional independent
timestamps serve only a stated requirement. Disclose access, deviations and
historical timing/authenticity limitations explicitly.

Every empirical citation must identify study, protocol revision, run and
comparison. Canonical calculations must resolve to the retained observations and
executed calculator owner. Preserve negative/inconclusive records. Qualification
requires the separate [promotion standard](docs/prior-art-review.md#default-promotion-and-demotion).
