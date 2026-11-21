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
signed commits and independent review. The shipped skills under .agents/skills
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
the check that the declarations a pinned target reads are unchanged. When a pull
request is opened or reopened and at every push to it, from a branch of the
repository or of a fork, GitHub runs the gate on its head commit and shows the
job's result on the pull request. Neither the absence of a run of that job nor a
failed run is by itself the result of a check: the
[verification guide](docs/verification.md#build-and-source-inventory) names the
cases in which GitHub starts no run and says how to read a run's ending.

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

## Missions for outside contributors and agents

[Missions](docs/missions.md) is the way in: what a mission costs and pays, step-by-step
instructions an agent can follow, and how the [mission board](docs/mission-board.md)
credits what has landed. This section states the rules those instructions rest on.

Acorn's mission is to discover and implement algorithms that enable agents to
achieve goals in big worlds. Pursuing it here means formally proving that they
work—that the agent achieves goals over a formally modelled class of big worlds.
In Acorn, missions are the work that serves it, and each mission's
acceptance is decided by the stated theorem or contract checked by Lean's
kernel and the repository gate (`./scripts/gate.sh`). Landing a mission is not
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
matters as a smoke test and demonstration, never acceptance evidence, and each
such run needs the owner's authorization ([running a program](#running-a-program)).

Because the mission stated above asks for algorithms that are discovered and
implemented, a mission's theorem is about an executable Acorn definition—the
algorithm itself. A proof that some algorithm merely exists, without exhibiting
an executable definition,
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
  that decides its acceptance, checked by Lean's kernel and `./scripts/gate.sh`;
  runs of the agent in its worlds are demonstrations, not acceptance evidence.
- **Where a contract is frozen:** a theorem's statement is frozen as a *target*,
  a Lean definition whose value is the statement, in a module under
  `lean/AcornVerif/Targets/`. Every build elaborates each target against the
  current definitions, so a statement cannot stop type-checking unnoticed.
  [CODEOWNERS](.github/CODEOWNERS) names the directory, which requests the
  owner's review on every pull request that changes it, and only the owner
  merges, so a change to a target is the owner's to make. A target fixes its
  own text: the definitions it names are outside the directory, and a mission
  does not change them either. Where a pin file stands beside a frozen
  statement, the gate's frame check also refuses a change to the statement of
  a pinned theorem, or to the type or value of a pinned definition, among the
  declarations of the project's own modules that the frozen statement reaches,
  until the owner pins again (`lean/AcornTools/Frame.lean`). A theorem's proof
  is not part of the pin, so a change to a proof alone is not refused.
  The frame of a learned-state result, below, is pinned in this way.
  `lean/AcornVerif/Targets/Registry.lean` lists the
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

### Learned-state results and changes to the agent's learners

A result on learned agent state
([#295](https://github.com/rbeauchamp/acorn/issues/295)) is stated in a fixed
frame. [The frame of a learned-state result](docs/learned-state-frame.md) is
its plain-word account, which the owner confirmed on 2026-11-20. The Lean is
`lean/AcornVerif/Targets/LearnedState.lean` and
`lean/AcornVerif/Targets/LearnedStateAcorn.lean`, and the agent it names is
pinned by `lean/AcornVerif/Targets/LearnedStateAcorn.frame`.

- **What a submission adds:** a state mechanism, a family of worlds and a goal,
  and the choice of a standard configuration apart from the seed. It does not
  change the agent's learners, the way the agent chooses actions or the way it
  explores. This is narrower than issue #295 read before the frame was adopted:
  its text asks a contributor to change how the agent learns, and that text is
  revised by a separate change.
- **How a learner change lands:** separately, and first. It is its own pull
  request to the agent, which states and proves what the change is for on its
  own terms and passes the same review and the same gate as any other
  contribution. A change to the agent alters the type or value of definitions
  the frame pins, so the frame check fails until the pin file is made again;
  a change to a pinned theorem's proof alone does not. The pin file is in
  the owner's directory, so the new pin comes under the owner's review with the
  change, and the pull request merges only on the owner's word. Only then does
  a learned-state submission build its mechanism on the changed agent.
  Theorems already proved about the earlier agent have to be proved again for
  the new one, and a later result is compared against the changed agent, not
  against the agent as it stood before.
- **What a complete result is:** a proof of
  `AcornVerif.LearnedState.Acorn.Complete` for the submitted configuration,
  mechanism and task: the seven statements the account lists, from the agent's
  cold start, at every seed. It is necessary and not sufficient for a
  learned-state result. It certifies that the agent's run satisfies a statement
  the contributor wrote and that the named comparisons do not, and it goes to a
  referee with the eight questions the account lists. A submission that does
  not prove all seven is partial, and is recorded by which of them it proved,
  with any assumption stated.
- **What is not there yet:** Acorn's program does not yet run its agent with a
  mechanism. The grid interface keeps room for a mechanism's words: every
  observation its adapter builds leaves room for at least 32 of them
  (`Acorn.Handcrafted.Grid.frame_room`). The place where a mechanism plugs into
  the host is a separate change and the owner's. Until it lands, the frame
  states what a complete result is and nobody can produce one for the program
  as it runs. It is also not known whether any complete result exists for the
  agent as it stands. [#296](https://github.com/rbeauchamp/acorn/issues/296)
  bears on it: that issue asks whether the standard agent's learners can make
  quick use of one added state feature, and its answer may leave part of this
  open.
- **That the frame is not empty** is proved of a small agent of its own, not
  of Acorn's: `lean/AcornVerif/LearnedStateSmall.lean` proves all seven
  statements of it, and `lean/AcornVerif/LearnedStateRefusals.lean` shows
  cheap kinds of result that have no proof.

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
  theorem or decision contract, and `./scripts/gate.sh`, never by trust in the
  author or the model.

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
  specification). Changes to the trusted-base files listed in
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

### Running a program

On 2026-11-19 the owner of the project ruled that no one runs Acorn's agent, or
one of its learners, without the owner's authorization for that run: not the
compiled program, not evaluation inside Lean, not a re-implementation. So no
step of work on a change starts a program that steps the agent or a learner over
percepts unless the owner's authorization for that run is stated in the change's
intent. What the step is for, and what the run is called, do not matter: a look
at the viewer's page, a screenshot, a smoke test and a diagnostic are all
covered. A smoke test of the core is a run of a learner, and a smoke test of the
viewer with the core as its child is treated as one.

Some of Acorn's programs step a learner without being asked to. The viewer,
started with no state file in its run directory, starts in the running state,
and its supervisor launches its child process, which is the core unless the
command line names another command. The launcher `./scripts/start.sh` starts
the viewer with the core as its child and a request to start. The diagnostics
argument of `./scripts/verify.sh` runs the mutation audit, which runs the agent.

The Test instructions of `.no-mistakes.yaml` are the one place that says, for
each executable that `lean/lakefile.lean` declares, whether running it steps a
learner and how to drive it so that it does not. Read them before starting an
Acorn program, and treat a program or a way of running one that they do not name
as stepping a learner.

The rule forbids no other drive. Building, the merge gate and the audit tools
start no program that steps a learner, and neither do the drives those
instructions list, such as the viewer serving its page from an explicitly stopped state with a child command
that cannot be a core. Those drives are still asked for where a change alters
what a program does. A drive that steps a learner stays available on the owner's
authorization, for the run it names. A claim that cannot be shown without
stepping a learner is reported open with that reason, never driven.

The rule is an instruction, which the people and agents who work on Acorn
follow. No program refuses the run.

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
