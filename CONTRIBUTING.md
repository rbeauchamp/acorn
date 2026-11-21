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

## Review protocol

One protocol governs every pull request, whoever wrote it: an outside
contributor, an agent they direct, the owner or one of the organization's
agents. It decides when work is complete. No statement by an author decides
that, and neither does a passing gate or the verdict of a reviewer the author
chose.

The maintainers are the owner and the organization's agents
([triage and response](#triage-and-response)); a human maintainer is the owner
or another person granted maintainer authority on the repository. A model family
is the models of one developer.

### Which review a pull request gets

Every pull request requires an independent review under this protocol (by the
maintainers' per-PR assignment below, or under the single-maintainer interim
provision while Acorn has one human maintainer), and never by a reviewer the
author chose; any model reviewer must belong to another model family than every
model that did the work, and the applicable assignment rule determines when an
uninvolved person is eligible. What differs is the depth. A pull request gets
the referee's review when it does any of these:

- it claims to complete or advance a mission, or an issue that asks for a
  proof or a discovery;
- it adds or changes the statement of a theorem about the agent, which is a
  theorem that says what the executed agent or one of its learners does, or
  it adds or changes a specification, which is a statement of what is to be
  established, such as a target, an intent record, a decision contract, the
  [mission contract](docs/mission-contract.md), an issue's contract or the
  [viewer specification](docs/viewer-ux.md);
- it claims learning or discovery.

Every other pull request is an ordinary change and gets the short review. The
line is drawn by what a pull request claims or changes, never by who wrote it
or by how its author describes it. The maintainers decide it at triage, from the pull request's
head, title and description, and decide it again whenever what the pull
request claims or changes changes, by a push or by an edit of its title or
description. In doubt, a pull request gets the referee's review.

An author may run a review of their own on any pull request, with a reviewer
of their choice, as [AGENTS](AGENTS.md#review-and-delivery) and the review
skills under .agents/skills describe. It helps the work and discharges nothing
of this protocol, for any pull request.

This holds for the organization's own changes as for anyone's. The review this
protocol requires is the review of a reviewer assigned under the rule of
assignment below, posted as a comment on the pull request for the exact head
commit, title and description. A pre-PR or post-PR check made by a validation
pipeline discharges nothing of the protocol on its own without that assignment
comment and the reviewer's posted unedited report or short review on the pull
request (and if a validation-pipeline run is relied on under the
single-maintainer provision below, both the assignment comment naming the head
commit and that unedited review on the pull request are still required).

### The gate on the exact head

GitHub runs the gate on a pull request's head commit and shows the job's result
on the pull request, where the contributor and the maintainers see the same
result. What the absence of a run or a failed run says of the checks is under
[working on code and proofs](#working-on-code-and-proofs). Before
a merge, the maintainers confirm the gate's pass on that exact head commit, by running
`./scripts/gate.sh` on it ([merge authority](#triage-and-response)). A result
on an earlier head counts for nothing.

### The referee's review

**Who the referee is.** The maintainers assign the referee (and for a short review,
the reviewer). The author never does, and an author's request for a reviewer or
against one, in the pull request or anywhere else, has no weight: the
maintainers neither take nor pass over a reviewer because of it. Outside the
cases covered by the single-maintainer interim provision below, each pull request
(including every pull request once Acorn has more than one human maintainer, any
fallback review when the interim designation cannot apply, and the second
referee on a claim of discovery) receives an individual maintainer-led
assignment:

- the referee is of another model family than every model that did the work,
  or is a person. Whom this admits for work a person did with no model is the
  maintainers' call;
- the referee took no part in the work: it did not write it, advise on it or
  review it for the author;
- where the author is one of the maintainers, another of them assigns: an
  agent other than the one that did the work, or a human maintainer;
- the assignment is written on the pull request: who assigned, and the
  referee's model family or that the referee is a person.

**Single-maintainer interim provision (owner-confirmed 2026-11-21).** While
Acorn has only one human maintainer, independent human maintainer cross-checking
on every pull request is unavailable. During this single-maintainer phase,
independent review remains mandatory on every pull request (by an external
model of another model family than every model that did the work, or an
uninvolved person where the general rule above admits one), with the same
referee's review or short review depth, exact head commit binding, findings, and
verdict of accept, revise or reject, plus exact-head `./scripts/gate.sh` and
any blind specification read-back required at merge under
[triage and response](#triage-and-response). Under this provision, the external
model configured as the analyzer/verifier in Acorn's no-mistakes validation
pipeline satisfies the protocol by standing owner designation (whether run via
no-mistakes or standalone against the exact pull request head, title and
description) when all of the following hold:

- an assignment comment is written on the pull request recording the owner's
  standing single-maintainer designation, the designated reviewer's model
  family, and the exact head commit;
- the reviewer's report or short review for that exact head commit, title and
  description is posted on the pull request, unedited except for any redaction
  required by the security-vulnerability rule below (and for a claim of
  discovery, withheld and posted together with the second referee's report under
  the discovery rule below);
- **no same-family self-review:** the designated reviewer took no part in writing
  or fixing the change and belongs to a different model family than every model
  that authored, fixed or advised on the work. In particular, if any contributing
  or pipeline-fixing model (whether directed by an outside contributor, an
  organization agent or a human maintainer) belongs to the same model family as
  the validation pipeline's configured analyzer/verifier, that analyzer/verifier
  cannot satisfy the protocol for that pull request and another reviewer is
  assigned under the general rule above (of another model family or an
  uninvolved person). Earlier review findings and reports issued by that model
  strictly in its designated referee or analyzer/verifier role (under Findings
  and revision below or in designated validation-pipeline verification rounds on
  revised commits) do not disqualify it from re-reading revised commits (and an
  author may relay the designated reviewer's unedited report), whereas seeking
  optional author-side review, advice, writing or fixing from that model does
  disqualify it;
- for a claim of discovery requiring two referees, this standing designation
  supplies at most one cross-family referee and never substitutes for the second
  independent referee assigned under the general rule above.

A review qualifying under this provision enters [When work is complete](#when-work-is-complete) once it is clean (verdict accept with no open findings), alongside the passed exact-head `./scripts/gate.sh` and merge.

**Restoration of full maintainer-led assignment.** Once Acorn has more than one
human maintainer, this single-maintainer standing designation retires and the
general per-PR maintainer-led assignment rule above governs every pull request
on its own. As before, outside pull requests merge only on the owner's word,
and any change loosening protections or removing checks merges only on the
owner's recorded confirmation.

A review by anyone who was not assigned under the applicable rule above, from
any account, is an ordinary comment. It is welcome as criticism and discharges
nothing.

**What the referee reads, and against what.** The maintainers give the referee
the pull request at its head commit, the issue it names and Acorn's tracked
text. The author addresses the referee only on the pull request, except on a
finding that discloses a security vulnerability, where the private route
given under the report below is the only one. The review is
adversarial: for each claim the referee looks for the cheapest way it could be
false, or weaker than the pull request says, while every check passes. It reads
the claims against the issue's contract, against Acorn's
[proof standard](.agents/skills/proof-review/references/proof-standard.md),
which includes its two questions on credit to learning, and against
[AGENTS](AGENTS.md). It reads the Lean statements themselves, not their names
or the description. The referee does not repair the work.

**The report.** The referee's report is a comment on the pull request, and
stays there. It names the head commit it read, counts only for that commit
and for the pull request's title and description as it read them, and has
four parts:

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

A finding that discloses a security vulnerability is not written out on the
pull request. The referee reports it through the private route that
[SECURITY](SECURITY.md) names, and what is said of it afterwards goes by that
route too: the author's answer, any objection and the maintainers' ruling.
While such a finding is open, no text on the pull request says what the
vulnerability is or where it is, whoever writes it and wherever it stands:
not the title, not the description or any section of it, and so not the
commit message that the description becomes, and not a comment, a review or
a reply. The pull request says only that a finding of that kind is open, or
that it is closed. This rule comes before every sentence of Acorn's tracked
text that asks for or describes what is written on a pull request. What the
pull request template and the guides ask an author to record there, such as
each place found, a finding accepted or a computation made, is recorded for
such a finding in the private report, until the process that
[SECURITY](SECURITY.md) sets out makes it public. The report is not clean
until that finding is closed. Whether a finding discloses a security
vulnerability is the maintainers' call: one that they judge does not is
written out, answered and ruled on on the pull request like any other, and
nothing else is kept off the pull request under this rule. The same holds
for a short review and its reviewer.

**Findings and revision.** The findings written out in the report go back to
the author on the pull request. The author answers each of them there, by a
change to the work or by a reasoned objection, and each stays open until the
referee withdraws it or the maintainers rule on it in writing on the pull
request. A finding that discloses a security vulnerability goes back, is
answered and is ruled on in the same way, by the private route and not on
the pull request. After a push, or an edit
of the pull request's title or description, the pull request has no clean
report until the referee has read it again and reported: the rule covers
every field of a pull request that becomes part of the merged commit's
message or states a claim. This
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

### The short review

The maintainers assign the reviewer of an ordinary change by the rule of
assignment above, as they assign a referee, and write the assignment on the
pull request. The reviewer reads the change at its head commit, adversarially,
against what the description says the change does and against Acorn's rules
([AGENTS](AGENTS.md)), asking three things:

- does the change do what its description says, and nothing else;
- does it leave Acorn's tracked text true;
- does it claim or change anything that calls for the referee's review.

The short review is one comment on the pull request, and stays there. It
counts as the review of an ordinary change only if it names the head commit it
read and states, in a line each, the three things it checked: that the change
does what its description says and nothing else; that it leaves Acorn's
tracked text true; and that it claims nothing that calls for the referee's
review. Then it gives its findings, each with its
place, its reason and what would correct it, or says that it has none, and a
verdict of accept, revise or reject. A comment that gives only a verdict, or
only that there are no findings, does not count, and the pull request has no
clean review until one that does is posted. Findings and revision go as they do for a referee's
report: the author answers each finding written out in the review on the pull
request, such a finding stays open until the reviewer withdraws it or the
maintainers rule on it there, a finding that discloses a security
vulnerability is answered and ruled on by the private route and not on the
pull request, and after a push, or an edit of the pull request's title or
description, it has no clean review until the reviewer has read it again.
A short review is clean when it counts, its verdict is accept and no finding
is open.

### When work is complete

Work under the referee's review is complete when its pull request has merged
and, on the head commit that merged and for the title and description it
merged with, each referee's report is clean and the gate has passed. An ordinary change is complete when its pull request has
merged and, on the head commit that merged and for the title and description
it merged with, its short review is clean and the gate has passed.

Until then the work is submitted, under review or accepted by its referees or
its reviewer, and nothing calls it complete: not its description, a commit message, a
comment, or its author's last message. A description says what the work
claims. An issue's own section on completion or acceptance says what is to be
established, and its line on the gate names one check; whether a pull request
has established it is decided here.

The owner's merge and the owner's review of changes to the trusted base are as
[triage and response](#triage-and-response) states them; this protocol changes
neither. No pull request merges before the review this protocol gives it is
clean: each referee's report, or the short review.

### What the protocol does not promise

No date is promised for an assignment, a report, a short review or a merge;
the target for a first response is in
[triage and response](#triage-and-response). The protocol is a written rule
that no check of the gate executes, a referee or a reviewer can be wrong, and
no rule can see whether the three lines of a short review were written after
reading or copied as a formula
([verification](docs/verification.md#review-protocol-and-the-rule-on-runs)).

## Missions for outside contributors and agents

[Missions](docs/missions.md) is the way in: what a mission costs and pays, step-by-step
instructions an agent can follow, and how the [mission board](docs/mission-board.md)
credits what has landed. This section states the rules those instructions rest on.

Acorn's mission is to discover and implement algorithms that enable agents to
achieve goals in big worlds. Pursuing it here means formally proving that they
work—that the agent achieves goals over a formally modelled class of big worlds.
In Acorn, missions are the work that serves it, and each mission
states the theorem or contract to establish. Lean's kernel and the
repository gate (`./scripts/gate.sh`) decide whether a theorem is proved and
whether the gate's checks pass. A referee reads the pull request against the
whole contract, the list of files it may change included, which no check
reads, and the [review protocol](#review-protocol) decides when a mission's
pull request is accepted. Landing a mission is not
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
  that its pull request must establish. Lean's kernel and
  `./scripts/gate.sh` decide whether a theorem is proved and whether the
  gate's checks pass, and a referee reads the pull request against the whole
  contract under the [review protocol](#review-protocol);
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
  not touch them unless the mission contract explicitly requires it. One
  document under `docs/` is also the owner's,
  [how a submission on learned agent state is checked](docs/learned-state-check.md):
  [CODEOWNERS](.github/CODEOWNERS) is the list of every such path, and a
  mission does not touch a path it names unless its contract explicitly
  requires it.
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
  learned-state result. It certifies that the goal the contributor wrote holds
  of the run of the agent with the mechanism in every world of the family, at
  every seed, and that for each agent it is compared with, whichever rule or
  schedule that agent is given, and for each seed, there is a world of the
  family in which the goal fails of that agent's run. It does not certify that
  the agent's run differs from a compared run in every world of the family.
  Nor does it certify that the goal is a task anyone would pose: a complete
  result is also one, over the same worlds, for the goal that asks only that
  the run be the agent's own at some seed
  (`AcornVerif.LearnedState.Result.recognized`). It goes to a
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
  and [#297](https://github.com/rbeauchamp/acorn/issues/297) bear on it and
  come ahead of #295 in the
  [roadmap's order](docs/roadmap.md#learned-agent-state-beside-the-active-rung);
  neither is a logical prerequisite of a complete result. #296 asks whether the
  standard agent's learners can make quick use of one added state feature
  within a stated horizon: a proved case in which they do need not meet all
  seven statements, an obstruction for one feature says nothing of several,
  and so its answer may leave part of this open. #297 asks for a reusable
  theorem about what the learners acquire after a first reward and for one
  designed place where a state feature enters the default agent; the seven
  statements name neither.
- **That the frame is not empty** is proved of a small agent of its own, not
  of Acorn's: `lean/AcornVerif/LearnedStateSmall.lean` proves all seven
  statements of it with one mechanism and one task
  (`AcornVerif.LearnedState.Small.inhabited`).
  `lean/AcornVerif/LearnedStateRefusals.lean` proves that the same small agent
  with the same mechanism has no complete result on two variants of that task:
  one whose goal gains an alternative that a constant answer satisfies
  (`AcornVerif.LearnedState.Small.alternative_refused`), and one over the
  worlds in which the cue the mechanism holds is itself the answer
  (`AcornVerif.LearnedState.Small.remembered_refused`). Both are statements
  about that agent with that mechanism. Two general theorems refuse a kind of
  result only under their hypotheses. No mechanism has a complete result on a
  task whose goal some agent, whose output is a function of the current
  percept, meets at some seed in every world of the family
  (`AcornVerif.LearnedState.Result.history_free_refused`). A mechanism has
  none on a task where, with that mechanism kept, stores fixed in advance meet
  the goal at some seed in every world of the family
  (`AcornVerif.LearnedState.fixed_stores_refused`).

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
  specification), and only once the review that the
  [review protocol](#review-protocol) gives the pull request, each referee's
  report or the short review, is clean on that head and for the title and
  description as they stand at the merge. A change to what the
  review protocol requires, allows or rules out merges only once the owner
  has confirmed it. Changes to the trusted-base files listed in
  [CODEOWNERS](.github/CODEOWNERS) are reviewed by the owner. Until the gate
  checks it, this holds as a practice: a change to those files prepared by the
  owner's agents that keeps or tightens a protection is read in full by the
  agent supervising the work and landed by the agent that coordinates them,
  under the owner's delegation of 2026-11-20; one that loosens a protection or
  removes a check is admitted only by the owner's own recorded words; and a
  pull request from any other account is read on the owner's side, its whole
  diff, before it is merged. No check enforces any of this yet.
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
learner stepped alone is a run, and so is stepping a copy of the agent's
arithmetic in another language.

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
stated proposition and failing is proof work and not a run. Where an attempt,
failed or not, evaluated the step on given percepts to see what it yields,
the criterion above decides: it is a run unless a theorem kept in the pull
request checks what it yielded. Stating
propositions about what the step yields on given percepts and discarding them
is different. Each is an evaluation of the step, and it is a run unless a
theorem kept in the pull request checks the value.

[AGENTS](AGENTS.md#correct-by-construction) says what a run needs before it is
made. Every pull request lists, on the line the
[pull request template](.github/pull_request_template.md) gives it, every
computation made on the agent or on one of its learners in preparing the
change, every evaluation of the step on given percepts included, whether or
not anything of it was kept: what was computed, by what means and what it
showed. An entry for a computation that stepped the agent or a learner over
one or more percepts, by any means, also names the theorem of the pull
request that checks its value, or says that it was a run and under what
authorization. Where none was made, it says so. No check can see an
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
