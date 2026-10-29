# Contributing

Questions, research criticism, documentation improvements and code contributions
are welcome. Open an [issue](https://github.com/rbeauchamp/acorn/issues) with the
question or problem and links to the relevant text, equation or source. You do
not need a proposed fix or Lean expertise to report something unclear.

For a substantial implementation or empirical study, discuss the research need
and scope before starting. For a focused code change, explain its intended
semantics, assumptions and implementation owner in the pull request. Use
[SECURITY](SECURITY.md) for private vulnerability reports.

## Working on code and proofs

[AGENTS](AGENTS.md) is the engineering and review policy: proof-first correctness,
learned-only boundaries, prior-art admission, and delivery requirements. Follow
its [review and delivery](AGENTS.md#review-and-delivery) section for checks,
signed commits and independent review. The shipped skills under .agents/skills
provide the review workflow, proof-specific questions and the Regula rules for
writing Lean.

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
opens, also requires the [Regula audit](docs/verification.md#regula-audit).

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

Acorn's missions serve [Oak Lab's mission](https://oaklab.ai/mission):
discovering and implementing algorithms that allow agents to achieve goals in
big worlds, and formally proving that they work—that the agent achieves goals
over a formally modelled class of big worlds. In Acorn, missions are that work
of discovering algorithms and proving that they work, and each mission's
acceptance is decided by the stated theorem or contract checked by Lean's
kernel and the repository gate (`./scripts/gate.sh`).

An Acorn mission is accepted by a proof rather than a benchmark score because a
score measures a finite set of cases, while a theorem covers every world in the
class it states. A score on a fixed evaluation suite can be high without
showing that the agent learns or achieves goals in general; for example, an
audit of [ARC-AGI-3](https://docs.arcprize.org/)'s 25 public games found that
all 25 are reachable by non-intelligent strategies and 10 are solvable in a
single blind step (Liew, 2026,
[arXiv:2605.25931](https://arxiv.org/abs/2605.25931)). Running the agent in its
worlds ([ARC-AGI-3](https://docs.arcprize.org/) games or Microduck) still
matters as a smoke test and demonstration, never acceptance evidence.

Because the mission is to discover and implement algorithms, a mission's
theorem is about an executable Acorn definition—the algorithm itself. A proof
that some algorithm merely exists, without exhibiting an executable definition,
is not a mission result, though it may serve as a lemma. Proofs about that
executable definition may use Lean's standard classical axioms (propext,
Quot.sound and Classical.choice, the standard-logical profile enforced by the
[Regula audit](docs/verification.md#regula-audit) via
`lean/foundation_manifest.json` and `lean/AcornTools/AxiomPins.lean`), since
the algorithm is explicit in the running code and Acorn's gate refuses
noncomputable executing declarations
([#132](https://github.com/rbeauchamp/acorn/issues/132)).

- **What a mission is:** a GitHub issue labelled mission whose contract, the
  exact Lean theorem statement or decision contract to establish, is frozen in
  the issue and may not be weakened. Each mission states the theorem or contract
  that decides its acceptance, checked by Lean's kernel and `./scripts/gate.sh`;
  runs of the agent in its worlds are demonstrations, not acceptance evidence.
  Category labels mark the kind of work: `mission:proof` for proofs over
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
  [open missions](https://github.com/rbeauchamp/acorn/issues?q=is%3Aopen+label%3Amission)
  or run `gh issue list -R rbeauchamp/acorn --label mission`.
- **How to claim it:** open a pull request that closes the issue (`Closes #<id>.`
  in the description), or comment claim on the issue; a claim comment lapses
  after seven days without a pull request that passes the gate.
- **Files a mission may touch:** modify only the modules and documents the
  mission names (such as the target modules in `lean/Acorn/` or
  `lean/AcornVerif/`, the decision registries `lean/Acorn/Decisions.lean` and
  `lean/AcornVerif/Decisions.lean`, `docs/` or `site/`). Files that make up
  Acorn's trusted base (`scripts/`, `lean/lakefile.lean`, `site/lakefile.toml`,
  `lean/AcornTools/`, `lean/AcornTools.lean`, `lean/Bootstrap.lean`, `lean/os/`
  and `.github/`) are listed in [CODEOWNERS](.github/CODEOWNERS), which requests
  the owner's review on every pull request that changes them, and only the
  owner's account, the one with write access, merges outside pull requests; do
  not touch them unless the mission contract explicitly requires it.
- **Gate to pass:** every mission pull request must pass `./scripts/gate.sh`
  (which provisions dependencies, runs `./scripts/verify.sh build-executing` and
  `./scripts/verify.sh` each under its 360-second deadline, and runs the Regula
  audit `./scripts/lean.sh lint`) and keep the sections of the
  [pull request template](.github/pull_request_template.md).
- **Credit:** squash merges keep the contributor's Git authorship on main, and
  the pull request description credits both the human contributor and the AI
  agent or model.

## Scientific evidence

Ordinary engineering needs implementation, proofs, useful documentation and a
concise PR, not a scientific dossier. Do not run a study to replace an unresolved
proof obligation. Scientific execution requires explicitly authorized scope.

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
