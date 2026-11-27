# Acorn

Acorn's mission is to discover and implement algorithms that enable agents to
achieve goals in big worlds. We tackle the challenges of the
[Alberta Plan](https://arxiv.org/abs/2208.11173v3) by developing and verifying
continual learning and planning algorithms in Lean 4: the agent learns one
observation at a time from one continuous stream of experience, without replay
buffers or curated training data.

- **Live today (tile world and viewer):** Launch the browser viewer
  (`./scripts/start.sh`) to watch an agent explore a 1024 × 1024 tile world
  across a 13-goal curriculum using the `ranked` *research profile* (a named
  combination of agent mechanisms with hierarchical options, ranked learned
  features, discounted rewards, and checkpointing). The tile world is the
  initial development environment and has no standing beyond being the first
  world built.
- **Target worlds (open formalization):** Acorn's two chosen target world
  families are [ARC-AGI-3](https://docs.arcprize.org/) interactive games
  ([#71](https://github.com/rbeauchamp/acorn/issues/71)) and
  [Microduck](https://github.com/pollen-robotics/microduck) simulated biped
  scenes ([#173](https://github.com/rbeauchamp/acorn/issues/173),
  [#236](https://github.com/rbeauchamp/acorn/issues/236)). Pure Lean host and
  interface bindings for Microduck (`microduck-host`) are built while its
  simulator daemons live outside this repository
  ([design](docs/design.md#an-embodied-world-the-microduck)); verifying
  interface conformance and formalizing world-class conditions for either target
  family remain open
  ([obligation 13](docs/mission-contract.md#open-obligations)).
- **Verification and roadmap status:** Lean 4 proofs establish host-kernel
  correspondence (`executed_visits_closed_loop`), exact checkpoint round-trips
  (`load_saved`), and first-rung lemmas (`rung_memory_bounded`, `rung_finds`,
  `rung_credit`), while the conditional first-rung theorem (`rung_mission`,
  with six of eight premises open and using the 2026-11-03 comparison) leaves
  the mission theorem open on every rung ([roadmap](docs/roadmap.md)). On the
  first-rung grid-world class
  ([#230](https://github.com/rbeauchamp/acorn/issues/230), 7-step visits at seed 1,
  side 64, `primitive` profile, no deer or food), contract 2 conditions (a),
  (b), and the weaker Lean count form of (c) are proved (at most 49 members
  solved without experience in a class of at least 147 and at most 392, a share
  between an eighth and a third not shown to be small), with no claim yet that
  the class is big, needs perceiving, or that the executed agent learns there
  ([contract 2](docs/mission-contract.md#contract-2-what-makes-a-class-of-worlds-big)).
  Ahead of scaling external contributor missions,
  [Milestone 4](docs/roadmap.md#architectural-foundation-active-priority-ahead-of-scaling-external-missions)
  ([#321](https://github.com/rbeauchamp/acorn/issues/321)) builds a 4-layer
  modular package architecture and always-on live-upgrade foundation.

## Start with the live viewer

> [!NOTE]
> **Contributors and AI agents working on a change:** Every launch of
> `./scripts/start.sh`—including cloning and launching, or reopening to
> resume—starts the agent and requires the owner's authorization for that run
> stated in the change's intent.
> [Running a program](CONTRIBUTING.md#running-a-program) points to the closed
> list of invocations permitted without authorization, and a launcher run is
> not among them.

From your Acorn checkout, run:

```sh
./scripts/start.sh
```

The launcher prepares the dependencies, builds Acorn, starts or resumes the
agent, and opens your browser. By default it selects the `ranked` configuration
with discounted rewards, a 1024 × 1024 world, the 13-goal curriculum, and
checkpointing; the core supports additional research profiles.

The viewer starts the agent only on an explicit request: the `--start` flag
(passed by `./scripts/start.sh` and accepted on direct viewer starts) or a Start
request to its control endpoint from the page's Start button. Without `--start`
and without an earlier Start left running for the same agent program, the
viewer shows the run stopped. Once started, it runs continuously until you stop
it, with no configuration required. The first launch needs internet access and
may trigger system installation prompts; subsequent launches reuse installed
dependencies and unchanged build outputs. Automatic setup supports macOS and
Ubuntu/Debian Linux.

<details>
<summary>Need to get the code first?</summary>

```sh
git clone https://github.com/rbeauchamp/acorn.git
cd acorn
./scripts/start.sh
```

You need Git to clone the repository: the launcher and build tools admit
sources from a Git checkout, so an unpacked source archive is not supported.

</details>

### Watch and explore

- **Follow the agent.** It sees a local patch of the world, plus its inventory,
  energy, and task. It can move, harvest, craft, eat, and wait.
- **Watch its goals.** Tasks include survival, collecting resources, reaching
  locations, and crafting. Learning continues across attempts.
- **Look inside.** Open **Inside the agent** to inspect predictions, action
  values, temporally extended actions called **options**, and learning and
  planning activity.

Some plots need experience before values appear. Follow goal outcomes and
predictions as the run develops.

### Stop, resume or start fresh

- **Stop** in the browser pauses execution after the current attempt.
- **Start** resumes execution with compatible saved learner state.
- **Ctrl-C** in the launcher's terminal finishes the current attempt and closes
  the viewer after shutdown. Wait for the command to return.
- Run **`./scripts/start.sh` again** to reopen the viewer and resume.
- **Clear** archives the run and prepares a fresh agent. If stopped, it stays
  stopped until you choose Start.

Closing the browser tab alone does not stop the agent. Your run stays in
`acorn-run/`, which is ignored by Git. A checkpoint holds the agent's whole
state for the supported profile; the world restarts when the core restarts.

## Point an agent at a mission

Acorn's open problems are posted as *missions*: GitHub issues that each freeze
one exact statement to establish, usually a Lean theorem about code that runs.
Whether a mission's theorem is proved is decided by Lean's kernel and a check
script you can run yourself, not by a score or by anyone's taste; a referee
then reads the pull request against the whole contract
([review protocol](CONTRIBUTING.md#review-protocol)). To contribute with an AI
agent, give it one instruction:

> Read https://github.com/rbeauchamp/acorn/blob/main/docs/missions.md and follow its instructions for agents.

[Missions](docs/missions.md) says what a mission costs and what you get for it,
and the [mission board](docs/mission-board.md) lists open missions and credits
each person and agent with what has landed. External outreach and new
monolith-coupled scaling currently wait on
[Milestone 4](docs/roadmap.md#architectural-foundation-active-priority-ahead-of-scaling-external-missions)
([#321](https://github.com/rbeauchamp/acorn/issues/321)).

## Purpose and worlds

The mission places no limit on which world: Acorn's agent must be able to learn
and generalize in any big world. Acorn restricts its worlds at first to make
progress practical, with each restriction a step toward that end rather than a
narrowing of it. The [roadmap](docs/roadmap.md) sets the order of work below
the mission: the first class of worlds
([#230](https://github.com/rbeauchamp/acorn/issues/230)) is decided, and the
order of the classes after it—including a class beyond the agent's capacity
([#276](https://github.com/rbeauchamp/acorn/issues/276), recommended next in
[#234](https://github.com/rbeauchamp/acorn/issues/234)), ARC-AGI-3 games
([#71](https://github.com/rbeauchamp/acorn/issues/71)), Microduck scenes
([#236](https://github.com/rbeauchamp/acorn/issues/236)), and continuing worlds
with no restarts—is not yet finalized in
[the roadmap](docs/roadmap.md#the-rungs-after-the-first). The
[mission contract](docs/mission-contract.md) states what Acorn promises to prove
about its agent, the decisions behind it, and the sources for each.

Acorn's architecture and mission are driven by the research of Rich Sutton,
Khurram Javed, and Oak Lab, and by the OaK architecture, aiming for each
requirement in the mission contract to match what that research indicates. Its
[four contracts](docs/mission-contract.md#the-mission-contract) specify the
agent's interface with a world, what makes a class of worlds big, the invariants
of learning from one stream, and what achieving goals promises. Each contract
opens with a plain restatement in numbered sentences labeled with citations to
the research that supports it, and records Acorn's departures from that
research.

Within Acorn's work, a *discovery* is an algorithm nobody has published.
Implementing a published algorithm, however well adapted and completely proved,
is prior-art work (and much of Acorn so far is that); it is never called or
counted as a discovery. Between the two lies a range with no bright line, judged
by extent with written reasons in
[prior art and discovery](docs/prior-art-review.md#prior-art-and-discovery).

Rich Sutton presented the OaK (*options and knowledge*) architecture at the 2025
Reinforcement Learning Conference in
[The OaK Architecture: A Vision of SuperIntelligence from Experience](https://www.youtube.com/watch?v=gEbbGyNkR2U)
(recording with the talk's abstract). An *option* pairs a policy with a
termination condition, and *knowledge* is what the agent learns about what
happens when following an option—a world model above single actions for
multi-step planning. Designed to contain nothing specific to one world, OaK
grows the agent's mind solely from runtime experience within its computational
resources as model-based reinforcement learning with three additions: continual
learning in every component, per-weight step sizes tuned online via
meta-learned cross-validation, and continual state/time abstraction in five
steps (construct features from observations, pose a subtask to raise a
high-ranked feature without sacrificing too much reward, learn an option for the
subtask, learn a model of that option, and plan with it, using feature-consumer
feedback to guide feature retention and generation). Sutton presents this as a
vision not yet fully specified: it needs reliable continual learning in deep
networks and a method for generating new features, treating both as unsolved.

Acorn's chosen target worlds are of two kinds:

- [ARC-AGI-3](https://docs.arcprize.org/) games, interactive games the agent
  learns by playing;
- [Microduck](https://github.com/pollen-robotics/microduck), a small simulated
  biped and embodied world
  ([Pollen Robotics](https://pollen-robotics.com/microduck/),
  [design](docs/design.md#an-embodied-world-the-microduck)).

The tile world shown in the viewer is not one of these target worlds; it has no
standing beyond being the first world built.

Two distinct questions are asked of Acorn's agent, each with its own evidence:

- **Is the agent built right?** Settled during development by mathematics: a
  change is accepted by a proof about the running code and by review, and no
  agent run, unit test, or score substitutes for either.
- **Is it the right agent?** Settled only by measured runs of a verified agent
  in the target world it is meant for (ARC-AGI-3 games and Microduck), because
  a theorem covers only the class of worlds it states and says nothing about any
  other world. Those measurements are the final indicator, and a running, live
  agent is what Acorn is for. Measured runs follow
  [scientific evidence](CONTRIBUTING.md#scientific-evidence) (with protocols
  fixed before observations) and the rule on runs
  ([running a program](CONTRIBUTING.md#running-a-program)).

Shaping worlds requires a model of what makes a world big.
[Contract 2](docs/mission-contract.md#contract-2-what-makes-a-class-of-worlds-big)
states the conditions that make a class *concealed* ((a)–(c)), make *perceiving
needed* ((e)), and make a class *big* for a stated bound on the agent
((d1)–(d5)). For one class in the tile world, conditions (a) and (b) are proved
along with a weaker Lean form of (c): an agent that keeps nothing of its
experience solves fewer than all of the class (at most 49 members in a class of
at least 147 and at most 392, a share between an eighth and a third not shown to
be small; [first class and (c)](docs/mission-contract.md#first-class-and-c)).
That class is therefore not yet shown to be concealed, it is
not a big class, and there is no claim yet that the agent learns there. Proving
these conditions for chosen classes is open work across Contract 2's record
([#214](https://github.com/rbeauchamp/acorn/issues/214)), ARC-AGI-3 games
([#71](https://github.com/rbeauchamp/acorn/issues/71)), and Microduck scenes
([#173](https://github.com/rbeauchamp/acorn/issues/173)); the last two are
[obligation 13](docs/mission-contract.md#open-obligations) of the mission
contract.

## Documentation map

You can read the design, contracts, and research reviews without installing
Lean.

| Area | Covers | Read |
|---|---|---|
| Viewer & CLI | Panels, bounded terminal runs, profiles, and learning criteria | [Reading the viewer](docs/design.md#reading-the-viewer), [Run controls](docs/design.md#run-controls), and [Profiles and criteria](docs/design.md#agent-configurations) |
| Setup & verification | Manual/headless setup, Lean/Regula checks, compiler boundaries, and documentation verification | [Verification](docs/verification.md) and [Setup and troubleshooting](docs/verification.md#platform-setup) |
| Learning mechanisms | OaK background, FC-STOMP learning loop, Alberta Plan scope, and Lean module owners | [Oak Lab's archived mission](https://web.archive.org/web/20260909143403/https://oaklab.ai/mission) (no longer published by Oak Lab), [The learning loop](docs/design.md#the-learning-loop), [Scope map](docs/design.md#implementation-scope), and [Mechanism owners](docs/design.md#mechanism-owners) |
| Prior art & departures | Admitted mechanism equations, adaptations, qualification register, and hand-authored departures | [Prior-art review](docs/prior-art-review.md) and [Learned-only binding](docs/learned-only-binding.md) |
| Contracts & research status | Formal mission contracts, open obligations, unresolved research questions, baseline assessment, and roadmap | [Mission contract](docs/mission-contract.md), [Research frontier and limitations](docs/frontier.md), [Baseline assessment](docs/baseline-assessment.md), and [Roadmap](docs/roadmap.md) |
| Learned agent state | Frame specification and referee review criteria for learned-state submissions | [The frame of a learned-state result](docs/learned-state-frame.md) and [How a submission on learned agent state is checked](docs/learned-state-check.md) |
| Architecture & live upgrades | Modular 4-layer federation and always-on operational lifecycle | [Architectural intent](docs/architectural-intent.md) and [Architectural foundation](docs/architecture-foundation.md) |
| Contributing & missions | Contribution workflow, review protocol, mission instructions, and landed credits | [Contributing](CONTRIBUTING.md), [Missions](docs/missions.md), and [Mission board](docs/mission-board.md) |

## Lean package layout

The `lean/` package holds the executing agent and its proof-bearing definitions
in `Acorn/`, implementation contracts and supporting mathematics in `AcornVerif/`,
and build/verification tools in `AcornTools/`. Native runtime modules live in
`NativeApp/` (its `Viewer.lean` module starts the viewer), executable entry
points live in `Entry/`, and `Bootstrap.lean` is the directly invoked build
bootstrap. The pure zero-JS Lean web viewer lives under `lean/Acorn/Host/Viewer/`
(served by `acorn-viewer` with `Content-Security-Policy` `script-src 'none'`), and
the Verso documentation site lives in `site/`.

Research criticism, proof/implementation review, and contributions are welcome,
including from outside contributors and their AI agents through
[missions](docs/missions.md). Questions about an equation, an adaptation, or an
unclear explanation are useful contributions too; see [support](SUPPORT.md) for
where to ask and what to include, and the [code of conduct](CODE_OF_CONDUCT.md)
for community standards. Report vulnerabilities through
[private reporting](SECURITY.md), not public issues. MIT licensed; see
[LICENSE](LICENSE). Dependencies retain their own licenses.
