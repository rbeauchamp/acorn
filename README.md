# Acorn

Acorn pursues [Oak Lab's mission](https://oaklab.ai/mission): agents that learn
from experience to achieve goals in big worlds. We tackle the challenges of the
[Alberta Plan](https://arxiv.org/abs/2208.11173v3) by developing and verifying
continual learning and planning algorithms in Lean. The agent learns one
observation at a time, without replay buffers or curated training data.

Watch an agent explore a tile world, gather resources and attempt tasks while
learning from one continuous stream of experience. Acorn's browser viewer lets
you inspect its predictions, chosen actions, options and planning as it runs.

## Point an agent at a mission

Acorn's open problems are posted as *missions*: GitHub issues that each freeze
one exact statement to establish, usually a Lean theorem about code that runs. A
mission is decided by Lean's kernel and a check script you can run yourself, not
by a score or by anyone's taste. To contribute with an AI agent, give it one
instruction:

> Read https://github.com/rbeauchamp/acorn/blob/main/docs/missions.md and follow its instructions for agents.

[Missions](docs/missions.md) says what a mission costs and what you get for it.
The [mission board](docs/mission-board.md) lists the open missions and credits
each person and agent with what has landed.

## Purpose and worlds

Acorn's highest-level goal is Oak Lab's mission, in its own words: "Our goal is
to discover and implement algorithms that allow agents to achieve goals in big
worlds." The mission places no limit on which world: Acorn's agent must be able
to learn and generalize in any big world. Acorn may restrict its worlds at first,
to make progress practical, but each restriction is a step toward that end, not a
narrowing of it. The [roadmap](docs/roadmap.md) gives the order of work below
the mission: the first class of worlds is decided, and the order of the classes
after it is not. The
[mission contract](docs/mission-contract.md) states what Acorn promises to prove
about its agent, the decisions behind it and the sources for each.

On 2026-11-03 the owner of the project stated this intent for Acorn: its
architecture and mission are driven by the research of Rich Sutton, Khurram
Javed and Oak Lab, and by the OaK architecture, so what each contract in the
mission contract requires is what that research indicates. On the same day the
owner confirmed plain restatements of its four contracts: the agent's interface
with a world, what makes a class of worlds big, the invariants of learning from
one stream, and what achieving goals promises. The mission contract
[records the confirmation](docs/mission-contract.md#the-owners-confirmation-of-2026-11-03),
with a citation of that research for each sentence that rests on it.

The OaK architecture is an overall design for an agent, which Rich Sutton
presented at the 2025 Reinforcement Learning Conference in
[The OaK Architecture: A Vision of SuperIntelligence from Experience](https://www.youtube.com/watch?v=gEbbGyNkR2U)
(the recording, with the talk's abstract). Its name stands for options and
knowledge. An option is a way of behaving together with a way of deciding when
to stop, and the agent's knowledge is what it learns about what happens when it
follows an option: a model of its world above the level of single actions, with
which it can plan in larger steps. The design is meant to contain nothing
specific to any one world, to grow the agent's mind only from the experience it
has while it runs, and to let it form whatever concepts its world calls for,
limited only by its computational resources. In outline it is model-based
reinforcement learning, in which the agent learns a model of its world and plans
with it, with three further features: every component learns continually; every
learned weight has its own step size, which the agent tunes as it runs
(meta-learned by online cross-validation); and abstractions in state and time
are built continually in five steps. The agent constructs features of its
situation from what it senses; for a feature it ranks highly it poses the
subtask of making that feature high without giving up too much reward; it
learns an option that solves the subtask, learns a model of that option, and
plans with the model. The parts that use the features report which ones have
proved useful, and that feedback informs which features are kept and which new
ones are made. The talk presents this as a vision not yet fully specified: it
needs reliable continual learning in deep networks and a method for generating
new features, and Sutton treats both as unsolved.

The owner of the project has chosen two kinds of worlds:

- [ARC-AGI-3](https://docs.arcprize.org/) games, interactive games the agent
  learns by playing;
- [Microduck](https://github.com/pollen-robotics/microduck), a small simulated
  biped and so an embodied world
  ([Pollen Robotics](https://pollen-robotics.com/microduck/),
  [design](docs/design.md#an-embodied-world-the-microduck)).

The tile world the viewer shows was chosen by an agent working on Acorn, not by
the owner. It has no standing beyond being the first world built.

Choosing and shaping worlds well needs a model of what a big world is. The mission
contract states the conditions that make a class of worlds big
([contract 2](docs/mission-contract.md#contract-2-what-makes-a-class-of-worlds-big)).
Three of its four conditions are proved of one class in the tile world, with no
claim yet that the agent learns there; proving them of chosen classes is open
work, in the issues on that contract's record
([#214](https://github.com/rbeauchamp/acorn/issues/214)), ARC-AGI-3 games
as a class of worlds ([#71](https://github.com/rbeauchamp/acorn/issues/71)) and a
class of Microduck scenes ([#173](https://github.com/rbeauchamp/acorn/issues/173));
the last two are
[obligation 13](docs/mission-contract.md#open-obligations) of the mission contract.

## Start with the live viewer

From your Acorn checkout, run:

```sh
./scripts/start.sh
```

The launcher prepares the dependencies, builds Acorn, starts or resumes the
agent, and opens your browser. It runs continuously until you stop it. No
configuration is required. The first launch needs internet access and may
require system installation prompts; subsequent launches reuse installed
dependencies and unchanged build outputs. Automatic setup supports macOS and
Ubuntu/Debian Linux.

<details>
<summary>Need to get the code first?</summary>

```sh
git clone https://github.com/rbeauchamp/acorn.git
cd acorn
./scripts/start.sh
```

You need Git to clone the repository. You can also download and unpack its
source archive, then run the launcher from that directory.

</details>

### Watch and explore

- **Follow the agent.** It sees a local patch of the world, plus its inventory,
  energy and task. It can move, harvest, craft, eat and wait.
- **Watch its goals.** Tasks include survival, collecting resources, reaching
  locations and crafting. Learning continues across attempts.
- **Look inside.** Open **Inside the agent** when you want predictions, action values, temporally
  extended actions called **options**, and learning and planning activity.

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
`acorn-run/`, which is ignored by Git. A checkpoint holds the agent's whole state
for the supported profile; the world restarts when the core restarts.

## Go a layer deeper

Start with [reading the viewer](docs/design.md#reading-the-viewer) when you want
to understand its panels. Then explore:

| If you want to… | Read |
|---|---|
| Run a short, bounded command in the terminal | [Run controls](docs/design.md#run-controls) |
| Compare agent configurations or learning objectives | [Profiles and criteria](docs/design.md#agent-configurations) |
| Understand the learning mechanisms | [The learning loop](docs/design.md#the-learning-loop) |
| Build manually, use a headless machine or resolve setup problems | [Setup and troubleshooting](docs/verification.md#platform-setup) |

The launcher explicitly selects the `ranked` configuration with discounted
rewards, a 1024 × 1024 world, the 13-goal curriculum and checkpointing.
The core supports additional research configurations.

Lean is both the implementation language and the proof assistant. Follow the
[verification guide](docs/verification.md) to the properties checked by its proofs.

## Explore the research

You can read the design without installing Lean.

- **New to OaK?** Start with [Oak Lab's mission](https://oaklab.ai/mission), then
  Acorn's [learning loop and terminology](docs/design.md#the-learning-loop).
- **Assessing the implementation?** Read the [scope map](docs/design.md#implementation-scope),
  then follow [mechanism owners](docs/design.md#mechanism-owners) to the source
  and [prior-art contracts](docs/prior-art-review.md).
- **Looking for research questions?** Read the [frontier](docs/frontier.md).
  The repository offers executable mechanisms, implementation-linked proofs
  and an observation tool.
- **Wondering how close Acorn is to the published baseline?** Read the
  [baseline assessment](docs/baseline-assessment.md); the
  [roadmap](docs/roadmap.md) orders the work that remains.
- **Wondering what comes next?** Read the [roadmap](docs/roadmap.md): the
  class of worlds Acorn is working on, what is proved of it and what is open.

## What to inspect

| Question | Read |
|---|---|
| Which mechanisms and Alberta Plan steps are implemented? | [Design](docs/design.md) |
| Which adaptations and assumptions matter? | [Prior-art review](docs/prior-art-review.md) |
| Which hand-authored choices remain? | [Learned-only binding](docs/learned-only-binding.md) |
| What do the compiler and proofs establish? | [Verification](docs/verification.md) |
| What remains unresolved? | [Research frontier and limitations](docs/frontier.md) |
| How close is Acorn to the published baseline, and what work remains? | [Baseline assessment](docs/baseline-assessment.md) and [roadmap](docs/roadmap.md) |
| How should work be proposed and checked? | [Contributing](CONTRIBUTING.md) and [missions](docs/missions.md) |
| Which missions are open, and who has landed what? | [Mission board](docs/mission-board.md) |

Research criticism, proof/implementation review and contributions are welcome,
including from outside contributors and their AI agents through
[missions](docs/missions.md).
Questions about an equation, an adaptation or an unclear explanation are useful
contributions too; see [support](SUPPORT.md) for where to ask and what to
include, and the [code of conduct](CODE_OF_CONDUCT.md) for community standards.
Report vulnerabilities through [private reporting](SECURITY.md), not public issues.
MIT licensed; see [LICENSE](LICENSE). Dependencies retain their own licenses.

## Lean package layout

The `lean/` package contains the executing agent and its proof-bearing definitions
in `Acorn/`, implementation contracts and supporting mathematics in `AcornVerif/`,
and build/verification tools in
`AcornTools/`. Native entry points live in `NativeApp/`; its `Viewer.lean` module
starts the viewer. `Bootstrap.lean` is the directly invoked build bootstrap.
