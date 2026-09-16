# Acorn

Acorn pursues [Oak Lab's mission](https://oaklab.ai/mission): agents that learn
from experience to achieve goals in big worlds. We tackle the challenges of the
[Alberta Plan](https://arxiv.org/abs/2208.11173v3) by developing and verifying
continual learning and planning algorithms in Lean. The agent learns one
observation at a time, without replay buffers or curated training data.

Watch an agent explore a tile world, gather resources and attempt tasks while
learning from one continuous stream of experience. Acorn's browser viewer lets
you inspect its predictions, chosen actions, options and planning as it runs.

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
`acorn-run/`, which is ignored by Git. Checkpoints preserve supported learner
state; the world and some transient state restart when the core restarts.

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

## What to inspect

| Question | Read |
|---|---|
| Which mechanisms and Alberta Plan steps are implemented? | [Design](docs/design.md) |
| Which adaptations and assumptions matter? | [Prior-art review](docs/prior-art-review.md) |
| Which hand-authored choices remain? | [Learned-only binding](docs/learned-only-binding.md) |
| What do the compiler and proofs establish? | [Verification](docs/verification.md) |
| What remains unresolved? | [Research frontier and limitations](docs/frontier.md) |
| How should work be proposed and checked? | [Contributing](CONTRIBUTING.md) |

Research criticism, proof/implementation review and contributions are welcome.
Questions about an equation, an adaptation or an unclear explanation are useful
contributions too; you do not need a Lean proof to open a discussion in an issue.
Report vulnerabilities through [private reporting](SECURITY.md), not public issues.
MIT licensed; see [LICENSE](LICENSE). Dependencies retain their own licenses.

## Lean package layout

The `lean/` package contains the executing agent and its proof-bearing definitions
in `Acorn/`, implementation contracts and supporting mathematics in `AcornVerif/`,
and build/verification tools in
`AcornTools/`. Native entry points live in `NativeApp/`; its `Viewer.lean` module
starts the viewer. `Bootstrap.lean` is the directly invoked build bootstrap.
