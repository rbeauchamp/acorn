# Support and questions

## Where to start

Before opening a question, check the repository documentation:

- [README](README.md) for launching the live viewer (`./scripts/start.sh`) and touring the repository layout;
- [Verification and platform setup](docs/verification.md#platform-setup) for provisioning pinned Lean, Mathlib, FloatLib, Regula and Verso and resolving build or setup problems on macOS and Ubuntu/Debian Linux;
- [Design](docs/design.md), [Prior-art review](docs/prior-art-review.md), [Learned-only binding](docs/learned-only-binding.md) and [Research frontier](docs/frontier.md) for implemented mechanisms, equations, adaptations, departures and open research questions;
- [Contributing](CONTRIBUTING.md) and [Missions for outside contributors and agents](CONTRIBUTING.md#missions-for-outside-contributors-and-agents) for finding and claiming an open mission and running the merge gate (`./scripts/gate.sh`).

## Where to ask questions

Open a [GitHub issue](https://github.com/rbeauchamp/acorn/issues) (or use [GitHub Discussions](https://github.com/rbeauchamp/acorn/discussions) once enabled in repository settings; while Discussions is disabled, Issues is the stated place for questions). You do not need a proposed fix or a Lean proof to ask about an equation, a theorem statement, a prior-art adaptation or an unclear explanation: apply the question label or open a blank issue with links to the relevant document, equation or module.

For a setup, build or verification problem, include:

- the commit hash (`git rev-parse HEAD`);
- your operating system and architecture;
- the output of `./scripts/lean.sh provision-status` (if dependencies are provisioned);
- the exact command run and its terminal output.

Do not post security vulnerabilities, credentials or private run data in public issues. Report them privately through [SECURITY](SECURITY.md) (`https://github.com/rbeauchamp/acorn/security/advisories/new`).

## What to expect

Acorn is maintained by one owner ([@rbeauchamp](https://github.com/rbeauchamp)) and the organization's autonomous agents, with a target initial triage within seven days and no 24/7 coverage or guaranteed response schedule (see [Triage and response](CONTRIBUTING.md#triage-and-response)).

Support covers questions about Acorn's specifications, proofs, equations, mission contracts, and reproducible build or gate problems on supported platforms. General Lean 4 or Mathlib tutoring and debugging of unsubmitted proof drafts are outside what a one-owner organization can provide; for missions, running `./scripts/gate.sh` locally gives immediate verification feedback before opening a pull request.
