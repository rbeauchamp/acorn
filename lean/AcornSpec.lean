/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornSpec.Constants
import AcornSpec.Rng
import AcornSpec.Float
import AcornSpec.World
import AcornSpec.Learner
import AcornSpec.Sarsa
import AcornSpec.Features
import AcornSpec.Exploration
import AcornSpec.Agent
import AcornSpec.AgentBaseline
import AcornSpec.Collapse
import AcornSpec.IntraOptionCredit
import AcornSpec.DerivedExplorationRate
import AcornSpec.Rows
import AcornSpec.Solvability
import AcornSpec.AverageRewardControl

/-!
# AcornSpec: preserved-data analysis and a historical evaluator

Current calculators consume preserved shard/row data through `StudySchema`,
`WorldSchema`, `MachineWords`, `Collapse` and the study-specific reductions.
These imports do not execute or compile the historical world, learner or agent.

The separate world/learner/agent implementation owns the baseline's specified
historical system and supports `specprobe` diagnostics. The original baseline
certification source and result remain in its dossier. Integer action folds
are mutation/localization evidence, not universal correspondence to the current
Rust agent or an identified historical Rust commit. No such matching commit is
claimed. Native calculator execution is neither kernel certification nor a
historical experiment rerun.

These modules use Lean core without Mathlib. Native targets compile their own
transitive imports; building the entire library also checks the retained
evaluator. Current executable agent ownership is the separate `Acorn` library.
-/
