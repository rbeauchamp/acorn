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
# AcornSpec: specification and analysis definitions

The world, learner and agent modules define a discounted, hand-authored-subtask
evaluator. This is a separate model from the executing `Acorn` library; its
contracts concern its own definitions, with no full-agent refinement asserted.

`StudySchema`, `WorldSchema`, `MachineWords`, `Collapse` and the comparison
reductions define analysis over explicit inputs. Their results depend on those
inputs; the repository supplies no observations for them.

These modules use Lean core without Mathlib. Native targets compile their own
transitive imports; the complete suite also checks every specification module.
-/
