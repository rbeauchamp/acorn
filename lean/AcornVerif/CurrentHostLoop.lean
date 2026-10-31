/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentGridWorld

/-!
# The agent of a step order, as the kernel's agent

`orderedAgent` is the executed agent's whole step at a step order as a kernel agent, and
`orderedAgent_default` shows that at the default order it is `CurrentGridWorld.executedAgent`, the
agent the kernel's bounds are stated for. `AcornVerif.CurrentVisits` relates the host's run of
visits to this agent. It takes no position in this module on the attempt loop.
-/

namespace AcornVerif.CurrentHostLoop
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentGridWorld

/-- The agent of a step order as a kernel agent. -/
def orderedAgent {interface : Interface} {profile : FeatureProfile} {features : Features.Config}
    {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}
    (order : StepOrder) (state : Agent interface profile features criterion dimension planning) :
    Kernel.Agent interface where
  Memory := Agent interface profile features criterion dimension planning
  initial := state
  act := fun memory percept =>
    ((memory.actOrdered order percept).2.action, (memory.actOrdered order percept).1)

/-- Under the default order this is the executed agent the kernel bounds are stated for. -/
theorem orderedAgent_default {interface : Interface} {profile : FeatureProfile}
    {features : Features.Config} {criterion : Criterion} {dimension : Dimension}
    {planning : PlanningSelection}
    (state : Agent interface profile features criterion dimension planning) :
    orderedAgent .learnThenAct state = executedAgent state := by
  unfold orderedAgent executedAgent
  congr
  funext memory percept
  rw [Agent.act_parts]

end AcornVerif.CurrentHostLoop
