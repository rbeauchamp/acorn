/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Word

/-!
# Time between an agent and a world

A step of the agent has two parts. The first chooses the action from the percept and
the agent's state. The second learns from the same percept. `StepOrder` declares when
a host releases the chosen action to the world: after the second part, or between the
two parts.

`Timing` names how a world's time relates to the agent's computation. It is a
declared value of a world: no definition reads it, and nothing checks a declaration
against the world that makes it.

Releasing the action before the learning update is the reordering of Travnik,
Mathewson, Sutton & Pilarski, *Reactive Reinforcement Learning in Asynchronous
Environments*, Frontiers in Robotics and AI 5:79 (2018), section 3. Its Algorithm 1
(SARSA) takes the action it chose at the start of the next iteration, after the
update; its Algorithm 2 (Reactive SARSA) takes the action directly after choosing it,
before the update. Both algorithms choose the action before the update, so the
reordering changes no value computed from a given sequence of observations. It
changes the time between an observation and the action taken on it. That conclusion
is Acorn's derivation from the two listings. Its counterparts for Acorn's composed
step are `Acorn.Handcrafted.Agent.act_parts` and
`Acorn.Host.DecisionInput.chooseOwned_commit`.
-/
namespace Acorn

/-- The discipline a world declares for its time against the agent's computation. The
constructors are names with declared numbers. No definition gives them a behaviour,
and no type obliges a world to declare one. -/
inductive Timing where
  /-- The world takes one transition for each action, when the action arrives. -/
  | agentSynchronized
  /-- The world runs on a wall clock. `cycle` is the declared period between action
  deadlines, in nanoseconds; `latency` is the declared number of cycles between an
  action's deadline and its effect. -/
  | wallClock (cycle : Word.Count) (latency : Nat)

/-- When a host releases the action of a two-part step to the world. -/
inductive StepOrder where
  /-- Both parts run before the world receives the action. -/
  | learnThenAct
  /-- The world receives the action after the first part; the second part runs after
  the world's transition. -/
  | actThenLearn
  deriving DecidableEq

/-- Canonical spelling of each order; the single text vocabulary shared by command
admission and run provenance. -/
def StepOrder.name : StepOrder → String
  | .learnThenAct => "learn-then-act"
  | .actThenLearn => "act-then-learn"

/-- The single closed textual admission rule: exactly the two canonical spellings
parse; every other string is refused and never substituted. -/
def StepOrder.parse (text : String) : Option StepOrder :=
  if text = "learn-then-act" then some .learnThenAct
  else if text = "act-then-learn" then some .actThenLearn
  else none

/-- Accepted spelling identifies exactly the selected constructor over the entire
string domain. -/
theorem StepOrder.parse_accepted (text : String) (order : StepOrder) :
    StepOrder.parse text = some order ↔ text = StepOrder.name order := by
  cases order <;> by_cases first : text = "learn-then-act" <;>
    by_cases second : text = "act-then-learn" <;>
    simp_all [StepOrder.parse, StepOrder.name]

end Acorn
