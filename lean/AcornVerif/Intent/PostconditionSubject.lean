/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.WorldInterface

/-!
# The subject of the postcondition's record

The types the intent record of the postcondition, `AcornVerif.Intent.Postcondition.postcondition`,
is stated over: `Member`, one world of a class with its reward and its goal, and `Trial`, a class
of worlds with what the class states and the agent that learns in it. They are in a module of their
own so that a second reading of the owner's words over the same subject imports them and nothing of
the record: the blind reading in `AcornVerif.Intent.PostconditionBlindReading` imports this module
and not `AcornVerif.Intent.Postcondition`, so no definition of the record can enter it. The module
holds no definition that is not a type.

The fields `horizon` and `lapses` are the form the record's writer gave, on the owner's behalf, to
the stated attempt and the stated number of the owner's decision of 2026-11-17 on the
postcondition's fourth sentence; the record's module says what each property reads of them.
-/

namespace AcornVerif.Intent.Postcondition

open LeanIntent WorldInterface

/-- One member of a class of worlds: a world over the class's observations and actions, with the
reward it generates and the goal it poses. -/
structure Member (Obs Act : Type) where
  /-- The world's states: everything its future depends on. -/
  State : Type
  /-- The world's state when a run begins. -/
  start : State
  /-- The world's observation at a state. -/
  observe : State → Obs
  /-- The reward the world generates at a state: the member's whole reward function. -/
  reward : State → Rat
  /-- The world's own dynamics: its next state after an action, restarts included. -/
  step : State → Act → State
  /-- Whether a state meets the member's goal. -/
  goal : State → Bool

/-- A class of worlds with the agent that learns in it: what the postcondition's second sentence
says a class states, and, as the fields `horizon` and `lapses`, the stated attempt and the stated
number of the owner's decision of 2026-11-17. -/
structure Trial where
  /-- What the worlds of the class show an agent. -/
  Obs : Type
  /-- The actions of the class. -/
  Act : Type
  /-- The names of the class's members. -/
  Index : Type
  /-- Each member: its world, its reward function and its goal. -/
  member : Index → Member Obs Act
  /-- The members the comparison counts. -/
  counted : List Index
  /-- How long an attempt lasts, in steps. -/
  length : Nat
  /-- How the rewards of one attempt are aggregated, from the rewards in the order given. -/
  total : List Rat → Rat
  /-- The attempt before which the class reads its promises of the advantage and of solving again:
  they cover the attempts that come before this one. -/
  horizon : Nat
  /-- On how many attempts before the horizon the agent may fail a member it has solved. -/
  lapses : Nat
  /-- The agent that learns. -/
  agent : Agent Obs Act

end AcornVerif.Intent.Postcondition
