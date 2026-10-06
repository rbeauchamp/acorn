/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Options
import Acorn.SignalValues

/-!
# The interface between the agent and a world

A world fixes five things for the agent: the shape of the symbol array the feature
generator samples; which signals it supplies as prediction targets and at which
horizons; how many primitive actions it accepts; how many words a frame carries at
most; and the first channel of the agent's prediction feedback words. Everything the
agent stores is indexed by this value, so one agent definition serves every world.
The interface names no world's types.

Each step the world hands the agent one percept: a frame and the reward of the
preceding transition. Nothing else reaches a learner. The agent answers with one
action, a `Fin` of the declared count.

The frame's three parts follow what the learners consume. The words are opaque
channel and value pairs, which the tiled coder hashes. The symbols are the input of
the generated units. The signals are the cumulants of the prediction questions.

The agent adds one word of prediction feedback per question, on the channels from
the interface's `feedback` channel. A frame cannot carry a word on one of them:
`Frame.clear` is part of the type, so every adapter proves it where it builds a frame.
-/
namespace Acorn.Features

/-- What one world fixes for the agent. -/
structure Interface where
  /-- Shape of the symbol array the feature generator samples. -/
  symbols : PatchShape
  /-- Horizon of each prediction signal the world supplies, in channel order. -/
  signals : List Discount
  /-- Number of primitive actions. -/
  actions : Word.Count
  /-- Most words one frame carries. -/
  words : Nat
  /-- First channel of the agent's own prediction feedback words. The channel of each
  question is this word plus the question's position in the layout. -/
  feedback : UInt64

/-- The agent's prediction layout: its own question about reward, at the horizon the
subtask ranking reads, then one question per signal of the world. -/
abbrev Interface.layout (interface : Interface) : List Discount := .g99 :: interface.signals

/-- Whether a channel is one of the agent's prediction feedback channels: the
interface's first feedback channel plus the position of a question of the layout, in
wrapping word arithmetic. -/
def Interface.reserved (interface : Interface) (channel : UInt64) : Bool :=
  (channel - interface.feedback).toNat < interface.layout.length

/-- One observation of a world, in the form the learners consume. -/
structure Frame (interface : Interface) where
  /-- Opaque channel and value pairs for the tiled coder. -/
  words : List SensorWord
  /-- A frame carries at most the declared number of words. -/
  bounded : words.length ≤ interface.words
  /-- No word uses a prediction feedback channel, so no word of the world is on the
  channel of a feedback word. Two words on different channels can still hash to one
  feature slot, as any two hashed words can. -/
  clear : ∀ word ∈ words, interface.reserved word.channel = false
  /-- Symbol array the generated units sample. -/
  symbols : Patch interface.symbols
  /-- One cumulant per declared signal, each with its declared origin. -/
  signals : Cumulants interface.signals
  /-- Declared subtask potentials in option-slot order. Only a profile whose subtasks
  are declared reads them. -/
  potentials : Vector Potential Acorn.FeatureConstants.skillCount
  /-- Whether the preceding transition achieved the installed goal. It forces an option's
  stopping decision to end, for the executing option and for the stored off-policy
  trajectory of every other option (departure D8), and it is no input of the coder. -/
  achieved : Bool

/-- Everything a world delivers to the agent at one step. -/
structure Percept (interface : Interface) where
  /-- The current observation. -/
  frame : Frame interface
  /-- Reward of the preceding transition, as a raw word. -/
  reward : Binary32

end Acorn.Features
