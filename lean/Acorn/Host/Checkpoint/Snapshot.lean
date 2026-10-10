/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Checkpoint.Load

/-!
# The image of the executing full agent

A save writes every field of the agent's temporal state: the representation and its
generator and tester state, every learner with its transient registers, the option
models, every option's off-policy questions, the process-local references with the action
generator and the last decision, primitive credit, the gain, the rate schedule and every
lifetime observation, durable or process-local. No world is encoded.
-/
namespace Acorn.Checkpoint
open Features Handcrafted

/-- The image of a state of a construction: its agent's exact image. This is where this
project makes an image from a state. -/
def stateImage (construction : AgentConstruction) (state : construction.State) :
    construction.Image :=
  ⟨state.agent.image⟩

/-- An image of a construction has one exact payload. The header holds the construction's
identity words, the image's clock and reward rate, and the word of the order of the image's
own construction: the writer takes no image of another construction and no order word. -/
def imagePayload (construction : AgentConstruction) (image : construction.Image) : Payload :=
  ⟨⟨formatVersion, construction.dimension.capacity.toUInt32, primaryCount.toUInt32,
      construction.config.seed, image.image.control.runtime.lifecycle.representation.progress.clock,
      construction.criterion.tag.toUInt32, image.image.control.average.rate.value,
      construction.config.tilings, construction.config.units.count.toUInt32,
      if construction.profile.Resumable then 1 else 0, construction.order.tag⟩,
    (imageFormat construction).encode image⟩

/-- Snapshotting reads the state; it does not act or advance the stream. -/
def snapshot (construction : AgentConstruction) (state : construction.State) : Payload :=
  imagePayload construction (stateImage construction state)

/-- Saving unsupported profiles is an explicit refusal before bytes are produced for IO. -/
@[noinline] def saveBytes (construction : AgentConstruction) (state : construction.State) : Except Error (List UInt8) :=
  if construction.profile.checkpointSupported then .ok (encode (snapshot construction state))
  else .error .unsupportedPolicy

/-- All supported constructions have a total pure writer. -/
theorem save_supported (construction : AgentConstruction) (state : construction.State)
    (supported : construction.profile.checkpointSupported = true) :
    saveBytes construction state = .ok (encode (snapshot construction state)) := by
  simp [saveBytes, supported]

/-- Non-ranked profiles cannot reach the filesystem writer. -/
theorem save_refuses (construction : AgentConstruction) (state : construction.State)
    (unsupported : construction.profile.checkpointSupported = false) :
    saveBytes construction state = .error .unsupportedPolicy := by
  simp [saveBytes, unsupported]

end Acorn.Checkpoint
