import Acorn.Host.Checkpoint.Load

namespace Acorn.Checkpoint
open Features Handcrafted

def stateImage (construction : AgentConstruction) (state : construction.State) :
    construction.Image :=
  ⟨state.agent.image⟩

def imagePayload (construction : AgentConstruction) (image : construction.Image) : Payload :=
  ⟨⟨formatVersion, construction.dimension.capacity.toUInt32, primaryCount.toUInt32,
      construction.config.seed, image.image.control.runtime.lifecycle.representation.progress.clock,
      construction.criterion.tag.toUInt32, image.image.control.average.rate.value,
      construction.config.tilings, construction.config.units.count.toUInt32,
      if construction.profile.Resumable then 1 else 0, construction.order.tag⟩,
    (imageFormat construction).encode image⟩

def snapshot (construction : AgentConstruction) (state : construction.State) : Payload :=
  imagePayload construction (stateImage construction state)

@[noinline] def saveBytes (construction : AgentConstruction) (state : construction.State) : Except Error (List UInt8) :=
  if construction.profile.checkpointSupported then .ok (encode (snapshot construction state))
  else .error .unsupportedPolicy

theorem save_supported (construction : AgentConstruction) (state : construction.State)
    (supported : construction.profile.checkpointSupported = true) :
    saveBytes construction state = .ok (encode (snapshot construction state)) := by
  simp [saveBytes, supported]

theorem save_refuses (construction : AgentConstruction) (state : construction.State)
    (unsupported : construction.profile.checkpointSupported = false) :
    saveBytes construction state = .error .unsupportedPolicy := by
  simp [saveBytes, unsupported]

end Acorn.Checkpoint
