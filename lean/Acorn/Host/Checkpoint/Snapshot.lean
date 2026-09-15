/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Checkpoint.Admission

/-!
# Durable projection of the executing full agent

Only primary weights and log step sizes, shared gain, exact assignment identities,
feature progress, pending ranking and durable lifetime observations are written.
No world, pending future, policy RNG, trace, model or planner state is encoded.
-/
namespace Acorn.Checkpoint
open Features Handcrafted Lifetime

/-- Prepend while preserving the receiving vector's exact length. -/
def prepend {α : Type} {count : Nat} (head : α) (tail : Vector α count) : Vector α (count + 1) :=
  (Vector.append #v[head] tail).cast (by omega)

/-- One typed total becomes two exact stored words. -/
def sumWords {quantity : Quantity} (record : SumCount quantity) : SumWords := (record.count, record.sum)

/-- One typed goal aggregate becomes its three exact counters. -/
def goalWords (record : GoalTotals) : GoalWords := (record.attempts, record.successes, record.steps)

/-- Three exact columns, indexed by the immutable horizon layout. -/
structure DemonColumns (discounts : List Discount) where
  /-- Count/sum pairs. -/
  sums : Vector SumWords discounts.length
  /-- Last settled returns. -/
  returns : Vector Binary32 discounts.length
  /-- Last signed errors. -/
  errors : Vector Binary32 discounts.length

/-- Column-major storage retains the complete horizon order. -/
def demonColumns {discounts : List Discount} : DurableDemons discounts → DemonColumns discounts
  | .nil => ⟨#v[], #v[], #v[]⟩
  | .cons head tail =>
    let rest := demonColumns tail
    ⟨prepend (sumWords head.squaredError) rest.sums,
      prepend head.lastReturn.value rest.returns, prepend head.lastError.value rest.errors⟩

/-- Every durable observation field is read directly from its maintained owner. -/
def lifetimeWords (record : Durable demonLayout) : LifetimeWords :=
  let demons := demonColumns record.demons
  ⟨sumWords record.reward, record.rewardByFamily.map sumWords, record.rewardHistory.map sumWords,
    demons.sums, demons.returns, demons.errors, record.errorHistory.map sumWords, record.options,
    record.goals.map goalWords, record.goalCycles.map (fun row => row.map goalWords)⟩

/-- The two knowledge arrays are read without changing their bit patterns. -/
def knowledge {config : Acorn.Config} {dimension : Dimension}
    (learner : Managed config dimension) : KnowledgeImage dimension :=
  ⟨learner.state.weights.map (·.value), learner.state.beta.map (·.value)⟩

/-- Each demon supplies its own learner, in the same order as the receiving shape. -/
def demonImages {dimension : Dimension} {discounts : List Discount} :
    DemonBank dimension discounts → DemonImages dimension discounts
  | .nil => .nil
  | .cons head tail => .cons (knowledge head) (demonImages tail)

/-- Primary images follow the same structural segments used during installation. -/
def primaryImage {config : Features.Config} {criterion : Criterion} {dimension : Dimension}
    (ensemble : Ensemble config criterion dimension demonLayout) : PrimaryImage dimension demonLayout :=
  ⟨ensemble.control.learners.map knowledge, ensemble.metaController.learners.map knowledge,
    ensemble.skills.map (fun skill => skill.policy.learners.map knowledge), demonImages ensemble.demons⟩

/-- Declared profiles use the canonical neutral sentinel and are refused by the profile header. -/
def savedAssignment {config : Features.Config} : Interest config → Assignment config
  | .learned assignment => assignment
  | .declared _ _ => .neutral

/-- The complete checkpoint projection already carries valid history and numeric state. -/
def snapshotImage (construction : AgentConstruction) (state : construction.State) :
    AgentImage construction.config construction.criterion construction.dimension :=
  let runtime := state.control.runtime
  ⟨⟨runtime.lifecycle.representation.progress,
      runtime.lifecycle.consumers.skills.map (fun skill => savedAssignment skill.interest),
      primaryImage runtime.lifecycle.consumers, runtime.refresh.pending⟩,
    state.control.average.rate, state.control.lifetime.durable, by
      intro slot
      have valid := state.episodes.1 slot
      exact ⟨valid.1, valid.2.1, by simp⟩⟩

/-- Every legal feature transcript fits the format-level count before narrowing. -/
def transcriptWords {config : Features.Config} (progress : Progress config) : Transcript :=
  ⟨progress.words, by
    simp only [Progress.words, List.length_map]
    exact Nat.le_trans progress.legal.1 config.units.bounded⟩

/-- A typed image has one exact format-14 word projection under its receiver. -/
def imagePayload (construction : AgentConstruction)
    (image : AgentImage construction.config construction.criterion construction.dimension) :
    Payload construction.dimension :=
  ⟨⟨formatVersion, construction.dimension.capacity.toUInt32, primaryCount.toUInt32,
      construction.config.seed, image.features.progress.clock, construction.criterion.tag.toUInt32,
      image.gain.value, construction.config.tilings, construction.config.units.count.toUInt32,
      if construction.profile.checkpointSupported then 1 else 0, if image.features.pending then 1 else 0⟩,
    image.features.assignments.map (Assignment.words construction.dimension), image.features.primary,
    lifetimeWords image.lifetime, transcriptWords image.features.progress⟩

/-- Snapshotting reads only the durable projection; it does not act or advance the stream. -/
def snapshot (construction : AgentConstruction) (state : construction.State) : Payload construction.dimension :=
  imagePayload construction (snapshotImage construction state)

/-- Saving unsupported profiles is an explicit refusal before bytes are produced for IO. -/
@[noinline] def saveBytes (construction : AgentConstruction) (state : construction.State) : Except Error (List UInt8) :=
  if construction.profile.checkpointSupported then .ok (encode construction.dimension (snapshot construction state))
  else .error .unsupportedPolicy

/-- All supported constructions have a total pure writer. -/
theorem save_supported (construction : AgentConstruction) (state : construction.State)
    (supported : construction.profile.checkpointSupported = true) :
    saveBytes construction state = .ok (encode construction.dimension (snapshot construction state)) := by
  simp [saveBytes, supported]

/-- Non-ranked profiles cannot reach the filesystem writer. -/
theorem save_refuses (construction : AgentConstruction) (state : construction.State)
    (unsupported : construction.profile.checkpointSupported = false) :
    saveBytes construction state = .error .unsupportedPolicy := by
  simp [saveBytes, unsupported]

end Acorn.Checkpoint
