/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Handcrafted.Cumulants
import Acorn.Handcrafted.PredictionControl
import Acorn.Handcrafted.TemporalProfile
import Acorn.Host.Terrain
import Acorn.Timing

/-!
# The grid world as one instance of the interface

The composed agent of `Acorn.Handcrafted.Agent` imports no world. This module binds
the grid world to its interface: the interface value, and the adapter that turns a
host observation and the preceding result into a percept. The adapter is built from
the executed host and channel definitions: D1's `sensorWords` and `observationPatch`,
D5's `Cumulant.eval` and D2's `spatialPotentials`. It also declares the grid world's
timing discipline, `Grid.timing`.

The theorems state what the instance feeds each consumer in terms of those executed
definitions: the prediction cumulants are `evaluateCumulants cumulantOrder`, the
declared potentials are `spatialPotentials`, and the feedback words are the
standalone coder's `predictionWords`. No grid word uses a prediction feedback channel
(`Grid.sensorWords_clear`), which the frame type requires of every adapter.
`Acorn.Host.AgentInterface` carries these to the agent the host calls. They are
equalities for every observation and reward word. `AcornVerif.GridCorrespondence`
proves the whole composed transition equal to a frozen composition over host
observations.
-/
namespace Acorn.Handcrafted
open Features Host

/-- Only the relation-ablation profile changes task-word construction. -/
def FeatureProfile.taskMode (profile : FeatureProfile) : TaskFeatureMode :=
  if profile.mode == .withoutReachRelation then .withoutReachRelation else .complete

/-- The standalone observation coder derives its mode from the immutable profile. -/
def FeatureProfile.encode (profile : FeatureProfile) (dimension : Dimension)
    {config : Features.Config} (bank : Bank Host.patchShape config) (observation : Host.Observation)
    (predictions : Predictions) : SwiftTd.ActiveSet dimension :=
  encodeObservation dimension bank observation predictions profile.taskMode

/-- Current raw spatial potential observations, in option table order. -/
def spatialPotentials (obs : Host.Observation) : DeclaredPotentials :=
  let kind := fun code => obs.tiles.any (fun row => row.any (fun tile => tile.kind == code))
  ⟨.spatialPotentials, #v[
    kind Host.TileKind.tree.code,
    kind Host.TileKind.ore.code || kind Host.TileKind.stone.code,
    obs.tiles.any (fun row => row.any (fun tile => tile.food != 0))]⟩

/-- A list built from pieces of bounded length is bounded by their count. -/
theorem flatMap_length_le {α β : Type} (items : List α) (piece : α → List β) (bound : Nat)
    (each : ∀ item, (piece item).length ≤ bound) :
    (items.flatMap piece).length ≤ items.length * bound := by
  induction items with
  | nil => simp
  | cons head tail ih =>
    have := each head
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- A window cell contributes its kind word and at most a food and a deer word. -/
theorem tileWords_length (row col : Fin patchSide) (tile : TileObservation) :
    (tileWords row col tile).length ≤ 3 := by
  simp only [tileWords]
  split <;> split <;> simp

namespace Grid

/-- The grid world accepts nine primitive actions. -/
abbrev actions : Word.Count := ⟨Acorn.FeatureConstants.primitiveCount.toUInt64, by decide⟩

/-- Most words of one grid frame: three per window cell, energy and day, the task
context, and six inventory words. -/
def wordBound : Nat := patchSide * patchSide * 3 + 2 + Acorn.FeatureConstants.taskContextWords + 6

/-- The grid world's interface: the window and task context as the symbol array, the
ten host signals after the agent's reward question, nine actions, the word bound and
prediction feedback channels from `0x50`. -/
abbrev interface : Interface := ⟨patchShape, signalLayout, actions, wordBound, 0x50⟩

/-- The grid world's timing discipline: the host steps the world once for each action,
and the world waits for that action however long the agent computes. This is a
declared value of the world; no definition reads it. -/
def timing : Timing := .agentSynchronized

/-- The agent's layout at the grid instance is the canonical eleven horizons. -/
theorem interface_layout : interface.layout = demonLayout := rfl

/-- Every grid observation stays within the declared word bound, in both task modes. -/
theorem sensorWords_length (obs : Observation) (mode : TaskFeatureMode) :
    (sensorWords obs mode).length ≤ wordBound := by
  have tiles := flatMap_length_le (List.finRange patchSide)
    (fun row => (List.finRange patchSide).flatMap fun col =>
      tileWords row col ((obs.tiles.get row).get col)) (patchSide * 3) (fun row => by
      have cells := flatMap_length_le (List.finRange patchSide)
        (fun col => tileWords row col ((obs.tiles.get row).get col)) 3
        (fun col => tileWords_length row col _)
      simpa [List.length_finRange] using cells)
  have task := taskWords_fit obs.task mode
  have regroup : patchSide * (patchSide * 3) = patchSide * patchSide * 3 :=
    (Nat.mul_assoc _ _ _).symm
  simp only [List.length_finRange] at tiles
  simp only [sensorWords, List.length_append, List.length_cons, List.length_nil, wordBound]
  omega

/-- A window cell's words use the kind, food and deer channels, none of them reserved. -/
theorem tileWords_clear (row col : Fin patchSide) (tile : TileObservation) :
    ∀ word ∈ tileWords row col tile, interface.reserved word.channel = false := by
  intro word member
  simp only [tileWords, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | member) | member
  · rfl
  · split at member
    · rw [List.mem_singleton.mp member]; rfl
    · simp at member
  · split at member
    · rw [List.mem_singleton.mp member]; rfl
    · simp at member

/-- Every task word uses a task channel, in every task and both task modes; none is
reserved. -/
theorem taskWords_clear (task : TaskObservation) (mode : TaskFeatureMode) :
    ∀ word ∈ taskWords task mode, interface.reserved word.channel = false := by
  intro word member
  cases task <;> cases mode <;>
    simp only [taskWords, List.mem_cons, List.not_mem_nil, or_false, beq_self_eq_true,
      reduceCtorEq, beq_iff_eq, ↓reduceIte] at member <;>
    repeat (first | (rcases member with rfl | member; · dsimp only; decide) |
      (rw [member]; dsimp only; decide))

/-- No word of a grid frame uses a prediction feedback channel, in both task modes. -/
theorem sensorWords_clear (obs : Observation) (mode : TaskFeatureMode) :
    ∀ word ∈ sensorWords obs mode, interface.reserved word.channel = false := by
  intro word member
  simp only [sensorWords, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with ((⟨row, _, col, _, cell⟩ | header) | task) | inventory
  · exact tileWords_clear row col _ word cell
  · rcases header with rfl | rfl <;> rfl
  · exact taskWords_clear obs.task mode word task
  · rcases inventory with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The ten signals the grid world supplies: every canonical question after the
agent's own reward question. None of them reads a reward word. -/
def signals (obs : Observation) : Cumulants interface.signals :=
  evaluateCumulants cumulantOrder.tail obs .zero

/-- One grid frame: the declared channel words, the kind patch with the task context,
the host signals, the spatial potentials and the host's achievement flag. -/
def frame (mode : TaskFeatureMode) (obs : Observation) (achieved : Bool) : Frame interface where
  words := sensorWords obs mode
  bounded := sensorWords_length obs mode
  clear := sensorWords_clear obs mode
  symbols := observationPatch obs mode
  signals := signals obs
  potentials := (spatialPotentials obs).values
  achieved := achieved

/-- The percept of one grid step: the frame of the current observation, the reward
word of the preceding transition, and whether that transition achieved the goal. -/
def percept (mode : TaskFeatureMode) (obs : Observation) (reward : Binary32) (achieved : Bool) :
    Percept interface :=
  ⟨frame mode obs achieved, reward⟩

/-- The grid frame's cumulants are the canonical eleven host signal values. -/
theorem signalValues_eq (mode : TaskFeatureMode) (obs : Observation) (reward : Binary32)
    (achieved : Bool) :
    signalValues (frame mode obs achieved) reward = evaluateCumulants cumulantOrder obs reward := rfl

/-- The grid frame's declared potentials are the D2 producer's, with its origin. -/
theorem declared_eq (mode : TaskFeatureMode) (obs : Observation) (achieved : Bool) :
    (frame mode obs achieved).declared = spatialPotentials obs := rfl

/-- There is one canonical signal per prediction channel. -/
theorem order_length : cumulantOrder.length = Acorn.FeatureConstants.demonCount := by
  simp [cumulantOrder]

/-- Feedback words over the canonical signals' horizons are the standalone coder's
prediction words, for every admitted prediction list. -/
theorem feedback_signals (predictions : Predictions) :
    feedbackWords interface.feedback (cumulantOrder.map demonDiscount) predictions.values 0 =
      predictionWords predictions := by
  have bound := predictions.bounded
  have order := order_length
  apply List.ext_getElem
  · simp only [feedbackWords_length, predictionWords, List.length_map, List.length_finRange]
    omega
  · intro position left right
    have stored : position < predictions.values.length := by
      simpa [predictionWords] using right
    rw [feedbackWords_getElem interface.feedback (cumulantOrder.map demonDiscount)
      predictions.values 0 position left (by simp only [List.length_map]; omega) stored]
    simp [predictionWords, cumulantOrder]

/-- The interface feedback words over the grid layout are the standalone coder's
prediction words, for every admitted prediction list. -/
theorem feedback_eq (predictions : Predictions) :
    feedbackWords interface.feedback demonLayout predictions.values 0 =
      predictionWords predictions :=
  feedback_signals predictions

end Grid

variable {profile : FeatureProfile} {criterion : Criterion} {dimension : Dimension}

/-- Encode using the stored previous predictions and this immutable profile. -/
def PredictionControl.encode (state : PredictionControl Grid.interface profile criterion dimension)
    {config : Features.Config} (bank : Bank patchShape config) (obs : Observation) :
    SwiftTd.ActiveSet dimension :=
  profile.encode dimension bank obs (feedbackPredictions state.predictions)

/-- Public action refusal precedes encoding and any state transition. -/
def PredictionControl.advanceRaw (state : PredictionControl Grid.interface profile criterion dimension)
    {config : Features.Config} (bank : Bank patchShape config) (obs : Observation)
    (reward : Binary32) (raw : Nat) (own : Bool) :
    Option (PredictionControl Grid.interface profile criterion dimension) :=
  (Action.admit Acorn.FeatureConstants.primitiveCount raw).map fun action =>
    state.advance (state.encode bank obs) (Grid.frame profile.taskMode obs false) reward action own

/-- Rejection produces no replacement even with arbitrary reward and sensory words. -/
theorem PredictionControl.raw_refusal (state : PredictionControl Grid.interface profile criterion dimension)
    {config : Features.Config} (bank : Bank patchShape config) (obs : Observation)
    (reward : Binary32) (raw : Nat) (own : Bool) (outside : Acorn.FeatureConstants.primitiveCount ≤ raw) :
    state.advanceRaw bank obs reward raw own = none := by
  simp only [PredictionControl.advanceRaw, Action.admit, Nat.not_lt.mpr outside, dite_false]
  rfl

/-- Recursive encoding reads precisely the old cache, before current demon writes. -/
theorem PredictionControl.feedback_input (state : PredictionControl Grid.interface profile criterion dimension)
    {config : Features.Config} (bank : Bank patchShape config) (obs : Observation) :
    state.encode bank obs = profile.encode dimension bank obs (feedbackPredictions state.predictions) := rfl

end Acorn.Handcrafted
