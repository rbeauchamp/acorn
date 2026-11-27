import Acorn.Handcrafted.Cumulants
import Acorn.Handcrafted.PredictionControl
import Acorn.Handcrafted.TemporalProfile
import Acorn.Host.Terrain

namespace Acorn.Handcrafted
open Features Host

def FeatureProfile.taskMode (profile : FeatureProfile) : TaskFeatureMode :=
  if profile.mode == .withoutReachRelation then .withoutReachRelation else .complete

def FeatureProfile.encode (profile : FeatureProfile) (dimension : Dimension)
    {config : Features.Config} (bank : Bank Host.patchShape config) (observation : Host.Observation)
    (predictions : Predictions) : SwiftTd.ActiveSet dimension :=
  encodeObservation dimension bank observation predictions profile.taskMode

def spatialPotentials (obs : Host.Observation) : DeclaredPotentials :=
  let kind := fun code => obs.tiles.any (fun row => row.any (fun tile => tile.kind == code))
  ⟨.spatialPotentials, #v[
    kind Host.TileKind.tree.code,
    kind Host.TileKind.ore.code || kind Host.TileKind.stone.code,
    obs.tiles.any (fun row => row.any (fun tile => tile.food != 0))]⟩

theorem flatMap_length_le {α β : Type} (items : List α) (piece : α → List β) (bound : Nat)
    (each : ∀ item, (piece item).length ≤ bound) :
    (items.flatMap piece).length ≤ items.length * bound := by
  induction items with
  | nil => simp
  | cons head tail ih =>
    have := each head
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem tileWords_length (row col : Fin patchSide) (tile : TileObservation) :
    (tileWords row col tile).length ≤ 3 := by
  simp only [tileWords]
  split <;> split <;> simp

namespace Grid

abbrev actions : Word.Count := ⟨Acorn.FeatureConstants.primitiveCount.toUInt64, by decide⟩

def wordBound : Nat := patchSide * patchSide * 3 + 2 + Acorn.FeatureConstants.taskContextWords + 6

def seatWords : Nat := 32

abbrev interface : Interface :=
  ⟨patchShape, signalLayout, actions, wordBound + seatWords, 0x50, .synchronized⟩

theorem interface_layout : interface.layout = demonLayout := rfl

theorem interface_timing : interface.timing = .synchronized := rfl

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

theorem taskWords_clear (task : TaskObservation) (mode : TaskFeatureMode) :
    ∀ word ∈ taskWords task mode, interface.reserved word.channel = false := by
  intro word member
  cases task <;> cases mode <;>
    simp only [taskWords, List.mem_cons, List.not_mem_nil, or_false, beq_self_eq_true,
      reduceCtorEq, beq_iff_eq, ↓reduceIte] at member <;>
    repeat (first | (rcases member with rfl | member; · dsimp only; decide) |
      (rw [member]; dsimp only; decide))

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

def signals (obs : Observation) : Cumulants interface.signals :=
  evaluateCumulants cumulantOrder.tail obs .zero

def frame (mode : TaskFeatureMode) (obs : Observation) (achieved : Bool) : Frame interface where
  words := sensorWords obs mode
  bounded := Nat.le_trans (sensorWords_length obs mode) (Nat.le_add_right wordBound seatWords)
  clear := sensorWords_clear obs mode
  symbols := observationPatch obs mode
  signals := signals obs
  potentials := (spatialPotentials obs).values
  achieved := achieved

def percept (mode : TaskFeatureMode) (obs : Observation) (reward : Binary32) (achieved : Bool) :
    Percept interface :=
  ⟨frame mode obs achieved, reward⟩

theorem frame_room (mode : TaskFeatureMode) (obs : Observation) (achieved : Bool) :
    (frame mode obs achieved).words.length + seatWords ≤ interface.words :=
  Nat.add_le_add_right (sensorWords_length obs mode) seatWords

theorem signalValues_eq (mode : TaskFeatureMode) (obs : Observation) (reward : Binary32)
    (achieved : Bool) :
    signalValues (frame mode obs achieved) reward = evaluateCumulants cumulantOrder obs reward := rfl

theorem declared_eq (mode : TaskFeatureMode) (obs : Observation) (achieved : Bool) :
    (frame mode obs achieved).declared = spatialPotentials obs := rfl

theorem order_length : cumulantOrder.length = Acorn.FeatureConstants.demonCount := by
  simp [cumulantOrder]

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

theorem feedback_eq (predictions : Predictions) :
    feedbackWords interface.feedback demonLayout predictions.values 0 =
      predictionWords predictions :=
  feedback_signals predictions

end Grid

variable {profile : FeatureProfile} {criterion : Criterion} {dimension : Dimension}

def PredictionControl.encode (state : PredictionControl Grid.interface profile criterion dimension)
    {config : Features.Config} (bank : Bank patchShape config) (obs : Observation) :
    SwiftTd.ActiveSet dimension :=
  profile.encode dimension bank obs (feedbackPredictions state.predictions)

def PredictionControl.advanceRaw (state : PredictionControl Grid.interface profile criterion dimension)
    {config : Features.Config} (bank : Bank patchShape config) (obs : Observation)
    (reward : Binary32) (raw : Nat) (own : Bool) :
    Option (PredictionControl Grid.interface profile criterion dimension) :=
  (Action.admit Acorn.FeatureConstants.primitiveCount raw).map fun action =>
    state.advance (state.encode bank obs) (Grid.frame profile.taskMode obs false) reward action own

theorem PredictionControl.raw_refusal (state : PredictionControl Grid.interface profile criterion dimension)
    {config : Features.Config} (bank : Bank patchShape config) (obs : Observation)
    (reward : Binary32) (raw : Nat) (own : Bool) (outside : Acorn.FeatureConstants.primitiveCount ≤ raw) :
    state.advanceRaw bank obs reward raw own = none := by
  simp only [PredictionControl.advanceRaw, Action.admit, Nat.not_lt.mpr outside, dite_false]
  rfl

theorem PredictionControl.feedback_input (state : PredictionControl Grid.interface profile criterion dimension)
    {config : Features.Config} (bank : Bank patchShape config) (obs : Observation) :
    state.encode bank obs = profile.encode dimension bank obs (feedbackPredictions state.predictions) := rfl

end Acorn.Handcrafted
