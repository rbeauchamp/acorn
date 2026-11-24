import Acorn.Policy
import Acorn.FeatureConstants

namespace Acorn.Features

def metaCount : Word.Count := ⟨Acorn.FeatureConstants.metaActionCount.toUInt64, by decide⟩

def explorationCap : Nat := Acorn.FeatureConstants.explorationMaxDuration

structure ExploratoryRun (count : Word.Count) where
  action : Action count.word.toNat
  remaining : Fin explorationCap

instance (count : Word.Count) : Provenance (ExploratoryRun count) := ⟨some .explorationDuration⟩

def ExploratoryRun.serve {count : Word.Count} (run : ExploratoryRun count) :
    Option (Action count.word.toNat × ExploratoryRun count) :=
  if h : 0 < run.remaining.val then
    some (run.action, ⟨run.action, ⟨run.remaining.val - 1, by have := run.remaining.isLt; omega⟩⟩)
  else none

theorem ExploratoryRun.serve_exact {count : Word.Count} (run next : ExploratoryRun count)
    (action : Action count.word.toNat) (served : run.serve = some (action, next)) :
    action = run.action ∧ next.action = run.action ∧ next.remaining.val + 1 = run.remaining.val := by
  unfold serve at served
  split at served
  · cases served
    exact ⟨rfl, rfl, by dsimp; omega⟩
  · contradiction

theorem ExploratoryRun.spent {count : Word.Count} (run : ExploratoryRun count) :
    run.serve = none ↔ run.remaining.val = 0 := by simp [serve]

def durationRemainingSpec (uniform : Binary64) : Fin explorationCap :=
  let one := Binary64.ofUInt64 1
  let reciprocal := one.div (one.sub uniform)
  let duration := if !(reciprocal.less (Binary64.ofUInt64 explorationCap.toUInt64)) then
    explorationCap else (Conversion.trunc64 reciprocal).toNat
  ⟨min (duration - 1) (explorationCap - 1), by
    have := Nat.min_le_right (duration - 1) (explorationCap - 1)
    simp only [explorationCap, Acorn.FeatureConstants.explorationMaxDuration] at *
    omega⟩

def durationCountWord (uniform : Binary64) : UInt32 :=
  let one := Binary64.ofUInt64 1
  let reciprocal := one.div (one.sub uniform)
  if !(reciprocal.less (Binary64.ofUInt64 explorationCap.toUInt64)) then 128
  else Conversion.cappedTrunc128 reciprocal

theorem durationCountWord_bound (uniform : Binary64) :
    (durationCountWord uniform).toNat ≤ 128 := by
  dsimp only [durationCountWord]
  split
  · decide
  · rw [Conversion.cappedTrunc128_exact]
    exact Nat.min_le_right _ _

def durationWord (uniform : Binary64) : UInt32 :=
  let count := durationCountWord uniform
  if count = 0 then 0 else count - 1

theorem durationWord_exact (uniform : Binary64) :
    (durationWord uniform).toNat = (durationCountWord uniform).toNat - 1 := by
  dsimp only [durationWord]
  split
  · rename_i zero
    simp [zero]
  · rename_i nonzero
    rw [UInt32.toNat_sub_of_le]
    · rfl
    · rw [UInt32.le_iff_toNat_le]
      have : (durationCountWord uniform).toNat ≠ 0 := by
        intro h
        exact nonzero (UInt32.toNat.inj h)
      change 1 ≤ _
      omega

def durationRemaining (uniform : Binary64) : Fin explorationCap :=
  ⟨(durationWord uniform).toNat, by
    rw [durationWord_exact]
    have := durationCountWord_bound uniform
    change _ < 128
    omega⟩

theorem durationRemaining_eq_spec (uniform : Binary64) :
    durationRemaining uniform = durationRemainingSpec uniform := by
  apply Fin.ext
  simp only [durationRemaining, durationWord_exact, durationCountWord, durationRemainingSpec]
  split
  · rfl
  · rw [Conversion.cappedTrunc128_exact]
    simp only [explorationCap, Acorn.FeatureConstants.explorationMaxDuration]
    omega

def beginExploration (count : Word.Count) (rate : SwiftTd.ExploreRate) (rng : Rng.Xoshiro256) :
    Option (ExploratoryRun count) × Rng.Xoshiro256 :=
  let branch := rng.nextF64
  if !(branch.1.less (Conversion.widen rate.value)) then (none, branch.2) else
    let duration := branch.2.nextF64
    let action := uniformAction count duration.2
    (some ⟨action.1, durationRemaining duration.1⟩, action.2)

structure PersistentDecision (count : Word.Count) where
  action : Action count.word.toNat
  explored : Bool
  run : Option (ExploratoryRun count)
  probabilities : Vector Binary32 count.word.toNat

def PolicySnapshot.drawPersistentCosted {count : Word.Count} (snapshot : PolicySnapshot count)
    (rng : Rng.Xoshiro256) : Costed (PersistentDecision count × Rng.Xoshiro256) :=
  let draw := beginExploration count snapshot.epsilon rng
  Costed.charge .explorationBegin <|
  match draw.1 with
  | some run => do
    let explored := true
    let masses ← snapshot.probabilitiesCosted
    Costed.pure (⟨run.action, explored, some run, masses⟩, draw.2)
  | none => do
    let greedy ← snapshot.greedyCosted draw.2
    let explored := false
    let masses ← snapshot.probabilitiesCosted
    Costed.pure (⟨greedy.1, explored, none, masses⟩, greedy.2)

def PolicySnapshot.drawPersistent {count : Word.Count} (snapshot : PolicySnapshot count)
    (rng : Rng.Xoshiro256) : PersistentDecision count × Rng.Xoshiro256 :=
  (snapshot.drawPersistentCosted rng).val

theorem PolicySnapshot.drawPersistent_def {count : Word.Count} (snapshot : PolicySnapshot count)
    (rng : Rng.Xoshiro256) :
    snapshot.drawPersistent rng =
      let draw := beginExploration count snapshot.epsilon rng
      match draw.1 with
      | some run => (⟨run.action, true, some run, snapshot.probabilities⟩, draw.2)
      | none =>
        let greedy := snapshot.greedy draw.2
        (⟨greedy.1, false, none, snapshot.probabilities⟩, greedy.2) := by
  unfold PolicySnapshot.drawPersistent PolicySnapshot.drawPersistentCosted
  dsimp only
  cases (beginExploration count snapshot.epsilon rng).1 <;> rfl

def Controller.persistentStepCosted {count : Word.Count} {config : Acorn.Config}
    {dimension : Dimension} (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (snapshot : PolicySnapshot count)
    (drawn : PersistentDecision count) (reward : Binary32) (duration : UInt32) :
    Costed (Controller config dimension count.word.toNat) :=
  Costed.charge .policyOpen <|
    controller.valuesStepCosted features snapshot.values drawn.action reward
      (Portable.pow config.rule.gamma duration) (Portable.pow controller.traceDecay duration)

def Controller.persistentStep {count : Word.Count} {config : Acorn.Config} {dimension : Dimension}
    (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (snapshot : PolicySnapshot count)
    (drawn : PersistentDecision count) (reward : Binary32) (duration : UInt32) :
    Controller config dimension count.word.toNat :=
  (controller.persistentStepCosted features snapshot drawn reward duration).val

theorem Controller.persistentStep_def {count : Word.Count} {config : Acorn.Config}
    {dimension : Dimension} (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (snapshot : PolicySnapshot count)
    (drawn : PersistentDecision count) (reward : Binary32) (duration : UInt32) :
    controller.persistentStep features snapshot drawn reward duration =
      controller.valuesStep features snapshot.values drawn.action reward
        (Portable.pow config.rule.gamma duration) (Portable.pow controller.traceDecay duration) :=
  rfl

theorem Controller.persistentStep_policy {count : Word.Count} {config : Acorn.Config}
    {dimension : Dimension} (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (drawn : PersistentDecision count)
    (decision : PolicyDecision count) (reward : Binary32) (duration : UInt32)
    (same : decision.action = drawn.action) :
    controller.policyStep features decision reward duration =
      controller.persistentStep features decision.snapshot drawn reward duration := by
  simp only [Controller.persistentStep_def, Controller.policyStep_def, same]

def servedProbabilitiesCosted {count : Word.Count} (action : Action count.word.toNat) :
    Costed (Vector Binary32 count.word.toNat) :=
  Costed.ofFn fun query => Costed.op .read (if query = action then .one else .zero)

def servedProbabilities {count : Word.Count} (action : Action count.word.toNat) :
    Vector Binary32 count.word.toNat := (servedProbabilitiesCosted action).val

theorem servedProbabilities_def {count : Word.Count} (action : Action count.word.toNat) :
    servedProbabilities action =
      Vector.ofFn fun query => if query = action then .one else .zero := rfl

theorem served_probability {count : Word.Count} (action query : Action count.word.toNat) :
    (servedProbabilities action).get query = (if query = action then .one else .zero) := by
  simp [servedProbabilities_def, Vector.get, Fin.cast]

theorem served_excludes_other {count : Word.Count} (run next : ExploratoryRun count)
    (action other : Action count.word.toNat) (served : run.serve = some (action, next))
    (different : other ≠ run.action) : action ≠ other := by
  rw [(run.serve_exact next action served).1]
  exact Ne.symm different

end Acorn.Features
