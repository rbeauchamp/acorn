import Acorn.Sarsa

namespace Acorn.Features

def tieWindow : Binary32 := ⟨Acorn.Constants.tie1e6Bits⟩

structure PolicySnapshot (count : Word.Count) where
  values : Vector Binary32 count.word.toNat
  epsilon : SwiftTd.ExploreRate

variable {count : Word.Count}

def firstAction (count : Word.Count) : Action count.word.toNat := ⟨0, count.positive⟩

def PolicySnapshot.bestCosted (snapshot : PolicySnapshot count) : Costed Binary32 := do
  let first ← Costed.op .read (snapshot.values.get (firstAction count))
  let skip := 1
  let values ← Costed.toList snapshot.values
  let rest ← Costed.drop skip values
  Costed.foldl (fun best value => Costed.op .compare (if best.Less value then value else best))
    first rest

def PolicySnapshot.best (snapshot : PolicySnapshot count) : Binary32 :=
  snapshot.bestCosted.val

theorem PolicySnapshot.best_def (snapshot : PolicySnapshot count) :
    snapshot.best = (snapshot.values.toList.drop 1).foldl
      (fun best value => if best.Less value then value else best)
      (snapshot.values.get (firstAction count)) := rfl

def PolicySnapshot.candidatesCosted (snapshot : PolicySnapshot count) :
    Costed (List (Action count.word.toNat)) := do
  let top ← snapshot.bestCosted
  let threshold ← Costed.op .tieThreshold (top.sub tieWindow)
  let range ← Costed.finRange count.word.toNat
  Costed.filter (fun action => Costed.op .candidate
    (decide (threshold.LessOrEqual (snapshot.values.get action)))) range

def PolicySnapshot.candidates (snapshot : PolicySnapshot count) : List (Action count.word.toNat) :=
  snapshot.candidatesCosted.val

theorem PolicySnapshot.candidates_def (snapshot : PolicySnapshot count) :
    snapshot.candidates =
      let threshold := snapshot.best.sub tieWindow
      (List.finRange count.word.toNat).filter fun action =>
        decide (threshold.LessOrEqual (snapshot.values.get action)) := rfl

def reservoirCosted {actions : Nat} : List (Action actions) → UInt64 → Action actions →
    Rng.Xoshiro256 → Costed (Action actions × Rng.Xoshiro256)
  | [], _, pick, rng => Costed.op .visit (pick, rng)
  | action :: rest, seen, pick, rng =>
    let seen := seen + 1
    let draw := rng.nextBelow (Word.Count.ofWord seen)
    Costed.charge .visit <| Costed.charge .reservoirDraw <|
      reservoirCosted rest seen (if draw.1.val == 0 then action else pick) draw.2

def reservoir {actions : Nat} (pending : List (Action actions)) (seen : UInt64)
    (pick : Action actions) (rng : Rng.Xoshiro256) : Action actions × Rng.Xoshiro256 :=
  (reservoirCosted pending seen pick rng).val

theorem reservoir_nil {actions : Nat} (seen : UInt64) (pick : Action actions)
    (rng : Rng.Xoshiro256) : reservoir [] seen pick rng = (pick, rng) := rfl

theorem reservoir_cons {actions : Nat} (action : Action actions) (rest : List (Action actions))
    (seen : UInt64) (pick : Action actions) (rng : Rng.Xoshiro256) :
    reservoir (action :: rest) seen pick rng =
      let seen := seen + 1
      let draw := rng.nextBelow (Word.Count.ofWord seen)
      reservoir rest seen (if draw.1.val == 0 then action else pick) draw.2 := rfl

theorem reservoir_def {actions : Nat} (pending : List (Action actions)) (seen : UInt64)
    (pick : Action actions) (rng : Rng.Xoshiro256) :
    reservoir pending seen pick rng =
      match pending with
      | [] => (pick, rng)
      | action :: rest =>
        let seen := seen + 1
        let draw := rng.nextBelow (Word.Count.ofWord seen)
        reservoir rest seen (if draw.1.val == 0 then action else pick) draw.2 := by
  cases pending <;> rfl

theorem reservoir_support {actions : Nat} (pending : List (Action actions)) (seen : UInt64)
    (pick : Action actions) (rng : Rng.Xoshiro256) :
    (reservoir pending seen pick rng).1 = pick ∨ (reservoir pending seen pick rng).1 ∈ pending := by
  induction pending generalizing seen pick rng with
  | nil => exact Or.inl rfl
  | cons action rest ih =>
    simp only [reservoir_cons]
    split
    · rcases ih (seen + 1) action (rng.nextBelow (Word.Count.ofWord (seen + 1))).2 with h | h
      · exact Or.inr (List.mem_cons.mpr (Or.inl h))
      · exact Or.inr (List.mem_cons.mpr (Or.inr h))
    · rcases ih (seen + 1) pick (rng.nextBelow (Word.Count.ofWord (seen + 1))).2 with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons.mpr (Or.inr h))

theorem first_reservoir_draw (rng : Rng.Xoshiro256) :
    (rng.nextBelow (Word.Count.ofWord 1)).1.val = 0 := by
  have bound := (rng.nextBelow (Word.Count.ofWord 1)).1.property
  have zero : (rng.nextBelow (Word.Count.ofWord 1)).1.val.toNat = 0 := by
    change (rng.nextBelow (Word.Count.ofWord 1)).1.val.toNat < 1 at bound
    omega
  exact UInt64.toNat_inj.mp zero

theorem reservoir_nonempty {actions : Nat} (action : Action actions)
    (rest : List (Action actions)) (pick : Action actions) (rng : Rng.Xoshiro256) :
    (reservoir (action :: rest) 0 pick rng).1 ∈ action :: rest := by
  rw [reservoir_cons]
  change (reservoir rest 1
    (if (rng.nextBelow (Word.Count.ofWord 1)).1.val == 0 then action else pick)
    (rng.nextBelow (Word.Count.ofWord 1)).2).1 ∈ action :: rest
  rw [first_reservoir_draw]
  simp only [beq_self_eq_true, ite_true]
  rcases reservoir_support rest 1 action (rng.nextBelow (Word.Count.ofWord 1)).2 with h | h
  · exact List.mem_cons.mpr (Or.inl h)
  · exact List.mem_cons.mpr (Or.inr h)

def PolicySnapshot.greedyCosted (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    Costed (Action count.word.toNat × Rng.Xoshiro256) := do
  let pending ← snapshot.candidatesCosted
  reservoirCosted pending 0 (firstAction count) rng

def PolicySnapshot.greedy (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    Action count.word.toNat × Rng.Xoshiro256 :=
  (snapshot.greedyCosted rng).val

theorem PolicySnapshot.greedy_def (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    snapshot.greedy rng = reservoir snapshot.candidates 0 (firstAction count) rng := rfl

def uniformAction (count : Word.Count) (rng : Rng.Xoshiro256) :
    Action count.word.toNat × Rng.Xoshiro256 :=
  let result := rng.nextBelow count
  (⟨result.1.val.toNat, result.1.property⟩, result.2)

def PolicySnapshot.probabilitiesCosted (snapshot : PolicySnapshot count) :
    Costed (Vector Binary32 count.word.toNat) := do
  let explore := snapshot.epsilon.value.div (Binary32.ofUInt64 count.word)
  let complement := Binary32.one.sub snapshot.epsilon.value
  let pending ← snapshot.candidatesCosted
  let size ← Costed.length pending
  let greedy := complement.div (Binary32.ofUInt64 size.toUInt64)
  let top ← snapshot.bestCosted
  let threshold := top.sub tieWindow
  Costed.charge .probabilitiesOpen <| Costed.mapVector (fun value => Costed.op .probability
    (explore.add (if threshold.LessOrEqual value then greedy else .zero))) snapshot.values

def PolicySnapshot.probabilities (snapshot : PolicySnapshot count) : Vector Binary32 count.word.toNat :=
  snapshot.probabilitiesCosted.val

theorem PolicySnapshot.probabilities_def (snapshot : PolicySnapshot count) :
    snapshot.probabilities =
      let explore := snapshot.epsilon.value.div (Binary32.ofUInt64 count.word)
      let greedy := (Binary32.one.sub snapshot.epsilon.value).div
        (Binary32.ofUInt64 snapshot.candidates.length.toUInt64)
      let threshold := snapshot.best.sub tieWindow
      snapshot.values.map fun value => explore.add
        (if threshold.LessOrEqual value then greedy else .zero) := rfl

theorem PolicySnapshot.best_less (snapshot : PolicySnapshot count) :
    snapshot.best = (snapshot.values.toList.drop 1).foldl
      (fun best value => if best.less value then value else best)
      (snapshot.values.get (firstAction count)) := by
  simp only [PolicySnapshot.best_def, Binary32.less_iff]

structure PolicyDecision (count : Word.Count) where
  private mk ::
  snapshot : PolicySnapshot count
  action : Action count.word.toNat
  explored : Bool

def PolicyDecision.stored (snapshot : PolicySnapshot count) (action : Action count.word.toNat)
    (explored : Bool) : PolicyDecision count := ⟨snapshot, action, explored⟩

def PolicySnapshot.drawCosted (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    Costed (PolicyDecision count × Rng.Xoshiro256) :=
  let branch := rng.nextF64
  let explored := branch.1.less (Conversion.widen snapshot.epsilon.value)
  Costed.charge .drawClose <| Costed.bind
    (if explored then Costed.op .uniform (uniformAction count branch.2)
      else snapshot.greedyCosted branch.2)
    fun chosen => Costed.pure (⟨snapshot, chosen.1, explored⟩, chosen.2)

def PolicySnapshot.draw (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    PolicyDecision count × Rng.Xoshiro256 :=
  (snapshot.drawCosted rng).val

theorem PolicySnapshot.draw_def (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    snapshot.draw rng =
      let branch := rng.nextF64
      let explored := branch.1.less (Conversion.widen snapshot.epsilon.value)
      let chosen := if explored then uniformAction count branch.2 else snapshot.greedy branch.2
      (⟨snapshot, chosen.1, explored⟩, chosen.2) := by
  unfold PolicySnapshot.draw PolicySnapshot.drawCosted
  dsimp only
  cases rng.nextF64.1.less (Conversion.widen snapshot.epsilon.value) <;> rfl

def PolicyDecision.continuation (decision : PolicyDecision count) : Binary32 :=
  decision.snapshot.values.get decision.action

def PolicyDecision.probabilities (decision : PolicyDecision count) : Vector Binary32 count.word.toNat :=
  decision.snapshot.probabilities

theorem PolicyDecision.continuation_selected (decision : PolicyDecision count) :
    decision.continuation = decision.snapshot.values.get decision.action := rfl

theorem PolicySnapshot.draw_snapshot (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    (snapshot.draw rng).1.snapshot = snapshot := by
  rw [PolicySnapshot.draw_def]

theorem PolicySnapshot.draw_admitted (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    (snapshot.draw rng).1.action.val < count.word.toNat := (snapshot.draw rng).1.action.isLt

def Controller.policyStepCosted {config : Acorn.Config} {dimension : Dimension}
    (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision count)
    (reward : Binary32) (duration : UInt32) :
    Costed (Controller config dimension count.word.toNat) :=
  Costed.charge .policyOpen <|
    controller.valuesStepCosted features decision.snapshot.values decision.action reward
      (Portable.pow config.rule.gamma duration) (Portable.pow controller.traceDecay duration)

def Controller.policyStep {config : Acorn.Config} {dimension : Dimension}
    (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision count)
    (reward : Binary32) (duration : UInt32) : Controller config dimension count.word.toNat :=
  (controller.policyStepCosted features decision reward duration).val

theorem Controller.policyStep_def {config : Acorn.Config} {dimension : Dimension}
    (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision count)
    (reward : Binary32) (duration : UInt32) :
    controller.policyStep features decision reward duration =
      controller.valuesStep features decision.snapshot.values decision.action reward
        (Portable.pow config.rule.gamma duration) (Portable.pow controller.traceDecay duration) :=
  rfl

def Controller.snapshotCosted {config : Acorn.Config} {dimension : Dimension}
    (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (epsilon : SwiftTd.ExploreRate) :
    Costed (PolicySnapshot count) := do
  let values ← controller.predictAllCosted features
  Costed.op .snapshot ⟨values, epsilon⟩

def Controller.snapshot {config : Acorn.Config} {dimension : Dimension}
    (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (epsilon : SwiftTd.ExploreRate) : PolicySnapshot count :=
  (controller.snapshotCosted features epsilon).val

theorem Controller.snapshot_def {config : Acorn.Config} {dimension : Dimension}
    (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (epsilon : SwiftTd.ExploreRate) :
    controller.snapshot features epsilon = ⟨controller.predictAll features, epsilon⟩ := rfl

def Controller.exploreRateCosted {config : Acorn.Config} {dimension : Dimension}
    (controller : Controller config dimension count.word.toNat) : Costed SwiftTd.ExploreRate := do
  let initial := (Binary32.zero, 0)
  let rows ← Costed.toList controller.learners
  let totals ← Costed.foldl (fun (sum, count) learner => do
    let contribution ← learner.state.normalizedStepSizeSumCosted
    Costed.op .rateTerm (sum.add contribution.1, count + contribution.2)) initial rows
  Costed.op .rateClose (SwiftTd.ExploreRate.project <| if totals.2 == 0 then
    (controller.learners.get (firstAction count)).state.initialNormalizedStepSize config
  else totals.1.div (Binary32.ofUInt64 totals.2.toUInt64))

def Controller.exploreRate {config : Acorn.Config} {dimension : Dimension}
    (controller : Controller config dimension count.word.toNat) : SwiftTd.ExploreRate :=
  controller.exploreRateCosted.val

theorem Controller.exploreRate_def {config : Acorn.Config} {dimension : Dimension}
    (controller : Controller config dimension count.word.toNat) :
    controller.exploreRate =
      let totals := controller.learners.toList.foldl (fun (sum, count) learner =>
        let contribution := learner.state.normalizedStepSizeSum
        (sum.add contribution.1, count + contribution.2)) (Binary32.zero, 0)
      SwiftTd.ExploreRate.project <| if totals.2 == 0 then
        (controller.learners.get (firstAction count)).state.initialNormalizedStepSize config
      else totals.1.div (Binary32.ofUInt64 totals.2.toUInt64) := rfl

def PolicySnapshot.expectedCosted (snapshot : PolicySnapshot count) : Costed Binary32 := do
  let first ← Costed.op .read (snapshot.values.get (firstAction count))
  let values ← Costed.toList snapshot.values
  let lower ← Costed.foldl (fun lo v => Costed.op .compare (if v.less lo then v else lo))
    first values
  let upper ← snapshot.bestCosted
  let threshold ← Costed.op .tieThreshold (upper.sub tieWindow)
  let totals ← Costed.foldl (fun (all, tied, n) v => Costed.op .expectedTerm
    (all.add (Conversion.widen v),
      if threshold.lessOrEqual v then tied.add (Conversion.widen v) else tied,
      if threshold.lessOrEqual v then n + 1 else n))
    (Binary64.ofUInt64 0, Binary64.ofUInt64 0, 0) values
  let eps := Conversion.widen snapshot.epsilon.value
  let value := ((Binary64.ofUInt64 1).sub eps).mul
    (totals.2.1.div (Binary64.ofUInt64 totals.2.2.toUInt64))
  let value := value.add (eps.mul (totals.1.div (Binary64.ofUInt64 count.word)))
  Costed.op .expectedClose ((Conversion.narrow value).saturate lower upper)

def PolicySnapshot.expected (snapshot : PolicySnapshot count) : Binary32 :=
  snapshot.expectedCosted.val

theorem PolicySnapshot.expected_def (snapshot : PolicySnapshot count) :
    snapshot.expected =
      let first := snapshot.values.get (firstAction count)
      let lower := snapshot.values.toList.foldl (fun lo v => if v.less lo then v else lo) first
      let upper := snapshot.best
      let threshold := upper.sub tieWindow
      let totals := snapshot.values.toList.foldl (fun (all, tied, n) v =>
        (all.add (Conversion.widen v),
          if threshold.lessOrEqual v then tied.add (Conversion.widen v) else tied,
          if threshold.lessOrEqual v then n + 1 else n))
        (Binary64.ofUInt64 0, Binary64.ofUInt64 0, 0)
      let eps := Conversion.widen snapshot.epsilon.value
      let value := ((Binary64.ofUInt64 1).sub eps).mul
        (totals.2.1.div (Binary64.ofUInt64 totals.2.2.toUInt64))
      let value := value.add (eps.mul (totals.1.div (Binary64.ofUInt64 count.word)))
      (Conversion.narrow value).saturate lower upper := rfl

def PolicySnapshot.consistentCosted (snapshot : PolicySnapshot count)
    (behaviour : Vector Binary32 count.word.toNat) : Costed Bool := do
  let masses ← snapshot.probabilitiesCosted
  Costed.vectorEq masses behaviour

def PolicySnapshot.consistent (snapshot : PolicySnapshot count)
    (behaviour : Vector Binary32 count.word.toNat) : Bool :=
  (snapshot.consistentCosted behaviour).val

theorem PolicySnapshot.consistent_def (snapshot : PolicySnapshot count)
    (behaviour : Vector Binary32 count.word.toNat) :
    snapshot.consistent behaviour = decide (snapshot.probabilities = behaviour) := rfl

theorem PolicySnapshot.consistent_iff (snapshot : PolicySnapshot count)
    (behaviour : Vector Binary32 count.word.toNat) :
    snapshot.consistent behaviour = true ↔ snapshot.probabilities = behaviour := by
  simp [PolicySnapshot.consistent_def]

theorem PolicySnapshot.consistent_mass (snapshot : PolicySnapshot count)
    (behaviour : Vector Binary32 count.word.toNat) (action : Action count.word.toNat)
    (consistent : snapshot.consistent behaviour = true) :
    snapshot.probabilities.get action = behaviour.get action := by
  rw [(snapshot.consistent_iff behaviour).mp consistent]

theorem PolicyDecision.consistent_own (decision : PolicyDecision count) :
    decision.snapshot.consistent decision.probabilities = true :=
  (decision.snapshot.consistent_iff _).mpr rfl

def PolicySnapshot.massCosted (snapshot : PolicySnapshot count)
    (action : Action count.word.toNat) : Costed SwiftTd.ExploreRate := do
  let masses ← snapshot.probabilitiesCosted
  Costed.op .probability (SwiftTd.ExploreRate.project (masses.get action))

def PolicySnapshot.mass (snapshot : PolicySnapshot count) (action : Action count.word.toNat) :
    SwiftTd.ExploreRate :=
  (snapshot.massCosted action).val

theorem PolicySnapshot.mass_def (snapshot : PolicySnapshot count)
    (action : Action count.word.toNat) :
    snapshot.mass action = SwiftTd.ExploreRate.project (snapshot.probabilities.get action) := rfl

def Controller.backupErrorCosted {config : Acorn.Config} {dimension : Dimension}
    (controller : Controller config dimension count.word.toNat) (snapshot : PolicySnapshot count)
    (reward : Binary32) : Costed Binary32 := do
  let gamma := config.rule.gamma
  let expected ← snapshot.expectedCosted
  Costed.op .learnerError ((reward.add (gamma.mul expected)).sub controller.vOld)

def Controller.backupError {config : Acorn.Config} {dimension : Dimension}
    (controller : Controller config dimension count.word.toNat) (snapshot : PolicySnapshot count)
    (reward : Binary32) : Binary32 :=
  (controller.backupErrorCosted snapshot reward).val

theorem Controller.backupError_def {config : Acorn.Config} {dimension : Dimension}
    (controller : Controller config dimension count.word.toNat) (snapshot : PolicySnapshot count)
    (reward : Binary32) :
    controller.backupError snapshot reward =
      (reward.add (config.rule.gamma.mul snapshot.expected)).sub controller.vOld := rfl

def Controller.backupStepCosted {config : Acorn.Config} {dimension : Dimension}
    (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (snapshot : PolicySnapshot count)
    (action : Action count.word.toNat) (reward : Binary32) :
    Costed (Controller config dimension count.word.toNat) := do
  let lag := snapshot.values.get action
  let delta ← controller.backupErrorCosted snapshot reward
  let decay := controller.traceDecay
  let mass ← snapshot.massCosted action
  controller.creditStepCosted features action lag delta (decay.mul mass.value)

def Controller.backupStep {config : Acorn.Config} {dimension : Dimension}
    (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (snapshot : PolicySnapshot count)
    (action : Action count.word.toNat) (reward : Binary32) :
    Controller config dimension count.word.toNat :=
  (controller.backupStepCosted features snapshot action reward).val

theorem Controller.backupStep_def {config : Acorn.Config} {dimension : Dimension}
    (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (snapshot : PolicySnapshot count)
    (action : Action count.word.toNat) (reward : Binary32) :
    controller.backupStep features snapshot action reward =
      controller.creditStep features action (snapshot.values.get action)
        (controller.backupError snapshot reward)
        (controller.traceDecay.mul (snapshot.mass action).value) := rfl

theorem PolicySnapshot.mass_bounded (snapshot : PolicySnapshot count)
    (action : Action count.word.toNat) :
    SwiftTd.exploreRange.Contains (snapshot.mass action).value := (snapshot.mass action).legal

theorem Controller.backupStep_lag {config : Acorn.Config} {dimension : Dimension}
    (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (snapshot : PolicySnapshot count)
    (action : Action count.word.toNat) (reward : Binary32) :
    (controller.backupStep features snapshot action reward).vOld = snapshot.values.get action := by
  rw [Controller.backupStep_def, Controller.creditStep_eq]

end Acorn.Features
