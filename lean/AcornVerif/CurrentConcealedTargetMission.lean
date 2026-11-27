import AcornVerif.CurrentArithmetic
import AcornVerif.CurrentConcealedTarget
import AcornVerif.MissionVisits

namespace AcornVerif.CurrentConcealedTargetMission
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentArithmetic AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.MissionVisits AcornVerif.Intent AcornVerif.Intent.MissionTheorem

variable {config : Host.WorldConfig}

def reward (percept : Percept Grid.interface) : ℚ :=
  numerical32 percept.reward

def goalMet : Option (Live config) → Bool
  | some live => live.world.goalSatisfied
  | none => false

theorem goalMet_iff (mode : TaskFeatureMode) (cap : ℕ) (state : Option (Live config)) :
    goalMet state = true ↔ (completion config mode cap).satisfied state := by
  cases state with
  | none =>
    exact ⟨fun shown => absurd shown Bool.false_ne_true, fun ⟨_, never, _⟩ => nomatch never⟩
  | some live =>
    exact ⟨fun met => ⟨live, rfl, met⟩, fun ⟨found, same, met⟩ => by cases same; exact met⟩

theorem reward_word_step (mode : TaskFeatureMode) (state : Option (Live config))
    (action : Kernel.Act Grid.interface) :
    ((gridWorld config mode).percept ((gridWorld config mode).step state action)).reward =
      if goalMet ((gridWorld config mode).step state action) then Binary32.one
      else Binary32.zero := by
  cases state with
  | none => rfl
  | some live =>
    change ((gridWorld config mode).percept (advance live action)).reward =
      if goalMet (advance live action) then Binary32.one else Binary32.zero
    cases stepped : advance live action with
    | none => rfl
    | some next =>
      obtain ⟨events, moved, carried⟩ := advance_some live next action stepped
      have done := Host.World.step_completion _ _ _ _ moved
      change next.carried.reward = if next.world.goalSatisfied then Binary32.one else Binary32.zero
      rw [carried, ← done]
      change events.reward = _
      unfold Host.StepResult.reward
      cases events.done <;> rfl

theorem reward_step (mode : TaskFeatureMode) (state : Option (Live config))
    (action : Kernel.Act Grid.interface) :
    reward ((gridWorld config mode).percept ((gridWorld config mode).step state action)) =
      if goalMet ((gridWorld config mode).step state action) then 1 else 0 := by
  have zero : numerical32 Binary32.zero = 0 := by decide
  have one : numerical32 Binary32.one = 1 := by
    change (1 : ℚ) * 8388608 * (2 : ℚ) ^ (-23 : Int) = 1
    norm_num
  change numerical32 ((gridWorld config mode).percept
    ((gridWorld config mode).step state action)).reward = _
  rw [reward_word_step]
  cases goalMet ((gridWorld config mode).step state action)
  · exact zero
  · exact one

theorem find_pays (mode : TaskFeatureMode) (live : Live config) (length : ℕ)
    (fresh : live.carried.reward = ⟨0⟩) :
    PaysAtGoals (feasibleFind config mode live length) (fun _ => completion config mode length)
      reward (fun _ => goalMet) where
  reads := fun _ state => goalMet_iff mode length state
  pays := fun _ state action => reward_step mode state action
  quiet := fun _ => by
    change numerical32 live.carried.reward = 0
    rw [fresh]
    decide

def findRung (config : Host.WorldConfig) (mode : TaskFeatureMode) (live : Live config)
    (length horizon lapses : ℕ) (counted : List (feasibleFind config mode live length).Index)
    (agent : Kernel.Agent Grid.interface)
    (updates : agent.Memory → Percept Grid.interface × ℚ → List OneStream.Update)
    (work : agent.Memory → Percept Grid.interface × ℚ → ℕ)
    (resume : agent.Memory → agent.Memory) : Rung :=
  visitsRung (feasibleFind config mode live length) length horizon lapses reward
    (fun _ => goalMet) counted agent updates work resume

theorem find_mission (config : Host.WorldConfig) (mode : TaskFeatureMode) (live : Live config)
    (length horizon lapses limit : ℕ) (fresh : live.carried.reward = ⟨0⟩)
    (counted : List (feasibleFind config mode live length).Index) (distinct : counted.Nodup)
    {agent : Kernel.Agent Grid.interface}
    {updates : agent.Memory → Percept Grid.interface × ℚ → List OneStream.Update}
    {work : agent.Memory → Percept Grid.interface × ℚ → ℕ}
    {resume : agent.Memory → agent.Memory}
    (separates : Kernel.SeparatesBy (feasibleFind config mode live length)
      (fun _ => completion config mode length) length (49 + 7 * length) counted limit agent)
    (room : limit + lapses < horizon)
    (retains : Kernel.RetainsBut (feasibleFind config mode live length)
      (fun _ => completion config mode length) length horizon lapses agent)
    (stream : ∀ target, OneStream.oneStream.Meets
      ((findRung config mode live length horizon lapses counted agent updates work
        resume).learner target)) :
    Mission (findRung config mode live length horizon lapses counted agent updates work resume) :=
  visits_mission (find_pays mode live length fresh) (feasibleFind_conceals mode live length length)
    (feasibleFind_covered config mode live length) (fun target => target.2) distinct separates
    room retains stream

theorem witness_mission (mode : TaskFeatureMode) :
    ∃ counted : List (feasibleFind witnessConfig mode witnessLive 7).Index,
      counted.Nodup ∧ counted.length = 147 ∧
        ∀ horizon, 3 < horizon →
          Mission (retraceRung (feasibleFind witnessConfig mode witnessLive 7) 7 horizon 2 reward
            (fun _ => goalMet) counted witnessExplore) := by
  classical
  obtain ⟨members, count, explored⟩ := witness_explored mode
  have feasible : ∀ target ∈ members,
      Kernel.Feasible (completion witnessConfig mode 7) (member witnessLive target.1) := by
    intro target chosen
    obtain ⟨visit, -, step, low, high, met⟩ := explored target chosen
    exact ⟨witnessExplore visit, step, low, high, met⟩
  let admitted : { target // target ∈ members } →
      (feasibleFind witnessConfig mode witnessLive 7).Index :=
    fun target => ⟨target.1, feasible target.1 target.2⟩
  have injective : Function.Injective admitted := by
    intro first second same
    exact Subtype.ext (congrArg
      (fun target : (feasibleFind witnessConfig mode witnessLive 7).Index => target.1) same)
  have size : (members.attach.map ⟨admitted, injective⟩).toList.length = 147 := by
    rw [Finset.length_toList, Finset.card_map, Finset.card_attach, count]
  refine ⟨(members.attach.map ⟨admitted, injective⟩).toList, Finset.nodup_toList _, size,
    fun horizon late => ?_⟩
  refine retrace_mission (find_pays mode witnessLive 7 rfl)
    (feasibleFind_conceals mode witnessLive 7 7) (feasibleFind_covered witnessConfig mode
      witnessLive 7) (fun target => target.2) (Finset.nodup_toList _) (by rw [size]; decide) 2
    late witnessExplore (fun index listed => ?_)
  obtain ⟨target, -, rfl⟩ := Finset.mem_map.mp (Finset.mem_toList.mp listed)
  exact explored target.1 target.2

section executed

variable {profile : FeatureProfile} {features : Features.Config} {criterion : Criterion}
  {dimension : Dimension} {planning : PlanningSelection}

def ActsAsExecuted (state : Agent Grid.interface profile features criterion dimension planning)
    (agent : Kernel.Agent Grid.interface) : Prop :=
  ∀ (world : Kernel.World Grid.interface) (start : world.State) (time : ℕ),
    Kernel.actionAt world agent start time = Kernel.actionAt world (executedAgent state) start time

theorem executedAgent_actsAs
    (state : Agent Grid.interface profile features criterion dimension planning) :
    ActsAsExecuted state (executedAgent state) :=
  fun _ _ _ => rfl

def ExecutedFinds (state : Agent Grid.interface profile features criterion dimension planning)
    (config : Host.WorldConfig) (live : Live config) (length : ℕ)
    (counted : List (feasibleFind config profile.taskMode live length).Index) : Prop :=
  Kernel.Finds (feasibleFind config profile.taskMode live length)
    (fun _ => completion config profile.taskMode length) length (49 + 7 * length) counted
    (executedAgent state)

def ExecutedFindsBy (state : Agent Grid.interface profile features criterion dimension planning)
    (config : Host.WorldConfig) (live : Live config) (length : ℕ)
    (counted : List (feasibleFind config profile.taskMode live length).Index)
    (last spare : ℕ) : Prop :=
  Kernel.FindsBy (feasibleFind config profile.taskMode live length)
    (fun _ => completion config profile.taskMode length) length (49 + 7 * length + spare) counted
    last (executedAgent state)

theorem ExecutedFindsBy.finds
    {state : Agent Grid.interface profile features criterion dimension planning}
    {live : Live config} {length last spare : ℕ}
    {counted : List (feasibleFind config profile.taskMode live length).Index}
    (finds : ExecutedFindsBy state config live length counted last spare) :
    ExecutedFinds state config live length counted := by
  obtain ⟨solved, many, each⟩ := Kernel.FindsBy.finds finds
  exact ⟨solved, by omega, each⟩

def ExecutedRetainsOn
    (state : Agent Grid.interface profile features criterion dimension planning)
    (config : Host.WorldConfig) (live : Live config) (length horizon : ℕ)
    (admits : (feasibleFind config profile.taskMode live length).Index → ℕ → Prop) : Prop :=
  Kernel.RetainsOn (feasibleFind config profile.taskMode live length)
    (fun _ => completion config profile.taskMode length) length horizon admits
    (executedAgent state)

def ExecutedCalm (state : Agent Grid.interface profile features criterion dimension planning)
    (config : Host.WorldConfig) (live : Live config) (length : ℕ)
    (index : (feasibleFind config profile.taskMode live length).Index) (visit : ℕ) : Prop :=
  ∀ step, step < length →
    ((Kernel.memoryAt
        (Kernel.visits ((feasibleFind config profile.taskMode live length).world index)
          ((feasibleFind config profile.taskMode live length).start index) length)
        (executedAgent state)
        (Kernel.visitStart ((feasibleFind config profile.taskMode live length).world index)
          ((feasibleFind config profile.taskMode live length).start index) length)
        (visit * (length + 1) + step)).act
      (Kernel.perceptAt
        (Kernel.visits ((feasibleFind config profile.taskMode live length).world index)
          ((feasibleFind config profile.taskMode live length).start index) length)
        (executedAgent state)
        (Kernel.visitStart ((feasibleFind config profile.taskMode live length).world index)
          ((feasibleFind config profile.taskMode live length).start index) length)
        (visit * (length + 1) + step))).2.explored = false

theorem executed_mission
    (state : Agent Grid.interface profile features criterion dimension planning)
    (config : Host.WorldConfig) (live : Live config)
    (length horizon lapses last limit spare : ℕ) (fresh : live.carried.reward = ⟨0⟩)
    (counted : List (feasibleFind config profile.taskMode live length).Index)
    (distinct : counted.Nodup) {agent : Kernel.Agent Grid.interface}
    (acts : ActsAsExecuted state agent)
    {updates : agent.Memory → Percept Grid.interface × ℚ → List OneStream.Update}
    {work : agent.Memory → Percept Grid.interface × ℚ → ℕ}
    {resume : agent.Memory → agent.Memory}
    {admits : (feasibleFind config profile.taskMode live length).Index → ℕ → Prop}
    (finds : ExecutedFindsBy state config live length counted last spare)
    (retains : ExecutedRetainsOn state config live length horizon admits)
    (few : Kernel.AdmitsBut admits horizon lapses)
    (once : Kernel.AdmitsOnce admits counted last limit spare)
    (room : limit + lapses < horizon)
    (memory : MemoryBounded (findRung config profile.taskMode live length horizon lapses
      counted agent updates work resume))
    (bounded : WorkBounded (findRung config profile.taskMode live length horizon lapses
      counted agent updates work resume))
    (arrival : LearnsOnArrival (findRung config profile.taskMode live length horizon lapses
      counted agent updates work resume))
    (discipline : KeepsDiscipline (findRung config profile.taskMode live length horizon lapses
      counted agent updates work resume)) :
    Mission (findRung config profile.taskMode live length horizon lapses counted agent updates
      work resume) :=
  find_mission config profile.taskMode live length horizon lapses limit fresh counted distinct
    (Kernel.separatesBy_of_finds_on (Kernel.FindsBy.of_actions acts finds)
      (Kernel.RetainsOn.of_actions acts retains) once (by omega))
    room ((Kernel.RetainsOn.of_actions acts retains).but few)
    (Rung.stream_met memory bounded arrival discipline)

end executed

end AcornVerif.CurrentConcealedTargetMission
