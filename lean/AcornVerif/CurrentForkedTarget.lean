import AcornVerif.CurrentConcealedTargetMission
import AcornVerif.Turns

namespace AcornVerif.CurrentForkedTarget
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.Coverage AcornVerif.CurrentGoals AcornVerif.CurrentGridWorld
open AcornVerif.CurrentConcealedTarget AcornVerif.CurrentConcealedTargetMission
open AcornVerif.CurrentStep

variable {config : Host.WorldConfig}

def forkedFind (config : Host.WorldConfig) (mode : TaskFeatureMode) (first second : Live config)
    (length : ℕ) : Kernel.TurnClass Grid.interface where
  Index := { pair : (feasibleFind config mode first length).Index ×
      (feasibleFind config mode second length).Index //
    ∀ actions : ℕ → Kernel.Act Grid.interface,
      ¬ ((completion config mode length).MetBy (member first pair.1.1.1) actions ∧
        (completion config mode length).MetBy (member second pair.2.1.1) actions) }
  world := fun _ => gridWorld config mode
  start := fun pair situation =>
    match situation with
    | false => member first pair.1.1.1.1
    | true => member second pair.1.2.1.1

def forkedGoals (config : Host.WorldConfig) (mode : TaskFeatureMode) (first second : Live config)
    (length : ℕ) : (forkedFind config mode first second length).Goals :=
  fun _ => completion config mode length

def firstTarget (mode : TaskFeatureMode) (first second : Live config) (length : ℕ)
    (pair : (forkedFind config mode first second length).Index) :
    (feasibleFind config mode first length).Index :=
  pair.1.1

theorem forked_apart (mode : TaskFeatureMode) (first second : Live config) (length : ℕ) :
    Kernel.Apart (forkedFind config mode first second length)
      (forkedGoals config mode first second length) length :=
  fun pair actions both => pair.2 actions both

theorem forked_conceals (mode : TaskFeatureMode) (first second : Live config) (length : ℕ) :
    Kernel.Conceals ((forkedFind config mode first second length).side false)
      (forkedGoals config mode first second length) (gridWorld config mode)
      (member first nowhere) :=
  fun pair actions time unmet =>
    find_conceals mode first length pair.1.1.1 actions time unmet

theorem forked_covered (mode : TaskFeatureMode) (first second : Live config) (length : ℕ)
    (actions : ℕ → Kernel.Act Grid.interface)
    (solved : Finset (forkedFind config mode first second length).Index)
    (distinct : ∀ one ∈ solved, ∀ two ∈ solved,
      firstTarget mode first second length one = firstTarget mode first second length two →
        one = two)
    (each : ∀ pair ∈ solved,
      (Kernel.turnGoal (forkedGoals config mode first second length) length pair).MetBy
        ((forkedFind config mode first second length).start pair false) actions) :
    solved.card ≤ 49 + 7 * length := by
  classical
  rw [← Finset.card_image_of_injOn (f := firstTarget mode first second length)
    (fun one inOne two inTwo same => distinct one inOne two inTwo same)]
  apply feasibleFind_covered config mode first length actions
  intro target chosen
  obtain ⟨pair, picked, rfl⟩ := Finset.mem_image.mp chosen
  exact each pair picked

theorem quiet_step (mode : TaskFeatureMode) (cap : ℕ) (state : Option (Live config))
    (action : Kernel.Act Grid.interface)
    (unmet : ¬ (completion config mode cap).satisfied
      ((gridWorld config mode).step state action)) :
    ((gridWorld config mode).percept ((gridWorld config mode).step state action)).reward =
        Binary32.zero ∧
      ((gridWorld config mode).percept
        ((gridWorld config mode).step state action)).frame.achieved = false := by
  have missed : goalMet ((gridWorld config mode).step state action) = false :=
    Bool.eq_false_iff.mpr (fun shown => unmet ((goalMet_iff mode cap _).mp shown))
  refine ⟨?_, Bool.eq_false_iff.mpr (fun shown =>
    unmet ((achieved_decodes config mode cap state action).mp shown))⟩
  rw [reward_word_step, missed]
  rfl

theorem forked_mute (mode : TaskFeatureMode) (first second : Live config) (length : ℕ)
    (carried : first.carried = second.carried) :
    Kernel.Mute (fun percept : Percept Grid.interface => (percept.reward, percept.frame.achieved))
      (forkedFind config mode first second length)
      (forkedGoals config mode first second length) := by
  intro pair actions time unmetFirst unmetSecond
  cases time with
  | zero =>
    change (first.carried.reward, first.carried.events.done) =
      (second.carried.reward, second.carried.events.done)
    rw [carried]
  | succ time =>
    have one := quiet_step mode length
      (Kernel.path (gridWorld config mode) (member first pair.1.1.1.1) actions time)
      (actions time) (unmetFirst (time + 1) (Nat.succ_pos time) (Nat.le_refl _))
    have two := quiet_step mode length
      (Kernel.path (gridWorld config mode) (member second pair.1.2.1.1) actions time)
      (actions time) (unmetSecond (time + 1) (Nat.succ_pos time) (Nat.le_refl _))
    exact Prod.ext (one.1.trans two.1.symm) (one.2.trans two.2.symm)

theorem forked_blind (mode : TaskFeatureMode) (first second : Live config) (length : ℕ)
    (carried : first.carried = second.carried) {agent : Kernel.Agent Grid.interface}
    (blind : Kernel.FeedbackDriven
      (fun percept : Percept Grid.interface => (percept.reward, percept.frame.achieved)) agent)
    (bound limit : ℕ) {κ : Type}
    (key : (forkedFind config mode first second length).Index → κ) :
    ¬ Kernel.MastersBy (forkedFind config mode first second length)
      (forkedGoals config mode first second length) length bound key limit agent :=
  blind.masters (forked_mute mode first second length carried)
    (forked_apart mode first second length) bound limit key

theorem forked_need (mode : TaskFeatureMode) (first second : Live config) (length : ℕ)
    {agent : Kernel.Agent Grid.interface} (free : Kernel.ExperienceFree agent) (limit : ℕ) :
    ¬ Kernel.MastersBy (forkedFind config mode first second length)
      (forkedGoals config mode first second length) length (49 + 7 * length)
      (firstTarget mode first second length) limit agent :=
  Kernel.turns_need (forked_conceals mode first second length)
    (firstTarget mode first second length) (forked_covered mode first second length) free limit

theorem step_heading (world next : Host.World config) (action : Host.Action)
    (events : Host.StepResult) (h : world.step action = .ok (next, events)) :
    next.body.position = world.body.position ∨
      ∃ direction, action.direction = some direction ∧
        world.body.position.position.translate direction.delta.1 direction.delta.2 =
          some next.body.position.position := by
  obtain ⟨active, paid, body, -⟩ := step_active world next action events h
  rw [body]
  obtain ⟨night, outcome⟩ := payAndAct_outcome world action active paid
  rcases outcome with ⟨-, exhausted, -⟩ | ⟨energy, -, performed, -⟩
  · left
    rw [exhausted]
  · cases performed with
    | unchanged same => left; rw [same]
    | moved direction candidate position picked heading translated admitted entered result =>
      right
      rw [result]
      refine ⟨direction, heading, ?_⟩
      change world.body.position.position.translate direction.delta.1 direction.delta.2 =
        some position.position
      rw [checked_position candidate position admitted]
      exact translated
    | harvested item amount result => left; rw [result]
    | crafted tool inventory recipe result => left; rw [result]
    | ate meal result => left; rw [result]

theorem physicalStep_heading (world next : Host.World config)
    (action : Kernel.Act Grid.interface) (h : physicalStep world action = some next) :
    tile next.body.position.position = tile world.body.position.position ∨
      ∃ direction, (Host.Action.fromIndex action.val).direction = some direction ∧
        tile next.body.position.position =
          ((tile world.body.position.position).1 + direction.delta.1,
            (tile world.body.position.position).2 + direction.delta.2) := by
  cases stepped : world.step (Host.Action.fromIndex action.val) with
  | error refusal => simp [physicalStep, stepped] at h
  | ok pair =>
    obtain ⟨after, events⟩ := pair
    simp only [physicalStep, stepped, Option.some.injEq] at h
    subst h
    rcases step_heading world after _ events stepped with same | ⟨direction, heading, moved⟩
    · left
      change tile after.body.position.position = _
      rw [same]
    · right
      obtain ⟨horizontal, vertical⟩ := CurrentCertificates.translate_some _ _ _ _ moved
      exact ⟨direction, heading, Prod.ext horizontal vertical⟩

def taken (actions : ℕ → Kernel.Act Grid.interface) (direction : Host.Direction) : ℕ → ℕ
  | 0 => 0
  | count + 1 => taken actions direction count +
      if (Host.Action.fromIndex (actions count).val).direction = some direction then 1 else 0

theorem taken_mono (actions : ℕ → Kernel.Act Grid.interface) (direction : Host.Direction)
    {count later : ℕ} (after : count ≤ later) :
    taken actions direction count ≤ taken actions direction later := by
  induction later with
  | zero => rw [Nat.le_zero.mp after]
  | succ later ih =>
    rcases Nat.lt_or_eq_of_le after with sooner | same
    · exact Nat.le_trans (ih (Nat.le_of_lt_succ sooner)) (Nat.le_add_right _ _)
    · rw [same]

theorem taken_pair (actions : ℕ → Kernel.Act Grid.interface) (one two : Host.Direction)
    (differ : one ≠ two) (count : ℕ) :
    taken actions one count + taken actions two count ≤ count := by
  induction count with
  | zero => exact Nat.le_refl 0
  | succ count ih =>
    change taken actions one count +
        (if (Host.Action.fromIndex (actions count).val).direction = some one then 1 else 0) +
      (taken actions two count +
        (if (Host.Action.fromIndex (actions count).val).direction = some two then 1 else 0)) ≤
      count + 1
    by_cases first : (Host.Action.fromIndex (actions count).val).direction = some one
    · have other : (Host.Action.fromIndex (actions count).val).direction ≠ some two :=
        fun second => differ (Option.some.inj (first.symm.trans second))
      rw [ite_eq_left first, ite_eq_right other]
      omega
    · rw [ite_eq_right first]
      split <;> omega

theorem walk_reach (start : Host.World config) (actions : ℕ → Kernel.Act Grid.interface)
    (count : ℕ) :
    (walk start actions count).1 ≤
        (tile start.body.position.position).1 + taken actions .east count ∧
      (tile start.body.position.position).1 - taken actions .west count ≤
        (walk start actions count).1 ∧
      (walk start actions count).2 ≤
        (tile start.body.position.position).2 + taken actions .south count ∧
      (tile start.body.position.position).2 - taken actions .north count ≤
        (walk start actions count).2 := by
  induction count with
  | zero =>
    change (tile start.body.position.position).1 ≤ _ + ((0 : ℕ) : ℤ) ∧
      _ - ((0 : ℕ) : ℤ) ≤ (tile start.body.position.position).1 ∧
      (tile start.body.position.position).2 ≤ _ + ((0 : ℕ) : ℤ) ∧
      _ - ((0 : ℕ) : ℤ) ≤ (tile start.body.position.position).2
    omega
  | succ count ih =>
    have grows : ∀ direction, taken actions direction count ≤
        taken actions direction (count + 1) := fun direction => Nat.le_add_right _ _
    have east := grows .east
    have west := grows .west
    have south := grows .south
    have north := grows .north
    cases later : physicalPath start actions (count + 1) with
    | none =>
      have same : walk start actions (count + 1) = walk start actions count := by
        simp only [walk, later]
      rw [same]
      omega
    | some after =>
      rw [walk_live start after actions (count + 1) later]
      cases before : physicalPath start actions count with
      | none =>
        have gone : physicalPath start actions (count + 1) = none :=
          congrArg (fun state => Option.bind state (physicalStep · (actions count))) before
        rw [gone] at later
        cases later
      | some middle =>
        have unfolded : physicalPath start actions (count + 1) =
            physicalStep middle (actions count) :=
          congrArg (fun state => Option.bind state (physicalStep · (actions count))) before
        rw [walk_live start middle actions count before] at ih
        rcases physicalStep_heading middle after (actions count) (unfolded.symm.trans later)
          with same | ⟨direction, heading, moved⟩
        · rw [same]
          omega
        · have hit : taken actions direction (count + 1) =
              taken actions direction count + 1 := by
            change _ + (if (Host.Action.fromIndex (actions count).val).direction =
              some direction then 1 else 0) = _
            rw [ite_eq_left heading]
          rw [moved]
          cases direction <;> simp only [Host.Direction.delta] <;> omega

theorem met_takes (mode : TaskFeatureMode) (live : Live config) (cap : ℕ)
    (actions : ℕ → Kernel.Act Grid.interface) (target : Host.Position)
    (met : (completion config mode cap).MetBy (member live target) actions) :
    (tile target).1 - 3 - (tile live.world.body.position.position).1 ≤
        taken actions .east cap ∧
      (tile live.world.body.position.position).1 - (tile target).1 - 3 ≤
        taken actions .west cap ∧
      (tile target).2 - 3 - (tile live.world.body.position.position).2 ≤
        taken actions .south cap ∧
      (tile live.world.body.position.position).2 - (tile target).2 - 3 ≤
        taken actions .north cap := by
  obtain ⟨time, -, high, final, reached, done⟩ := met
  have within : time ≤ cap := high
  have installed : final.world.goal = some (.find target) :=
    path_goal mode ⟨live.world.setGoal (.find target), live.carried⟩ final actions time reached
  have inside : InGoalBox target final.world.body.position.position :=
    (find_goal_iff final.world target installed).mp done
  have track :=
    path_physical mode ⟨live.world.setGoal (.find target), live.carried⟩ actions time
  change (Kernel.path (gridWorld config mode) (member live target) actions time).map
    (fun state => physical state.world) = _ at track
  rw [reached] at track
  have here : walk (physical live.world) actions time =
      tile final.world.body.position.position :=
    walk_live (physical live.world) (physical final.world) actions time track.symm
  have near := mem_box.mp (box_of_goalBox target _ inside)
  rw [← here] at near
  have reach : (walk (physical live.world) actions time).1 ≤
        (tile live.world.body.position.position).1 + taken actions .east time ∧
      (tile live.world.body.position.position).1 - taken actions .west time ≤
        (walk (physical live.world) actions time).1 ∧
      (walk (physical live.world) actions time).2 ≤
        (tile live.world.body.position.position).2 + taken actions .south time ∧
      (tile live.world.body.position.position).2 - taken actions .north time ≤
        (walk (physical live.world) actions time).2 :=
    walk_reach (physical live.world) actions time
  have east := taken_mono actions .east within
  have west := taken_mono actions .west within
  have south := taken_mono actions .south within
  have north := taken_mono actions .north within
  omega

end AcornVerif.CurrentForkedTarget
