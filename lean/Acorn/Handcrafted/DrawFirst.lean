/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Handcrafted.AgentEpisodes

/-!
# Selection that draws before it credits

`TemporalControl.select` interleaves draws with writes that read the reward of the
percept: the owed meta reward, a closing option's terminal credit, the on-policy credit
of the meta decision, the settlement and the start of a selected option, and the
executing option's own credit. This module states the same dispatch as two functions.

`TemporalControl.drawFirst` makes every draw of a step and takes no reward word. So no
draw reads a learner write of the reward of the percept: that is what its type states.
It does take the frame's achievement event (D8), on which an executing option ends
(`Skill.goal_ends`), and in the grid world the reward word is a function of that event
(`Host.StepResult.reward_completion`); the action is therefore not independent of the
event. It writes what a draw reads and what holds no learned value: the rate schedule, the
model caches, the assignment refresh of a free boundary, the trajectory link of an
option that a run interrupts, the diagnostic planning errors, occupancy and the action
generator. It returns the decision and an `Owed` record of the writes it did not make.

`TemporalControl.settle` makes those writes from the record and the reward, in the
order `select` makes them: the owed meta reward, then the advance of the deferred meta
clock of a served step; or the terminal credit, the meta credit and the settlement, the
start and the first credit of a selected option; or the credit of a continuing one. It
draws nothing.

The order of choice and update is that of J. B. Travnik, K. W. Mathewson, R. S. Sutton
and P. M. Pilarski, *Reactive Reinforcement Learning in Asynchronous Environments*,
Frontiers in Robotics and AI 5:79 (2018): Algorithm 1 (SARSA, section 2) and Algorithm 2
(Reactive SARSA, section 3) both choose the next action from the action values before
the update of that iteration, and Algorithm 2 also takes it before the update. The
source has no options, no assignment refresh and no planning; what this module does with
them is Acorn's own and is declared in PAR-20.

The dispatch can differ from `select` at two points, and at no other (PAR-20;
`AcornVerif.DrawFirst` states both dispatches as one form that reads its mode at these
two points):

- An option that starts draws its first action from its own frozen policy as the
  preceding step left it, after the assignment refresh (`Skill.frozenPolicy`). `select`
  draws it after the terminal credit, the settlement and the invocation start. The
  credit of that action is the ordinary one against the started policy's own values
  (`Skill.startTemporal`, `Skill.startTemporal_step`).
- Under the discounted criterion the terminal credit of an option that closes follows
  the assignment refresh, as it does under the differential criterion in `select`. The
  refresh has to precede the draws, and the credit reads the reward. The refresh
  retains the original owner of a slot it replaces (`Closing.oldOwner`), and that owner
  takes no credit.
-/
namespace Acorn.Handcrafted
open Features

variable {interface : Interface} {profile : FeatureProfile}
  {config : Features.Config} {criterion : Criterion} {dimension : Dimension}

/-- The first action of an invocation, drawn before the invocation start is written. -/
structure StartDraw (interface : Interface) where
  /-- The option the meta decision selected. -/
  slot : Fin Acorn.FeatureConstants.skillCount
  /-- The option's potential at the start frame. -/
  potential : Potential
  /-- The persistent draw from the option's frozen policy at the start frame. -/
  drawn : PersistentDecision interface.actions

/-- The writes a draw-first selection did not make. Each constructor names one dispatch
branch, with the draws that branch made. `TemporalControl.settle` makes the writes. -/
inductive Owed (interface : Interface) (profile : FeatureProfile) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) where
  /-- Nothing is owed: selection made every write, or the profile has no hierarchy. -/
  | settled
  /-- A served exploration step owes the meta reward and, when the run held no option,
  the advance of the deferred meta clock. -/
  | served (skip : Bool)
  /-- A continuing option owes the meta reward, its own credit for the drawn decision and
  the advance of the deferred meta clock. -/
  | continuing (slot : Fin Acorn.FeatureConstants.skillCount)
      (activation : OptionActivation (profile.mode != .frozen))
      (next : OptionContinuation interface.actions dimension activation)
      (drawn : PersistentDecision interface.actions)
  /-- A free dispatch owes the meta reward, the terminal credit of an option that closes
  with its terminal value, the credit of the drawn meta decision, and the settlement,
  the start and the first credit of an option that starts. -/
  | boundary
      (closing : Option (Closing interface.actions config criterion dimension interface.layout
        (EndingPayload (profile.mode != .frozen)) × Binary32))
      (decision : PolicyDecision metaCount) (start : Option (StartDraw interface))

/-- Selection preparation that reads no reward: advance the rate schedule, then observe
the models before dispatch under the current value function. -/
def TemporalControl.prepareDraw (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension) :
    TemporalControl interface profile config criterion dimension :=
  let state := { state with rate := state.rate.advance }
  if profile.usesHierarchy then
    { state with runtime := { state.runtime with references := { state.runtime.references with
      modelPredictions := state.runtime.lifecycle.consumers.skills.map
        (fun skill => models.predict skill.model state.valueFunction features) } } }
    else state

/-- The reward of a percept enters the owed meta span of a learning hierarchy. -/
def TemporalControl.oweReward (state : TemporalControl interface profile config criterion dimension)
    (reward : Binary32) : TemporalControl interface profile config criterion dimension :=
  if profile.usesHierarchy && profile.mode != .frozen then
    state.withGap (state.gap.accumulate reward criterion.rule.gamma) else state

/-- Selection preparation is the reward-free preparation followed by the owed reward,
for every state, frame and reward word. -/
theorem TemporalControl.prepareSelection_owe
    (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) :
    state.prepareSelection models features reward =
      (state.prepareDraw models features).oweReward reward := by
  unfold TemporalControl.prepareSelection TemporalControl.prepareDraw TemporalControl.oweReward
  dsimp only
  split <;> split <;> rfl

/-- A served exploration step without the advance of the deferred meta clock, which
follows the owed reward. The flag reports whether that advance is owed: the run held no
option. Every other write and the decision are those of `TemporalControl.serve`. -/
def TemporalControl.serveDraw (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) :
    Option (TemporalControl interface profile config criterion dimension × Bool ×
      TemporalDecision interface.actions) :=
  match state.runtime.references.phase with
  | .exploring committed => do
    let (action, next) ← committed.run.serve
    let interrupted := state.interrupt committed.origin
    let state := interrupted.1.withPhase (.exploring (.bare next))
    let state := if profile.usesHierarchy then state.withoutPlanning else state
    let values := state.runtime.lifecycle.consumers.control.predictAll features
    let metaValues := if profile.usesHierarchy then state.runtime.lifecycle.consumers.metaController.predictAll features
      else Vector.replicate _ .zero
    pure (state, !committed.origin.isSome, ⟨.explorationContinuation, action, values,
      servedProbabilities action, true, metaValues, none, none, interrupted.2⟩)
  | .idle | .option _ _ => none

/-- The event a closing option's terminal credit records. It reads the closing record
only. -/
def closingEvent (closing : Closing interface.actions config criterion dimension interface.layout
    (EndingPayload (profile.mode != .frozen))) : EndEvent :=
  ⟨closing.slot, closing.activation.activation.age, closing.activation.reason⟩

/-- The terminal value of an option that closes at a free dispatch: the value of the
drawn meta action under the differential criterion, and the supplied estimate under the
discounted one. -/
def terminalValue (criterion : Criterion) (decision : PolicyDecision metaCount)
    (estimate : Binary32) : Binary32 :=
  match criterion with
  | .differential => decision.continuation
  | .discounted => estimate

/-- A free dispatch that draws before it credits: refresh the assignments and the
models, run the supplied planning, draw the meta action, then draw the primitive action
or the first action of the selected option from that option's frozen policy. It writes
the refresh, occupancy and the generator, and it owes the terminal credit, the meta
credit and the start. The terminal value of a closing option is `terminalValue`. -/
def TemporalControl.drawBoundary (state : TemporalControl interface profile config criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen))))
    (estimate : Binary32) :
    Option (TemporalControl interface profile config criterion dimension ×
      Owed interface profile config criterion dimension × TemporalDecision interface.actions) :=
  let refreshed := state.refreshFree closing
  let drawn := (refreshed.1.planFree plan features).drawMeta features
  let decision := drawn.2
  let state := drawn.1
  let terminal := terminalValue criterion decision estimate
  let ended := refreshed.2.map closingEvent
  let owed := refreshed.2.map fun closing => (closing, terminal)
  match skillOfMeta decision.action with
  | none =>
    let result := state.choosePrimitive features decision.snapshot.values (some decision) ended
    some (result.1, .boundary owed decision none, result.2)
  | some slot => do
    let skill := state.runtime.lifecycle.consumers.skills.get slot
    let potential ← skill.interest.potential features declared
    let policy := skill.frozenPolicy features state.skillRate
    let first := policy.drawPersistent state.runtime.references.rng
    let state := state.withPhase
      (Occupancy.afterOption slot (OptionActivation.first _ potential) first.1.run)
    let state := { state with runtime := { state.runtime with references :=
      { state.runtime.references with rng := first.2 } } }
    pure (state, .boundary owed decision (some ⟨slot, potential, first.1⟩),
      ⟨.option slot, first.1.action, policy.values, first.1.probabilities, first.1.explored,
        decision.snapshot.values, some decision, some slot, ended⟩)

/-- Selection that draws before it credits, with the branch priority of
`TemporalControl.selectWithOperations`. It takes no reward. Refusal returns no
replacement state when a declared potential is not owned by the supplied source. -/
def TemporalControl.drawFirst (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (goal : Bool) :
    Option (TemporalControl interface profile config criterion dimension ×
      Owed interface profile config criterion dimension × TemporalDecision interface.actions) := do
  let state := state.prepareDraw models features
  if let some result := state.serveDraw features then
    return (result.1, .served result.2.1, result.2.2)
  if !profile.usesHierarchy then
    let result := (state.withPhase .idle).choosePrimitive features (Vector.replicate _ .zero) none none
    return (result.1, .settled, result.2)
  let phase := state.runtime.references.phase
  let state := state.withPhase .idle
  match phase with
  | .idle | .exploring _ => state.drawBoundary plan features declared none .zero
  | .option slot activation =>
    let skill := state.runtime.lifecycle.consumers.skills.get slot
    let potential ← skill.interest.potential features declared
    let metaPolicy := state.runtime.lifecycle.consumers.metaController.snapshot (count := metaCount) features state.metaRate
    let estimate := comparisonValue criterion metaPolicy
    match skill.decideOption activation features potential goal estimate state.skillRate with
    | .continuing next =>
      let drawn := next.policy.drawPersistent state.runtime.references.rng
      let state := state.withoutPlanning.withPhase
        (Occupancy.afterOption slot (activation.advance next) drawn.1.run)
      let state := { state with runtime := { state.runtime with references :=
        { state.runtime.references with rng := drawn.2 } } }
      pure (state, .continuing slot activation next drawn.1,
        ⟨.option slot, drawn.1.action, next.policy.values, drawn.1.probabilities,
          drawn.1.explored, metaPolicy.values, none, none, none⟩)
    | .ending reason =>
      state.drawBoundary plan features declared (some ⟨slot, ⟨activation, potential, reason⟩, none⟩)
        estimate

/-- The executing option's credit for a decision that is already drawn: the skill write
of `TemporalControl.stepOption`, with no draw and no occupancy write. The state is
consumed and the option taken out of the table before its learners are updated, and
`TemporalControl.creditOption_eq` proves the result equal to the listed composition;
storage reuse is a performance expectation, not a proved property (see
`detachedUpdate`). -/
def TemporalControl.creditOption (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen))
    (next : OptionContinuation interface.actions dimension activation)
    (drawn : PersistentDecision interface.actions) (reward : Binary32) :
    TemporalControl interface profile config criterion dimension :=
  let ⟨⟨⟨representation, ⟨control, metaController, skills, demons⟩⟩, references⟩,
    credit, creditMatches, average, rate, lifetime⟩ := state
  let credited := detachedUpdate skills slot fun skill =>
    (skill.creditTemporal models activation next drawn reward average.rate, ())
  ⟨⟨⟨representation, ⟨control, metaController, credited.1, demons⟩⟩, references⟩,
    credit, creditMatches, average, rate, lifetime⟩

/-- Taking the option out of the table before its credit preserves the composition:
the credited option is written back to its slot and nothing else changes. -/
theorem TemporalControl.creditOption_eq (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen))
    (next : OptionContinuation interface.actions dimension activation)
    (drawn : PersistentDecision interface.actions) (reward : Binary32) :
    state.creditOption models slot activation next drawn reward =
      state.withSkill slot ((state.runtime.lifecycle.consumers.skills.get slot).creditTemporal
        models activation next drawn reward state.average.rate) := by
  cases state with
  | mk runtime credit creditMatches average rate lifetime =>
    cases runtime with
    | mk lifecycle references =>
      cases lifecycle with
      | mk representation consumers =>
        cases consumers
        simp only [TemporalControl.creditOption, detachedUpdate_eq]
        rfl

/-- The settlement, the start and the first credit of a selected option whose first
action is already drawn: the skill writes of the option branch of
`TemporalControl.dispatchMeta`, with no draw and no occupancy write. The value function
and the rate source are read from the state it is given, which the meta credit has
already written, and the stopping estimate is supplied by the caller from the recorded
meta decision. The state is consumed and the option taken out of the table before it is
updated, and `TemporalControl.startOption_eq` proves the result equal to the listed
composition; storage reuse is a performance expectation, not a proved property (see
`detachedUpdate`). -/
def TemporalControl.startOption (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (start : StartDraw interface) (goal : Bool) (estimate reward : Binary32) :
    TemporalControl interface profile config criterion dimension :=
  let value := state.valueFunction
  let skillRate := state.skillRate
  let ⟨⟨⟨representation, ⟨control, metaController, skills, demons⟩⟩, references⟩,
    credit, creditMatches, average, rate, lifetime⟩ := state
  let started := detachedUpdate skills start.slot fun skill =>
    (skill.startTemporal models value features start.potential goal estimate skillRate reward
      average.rate (profile.mode != .frozen) start.drawn, ())
  ⟨⟨⟨representation, ⟨control, metaController, started.1, demons⟩⟩, references⟩,
    credit, creditMatches, average, rate, lifetime⟩

/-- Taking the selected option out of the table before its start preserves the
composition: the started option is written back to its slot and nothing else changes. -/
theorem TemporalControl.startOption_eq (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (start : StartDraw interface) (goal : Bool) (estimate reward : Binary32) :
    state.startOption models features start goal estimate reward =
      state.withSkill start.slot
        ((state.runtime.lifecycle.consumers.skills.get start.slot).startTemporal models
          state.valueFunction features start.potential goal estimate state.skillRate reward
          state.average.rate (profile.mode != .frozen) start.drawn) := by
  cases state with
  | mk runtime credit creditMatches average rate lifetime =>
    cases runtime with
    | mk lifecycle references =>
      cases lifecycle with
      | mk representation consumers =>
        cases consumers
        simp only [TemporalControl.startOption, detachedUpdate_eq]
        rfl

/-- The writes a draw-first selection owes, from the reward of the percept, in the
order `TemporalControl.selectWithOperations` makes them. It draws nothing and writes
neither occupancy nor the action generator. -/
def TemporalControl.settle (state : TemporalControl interface profile config criterion dimension)
    (owed : Owed interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) (goal : Bool) :
    TemporalControl interface profile config criterion dimension :=
  match owed with
  | .settled => state
  | .served skip =>
    if skip then (state.oweReward reward).skipMeta else state.oweReward reward
  | .continuing slot activation next drawn =>
    ((state.oweReward reward).creditOption models slot activation next drawn reward).skipMeta
  | .boundary closing decision start =>
    let state := state.oweReward reward
    let state := match closing with
      | none => state
      | some closing => (state.closeOption models features closing.1 reward closing.2).1
    let state := state.learnMeta features decision
    match start with
    | none => state
    | some start => state.startOption models features start goal
        (comparisonValue criterion decision.snapshot) reward

/-- The owed writes of a free dispatch that starts an option: the owed reward, the
terminal credit of an option that closes, the meta credit, and then
`TemporalControl.startOption` on the recorded first action, with the stopping estimate of
the recorded meta decision. -/
theorem TemporalControl.settle_started (state : TemporalControl interface profile config criterion dimension)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen)) × Binary32))
    (decision : PolicyDecision metaCount) (start : StartDraw interface)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) (goal : Bool) :
    state.settle (.boundary closing decision (some start)) models features reward goal =
      ((match closing with
          | none => state.oweReward reward
          | some closing => ((state.oweReward reward).closeOption models features closing.1
              reward closing.2).1).learnMeta features decision).startOption models features start
        goal (comparisonValue criterion decision.snapshot) reward := rfl

/-! ## Every declared source stays matched -/

/-- The reward-free preparation changes the rate schedule and the model caches only. -/
theorem TemporalControl.prepareDraw_aligned (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) : (state.prepareDraw models features).Aligned := by
  unfold TemporalControl.prepareDraw
  dsimp only
  split <;> exact aligned

/-- The owed reward writes the meta span only. -/
theorem TemporalControl.oweReward_aligned (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (reward : Binary32) : (state.oweReward reward).Aligned := by
  unfold TemporalControl.oweReward
  split <;> exact aligned

/-- A served step that draws first retains every admitted interest. -/
theorem TemporalControl.serveDraw_aligned (state next : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (features : SwiftTd.ActiveSet dimension) (skip : Bool)
    (decision : TemporalDecision interface.actions)
    (served : state.serveDraw features = some (next, skip, decision)) : next.Aligned := by
  unfold TemporalControl.serveDraw at served
  split at served
  · rename_i committed phase
    cases hs : committed.run.serve with
    | none => simp [hs, bind, Option.bind] at served
    | some pair =>
      simp only [hs, bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq] at served
      rw [← served.1]
      have base := state.interrupt_aligned aligned committed.origin
      split <;> exact base
  · contradiction
  · contradiction

/-- A free dispatch that draws first always has a potential for the option it selects,
and its writes retain every admitted interest. -/
theorem TemporalControl.drawBoundary_total (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (observation : Frame interface)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen))))
    (estimate : Binary32) :
    ∃ next owed decision, state.drawBoundary plan features observation.declared closing estimate =
        some (next, owed, decision) ∧ next.Aligned := by
  unfold TemporalControl.drawBoundary
  generalize hr : state.refreshFree closing = refreshed
  have refreshedAligned : refreshed.1.Aligned := by
    rw [← hr]
    exact state.refreshFree_aligned aligned closing
  dsimp only
  generalize hd : (refreshed.1.planFree plan features).drawMeta features = drawn
  have drawnAligned : drawn.1.Aligned := by rw [← hd]; exact refreshedAligned
  split
  · exact ⟨_, _, _, rfl, drawnAligned⟩
  · rename_i slot selected
    obtain ⟨potential, hp⟩ := Interest.aligned_potential
      (drawn.1.runtime.lifecycle.consumers.skills.get slot).interest (drawnAligned.1 slot)
      features observation
    simp only [hp, bind, Option.bind, pure]
    exact ⟨_, _, _, rfl, drawnAligned⟩

/-- Every aligned local state draws a real action before it credits, with the priority
of selection and a matching potential producer, and retains source alignment. -/
theorem TemporalControl.drawFirst_total (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (observation : Frame interface) (goal : Bool) :
    ∃ next owed decision, state.drawFirst models plan features observation.declared goal =
      some (next, owed, decision) ∧ next.Aligned := by
  unfold TemporalControl.drawFirst
  generalize hp : state.prepareDraw models features = prepared
  have preparedAligned : prepared.Aligned := by
    rw [← hp]
    exact state.prepareDraw_aligned aligned models features
  dsimp only
  cases hs : prepared.serveDraw features with
  | some result =>
    simp only
    exact ⟨_, _, _, rfl, prepared.serveDraw_aligned result.1 preparedAligned features result.2.1
      result.2.2 hs⟩
  | none =>
    simp only
    split
    · exact ⟨_, _, _, rfl, (prepared.withPhase .idle).primitive_aligned preparedAligned features
        (Vector.replicate _ .zero) none none⟩
    · split
      · exact (prepared.withPhase .idle).drawBoundary_total preparedAligned plan features
          observation none .zero
      · exact (prepared.withPhase .idle).drawBoundary_total preparedAligned plan features
          observation none .zero
      · rename_i slot activation phase
        obtain ⟨potential, hpotential⟩ := Interest.aligned_potential
          ((prepared.withPhase .idle).runtime.lifecycle.consumers.skills.get slot).interest
          (preparedAligned.1 slot) features observation
        simp only [hpotential, bind, Option.bind]
        split
        · exact ⟨_, _, _, rfl, preparedAligned⟩
        · exact (prepared.withPhase .idle).drawBoundary_total preparedAligned plan features
            observation _ _

/-- The credit of a drawn decision keeps the source of the current table owner. -/
theorem TemporalControl.creditOption_aligned (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (models : OptionModelOps criterion dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen))
    (next : OptionContinuation interface.actions dimension activation)
    (drawn : PersistentDecision interface.actions) (reward : Binary32) :
    (state.creditOption models slot activation next drawn reward).Aligned := by
  rw [TemporalControl.creditOption_eq]
  apply state.withSkill_aligned aligned slot
  rw [Skill.creditTemporal_interest]
  rfl

/-- The start of a selected option keeps the source of the current table owner. -/
theorem TemporalControl.startOption_aligned (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (start : StartDraw interface) (goal : Bool)
    (estimate reward : Binary32) :
    (state.startOption models features start goal estimate reward).Aligned := by
  rw [TemporalControl.startOption_eq]
  apply state.withSkill_aligned aligned start.slot
  rw [Skill.startTemporal_interest]
  rfl

/-- The owed writes keep every declared option source matched, for every record. -/
theorem TemporalControl.settle_aligned (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (owed : Owed interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) (goal : Bool) : (state.settle owed models features reward goal).Aligned := by
  have owedAligned := state.oweReward_aligned aligned reward
  cases owed with
  | settled => exact aligned
  | served skip =>
    cases skip
    · exact owedAligned
    · exact TemporalControl.skipMeta_aligned _ owedAligned
  | continuing slot activation next drawn =>
    exact TemporalControl.skipMeta_aligned _
      ((state.oweReward reward).creditOption_aligned owedAligned models slot activation next drawn
        reward)
  | boundary closing decision start =>
    have closedAligned : (match closing with
        | none => state.oweReward reward
        | some closing => ((state.oweReward reward).closeOption models features closing.1 reward
            closing.2).1).Aligned := by
      cases closing with
      | none => exact owedAligned
      | some closing =>
        exact (state.oweReward reward).closeOption_aligned owedAligned models features closing.1
          reward closing.2
    have learnedAligned := TemporalControl.learnMeta_aligned _ closedAligned features decision
    cases start with
    | none => exact learnedAligned
    | some start =>
      exact TemporalControl.startOption_aligned _ learnedAligned models features start goal _ reward

/-! ## Episode ownership -/

/-- The reward-free preparation updates neither the active invocation nor any episode
observation. -/
theorem TemporalControl.prepareDraw_episodes (state : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension) :
    (state.prepareDraw models features).lifetime = state.lifetime ∧
      (state.prepareDraw models features).activeSlot = state.activeSlot := by
  unfold TemporalControl.prepareDraw
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

/-- A served step that draws first starts nothing, leaves no option executing and ends
exactly the option the run held. -/
theorem TemporalControl.serveDraw_episodes (state next : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (skip : Bool)
    (observed : TemporalDecision interface.actions)
    (executed : state.serveDraw features = some (next, skip, observed)) :
    next.lifetime = state.lifetime ∧ next.activeSlot = none ∧
      observed.started = none ∧ observed.ended.map (·.slot) = state.activeSlot := by
  unfold TemporalControl.serveDraw at executed
  cases phase : state.runtime.references.phase with
  | idle => simp [phase] at executed
  | option slot activation => simp [phase] at executed
  | exploring committed =>
    simp only [phase] at executed
    cases served : committed.run.serve with
    | none => simp [served] at executed
    | some result =>
      simp only [served, bind, Option.bind, pure, Option.some.injEq] at executed
      cases executed
      have interrupted := state.interrupt_frame committed.origin
      have active : state.activeSlot = committed.origin.map (·.1) := by
        simp [TemporalControl.activeSlot, phase, Occupancy.executing]
      refine ⟨?_, ?_, rfl, ?_⟩
      · split <;> exact interrupted.1
      · split <;> rfl
      · rw [active]
        exact interrupted.2.2

/-- A served step that draws first draws no meta decision. -/
theorem TemporalControl.serveDraw_undrawn (state next : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (skip : Bool)
    (decision : TemporalDecision interface.actions)
    (served : state.serveDraw features = some (next, skip, decision)) :
    decision.metaDecision = none ∧ decision.started = none := by
  unfold TemporalControl.serveDraw at served
  split at served
  · rename_i committed phase
    cases hs : committed.run.serve with
    | none => simp [hs, bind, Option.bind] at served
    | some pair =>
      simp only [hs, bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq] at served
      obtain ⟨_, _, rfl⟩ := served
      exact ⟨rfl, rfl⟩
  · contradiction
  · contradiction

/-- A free dispatch that draws first has a new active slot exactly when its decision
records a start, and its decision ends exactly the supplied closing activation. -/
theorem TemporalControl.drawBoundary_episodes (state next : TemporalControl interface profile config criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen))))
    (estimate : Binary32) (owed : Owed interface profile config criterion dimension)
    (observed : TemporalDecision interface.actions)
    (executed : state.drawBoundary plan features declared closing estimate =
      some (next, owed, observed)) :
    next.lifetime = state.lifetime ∧ next.activeSlot = observed.started ∧
      observed.ended.map (·.slot) = closing.map (·.slot) ∧
      observed.metaDecision.isSome = true := by
  unfold TemporalControl.drawBoundary at executed
  generalize hr : state.refreshFree closing = refreshed at executed
  have refreshedLifetime : refreshed.1.lifetime = state.lifetime := by rw [← hr]; rfl
  have endedSlot : (refreshed.2.map closingEvent).map (·.slot) = closing.map (·.slot) := by
    rw [← hr, ← state.refresh_episode_slot closing, Option.map_map]
    rfl
  dsimp only at executed
  generalize hd : (refreshed.1.planFree plan features).drawMeta features = drawn at executed
  have drawnLifetime : drawn.1.lifetime = state.lifetime := by rw [← hd]; exact refreshedLifetime
  split at executed
  · cases executed
    have proof := drawn.1.primitive_episodes features drawn.2.snapshot.values (some drawn.2)
      (refreshed.2.map closingEvent)
    exact ⟨proof.1.trans drawnLifetime, proof.2.1.trans proof.2.2.1.symm,
      (congrArg (Option.map (·.slot)) proof.2.2.2).trans endedSlot, rfl⟩
  · rename_i slot selected
    cases potential : (drawn.1.runtime.lifecycle.consumers.skills.get slot).interest.potential
        features declared with
    | none => simp [potential, bind, Option.bind] at executed
    | some value =>
      simp only [potential, bind, Option.bind, pure, Option.some.injEq] at executed
      cases executed
      exact ⟨drawnLifetime, Occupancy.afterOption_executing _ _ _, endedSlot, rfl⟩

/-- Selection that draws first exposes the complete start and end transition of each
activation, as `TemporalControl.select_episodes` does for selection. -/
theorem TemporalControl.drawFirst_episodes (state next : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (goal : Bool)
    (owed : Owed interface profile config criterion dimension)
    (observed : TemporalDecision interface.actions)
    (primitive : profile.usesHierarchy = false → state.activeSlot = none)
    (executed : state.drawFirst models plan features declared goal = some (next, owed, observed)) :
    next.lifetime = state.lifetime ∧
      EpisodeTrace state.activeSlot (observed.ended.map (·.slot)) observed.started next.activeSlot := by
  unfold TemporalControl.drawFirst at executed
  generalize hp : state.prepareDraw models features = prepared at executed
  have preparedLifetime : prepared.lifetime = state.lifetime := by
    rw [← hp]; exact (state.prepareDraw_episodes models features).1
  have preparedActive : prepared.activeSlot = state.activeSlot := by
    rw [← hp]; exact (state.prepareDraw_episodes models features).2
  dsimp only at executed
  cases served : prepared.serveDraw features with
  | some result =>
    simp only [served] at executed
    cases executed
    have proof := prepared.serveDraw_episodes result.1 features result.2.1 result.2.2 served
    refine ⟨proof.1.trans preparedLifetime, ?_⟩
    rw [proof.2.1, proof.2.2.1, proof.2.2.2, preparedActive]
    cases state.activeSlot with
    | none => exact .continuing none
    | some old => exact .ending old none
  | none =>
    simp only [served] at executed
    split at executed
    · rename_i noHierarchy
      have noHierarchy' : profile.usesHierarchy = false := by simpa using noHierarchy
      cases executed
      have proof := (prepared.withPhase .idle).primitive_episodes features (Vector.replicate _ .zero) none none
      refine ⟨proof.1.trans preparedLifetime, ?_⟩
      rw [primitive noHierarchy', proof.2.1, proof.2.2.1, proof.2.2.2]
      exact .free none
    · cases phase : prepared.runtime.references.phase with
      | idle =>
        simp only [phase] at executed
        have proof := (prepared.withPhase .idle).drawBoundary_episodes next plan features declared
          none .zero owed observed executed
        refine ⟨proof.1.trans preparedLifetime, ?_⟩
        have empty : state.activeSlot = none := by
          rw [← preparedActive]; simp [TemporalControl.activeSlot, phase, Occupancy.executing]
        rw [empty, proof.2.1, proof.2.2.1]
        exact .free observed.started
      | exploring committed =>
        simp only [phase] at executed
        have proof := (prepared.withPhase .idle).drawBoundary_episodes next plan features declared
          none .zero owed observed executed
        refine ⟨proof.1.trans preparedLifetime, ?_⟩
        have unserved : prepared.serve features = none := by
          cases spent : committed.run.serve with
          | none => simp [TemporalControl.serve, phase, spent]
          | some result => simp [TemporalControl.serveDraw, phase, spent] at served
        have empty : state.activeSlot = none := by
          rw [← preparedActive]; exact prepared.unserved_free features committed phase unserved
        rw [empty, proof.2.1, proof.2.2.1]
        exact .free observed.started
      | option slot activation =>
        simp only [phase] at executed
        have active : state.activeSlot = some slot := by
          rw [← preparedActive]; simp [TemporalControl.activeSlot, phase, Occupancy.executing]
        cases potential : ((prepared.withPhase .idle).runtime.lifecycle.consumers.skills.get
            slot).interest.potential features declared with
        | none => simp [potential] at executed
        | some value =>
          simp only [potential, bind, Option.bind] at executed
          split at executed
          · simp only [pure, Option.some.injEq] at executed
            cases executed
            refine ⟨preparedLifetime, ?_⟩
            rw [active]
            change EpisodeTrace (some slot) none none
              (Occupancy.executing (Occupancy.afterOption slot _ _))
            rw [Occupancy.afterOption_executing]
            exact .continuing (some slot)
          · have proof := (prepared.withPhase .idle).drawBoundary_episodes next plan features
              declared _ _ owed observed executed
            refine ⟨proof.1.trans preparedLifetime, ?_⟩
            rw [active, proof.2.1, proof.2.2.1]
            exact .ending slot observed.started

/-- Selection that draws first cannot leave an option active in a primitive-only
profile. -/
theorem TemporalControl.drawFirst_primitive (state next : TemporalControl interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (goal : Bool)
    (owed : Owed interface profile config criterion dimension)
    (observed : TemporalDecision interface.actions) (primitive : profile.usesHierarchy = false)
    (executed : state.drawFirst models plan features declared goal = some (next, owed, observed)) :
    next.activeSlot = none := by
  unfold TemporalControl.drawFirst at executed
  generalize hp : state.prepareDraw models features = prepared at executed
  dsimp only at executed
  cases served : prepared.serveDraw features with
  | some result =>
    simp only [served] at executed
    cases executed
    exact (prepared.serveDraw_episodes result.1 features result.2.1 result.2.2 served).2.1
  | none =>
    simp only [served, primitive, Bool.not_false, ↓reduceIte] at executed
    cases executed
    exact ((prepared.withPhase .idle).primitive_episodes features (Vector.replicate _ .zero) none
      none).2.1

/-- One temporal state holds the lifetime record, occupancy and the action generator of
another: no operation between the two recorded an episode, moved an activation or drew. -/
abbrev TemporalControl.Framed
    (next origin : TemporalControl interface profile config criterion dimension) : Prop :=
  next.lifetime = origin.lifetime ∧
    next.runtime.references.phase = origin.runtime.references.phase ∧
    next.runtime.references.rng = origin.runtime.references.rng

/-- The owed reward writes the meta span only. -/
theorem TemporalControl.oweReward_framed
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Framed origin) (reward : Binary32) : (state.oweReward reward).Framed origin := by
  unfold TemporalControl.oweReward
  split <;> exact kept

/-- A skipped meta decision writes the meta span only. -/
theorem TemporalControl.skipMeta_framed
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Framed origin) : state.skipMeta.Framed origin := by
  unfold TemporalControl.skipMeta
  split <;> exact kept

/-- The credit of a drawn decision writes the option table only. -/
theorem TemporalControl.creditOption_framed
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Framed origin) (models : OptionModelOps criterion dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen))
    (next : OptionContinuation interface.actions dimension activation)
    (drawn : PersistentDecision interface.actions) (reward : Binary32) :
    (state.creditOption models slot activation next drawn reward).Framed origin := by
  rw [TemporalControl.creditOption_eq]
  exact kept

/-- The start of a selected option writes the option table only. -/
theorem TemporalControl.startOption_framed
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Framed origin) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (start : StartDraw interface) (goal : Bool)
    (estimate reward : Binary32) :
    (state.startOption models features start goal estimate reward).Framed origin := by
  rw [TemporalControl.startOption_eq]
  exact kept

/-- Terminal credit writes the option table only. -/
theorem TemporalControl.closeOption_framed
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Framed origin) (models : OptionModelOps criterion dimension)
    (features : SwiftTd.ActiveSet dimension)
    (closing : Closing interface.actions config criterion dimension interface.layout (EndingPayload (profile.mode != .frozen)))
    (reward terminal : Binary32) :
    (state.closeOption models features closing reward terminal).1.Framed origin := by
  rw [TemporalControl.closeOption_eq]
  dsimp only
  cases closing.oldOwner with
  | none => exact kept
  | some owner => exact kept

/-- Meta credit writes the meta-controller and the meta span only. -/
theorem TemporalControl.learnMeta_framed
    (state origin : TemporalControl interface profile config criterion dimension)
    (kept : state.Framed origin) (features : SwiftTd.ActiveSet dimension)
    (decision : PolicyDecision metaCount) : (state.learnMeta features decision).Framed origin := by
  rw [TemporalControl.learnMeta_eq]
  split <;> exact kept

/-- **The owed writes record no episode, move no activation and draw nothing.** For
every state, record, frame and reward word, the settled state holds the lifetime record,
occupancy and the action generator it was given. -/
theorem TemporalControl.settle_framed (state : TemporalControl interface profile config criterion dimension)
    (owed : Owed interface profile config criterion dimension)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (reward : Binary32) (goal : Bool) :
    (state.settle owed models features reward goal).Framed state := by
  have owedKept := state.oweReward_framed state ⟨rfl, rfl, rfl⟩ reward
  cases owed with
  | settled => exact ⟨rfl, rfl, rfl⟩
  | served skip =>
    cases skip
    · exact owedKept
    · exact TemporalControl.skipMeta_framed _ state owedKept
  | continuing slot activation next drawn =>
    exact TemporalControl.skipMeta_framed _ state
      ((state.oweReward reward).creditOption_framed state owedKept models slot activation next
        drawn reward)
  | boundary closing decision start =>
    have closedKept : (match closing with
        | none => state.oweReward reward
        | some closing => ((state.oweReward reward).closeOption models features closing.1 reward
            closing.2).1).Framed state := by
      cases closing with
      | none => exact owedKept
      | some closing =>
        exact (state.oweReward reward).closeOption_framed state owedKept models features
          closing.1 reward closing.2
    have learnedKept := TemporalControl.learnMeta_framed _ state closedKept features decision
    cases start with
    | none => exact learnedKept
    | some start =>
      exact TemporalControl.startOption_framed _ state learnedKept models features start goal _
        reward

end Acorn.Handcrafted
