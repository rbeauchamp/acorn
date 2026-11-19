/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentExplorer
import AcornVerif.CurrentFirstCredit

/-!
# The declared step, and what it is for an agent to step by it

`StepsByRule` says of the executed agent's type that its step is the declared step in everything
but the representation: the readout, the draw and every learning update are the declared ones,
and only which units the feature bank holds is left to the step.

**The declared step.** `declaredStep` is `Acorn.Handcrafted.TemporalControl.alignedStep` applied
to the agent's clock-advanced control at the active set of the percept's frame, with the
percept's frame, reward word and achievement flag. It selects the action by one decision of
primitive control over the policy the primitive controller freezes from its weights, then
learns: the primitive controller by executed-action Sarsa through SwiftTD at that active set,
that action and that reward word, then every prediction demon, then the gain
(`Acorn.Handcrafted.PredictionControl.advanceWith`).

**Forgetting units.** `forgetUnits` retires every learner's weight on the slot of each listed
unit and releases every slot that holds one. It is what the executing tester does to the
learners for the units it replaces.

**The clause.** For every state and percept there is a list of units such that:

- the step's decision is the declared step's;
- the learners the step leaves are the declared step's with the listed units forgotten;
- the temporal references it leaves are the declared step's, with the listed units' slots
  erased from the stored recent frames;
- the credit, the gain and the rate it leaves are the declared step's;
- every unit outside the list has the projection it had.

What the clause does not constrain is the representation (the bank's units, their origins,
utilities and the tester's clock and credit) and the lifetime observations. The encoder reads
the bank, so a step may decide which units exist. A unit whose projection changes is in the
list, so no weight learned on a unit's slot outlives the unit.

**The executing step meets it** (`act_steps`), for every interface, profile, configuration,
criterion, dimension and planning selection: its list is the list of units its tester replaces.

A degenerate instance, read for what it says: with the empty list the clause says that the step
is the declared step outside the representation and that no unit's projection changed. The
executing step of a frozen profile is that instance.
-/

namespace AcornVerif.CurrentDeclaredStep
open Acorn Acorn.Features Acorn.Handcrafted

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

/-! ## The declared step and forgetting -/

/-- **The declared step.** The executing library's local transition on the agent's
clock-advanced control, at the active set of the percept's frame. -/
def declaredStep (agent : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    TemporalControl interface profile config criterion dimension ×
      TemporalDecision interface.actions :=
  (agent.advanceClock.control.alignedStep agent.advanceClock.aligned planning
    (agent.advanceClock.frame percept.frame).active percept.frame percept.reward
    percept.frame.achieved).1

/-- Retire every learner's weight on the slot of each listed unit, in order. -/
def retireUnits {actions : Word.Count} {discounts : List Discount}
    (ensemble : Ensemble actions config criterion dimension discounts)
    (units : List (Fin config.units.count)) :
    Ensemble actions config criterion dimension discounts :=
  units.foldl (fun held unit => held.retire (unitFeature dimension config unit)) ensemble

/-- **Forgetting units.** Retire every learner's weight on the slot of each listed unit, then
release every slot that holds one of them. -/
def forgetUnits {actions : Word.Count} {discounts : List Discount}
    (ensemble : Ensemble actions config criterion dimension discounts)
    (units : List (Fin config.units.count)) :
    Ensemble actions config criterion dimension discounts :=
  (retireUnits ensemble units).releaseAll units

/-- **The agent steps by the declared rule.** For every state and percept there is a list of
units such that the step's decision is the declared step's; its learners are the declared
step's with those units forgotten; its temporal references are the declared step's, with those
units' slots erased from the stored recent frames; its credit, gain and rate are the declared
step's; and every unit outside the list has the projection it had. -/
def StepsByRule (interface : Interface) (profile : FeatureProfile) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) (planning : PlanningSelection) : Prop :=
  ∀ (agent : Agent interface profile config criterion dimension planning)
    (percept : Percept interface),
    ∃ units : List (Fin config.units.count),
      (agent.act percept).2 = (declaredStep agent percept).2 ∧
      (agent.act percept).1.control.runtime.lifecycle.consumers =
        forgetUnits (declaredStep agent percept).1.runtime.lifecycle.consumers units ∧
      (agent.act percept).1.control.runtime.references =
        { (declaredStep agent percept).1.runtime.references with
          recent := (declaredStep agent percept).1.runtime.references.recent.retireAll units } ∧
      (agent.act percept).1.control.credit = (declaredStep agent percept).1.credit ∧
      (agent.act percept).1.control.average = (declaredStep agent percept).1.average ∧
      (agent.act percept).1.control.rate = (declaredStep agent percept).1.rate ∧
      ∀ unit : Fin config.units.count, unit ∉ units →
        (agent.act percept).1.control.runtime.lifecycle.representation.bank.projections.get
            unit =
          agent.control.runtime.lifecycle.representation.bank.projections.get unit

/-! ## The executing tester forgets exactly the units it replaces -/

section Tester

variable {shape : PatchShape} {actions : Word.Count} {discounts : List Discount}

/-- The due replacements retire the learners' weights on the replaced units' slots, in order,
and write the learners in no other way. -/
theorem replaceDue_consumers (free : Bool) :
    ∀ (due : ℕ) (state : Lifecycle shape actions config criterion dimension discounts),
      (Lifecycle.replaceDue free due state).1.consumers =
        retireUnits state.consumers (Lifecycle.replaceDue free due state).2
  | 0, _ => rfl
  | due + 1, state => by
    cases selected : state.candidate free with
    | none =>
      simp only [Lifecycle.replaceDue, selected, retireUnits, List.foldl_nil]
    | some unit =>
      have rest := replaceDue_consumers free due (state.replace unit)
      have retired : (state.replace unit).consumers =
          state.consumers.retire (unitFeature dimension config unit) := rfl
      simp only [Lifecycle.replaceDue, selected]
      rw [rest, retired]
      simp only [retireUnits, List.foldl_cons]

/-- The due replacements leave the projection of every unit they do not replace. -/
theorem replaceDue_projection (free : Bool) :
    ∀ (due : ℕ) (state : Lifecycle shape actions config criterion dimension discounts)
      (unit : Fin config.units.count), unit ∉ (Lifecycle.replaceDue free due state).2 →
        (Lifecycle.replaceDue free due state).1.representation.bank.projections.get unit =
          state.representation.bank.projections.get unit
  | 0, _, _, _ => rfl
  | due + 1, state, unit, absent => by
    cases selected : state.candidate free with
    | none =>
      simp only [Lifecycle.replaceDue, selected]
    | some chosen =>
      simp only [Lifecycle.replaceDue, selected, List.mem_cons, not_or] at absent ⊢
      have different : unit ≠ chosen := absent.1
      refine (replaceDue_projection free due (state.replace chosen) unit absent.2).trans ?_
      have kept := state.representation.bank.replace_other chosen unit different
      simp only [Vector.get, Fin.val_cast, Vector.getElem_toArray] at kept ⊢
      exact kept

/-- The tester's step retires the learners' weights on the replaced units' slots, in order, and
writes the learners in no other way. -/
theorem test_consumers (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) (active : Vector Bool config.units.count) :
    (state.test free active).1.consumers = retireUnits state.consumers (state.test free active).2 :=
  replaceDue_consumers free _ _

/-- The tester's step leaves the projection of every unit it does not replace. -/
theorem test_projection (state : Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) (active : Vector Bool config.units.count) (unit : Fin config.units.count)
    (absent : unit ∉ (state.test free active).2) :
    (state.test free active).1.representation.bank.projections.get unit =
      state.representation.bank.projections.get unit :=
  replaceDue_projection free _ _ unit absent

end Tester

/-! ## The declared step keeps the representation -/

/-- What the declared step returns is a selection followed by the learning part on it. -/
theorem declaredStep_parts (agent : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    ∃ selected : TemporalControl interface profile config criterion dimension ×
        TemporalDecision interface.actions,
      agent.advanceClock.control.select planning (agent.advanceClock.frame percept.frame).active
          percept.frame.declared percept.reward percept.frame.achieved = some selected ∧
        declaredStep agent percept =
          (selected.1.learn (agent.advanceClock.frame percept.frame).active percept.frame
            percept.reward percept.frame.achieved selected.2, selected.2) := by
  have executed : agent.advanceClock.control.step planning
      (agent.advanceClock.frame percept.frame).active percept.frame percept.reward
      percept.frame.achieved = some (declaredStep agent percept) :=
    (agent.advanceClock.control.alignedStep agent.advanceClock.aligned planning
      (agent.advanceClock.frame percept.frame).active percept.frame percept.reward
      percept.frame.achieved).2.1
  rw [TemporalControl.step_parts] at executed
  cases chosen : agent.advanceClock.control.select planning
      (agent.advanceClock.frame percept.frame).active percept.frame.declared percept.reward
      percept.frame.achieved with
  | none =>
    rw [chosen] at executed
    exact absurd executed (by simp)
  | some selected =>
    rw [chosen] at executed
    exact ⟨selected, rfl, (Option.some.inj executed).symm⟩

/-- **The declared step of a profile with no hierarchy keeps the representation.** It replaces
no unit and moves no tester state; only the clock the step advanced before it differs from the
agent's. -/
theorem declaredStep_representation
    (agent : Agent interface profile config criterion dimension planning)
    (primitive : profile.usesHierarchy = false) (percept : Percept interface) :
    (declaredStep agent percept).1.runtime.lifecycle.representation =
      agent.advanceClock.control.runtime.lifecycle.representation := by
  obtain ⟨selected, chosen, parts⟩ := declaredStep_parts agent percept
  rw [parts]
  unfold TemporalControl.select at chosen
  exact (CurrentFirstCredit.learn_representation selected.1 _ percept.frame percept.reward
    percept.frame.achieved selected.2).trans
    (CurrentFirstCredit.select_representation agent.advanceClock.control selected.1 primitive _ _
      _ _ _ _ selected.2 chosen)

/-! ## The executing step meets the clause -/

/-- **The executing step steps by the declared rule**, for every profile with no hierarchy. Its
list of forgotten units is the list its tester replaces, and is empty for a frozen profile. -/
theorem act_steps (primitive : profile.usesHierarchy = false) :
    StepsByRule interface profile config criterion dimension planning := by
  intro agent percept
  have kept := declaredStep_representation agent primitive percept
  have stepped : agent.act percept =
      (Agent.retire ⟨(declaredStep agent percept).1,
          (agent.advanceClock.control.alignedStep agent.advanceClock.aligned planning
            (agent.advanceClock.frame percept.frame).active percept.frame percept.reward
            percept.frame.achieved).2.2,
          agent.advanceClock.control.step_episodes _ agent.advanceClock.episodes planning
            (agent.advanceClock.frame percept.frame).active percept.frame percept.reward
            percept.frame.achieved _
            (agent.advanceClock.control.alignedStep agent.advanceClock.aligned planning
              (agent.advanceClock.frame percept.frame).active percept.frame percept.reward
              percept.frame.achieved).2.1⟩
        (agent.advanceClock.frame percept.frame).units,
      (declaredStep agent percept).2) := rfl
  rw [stepped]
  unfold Agent.retire
  split
  · refine ⟨[], rfl, rfl, rfl, rfl, rfl, rfl, fun unit _ => ?_⟩
    have bank := congrArg (fun held : Representation interface.symbols config =>
      held.bank.projections.get unit) kept
    exact bank
  · refine ⟨((declaredStep agent percept).1.runtime.lifecycle.test
        (declaredStep agent percept).1.runtime.references.phase.free
        (agent.advanceClock.frame percept.frame).units).2, rfl, ?_, rfl, rfl, rfl, rfl,
      fun unit absent => ?_⟩
    · exact congrArg (fun held => Ensemble.releaseAll held _)
        (test_consumers (declaredStep agent percept).1.runtime.lifecycle _ _)
    · have bank := congrArg (fun held : Representation interface.symbols config =>
        held.bank.projections.get unit) kept
      exact (test_projection (declaredStep agent percept).1.runtime.lifecycle _ _ unit
        absent).trans bank

/-! ## What follows for every agent that steps by the declared rule -/

open AcornVerif.CurrentExplorer AcornVerif.CurrentPreReward AcornVerif.CurrentGridWorld

/-- The explorer's state after a step by the rule is the declared step's: forgetting units
moves neither the committed run nor the generator. -/
theorem StepsByRule.explorer
    (rule : StepsByRule interface profile config criterion dimension planning)
    (agent : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    explorerOf (agent.act percept).1.control = explorerOf (declaredStep agent percept).1 := by
  obtain ⟨units, -, -, references, -⟩ := rule agent percept
  unfold explorerOf
  rw [references]

/-- **Every agent that steps by the rule acts by the declared readout.** For a profile with no
hierarchy under the declared rate, on every percept and from every state: the step's action is
the action of one decision of primitive control over the policy the primitive controller freezes
from its weights at the active set of the percept's frame, and the agent it returns holds that
decision's run and generator. -/
theorem StepsByRule.draws
    (rule : StepsByRule interface profile config criterion dimension planning)
    (primitive : profile.usesHierarchy = false) (declared : profile.rate = .declared)
    (agent : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    (agent.act percept).2.action = ((explorerOf agent.control).stepOver
        (agent.control.runtime.lifecycle.consumers.control.snapshot
          (agent.advanceClock.frame percept.frame).active declaredRate)).1 ∧
      explorerOf (agent.act percept).1.control = ((explorerOf agent.control).stepOver
        (agent.control.runtime.lifecycle.consumers.control.snapshot
          (agent.advanceClock.frame percept.frame).active declaredRate)).2 := by
  obtain ⟨selected, chosen, parts⟩ := declaredStep_parts agent percept
  unfold TemporalControl.select at chosen
  have drawn := select_draws agent.advanceClock.control selected.1 primitive declared _ _ _ _ _
    _ selected.2 chosen
  have kept : explorerOf (declaredStep agent percept).1 = explorerOf selected.1 := by
    rw [parts]
    change Explorer.mk _ _ = Explorer.mk _ _
    rw [learn_phase, TemporalControl.learn_rng]
  obtain ⟨units, decision, -⟩ := rule agent percept
  refine ⟨?_, ((rule.explorer agent percept).trans kept).trans drawn.2⟩
  rw [decision, parts]
  exact drawn.1

/-- Retiring listed units' slots keeps an ensemble at rest. -/
theorem retireUnits_quiet {actions : Word.Count} {rest : List Discount} {learned : Bool}
    (units : List (Fin config.units.count)) :
    ∀ ensemble : Ensemble actions config criterion dimension (.g99 :: rest),
      EnsembleQuiet learned ensemble → EnsembleQuiet learned (retireUnits ensemble units) := by
  induction units with
  | nil => intro ensemble quiet; exact quiet
  | cons unit others ih =>
    intro ensemble quiet
    exact ih _ (quiet.retire (unitFeature dimension config unit))

/-- **A step by the rule keeps an agent at rest on a reward-free percept.** If the agent's
learners are at rest and the percept's reward word is a zero word, the learners the step leaves
are at rest: the declared step keeps them so, and forgetting units keeps them so. -/
theorem StepsByRule.quiet
    (rule : StepsByRule interface profile config criterion dimension planning)
    (agent : Agent interface profile config criterion dimension planning)
    (rest : Quiet agent.control) (percept : Percept interface)
    (unpaid : percept.reward.isZero = true) : Quiet (agent.act percept).1.control := by
  obtain ⟨selected, chosen, parts⟩ := declaredStep_parts agent percept
  unfold TemporalControl.select at chosen
  have chose := rest.advanceClock.selectWithOperations modelOperations_quiet planning
    (agent.advanceClock.frame percept.frame).active percept.frame.declared
    (Inert32.ofZero unpaid) percept.frame.achieved chosen
  have learned : Quiet (declaredStep agent percept).1 := by
    rw [parts]
    exact chose.1.learn _ percept.frame (Inert32.ofZero unpaid) percept.frame.achieved chose.2
  obtain ⟨units, -, consumers, references, credit, average, -, -⟩ := rule agent percept
  have forgotten := EnsembleQuiet.releaseAll units _
    (retireUnits_quiet units _ learned.ensemble)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [consumers]; exact forgotten.control
  · rw [consumers]; exact forgotten.metaController
  · rw [consumers]; exact forgotten.skills
  · rw [consumers]; exact forgotten.demon
  · rw [references]; exact learned.gap
  · rw [credit]; exact learned.credit
  · rw [average]; exact learned.rate
  · rw [references]; exact learned.phase

/-- **A step by the rule from rest takes the explorer's action.** For a profile with no
hierarchy under the declared rate, from a state whose primitive controller is at rest, the
step's action is the explorer's on every percept, whatever its reward word, and the agent it
returns holds the explorer's next state. -/
theorem StepsByRule.explores
    (rule : StepsByRule interface profile config criterion dimension planning)
    (primitive : profile.usesHierarchy = false) (declared : profile.rate = .declared)
    (agent : Agent interface profile config criterion dimension planning)
    (still : Still agent.control.runtime.lifecycle.consumers.control)
    (percept : Percept interface) :
    (agent.act percept).2.action = (explorerOf agent.control).step.1 ∧
      explorerOf (agent.act percept).1.control = (explorerOf agent.control).step.2 := by
  have drawn := rule.draws primitive declared agent percept
  rw [(explorerOf agent.control).stepOver_congr
    (agent.control.runtime.lifecycle.consumers.control.snapshot
      (agent.advanceClock.frame percept.frame).active declaredRate)
    (restingPolicy interface.actions) rfl
    (settled_candidates _ (still.snapshot _ declaredRate))] at drawn
  exact drawn

/-- **Until its first reward, an agent that steps by the rule takes the explorer's actions.**
For a profile with no hierarchy under the declared rate, from an agent state whose learners are
at rest: in every world of the agent's interface, from every start, if every reward word the
world delivers before a time is a zero word, then at that time the agent is at rest, holds the
explorer's state after that many decisions, and takes the explorer's action, whatever reward
word that time's percept carries. What the step does to the representation plays no part. -/
theorem StepsByRule.quiet_actions
    (rule : StepsByRule interface profile config criterion dimension planning)
    (primitive : profile.usesHierarchy = false) (declared : profile.rate = .declared)
    (agent : Agent interface profile config criterion dimension planning)
    (rest : Quiet agent.control) (world : Kernel.World interface) (start : world.State)
    (time : ℕ)
    (unpaid : ∀ earlier, earlier < time →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward.isZero = true) :
    Quiet (Kernel.memoryAt world (executedAgent agent) start time).control ∧
      explorerOf (Kernel.memoryAt world (executedAgent agent) start time).control =
        (explorerOf agent.control).after time ∧
      Kernel.actionAt world (executedAgent agent) start time =
        (explorerOf agent.control).actionAt time := by
  have reached : Quiet (Kernel.memoryAt world (executedAgent agent) start time).control ∧
      explorerOf (Kernel.memoryAt world (executedAgent agent) start time).control =
        (explorerOf agent.control).after time := by
    induction time with
    | zero => exact ⟨rest, rfl⟩
    | succ time ih =>
      obtain ⟨still, tracked⟩ :=
        ih (fun earlier before => unpaid earlier (Nat.lt_succ_of_lt before))
      have stepped := rule.explores primitive declared
        (Kernel.memoryAt world (executedAgent agent) start time) still.control
        (Kernel.perceptAt world (executedAgent agent) start time)
      refine ⟨rule.quiet (Kernel.memoryAt world (executedAgent agent) start time) still
        (Kernel.perceptAt world (executedAgent agent) start time)
        (unpaid time (Nat.lt_succ_self time)), ?_⟩
      change explorerOf ((Kernel.memoryAt world (executedAgent agent) start time).act
        (Kernel.perceptAt world (executedAgent agent) start time)).1.control = _
      rw [stepped.2, tracked]
      rfl
  refine ⟨reached.1, reached.2, ?_⟩
  have stepped := rule.explores primitive declared
    (Kernel.memoryAt world (executedAgent agent) start time) reached.1.control
    (Kernel.perceptAt world (executedAgent agent) start time)
  change ((Kernel.memoryAt world (executedAgent agent) start time).act
    (Kernel.perceptAt world (executedAgent agent) start time)).2.action = _
  rw [stepped.1, reached.2]
  rfl

/-! ## A forgotten unit carries no weight -/

section Forgetting

open AcornVerif.CurrentLearner

/-- Retiring one slot leaves the weight on every other slot. -/
theorem retireIndex_other {learnerConfig : Acorn.Config}
    (state : NumericState learnerConfig dimension) (idx other : FeatIdx dimension)
    (different : idx ≠ other) :
    (state.retireIndex idx).weights.get other = state.weights.get other := by
  rw [NumericState.retireIndex_def]
  split <;> simp [NumericState.removeEligibleAt, NumericState.clearFeatureRegisters,
    NumericState.writeZ, NumericState.writeP, NumericState.writeZBar,
    NumericState.writeDeltaWeight, NumericState.writeZDelta, NumericState.writeH,
    NumericState.writeHOld, NumericState.writeHTemp, NumericState.writeLastAlpha,
    NumericState.writeWeight, NumericState.writeBetaValue, get_set_vec, different]

/-- Every row of the primitive controller holds a zero word on a slot. -/
def ClearedAt {actions : Word.Count} {discounts : List Discount}
    (ensemble : Ensemble actions config criterion dimension discounts)
    (slot : FeatIdx dimension) : Prop :=
  ∀ row, ((ensemble.control.learners.get row).state.weights.get slot).value.isZero = true

/-- Retiring a slot clears it in the primitive controller, and retiring any slot keeps a
cleared slot cleared. -/
theorem retire_cleared {actions : Word.Count} {discounts : List Discount}
    (ensemble : Ensemble actions config criterion dimension discounts)
    (retired slot : FeatIdx dimension) (held : retired = slot ∨ ClearedAt ensemble slot) :
    ClearedAt (ensemble.retire retired) slot := by
  intro row
  change (((ensemble.control.retire retired).learners.get row).state.weights.get slot).value.isZero
    = true
  rw [Controller.retire_def]
  dsimp only
  rw [get_map_vec, Managed.retire_def, Managed.apply_state, SwiftTd.Entry.apply_def]
  dsimp only
  by_cases same : retired = slot
  · subst same
    rw [(retire_registers _ retired).2.1]
    rfl
  · rw [retireIndex_other _ retired slot same]
    exact (held.resolve_left same) row

/-- **Forgetting a unit clears its slot.** After the listed units are forgotten, every row of
the primitive controller holds a zero word on the slot of each listed unit. -/
theorem forgetUnits_cleared {actions : Word.Count} {discounts : List Discount}
    (units : List (Fin config.units.count)) (unit : Fin config.units.count)
    (listed : unit ∈ units) :
    ∀ ensemble : Ensemble actions config criterion dimension discounts,
      ClearedAt (forgetUnits ensemble units) (unitFeature dimension config unit) := by
  have retired : ∀ (others : List (Fin config.units.count))
      (ensemble : Ensemble actions config criterion dimension discounts),
      unit ∈ others ∨ ClearedAt ensemble (unitFeature dimension config unit) →
        ClearedAt (retireUnits ensemble others) (unitFeature dimension config unit) := by
    intro others
    induction others with
    | nil =>
      intro ensemble held
      exact held.resolve_left (fun member => by cases member)
    | cons head rest ih =>
      intro ensemble held
      refine ih _ ?_
      by_cases later : unit ∈ rest
      · exact Or.inl later
      · refine Or.inr (retire_cleared ensemble _ _ ?_)
        rcases held with member | cleared
        · rcases List.mem_cons.mp member with same | inRest
          · exact Or.inl (congrArg (unitFeature dimension config) same.symm)
          · exact absurd inRest later
        · exact Or.inr cleared
  have released : ∀ (others : List (Fin config.units.count))
      (ensemble : Ensemble actions config criterion dimension discounts),
      (ensemble.releaseAll others).control = ensemble.control := by
    intro others
    induction others with
    | nil => intro ensemble; rfl
    | cons head rest ih => intro ensemble; exact (ih _).trans rfl
  intro ensemble row
  unfold forgetUnits
  rw [released]
  exact retired units ensemble (Or.inl listed) row

/-- **A unit that a step by the rule rewrites carries no weight.** If the step leaves a unit
with another projection than it had, every row of the primitive controller holds a zero word on
that unit's slot after the step. -/
theorem StepsByRule.forgets
    (rule : StepsByRule interface profile config criterion dimension planning)
    (agent : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) (unit : Fin config.units.count)
    (changed : (agent.act percept).1.control.runtime.lifecycle.representation.bank.projections.get
        unit ≠ agent.control.runtime.lifecycle.representation.bank.projections.get unit) :
    ClearedAt (agent.act percept).1.control.runtime.lifecycle.consumers
      (unitFeature dimension config unit) := by
  obtain ⟨units, -, consumers, -, -, -, -, kept⟩ := rule agent percept
  rw [consumers]
  exact forgetUnits_cleared units unit (by
    by_contra absent
    exact changed (kept unit absent)) _

end Forgetting

end AcornVerif.CurrentDeclaredStep
