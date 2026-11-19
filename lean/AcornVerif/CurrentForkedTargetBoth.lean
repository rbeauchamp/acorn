/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentForkedTarget
import AcornVerif.TurnsBoth

/-!
# What mastery of a grid of concealed targets forces

A member of `AcornVerif.CurrentForkedTarget.forkedFind` is a pair of concealed targets, one for
each situation. This module proves, for mastery of a grid of such members
(`AcornVerif.Kernel.MastersGridBy`), the bounds and the consequence that the definition is for.

**The sharp covering bound.** A walk of `cap` steps comes within three tiles of at most
`49 + 7 cap` tiles, and 49 of those are the tiles within three of the start, none of which is a
target of the class. So one action sequence meets at most `7 cap` concealed targets
(`find_covered_sharp`, `feasibleFind_covered_sharp`): 49 for a visit of seven steps, where
`AcornVerif.CurrentConcealedTarget.find_covered` gives 98.

**No agent that keeps nothing masters a grid** at the bound `7 length`, and no agent driven by
its reward words and achievement flags masters one at any bound (`forked_need_grid`,
`forked_blind_grid`).

**Mastery of a grid needs experience of each situation.** Take a run of a member under an order.
While no visit of the first situation has been solved, the agent's memory at the start of each
visit is its memory in the run whose first situation holds the target `nowhere`, with the same
second target (`first_unmet_memory`): what it has met in the first situation is what every first
target shows before it is met, and what it has met in the second is decided by the second target
alone. So among members with one second target, those the agent solves in the first situation
on a visit, without having solved a visit of the first situation before, have at most `7 length`
different first targets (`first_fresh_covered`): they are met by one walk. The same holds with
the situations exchanged (`second_unmet_memory`, `second_fresh_covered`).

For a grid this says: under each second target of the grid, all but at most `7 length` of the
grid's first targets are targets the agent had already solved, in that run, on an earlier visit
of the first situation; and likewise for the second situation. What an agent meets in one
situation cannot stand in for experience of the other, however the grid is chosen.
-/

namespace AcornVerif.CurrentForkedTargetBoth
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.Coverage AcornVerif.CurrentGoals AcornVerif.CurrentGridWorld
open AcornVerif.CurrentConcealedTarget AcornVerif.CurrentForkedTarget

variable {config : Host.WorldConfig}

/-! ## The sharp covering bound -/

/-- **One action sequence meets at most `7 cap` concealed targets.** The tiles a walk of `cap`
steps comes within three of number at most `49 + 7 cap`, and they include the 49 within three of
the start, none of which is a target of the class. -/
theorem find_covered_sharp (config : Host.WorldConfig) (mode : TaskFeatureMode)
    (live : Live config) (cap : ℕ) :
    Kernel.Covered (findClass config mode live) (fun _ => completion config mode cap)
      (7 * cap) := by
  intro actions solved each
  have inside : solved.image (fun target => tile target.1) ⊆
      swept 3 (walk (physical live.world) actions) cap \
        box 3 (tile live.world.body.position.position) := by
    intro point chosen
    obtain ⟨target, picked, rfl⟩ := Finset.mem_image.mp chosen
    exact Finset.mem_sdiff.mpr ⟨find_met_swept mode live cap actions target.1
      (each target picked), (member_tile live target.1).mp target.2⟩
  have start : box 3 (tile live.world.body.position.position) ⊆
      swept 3 (walk (physical live.world) actions) cap :=
    box_subset_swept 3 (walk (physical live.world) actions) cap 0 (Nat.zero_le cap)
  have total := card_swept 3 (walk (physical live.world) actions) cap
    (fun index _ => walk_near _ actions index)
  have image : (solved.image fun target => tile target.1).card = solved.card :=
    Finset.card_image_of_injective solved
      (fun first second same => Subtype.ext (tile_injective same))
  have fewer := Finset.card_le_card inside
  rw [Finset.card_sdiff_of_subset start, card_box, image] at fewer
  omega

/-- One action sequence meets at most `7 length` feasible concealed targets. -/
theorem feasibleFind_covered_sharp (config : Host.WorldConfig) (mode : TaskFeatureMode)
    (live : Live config) (length : ℕ) :
    Kernel.Covered (feasibleFind config mode live length)
      (Kernel.visitGoals (fun _ => completion config mode length) length) (7 * length) := by
  classical
  intro actions solved each
  have injective : Function.Injective
      (fun target : (feasibleFind config mode live length).Index => target.1) :=
    fun _ _ same => Subtype.ext same
  rw [← Finset.card_image_of_injective solved injective]
  apply find_covered_sharp config mode live length actions
  intro target chosen
  obtain ⟨original, picked, rfl⟩ := Finset.mem_image.mp chosen
  exact each original picked

/-- A member's key in the second situation: its second target. -/
def secondTarget (mode : TaskFeatureMode) (first second : Live config) (length : ℕ)
    (pair : (forkedFind config mode first second length).Index) :
    (feasibleFind config mode second length).Index :=
  pair.1.2

/-- One action sequence meets, from the first situation's starts within a visit, the goals of at
most `7 length` members no two of which have one first target. -/
theorem forked_covered_sharp (mode : TaskFeatureMode) (first second : Live config) (length : ℕ)
    (actions : ℕ → Kernel.Act Grid.interface)
    (solved : Finset (forkedFind config mode first second length).Index)
    (distinct : ∀ one ∈ solved, ∀ two ∈ solved,
      firstTarget mode first second length one = firstTarget mode first second length two →
        one = two)
    (each : ∀ pair ∈ solved,
      (Kernel.turnGoal (forkedGoals config mode first second length) length pair).MetBy
        ((forkedFind config mode first second length).start pair false) actions) :
    solved.card ≤ 7 * length := by
  classical
  rw [← Finset.card_image_of_injOn (f := firstTarget mode first second length)
    (fun one inOne two inTwo same => distinct one inOne two inTwo same)]
  apply feasibleFind_covered_sharp config mode first length actions
  intro target chosen
  obtain ⟨pair, picked, rfl⟩ := Finset.mem_image.mp chosen
  exact each pair picked

/-- **No agent that keeps nothing masters a grid** at the bound `7 length`, whatever the limit,
the horizon, the lapses and the predicate. -/
theorem forked_need_grid (mode : TaskFeatureMode) (first second : Live config) (length : ℕ)
    {agent : Kernel.Agent Grid.interface} (free : Kernel.ExperienceFree agent)
    (limit horizon lapses : ℕ)
    (admits : (forkedFind config mode first second length).Index → (ℕ → Bool) → ℕ → Prop) :
    ¬ Kernel.MastersGridBy (forkedFind config mode first second length)
      (forkedGoals config mode first second length) length (7 * length)
      (firstTarget mode first second length) (secondTarget mode first second length)
      limit horizon lapses admits agent :=
  Kernel.turns_need_grid (forked_conceals mode first second length)
    (forked_covered_sharp mode first second length) free

/-- **No agent that goes by its clock, its reward words and its achievement flags masters a
grid**, at any bound, keys, limit, horizon, lapses and predicate. -/
theorem forked_blind_grid (mode : TaskFeatureMode) (first second : Live config) (length : ℕ)
    (carried : first.carried = second.carried) {agent : Kernel.Agent Grid.interface}
    (blind : Kernel.FeedbackDriven
      (fun percept : Percept Grid.interface => (percept.reward, percept.frame.achieved)) agent)
    (bound limit horizon lapses : ℕ) {κ μ : Type}
    (one : (forkedFind config mode first second length).Index → κ)
    (two : (forkedFind config mode first second length).Index → μ)
    (admits : (forkedFind config mode first second length).Index → (ℕ → Bool) → ℕ → Prop) :
    ¬ Kernel.MastersGridBy (forkedFind config mode first second length)
      (forkedGoals config mode first second length) length bound one two limit horizon lapses
      admits agent :=
  blind.mastersGrid (forked_mute mode first second length carried)
    (forked_apart mode first second length)

/-! ## Before a situation is first solved -/

/-- **A visit that does not meet a concealed target leaves the memory of the visit with no
target.** Entered with one memory, a visit from a live state with a concealed target installed,
on which the agent does not meet the target, leaves the agent the memory it would hold after the
visit from that live state with the target `nowhere` installed. -/
theorem unmet_visitMemory (mode : TaskFeatureMode) (live : Live config) (cap : ℕ)
    (target : (findClass config mode live).Index) (agent : Kernel.Agent Grid.interface)
    (memory : agent.Memory)
    (unmet : ¬ Kernel.Achieves (agent.resume memory)
      (⟨(completion config mode cap).satisfied, cap⟩ :
        Kernel.AttemptGoal (gridWorld config mode)) (member live target.1)) :
    Kernel.visitMemory agent (gridWorld config mode) (member live target.1) cap memory =
      Kernel.visitMemory agent (gridWorld config mode) (member live nowhere) cap memory := by
  have hidden := find_conceals mode live cap
  have never : ∀ step, 1 ≤ step → step ≤ cap → ¬ (completion config mode cap).satisfied
      (Kernel.stateAt (gridWorld config mode) (agent.resume memory) (member live target.1)
        step) :=
    fun step low high met => unmet ⟨step, low, high, met⟩
  obtain ⟨same, actions⟩ := hidden.agree (agent.resume memory) target cap never
  have percept := hidden.perceptAt_eq (agent.resume memory) target cap never
    (fun step before => actions step (Nat.le_of_lt before))
  have sameMemory : Kernel.memoryAt (gridWorld config mode) (agent.resume memory)
      (member live target.1) cap =
      Kernel.memoryAt (gridWorld config mode) (agent.resume memory) (member live nowhere) cap :=
    same
  have samePercept : Kernel.perceptAt (gridWorld config mode) (agent.resume memory)
      (member live target.1) cap =
      Kernel.perceptAt (gridWorld config mode) (agent.resume memory) (member live nowhere)
        cap := percept
  unfold Kernel.visitMemory
  rw [sameMemory, samePercept]

/-- The starts of the run whose first situation holds the target `nowhere`, beside one target of
the other situation. -/
def blankFirst (first second : Live config) (target : Host.Position) : Bool → Option (Live config)
  | false => member first nowhere
  | true => member second target

/-- **Before the first situation is first solved, the agent's memory is that of the run with no
first target.** In a member's run under an order, if no earlier visit of the first situation was
solved, the agent's memory at a visit's start is its memory in the run whose first situation holds
the target `nowhere`, with the member's other target. -/
theorem first_unmet_memory (mode : TaskFeatureMode) (first second : Live config) (length : ℕ)
    (agent : Kernel.Agent Grid.interface)
    (pair : (forkedFind config mode first second length).Index) (order : ℕ → Bool) (visit : ℕ)
    (fresh : ∀ earlier, earlier < visit → order earlier = false →
      ¬ Kernel.SolvesTurn (forkedFind config mode first second length)
        (forkedGoals config mode first second length) length order agent earlier pair) :
    Kernel.turnMemory ((forkedFind config mode first second length).world pair)
        ((forkedFind config mode first second length).start pair) order length agent visit =
      Kernel.turnMemory (gridWorld config mode) (blankFirst first second pair.1.2.1.1) order
        length agent visit := by
  induction visit with
  | zero =>
    unfold Kernel.turnMemory
    rw [Nat.zero_mul]
    rfl
  | succ visit ih =>
    have before := ih (fun earlier early => fresh earlier (Nat.lt_succ_of_lt early))
    rw [Kernel.turnMemory_succ, Kernel.turnMemory_succ, ← before]
    cases side : order visit with
    | true => rfl
    | false =>
      have unsolved := fresh visit (Nat.lt_succ_self visit) side
      rw [Kernel.solvesTurn_iff, side] at unsolved
      exact unmet_visitMemory mode first length pair.1.1.1 agent _ unsolved

/-- One action sequence meets, from the first situation's starts within a visit, the goals of at
most `7 length` members no two of which have one first target. -/
theorem forked_first_covered (mode : TaskFeatureMode) (first second : Live config) (length : ℕ)
    (actions : ℕ → Kernel.Act Grid.interface)
    (solved : Finset (forkedFind config mode first second length).Index)
    (distinct : ∀ one ∈ solved, ∀ two ∈ solved,
      firstTarget mode first second length one = firstTarget mode first second length two →
        one = two)
    (each : ∀ pair ∈ solved,
      (Kernel.turnGoal (forkedGoals config mode first second length) length pair).MetBy
        ((forkedFind config mode first second length).start pair false) actions) :
    solved.card ≤ 7 * length := by
  classical
  rw [← Finset.card_image_of_injOn (f := firstTarget mode first second length)
    (fun one inOne two inTwo same => distinct one inOne two inTwo same)]
  apply feasibleFind_covered_sharp config mode first length actions
  intro target chosen
  obtain ⟨pair, picked, rfl⟩ := Finset.mem_image.mp chosen
  exact each pair picked

/-- **What the other situation shows cannot stand in for the first situation.** Take members with
one target in the other situation, a run under one order, and a visit. Those the agent solves in
the first situation on that visit, having solved no earlier visit of the first situation,
number at most `7 length`: they are met by one walk. -/
theorem first_fresh_covered (mode : TaskFeatureMode) (first second : Live config) (length : ℕ)
    (agent : Kernel.Agent Grid.interface) (order : ℕ → Bool) (visit : ℕ)
    (target : (feasibleFind config mode second length).Index)
    (solved : Finset (forkedFind config mode first second length).Index)
    (same : ∀ pair ∈ solved,
      secondTarget mode first second length pair = target)
    (fresh : ∀ pair ∈ solved, ∀ earlier, earlier < visit → order earlier = false →
      ¬ Kernel.SolvesTurn (forkedFind config mode first second length)
        (forkedGoals config mode first second length) length order agent earlier pair)
    (each : ∀ pair ∈ solved, Kernel.SolvesTurn (forkedFind config mode first second length)
      (forkedGoals config mode first second length) length (Function.update order visit false)
      agent visit pair) :
    solved.card ≤ 7 * length := by
  have distinct : ∀ one ∈ solved, ∀ two ∈ solved,
      firstTarget mode first second length one = firstTarget mode first second length two →
        one = two := by
    intro one inOne two inTwo sameOwn
    exact Subtype.ext (Prod.ext sameOwn ((same one inOne).trans (same two inTwo).symm))
  refine forked_first_covered mode first second length
    (Kernel.actionAt (gridWorld config mode)
      (agent.resume (Kernel.turnMemory (gridWorld config mode)
        (blankFirst first second target.1.1) order length agent visit))
      (member first nowhere)) solved distinct (fun pair member => ?_)
  have solves := (Kernel.solvesTurn_side (forkedFind config mode first second length)
    (forkedGoals config mode first second length) length order agent visit pair false).mp
    (each pair member)
  rw [first_unmet_memory mode first second length agent pair order visit (fresh pair member)]
    at solves
  have shared : pair.1.2.1.1 = target.1.1 :=
    congrArg (fun other : (feasibleFind config mode second length).Index => other.1.1)
      (same pair member)
  rw [shared] at solves
  exact ((find_conceals mode first length).solves_iff _ pair.1.1.1).mp solves

/-- The starts of the run whose second situation holds the target `nowhere`, beside one target of
the other situation. -/
def blankSecond (first second : Live config) (target : Host.Position) : Bool → Option (Live config)
  | false => member first target
  | true => member second nowhere

/-- **Before the second situation is first solved, the agent's memory is that of the run with no
second target.** In a member's run under an order, if no earlier visit of the second situation was
solved, the agent's memory at a visit's start is its memory in the run whose second situation holds
the target `nowhere`, with the member's other target. -/
theorem second_unmet_memory (mode : TaskFeatureMode) (first second : Live config) (length : ℕ)
    (agent : Kernel.Agent Grid.interface)
    (pair : (forkedFind config mode first second length).Index) (order : ℕ → Bool) (visit : ℕ)
    (fresh : ∀ earlier, earlier < visit → order earlier = true →
      ¬ Kernel.SolvesTurn (forkedFind config mode first second length)
        (forkedGoals config mode first second length) length order agent earlier pair) :
    Kernel.turnMemory ((forkedFind config mode first second length).world pair)
        ((forkedFind config mode first second length).start pair) order length agent visit =
      Kernel.turnMemory (gridWorld config mode) (blankSecond first second pair.1.1.1.1) order
        length agent visit := by
  induction visit with
  | zero =>
    unfold Kernel.turnMemory
    rw [Nat.zero_mul]
    rfl
  | succ visit ih =>
    have before := ih (fun earlier early => fresh earlier (Nat.lt_succ_of_lt early))
    rw [Kernel.turnMemory_succ, Kernel.turnMemory_succ, ← before]
    cases side : order visit with
    | false => rfl
    | true =>
      have unsolved := fresh visit (Nat.lt_succ_self visit) side
      rw [Kernel.solvesTurn_iff, side] at unsolved
      exact unmet_visitMemory mode second length pair.1.2.1 agent _ unsolved

/-- One action sequence meets, from the second situation's starts within a visit, the goals of at
most `7 length` members no two of which have one second target. -/
theorem forked_second_covered (mode : TaskFeatureMode) (first second : Live config) (length : ℕ)
    (actions : ℕ → Kernel.Act Grid.interface)
    (solved : Finset (forkedFind config mode first second length).Index)
    (distinct : ∀ one ∈ solved, ∀ two ∈ solved,
      secondTarget mode first second length one = secondTarget mode first second length two →
        one = two)
    (each : ∀ pair ∈ solved,
      (Kernel.turnGoal (forkedGoals config mode first second length) length pair).MetBy
        ((forkedFind config mode first second length).start pair true) actions) :
    solved.card ≤ 7 * length := by
  classical
  rw [← Finset.card_image_of_injOn (f := secondTarget mode first second length)
    (fun one inOne two inTwo same => distinct one inOne two inTwo same)]
  apply feasibleFind_covered_sharp config mode second length actions
  intro target chosen
  obtain ⟨pair, picked, rfl⟩ := Finset.mem_image.mp chosen
  exact each pair picked

/-- **What the other situation shows cannot stand in for the second situation.** Take members with
one target in the other situation, a run under one order, and a visit. Those the agent solves in
the second situation on that visit, having solved no earlier visit of the second situation,
number at most `7 length`: they are met by one walk. -/
theorem second_fresh_covered (mode : TaskFeatureMode) (first second : Live config) (length : ℕ)
    (agent : Kernel.Agent Grid.interface) (order : ℕ → Bool) (visit : ℕ)
    (target : (feasibleFind config mode first length).Index)
    (solved : Finset (forkedFind config mode first second length).Index)
    (same : ∀ pair ∈ solved,
      firstTarget mode first second length pair = target)
    (fresh : ∀ pair ∈ solved, ∀ earlier, earlier < visit → order earlier = true →
      ¬ Kernel.SolvesTurn (forkedFind config mode first second length)
        (forkedGoals config mode first second length) length order agent earlier pair)
    (each : ∀ pair ∈ solved, Kernel.SolvesTurn (forkedFind config mode first second length)
      (forkedGoals config mode first second length) length (Function.update order visit true)
      agent visit pair) :
    solved.card ≤ 7 * length := by
  have distinct : ∀ one ∈ solved, ∀ two ∈ solved,
      secondTarget mode first second length one = secondTarget mode first second length two →
        one = two := by
    intro one inOne two inTwo sameOwn
    exact Subtype.ext (Prod.ext ((same one inOne).trans (same two inTwo).symm) sameOwn)
  refine forked_second_covered mode first second length
    (Kernel.actionAt (gridWorld config mode)
      (agent.resume (Kernel.turnMemory (gridWorld config mode)
        (blankSecond first second target.1.1) order length agent visit))
      (member second nowhere)) solved distinct (fun pair member => ?_)
  have solves := (Kernel.solvesTurn_side (forkedFind config mode first second length)
    (forkedGoals config mode first second length) length order agent visit pair true).mp
    (each pair member)
  rw [second_unmet_memory mode first second length agent pair order visit (fresh pair member)]
    at solves
  have shared : pair.1.1.1.1 = target.1.1 :=
    congrArg (fun other : (feasibleFind config mode first length).Index => other.1.1)
      (same pair member)
  rw [shared] at solves
  exact ((find_conceals mode second length).solves_iff _ pair.1.2.1).mp solves

/-- **Under one second target, the first targets solved without earlier experience are few.** Take
a set of first targets and one second target. Suppose each first target of the set has a member,
with that second target, that the agent solves in the first situation on a visit, having solved
no earlier visit of the first situation in that member's run. Then the set holds at most
`7 length` targets. -/
theorem grid_first_experience (mode : TaskFeatureMode) (first second : Live config) (length : ℕ)
    (agent : Kernel.Agent Grid.interface) (order : ℕ → Bool) (visit : ℕ)
    (targets : Finset (feasibleFind config mode first length).Index)
    (other : (feasibleFind config mode second length).Index)
    (each : ∀ own ∈ targets, ∃ pair : (forkedFind config mode first second length).Index,
      firstTarget mode first second length pair = own ∧
        secondTarget mode first second length pair = other ∧
        Kernel.SolvesTurn (forkedFind config mode first second length)
          (forkedGoals config mode first second length) length
          (Function.update order visit false) agent visit pair ∧
        ∀ earlier, earlier < visit → order earlier = false →
          ¬ Kernel.SolvesTurn (forkedFind config mode first second length)
            (forkedGoals config mode first second length) length order agent earlier pair) :
    targets.card ≤ 7 * length := by
  classical
  choose pick isOwn isOther solved fresh using each
  have image : (targets.attach.image fun own => pick own.1 own.2).card = targets.card := by
    rw [Finset.card_image_of_injective _ (fun own another same => Subtype.ext (by
      rw [← isOwn own.1 own.2, ← isOwn another.1 another.2, same])), Finset.card_attach]
  rw [← image]
  refine first_fresh_covered mode first second length agent order visit other _
    (fun pair member => ?_) (fun pair member => ?_) (fun pair member => ?_)
  · obtain ⟨own, -, rfl⟩ := Finset.mem_image.mp member
    exact isOther own.1 own.2
  · obtain ⟨own, -, rfl⟩ := Finset.mem_image.mp member
    exact fresh own.1 own.2
  · obtain ⟨own, -, rfl⟩ := Finset.mem_image.mp member
    exact solved own.1 own.2

/-- **Under one first target, the second targets solved without earlier experience are few.** Take
a set of second targets and one first target. Suppose each second target of the set has a member,
with that first target, that the agent solves in the second situation on a visit, having solved
no earlier visit of the second situation in that member's run. Then the set holds at most
`7 length` targets. -/
theorem grid_second_experience (mode : TaskFeatureMode) (first second : Live config) (length : ℕ)
    (agent : Kernel.Agent Grid.interface) (order : ℕ → Bool) (visit : ℕ)
    (targets : Finset (feasibleFind config mode second length).Index)
    (other : (feasibleFind config mode first length).Index)
    (each : ∀ own ∈ targets, ∃ pair : (forkedFind config mode first second length).Index,
      secondTarget mode first second length pair = own ∧
        firstTarget mode first second length pair = other ∧
        Kernel.SolvesTurn (forkedFind config mode first second length)
          (forkedGoals config mode first second length) length
          (Function.update order visit true) agent visit pair ∧
        ∀ earlier, earlier < visit → order earlier = true →
          ¬ Kernel.SolvesTurn (forkedFind config mode first second length)
            (forkedGoals config mode first second length) length order agent earlier pair) :
    targets.card ≤ 7 * length := by
  classical
  choose pick isOwn isOther solved fresh using each
  have image : (targets.attach.image fun own => pick own.1 own.2).card = targets.card := by
    rw [Finset.card_image_of_injective _ (fun own another same => Subtype.ext (by
      rw [← isOwn own.1 own.2, ← isOwn another.1 another.2, same])), Finset.card_attach]
  rw [← image]
  refine second_fresh_covered mode first second length agent order visit other _
    (fun pair member => ?_) (fun pair member => ?_) (fun pair member => ?_)
  · obtain ⟨own, -, rfl⟩ := Finset.mem_image.mp member
    exact isOther own.1 own.2
  · obtain ⟨own, -, rfl⟩ := Finset.mem_image.mp member
    exact fresh own.1 own.2
  · obtain ⟨own, -, rfl⟩ := Finset.mem_image.mp member
    exact solved own.1 own.2

end AcornVerif.CurrentForkedTargetBoth
