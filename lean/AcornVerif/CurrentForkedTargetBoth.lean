import AcornVerif.CurrentForkedTarget
import AcornVerif.TurnsBoth

namespace AcornVerif.CurrentForkedTargetBoth
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.Coverage AcornVerif.CurrentGoals AcornVerif.CurrentGridWorld
open AcornVerif.CurrentConcealedTarget AcornVerif.CurrentForkedTarget

variable {config : Host.WorldConfig}

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

def secondTarget (mode : TaskFeatureMode) (first second : Live config) (length : ℕ)
    (pair : (forkedFind config mode first second length).Index) :
    (feasibleFind config mode second length).Index :=
  pair.1.2

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

theorem forked_need_grid (mode : TaskFeatureMode) (first second : Live config) (length : ℕ)
    {agent : Kernel.Agent Grid.interface} (free : Kernel.ExperienceFree agent)
    (limit horizon returns : ℕ)
    (admits : (forkedFind config mode first second length).Index → (ℕ → Bool) → ℕ → Prop) :
    ¬ Kernel.MastersGridBy (forkedFind config mode first second length)
      (forkedGoals config mode first second length) length (7 * length)
      (firstTarget mode first second length) (secondTarget mode first second length)
      limit horizon returns admits agent :=
  Kernel.turns_need_grid (forked_conceals mode first second length)
    (forked_first_covered mode first second length) free

theorem forked_blind_grid (mode : TaskFeatureMode) (first second : Live config) (length : ℕ)
    (carried : first.carried = second.carried) {agent : Kernel.Agent Grid.interface}
    (blind : Kernel.FeedbackDriven
      (fun percept : Percept Grid.interface => (percept.reward, percept.frame.achieved)) agent)
    (bound limit horizon returns : ℕ) {κ μ : Type}
    (one : (forkedFind config mode first second length).Index → κ)
    (two : (forkedFind config mode first second length).Index → μ)
    (admits : (forkedFind config mode first second length).Index → (ℕ → Bool) → ℕ → Prop) :
    ¬ Kernel.MastersGridBy (forkedFind config mode first second length)
      (forkedGoals config mode first second length) length bound one two limit horizon returns
      admits agent :=
  blind.mastersGrid (forked_mute mode first second length carried)
    (forked_apart mode first second length)

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

def blankFirst (first second : Live config) (target : Host.Position) : Bool → Option (Live config)
  | false => member first nowhere
  | true => member second target

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

def blankSecond (first second : Live config) (target : Host.Position) : Bool → Option (Live config)
  | false => member first target
  | true => member second nowhere

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
