/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Certificate
import AcornVerif.CurrentGoals

/-!
# Soundness of the certificate checkers

The checkers of `Acorn.Host.Certificate` decide selecting properties: facts about
one generated world that hold for some seeds and fail for others. Each theorem
here takes the executed checker's acceptance of a certificate as its hypothesis
and concludes a statement about the executed `World.step`. No checker is
complete: a rejected certificate establishes nothing.

An accepted replay certificate shows a goal `Feasible`: some run of at least one
and at most `cap` executed steps, from the checked world with the goal installed,
ends in a world that satisfies the goal (`replay_feasible`), and the last step of
that run reports completion (`feasible_done`). For a reach goal the run ends in the
goal box (`reach_path`); for a collect goal it ends holding the count
(`collect_path`). The statement is about the checked start world. It says nothing
about the world a campaign leaves at the start of a later attempt, and it is a
statement about `World.step`, not about the attempt loop an agent drives.

An accepted blocked certificate shows that no run of steps and goal installations,
in any order, from a world whose body is on the checked start tile puts the body
in the goal box (`blocked_outside`). A region that counts water as impassable
covers only runs that end without a boat. A region that counts mountains alone
makes the reach goal infeasible at every cap (`blocked_infeasible`).

An accepted stance certificate shows that a paid harvest from the stance yields
the named item in every world, for wood provided the tree is standing
(`stance_harvest`), and that a paid move from the tile behind the stance enters it
facing the resource (`stance_enter`), where that tile is in the box and walkable
(`stance_approach`). Stone and ore have no standing condition: no step depletes
them.

A successful step is a hypothesis of the blocked and stance theorems, as in
`AcornVerif.CurrentStep`: a step the world refuses returns no successor.
-/
namespace AcornVerif.CurrentCertificates
open Acorn Acorn.Host
open AcornVerif.CurrentStep AcornVerif.CurrentGoals

/-! ## Replay -/

/-- A goal is feasible from a world within a cap: some run of at least one and at most
`cap` executed steps, from the world with the goal installed, ends in a world that
satisfies the goal. -/
def Feasible {config : WorldConfig} (world : World config) (goal : Goal) (cap : Nat) : Prop :=
  ∃ (trace : List (Action × StepResult)) (final : World config),
    Trace (world.setGoal goal) trace final ∧ 0 < trace.length ∧ trace.length ≤ cap ∧
      final.goalSatisfied = true

/-- A run keeps the goal it started with. -/
theorem trace_goal {config : WorldConfig} {world final : World config}
    {trace : List (Action × StepResult)} (run : Trace world trace final) :
    final.goal = world.goal :=
  (World.advanceActions_goal _ _ _ (trace_actions run)).1

/-- The last step of a nonempty run reports the completion flag of the run's final world. -/
theorem trace_last {config : WorldConfig} {world final : World config}
    {trace : List (Action × StepResult)} (run : Trace world trace final)
    (nonempty : 0 < trace.length) :
    ∃ entry, trace.getLast? = some entry ∧ entry.2.done = final.goalSatisfied := by
  induction run with
  | done world => exact absurd nonempty (by simp)
  | @step world middle final action events rest stepped later ih =>
    cases later with
    | done _ => exact ⟨(action, events), rfl, World.step_completion _ _ _ _ stepped⟩
    | step inner following =>
      obtain ⟨entry, last, flag⟩ := ih (by simp)
      exact ⟨entry, by rw [List.getLast?_cons_cons]; exact last, flag⟩

/-- An action list the replay checker accepts shows its goal feasible from its world
within its cap. -/
theorem replay_feasible {config : WorldConfig} {world : World config} {goal : Goal} {cap : Nat}
    {actions : List Action} (accepted : replayCertified world goal cap actions = true) :
    Feasible world goal cap := by
  unfold replayCertified at accepted
  simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
  obtain ⟨⟨nonempty, short⟩, replayed⟩ := accepted
  cases run : (world.setGoal goal).advanceActions actions with
  | error refusal =>
    rw [run] at replayed
    exact absurd replayed (by simp)
  | ok final =>
    rw [run] at replayed
    obtain ⟨trace, traced, same⟩ := actions_trace _ _ _ run
    have length : trace.length = actions.length := by
      rw [← same, List.length_map]
    refine ⟨trace, final, traced, ?_, ?_, replayed⟩
    · rw [length]
      cases actions with
      | nil => simp at nonempty
      | cons action rest => simp
    · rw [length]
      exact short

/-- A feasible goal is reported complete by the last step of some run within the cap. -/
theorem feasible_done {config : WorldConfig} {world : World config} {goal : Goal} {cap : Nat}
    (feasible : Feasible world goal cap) :
    ∃ (trace : List (Action × StepResult)) (final : World config) (entry : Action × StepResult),
      Trace (world.setGoal goal) trace final ∧ trace.length ≤ cap ∧
        trace.getLast? = some entry ∧ entry.2.done = true := by
  obtain ⟨trace, final, run, nonempty, short, satisfied⟩ := feasible
  obtain ⟨entry, last, flag⟩ := trace_last run nonempty
  exact ⟨trace, final, entry, run, short, last, flag.trans satisfied⟩

/-- An action list the replay checker accepts for a reach goal: a run of at least one and
at most `cap` executed steps from the world ends with the body in the goal box. -/
theorem reach_path {config : WorldConfig} {world : World config} {target : Position} {cap : Nat}
    {actions : List Action}
    (accepted : replayCertified world (.reach target) cap actions = true) :
    ∃ (trace : List (Action × StepResult)) (final : World config),
      Trace (world.setGoal (.reach target)) trace final ∧ 0 < trace.length ∧
        trace.length ≤ cap ∧ InGoalBox target final.body.position.position := by
  obtain ⟨trace, final, run, nonempty, short, satisfied⟩ := replay_feasible accepted
  exact ⟨trace, final, run, nonempty, short,
    (reach_goal_iff final target (trace_goal run)).mp satisfied⟩

/-- An action list the replay checker accepts for a collect goal: a run of at least one
and at most `cap` executed steps from the world ends holding the requested count. -/
theorem collect_path {config : WorldConfig} {world : World config} {item : Item}
    {count : UInt32} {cap : Nat} {actions : List Action}
    (accepted : replayCertified world (.collect item count) cap actions = true) :
    ∃ (trace : List (Action × StepResult)) (final : World config),
      Trace (world.setGoal (.collect item count)) trace final ∧ 0 < trace.length ∧
        trace.length ≤ cap ∧ count.toNat ≤ (final.body.inventory.count item).toNat := by
  obtain ⟨trace, final, run, nonempty, short, satisfied⟩ := replay_feasible accepted
  rw [goalSatisfied_eq final _ (trace_goal run)] at satisfied
  exact ⟨trace, final, run, nonempty, short, (collect_satisfied_iff _ _ _ _ _).mp satisfied⟩

/-! ## Translation -/

/-- Coordinate admission returns a coordinate's own value. -/
theorem checked_val (coordinate : Coordinate) :
    Coordinate.checked coordinate.val = some coordinate := by
  unfold Coordinate.checked
  split
  · rfl
  · rename_i outside
    exact absurd coordinate.property outside

/-- A successful translation adds its offsets exactly. -/
theorem translate_some (origin tile : Position) (dx dy : Int)
    (h : origin.translate dx dy = some tile) :
    tile.x.val = origin.x.val + dx ∧ tile.y.val = origin.y.val + dy := by
  unfold Position.translate at h
  cases hx : Coordinate.checked (origin.x.val + dx) with
  | none => simp [hx] at h
  | some x =>
    cases hy : Coordinate.checked (origin.y.val + dy) with
    | none => simp [hx, hy] at h
    | some y =>
      simp only [hx, hy, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      subst h
      exact ⟨Coordinate.checked_exact _ _ hx, Coordinate.checked_exact _ _ hy⟩

/-- A translation whose exact sums are a position's coordinates returns that position. -/
theorem translate_of_eq (origin tile : Position) (dx dy : Int)
    (hx : tile.x.val = origin.x.val + dx) (hy : tile.y.val = origin.y.val + dy) :
    origin.translate dx dy = some tile := by
  unfold Position.translate
  rw [← hx, ← hy, checked_val, checked_val]
  rfl

/-- A move in a direction is undone by a move in some direction. -/
theorem translate_back (origin tile : Position) (direction : Direction)
    (h : origin.translate direction.delta.1 direction.delta.2 = some tile) :
    ∃ back, back ∈ Direction.all ∧ tile.translate back.delta.1 back.delta.2 = some origin := by
  obtain ⟨hx, hy⟩ := translate_some _ _ _ _ h
  cases direction <;> simp only [Direction.delta] at hx hy
  · exact ⟨.south, by simp [Direction.all],
      translate_of_eq _ _ _ _ (by simp only [Direction.delta]; omega)
        (by simp only [Direction.delta]; omega)⟩
  · exact ⟨.north, by simp [Direction.all],
      translate_of_eq _ _ _ _ (by simp only [Direction.delta]; omega)
        (by simp only [Direction.delta]; omega)⟩
  · exact ⟨.west, by simp [Direction.all],
      translate_of_eq _ _ _ _ (by simp only [Direction.delta]; omega)
        (by simp only [Direction.delta]; omega)⟩
  · exact ⟨.east, by simp [Direction.all],
      translate_of_eq _ _ _ _ (by simp only [Direction.delta]; omega)
        (by simp only [Direction.delta]; omega)⟩

/-! ## Blocked goal box -/

/-- Region membership is list membership. -/
theorem inRegion_iff (cells : List Position) (tile : Position) :
    inRegion cells tile = true ↔ tile ∈ cells := by
  simp [inRegion]

/-- A body position is inside the box. -/
theorem inBox_position {config : WorldConfig} (position : BoxPosition config) :
    inBox config position.position = true := by
  simp [inBox, BoxPosition.checked_position]

/-- Every offset within the reach radius is one of the goal box's offsets. -/
theorem offset_mem (offset : Int) (low : -(FeatureConstants.reachRadius : Int) ≤ offset)
    (high : offset ≤ FeatureConstants.reachRadius) : offset ∈ boxOffsets := by
  unfold boxOffsets
  refine List.mem_map.mpr
    ⟨(offset + FeatureConstants.reachRadius).toNat, List.mem_range.mpr ?_, ?_⟩
  · omega
  · omega

/-- An accepted region contains every body position of the goal box. -/
theorem box_in_region {config : WorldConfig} {boat : Bool} {target start : Position}
    {cells : List Position} (accepted : regionBlocked config boat target cells start = true)
    (position : BoxPosition config) (inside : InGoalBox target position.position) :
    inRegion cells position.position = true := by
  unfold regionBlocked at accepted
  simp only [Bool.and_eq_true, List.all_eq_true] at accepted
  obtain ⟨⟨-, boxed⟩, -⟩ := accepted
  unfold InGoalBox at inside
  have listed := boxed (position.position.y.val - target.y.val)
    (offset_mem _ (by omega) (by omega)) (position.position.x.val - target.x.val)
    (offset_mem _ (by omega) (by omega))
  rw [translate_of_eq target position.position _ _ (by omega) (by omega)] at listed
  simpa [covered, inBox_position] using listed

/-- One step keeps the body outside an accepted region, for a body that owns no boat
when the region counts water as impassable. -/
theorem blocked_step {config : WorldConfig} {boat : Bool} {target start : Position}
    {cells : List Position} (accepted : regionBlocked config boat target cells start = true)
    (world next : World config) (action : Action) (events : StepResult)
    (h : world.step action = .ok (next, events))
    (boatless : boat = false → world.body.inventory.boat = false)
    (outside : inRegion cells world.body.position.position = false) :
    inRegion cells next.body.position.position = false := by
  rcases step_adjacent world next action events h with
    same | ⟨direction, base, moved, located, enters⟩
  · rw [same]
    exact outside
  · cases inside : inRegion cells next.body.position.position with
    | false => rfl
    | true =>
      exfalso
      unfold regionBlocked at accepted
      simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at accepted
      obtain ⟨-, closed⟩ := accepted
      rcases closed _ ((inRegion_iff _ _).mp inside) with blocked | surrounded
      · unfold impassable at blocked
        rw [located] at blocked
        cases base with
        | mountain => simp [passable, TileKind.walkable] at enters
        | water =>
          have off : boat = false := by simpa using blocked
          simp [passable, boatless off] at enters
        | sand | grass | forest | tree | stone | ore => simp at blocked
      · obtain ⟨back, listed, returned⟩ := translate_back _ _ direction moved
        have held := surrounded back listed
        rw [returned] at held
        simp [covered, outside, inBox_position] at held

/-- No run of steps and goal installations moves the body into an accepted region from
outside it, for a run that ends without a boat when the region counts water as
impassable. -/
theorem blocked_later {config : WorldConfig} {boat : Bool} {target start : Position}
    {cells : List Position} (accepted : regionBlocked config boat target cells start = true)
    {world final : World config} (later : Later world final)
    (boatless : boat = false → final.body.inventory.boat = false)
    (outside : inRegion cells world.body.position.position = false) :
    inRegion cells final.body.position.position = false := by
  induction later with
  | here world => exact outside
  | @step world next final action events stepped rest ih =>
    refine ih boatless (blocked_step accepted world next action events stepped ?_ outside)
    intro off
    cases owned : world.body.inventory.boat with
    | false => rfl
    | true =>
      have kept := (later_retains rest).boat ((step_retains _ _ _ _ stepped).boat owned)
      rw [boatless off] at kept
      exact absurd kept (by simp)
  | install goal rest ih => exact ih boatless outside

/-- A run of steps is a run of steps and goal installations. -/
theorem trace_later {config : WorldConfig} {world final : World config}
    {trace : List (Action × StepResult)} (run : Trace world trace final) : Later world final := by
  induction run with
  | done world => exact .here world
  | step stepped later ih => exact .step stepped ih

/-- A region the blocked checker accepts for a world's body tile: after any run of steps
and goal installations from that world, the body is outside the goal box. A region that
counts water as impassable covers the runs that end without a boat. -/
theorem blocked_outside {config : WorldConfig} {boat : Bool} {target : Position}
    {cells : List Position} {world final : World config}
    (accepted : regionBlocked config boat target cells world.body.position.position = true)
    (later : Later world final) (boatless : boat = false → final.body.inventory.boat = false) :
    ¬ InGoalBox target final.body.position.position := by
  intro inside
  have outside : inRegion cells world.body.position.position = false := by
    have start := accepted
    unfold regionBlocked at start
    simp only [Bool.and_eq_true] at start
    simpa using start.1.1
  have kept := blocked_later accepted later boatless outside
  rw [box_in_region accepted final.body.position inside] at kept
  exact absurd kept (by simp)

/-- A region the blocked checker accepts for a world's body tile: a world reached from it
by any run of steps and goal installations, with the reach goal installed, does not
satisfy it. -/
theorem blocked_unsatisfied {config : WorldConfig} {boat : Bool} {target : Position}
    {cells : List Position} {world final : World config}
    (accepted : regionBlocked config boat target cells world.body.position.position = true)
    (later : Later world final) (boatless : boat = false → final.body.inventory.boat = false)
    (installed : final.goal = some (.reach target)) : final.goalSatisfied = false := by
  cases satisfied : final.goalSatisfied with
  | false => rfl
  | true =>
    exact absurd ((reach_goal_iff final target installed).mp satisfied)
      (blocked_outside accepted later boatless)

/-- A region of mountains alone that the blocked checker accepts for a world's body tile
makes the reach goal infeasible from that world at every cap. -/
theorem blocked_infeasible {config : WorldConfig} {target : Position} {cells : List Position}
    {world : World config}
    (accepted : regionBlocked config true target cells world.body.position.position = true)
    (cap : Nat) : ¬ Feasible world (.reach target) cap := by
  rintro ⟨trace, final, run, -, -, satisfied⟩
  have later : Later world final := .install (.reach target) (trace_later run)
  have unsatisfied := blocked_unsatisfied accepted later (fun off => absurd off (by simp))
    (trace_goal run)
  rw [satisfied] at unsatisfied
  exact absurd unsatisfied (by simp)

/-! ## Harvest stance -/

/-- A walkable tile is enterable in every world, with or without a boat. -/
theorem walkable_enterable {config : WorldConfig} (world : World config) (tile : Position)
    (walkable : walkableTile config tile = true) : world.enterable tile = .ok true := by
  rw [enterable_static]
  unfold walkableTile at walkable
  cases located : terrain tile config.raw.seed config.raw.baseScale with
  | error refusal =>
    rw [located] at walkable
    exact absurd walkable (by simp)
  | ok kind =>
    rw [located] at walkable
    cases kind <;> simp_all [Except.map, passable, TileKind.walkable]

/-- A paid move toward an enterable in-box tile puts the body on it, facing the move's
direction. -/
theorem perform_move {config : WorldConfig} (world : World config) (action : Action)
    (direction : Direction) (position : BoxPosition config)
    (heading : action.direction = some direction)
    (ahead : world.body.position.position.translate direction.delta.1 direction.delta.2 =
      some position.position)
    (enter : world.enterable position.position = .ok true) (active : ActionChange config)
    (h : performAction world action = .ok active) :
    active.body.position = position ∧ active.body.facing = direction := by
  unfold performAction at h
  simp only [heading, ahead, BoxPosition.checked_position, enter, bind, Except.bind, pure,
    Except.pure, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
  subst h
  exact ⟨rfl, rfl⟩

/-- The static terrain an accepted stance faces yields the item. -/
theorem stance_yield {config : WorldConfig} {stance : BoxPosition config}
    {direction : Direction} {item : Item}
    (accepted : stanceCertified config stance direction item = true) :
    ∃ kind, terrain (stance.facingPosition direction) config.raw.seed
        config.raw.baseScale = .ok kind ∧ kind.harvestYield = some item := by
  unfold stanceCertified at accepted
  simp only [Bool.and_eq_true] at accepted
  obtain ⟨⟨yields, -⟩, -⟩ := accepted
  cases located : terrain (stance.facingPosition direction)
      config.raw.seed config.raw.baseScale with
  | error refusal =>
    rw [located] at yields
    exact absurd yields (by simp)
  | ok kind =>
    rw [located] at yields
    exact ⟨kind, rfl, by simpa using yields⟩

/-- The tile behind an accepted stance is in the box and walkable, and a move in the
facing direction leads from it to the stance. -/
theorem stance_approach {config : WorldConfig} {stance : BoxPosition config}
    {direction : Direction} {item : Item}
    (accepted : stanceCertified config stance direction item = true) :
    ∃ approach : BoxPosition config,
      approach.position.translate direction.delta.1 direction.delta.2 =
        some stance.position ∧ walkableTile config approach.position = true := by
  unfold stanceCertified at accepted
  simp only [Bool.and_eq_true] at accepted
  obtain ⟨-, lane⟩ := accepted
  cases behind : stance.position.translate (-direction.delta.1) (-direction.delta.2) with
  | none =>
    rw [behind] at lane
    exact absurd lane (by simp)
  | some tile =>
    rw [behind] at lane
    simp only [Bool.and_eq_true] at lane
    obtain ⟨boxed, walkable⟩ := lane
    unfold inBox at boxed
    cases admitted : BoxPosition.checked config tile.x.val tile.y.val with
    | none => simp [admitted] at boxed
    | some approach =>
      have same := checked_position tile approach admitted
      obtain ⟨hx, hy⟩ := translate_some _ _ _ _ behind
      exact ⟨approach, by rw [same]; exact translate_of_eq _ _ _ _ (by omega) (by omega),
        by rw [same]; exact walkable⟩

/-- Entering a stance. From the tile behind a stance the checker accepts, a paid move in
the facing direction puts the body on the stance facing the resource, in every world. -/
theorem stance_enter {config : WorldConfig} {stance : BoxPosition config}
    {direction : Direction} {item : Item}
    (accepted : stanceCertified config stance direction item = true)
    (world next : World config) (action : Action) (events : StepResult)
    (heading : action.direction = some direction)
    (behind : world.body.position.position.translate direction.delta.1 direction.delta.2 =
      some stance.position)
    (h : world.step action = .ok (next, events)) (paid : events.exhausted = false) :
    next.body.position = stance ∧ next.body.facing = direction := by
  unfold stanceCertified at accepted
  simp only [Bool.and_eq_true] at accepted
  obtain ⟨⟨-, walkable⟩, -⟩ := accepted
  obtain ⟨active, acted, body, same⟩ := step_events world next action events h
  rw [body]
  unfold payAndAct at acted
  split at acted
  · cases Except.ok.inj acted
    rw [same] at paid
    exact absurd paid (by simp)
  · rename_i energy spent
    exact perform_move { world with body := { world.body with energy := energy } } action
      direction stance heading behind (walkable_enterable _ _ walkable) active acted

/-- Harvesting from a stance. In every world whose body stands on a stance the checker
accepts, facing its direction, a paid harvest yields the item and adds it to the
inventory: three wood with an axe, one item otherwise. A wood stance needs its tree
standing; stone and ore have no such condition. -/
theorem stance_harvest {config : WorldConfig} {stance : BoxPosition config}
    {direction : Direction} {item : Item}
    (accepted : stanceCertified config stance direction item = true)
    (world next : World config) (events : StepResult)
    (standing : world.body.position = stance) (facing : world.body.facing = direction)
    (grown : item = .wood → world.tileKind (stance.facingPosition direction) = .ok .tree)
    (h : world.step .harvest = .ok (next, events)) (paid : events.exhausted = false) :
    events.harvested = some item ∧
      next.body.inventory = world.body.inventory.add item
        (if item == .wood && world.body.inventory.axe then 3 else 1) := by
  obtain ⟨base, located, yields⟩ := stance_yield accepted
  have found : ∃ kind, world.tileKind (world.body.position.facingPosition world.body.facing) =
      .ok kind ∧ kind.harvestYield = some item := by
    rw [standing, facing]
    cases base with
    | tree =>
      have wood : item = .wood := by simpa [TileKind.harvestYield] using yields.symm
      exact ⟨.tree, grown wood, yields⟩
    | stone | ore =>
      refine ⟨_, ?_, yields⟩
      unfold World.tileKind
      rw [located]
      rfl
    | water | sand | grass | forest | mountain => simp [TileKind.harvestYield] at yields
  obtain ⟨kind, kinded, yielded⟩ := found
  obtain ⟨active, acted, body, same⟩ := step_events world next .harvest events h
  rw [body, same]
  unfold payAndAct at acted
  split at acted
  · cases Except.ok.inj acted
    rw [same] at paid
    exact absurd paid (by simp)
  · rename_i energy spent
    have kinded' : World.tileKind { world with body := { world.body with energy := energy } }
        (world.body.position.facingPosition world.body.facing) = .ok kind := kinded
    unfold performAction at acted
    simp only [Action.direction, kinded', yielded, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at acted
    subst acted
    exact ⟨rfl, rfl⟩

end AcornVerif.CurrentCertificates
