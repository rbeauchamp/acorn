import Acorn.Host.WorldDynamics

namespace AcornVerif.CurrentStep
open Acorn Acorn.Host

inductive Performed {config : WorldConfig} (world : World config) (action : Action)
    (body : Body config) : Prop where
  | unchanged (same : body = world.body)
  | moved (direction : Direction) (candidate : Position) (position : BoxPosition config)
      (picked : UInt32) (heading : action.direction = some direction)
      (translated : world.body.position.position.translate direction.delta.1 direction.delta.2 =
        some candidate)
      (admitted : BoxPosition.checked config candidate.x.val candidate.y.val = some position)
      (entered : world.enterable candidate = .ok true)
      (result : body = ⟨position, direction, world.body.energy,
        world.body.inventory.add .food picked⟩)
  | harvested (item : Item) (amount : UInt32)
      (result : body = { world.body with inventory := world.body.inventory.add item amount })
  | crafted (tool : Craftable) (inventory : Inventory)
      (recipe : world.body.inventory.craft tool = .ok inventory)
      (result : body = { world.body with inventory := inventory })
  | ate (meal : action = .eat)
      (result : body = { world.body with
        inventory := { world.body.inventory with food := world.body.inventory.food - 1 }
        energy := world.body.energy.gain .eat })

theorem performAction_outcome {config : WorldConfig} (world : World config) (action : Action)
    (active : ActionChange config) (h : performAction world action = .ok active) :
    Performed world action active.body ∧ active.events.exhausted = false := by
  unfold performAction at h
  cases heading : action.direction with
  | some direction =>
    simp only [heading] at h
    cases translated :
        world.body.position.position.translate direction.delta.fst direction.delta.snd with
    | none => simp [translated] at h
    | some candidate =>
      simp only [translated] at h
      cases admitted : BoxPosition.checked config candidate.x.val candidate.y.val with
      | none =>
        simp only [admitted, pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact ⟨.unchanged rfl, rfl⟩
      | some position =>
        simp only [admitted] at h
        cases entered : world.enterable candidate with
        | error refusal => simp [entered, bind, Except.bind] at h
        | ok allowed =>
          cases allowed with
          | false =>
            simp only [entered, bind, Except.bind, pure, Except.pure, Bool.not_false, eq_self,
              ↓reduceIte, Except.ok.injEq] at h
            subst h
            exact ⟨.unchanged rfl, rfl⟩
          | true =>
            simp only [entered, bind, Except.bind, pure, Except.pure, Bool.not_true,
              Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
            subst h
            exact ⟨.moved direction candidate position _ heading translated admitted entered rfl,
              rfl⟩
  | none =>
    cases action with
    | north | south | east | west => simp [Action.direction] at heading
    | harvest =>
      simp only [Action.direction] at h
      cases located : world.tileKind (world.body.position.facingPosition world.body.facing) with
      | error refusal => simp [located, bind, Except.bind] at h
      | ok kind =>
        simp only [located, bind, Except.bind] at h
        split at h
        · simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          exact ⟨.harvested _ _ rfl, rfl⟩
        · simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          exact ⟨.unchanged rfl, rfl⟩
    | craftAxe | craftBoat =>
      simp only [Action.direction] at h
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact ⟨.unchanged rfl, rfl⟩
      · rename_i inventory recipe
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact ⟨.crafted _ inventory recipe rfl, rfl⟩
    | eat =>
      simp only [Action.direction] at h
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact ⟨.ate rfl rfl, rfl⟩
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact ⟨.unchanged rfl, rfl⟩
    | wait =>
      simp only [Action.direction, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨.unchanged rfl, rfl⟩

theorem payAndAct_outcome {config : WorldConfig} (world : World config) (action : Action)
    (active : ActionChange config) (h : payAndAct world action = .ok active) :
    ∃ night,
      (world.body.energy.spend (action.energyCost night) = none ∧
        active.body = { world.body with energy := world.body.energy.gain .rest } ∧
        active.events.exhausted = true) ∨
      (∃ energy, world.body.energy.spend (action.energyCost night) = some energy ∧
        Performed { world with body := { world.body with energy := energy } } action active.body ∧
        active.events.exhausted = false) := by
  unfold payAndAct at h
  refine ⟨decide (world.dayPhase.val ≥ 4), ?_⟩
  split at h
  · rename_i unpaid
    cases Except.ok.inj h
    exact Or.inl ⟨unpaid, rfl, rfl⟩
  · rename_i energy paid
    exact Or.inr ⟨energy, paid, performAction_outcome _ _ _ h⟩

theorem step_events {config : WorldConfig} (world next : World config) (action : Action)
    (events : StepResult) (h : world.step action = .ok (next, events)) :
    ∃ active, payAndAct world action = .ok active ∧ next.body = active.body ∧
      events = { active.events with done := next.goalSatisfied } := by
  unfold World.step at h
  cases ha : payAndAct world action with
  | error error => simp [ha, bind, Except.bind] at h
  | ok active =>
    simp only [ha, bind, Except.bind] at h
    cases hp : passiveChange
        { world.applyActive active with time := (world.applyActive active).time + 1 } with
    | error error => simp [hp] at h
    | ok passive =>
      simp only [hp, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨active, rfl, rfl, by rw [World.decide_goalSatisfied]⟩

theorem step_active {config : WorldConfig} (world next : World config) (action : Action)
    (events : StepResult) (h : world.step action = .ok (next, events)) :
    ∃ active, payAndAct world action = .ok active ∧ next.body = active.body ∧
      events.exhausted = active.events.exhausted := by
  obtain ⟨active, paid, body, same⟩ := step_events world next action events h
  exact ⟨active, paid, body, by rw [same]⟩

structure Retains (before after : Inventory) : Prop where
  axe : before.axe = true → after.axe = true
  boat : before.boat = true → after.boat = true
  gold : before.gold.toNat ≤ after.gold.toNat

theorem Retains.refl (inventory : Inventory) : Retains inventory inventory :=
  ⟨id, id, Nat.le_refl _⟩

theorem Retains.trans {first second third : Inventory} (early : Retains first second)
    (late : Retains second third) : Retains first third :=
  ⟨fun owned => late.axe (early.axe owned), fun owned => late.boat (early.boat owned),
    Nat.le_trans early.gold late.gold⟩

theorem add_retains (inventory : Inventory) (item : Item) (amount : UInt32) :
    Retains inventory (inventory.add item amount) := by
  cases item
  · exact ⟨id, id, Nat.le_refl _⟩
  · exact ⟨id, id, Nat.le_refl _⟩
  · exact ⟨id, id, Nat.le_refl _⟩
  · refine ⟨id, id, ?_⟩
    have bound := inventory.gold.toNat_lt
    change inventory.gold.toNat ≤
      (UInt32.ofNat (min (2 ^ 32 - 1) (inventory.gold.toNat + amount.toNat))).toNat
    rw [UInt32.toNat_ofNat_of_lt'
      (show min (2 ^ 32 - 1) (inventory.gold.toNat + amount.toNat) < 2 ^ 32 by omega)]
    omega

theorem craft_retains (inventory next : Inventory) (tool : Craftable)
    (h : inventory.craft tool = .ok next) : Retains inventory next := by
  rcases hr : tool.recipe with ⟨wood, stone⟩
  by_cases ho : inventory.Owns tool
  · simp [Inventory.craft, ho] at h
  · by_cases hw : inventory.wood.toNat < wood
    · simp [Inventory.craft, hr, ho, hw] at h
    · by_cases hs : inventory.stone.toNat < stone
      · simp [Inventory.craft, hr, ho, hw, hs] at h
      · simp only [Inventory.craft, hr, ho, hw, hs, ↓reduceIte] at h
        cases tool <;> cases Except.ok.inj h
        · exact ⟨fun _ => rfl, id, Nat.le_refl _⟩
        · exact ⟨id, fun _ => rfl, Nat.le_refl _⟩

theorem step_retains {config : WorldConfig} (world next : World config) (action : Action)
    (events : StepResult) (h : world.step action = .ok (next, events)) :
    Retains world.body.inventory next.body.inventory := by
  obtain ⟨active, paid, body, -⟩ := step_active world next action events h
  rw [body]
  obtain ⟨night, outcome⟩ := payAndAct_outcome world action active paid
  rcases outcome with ⟨-, exhausted, -⟩ | ⟨energy, -, performed, -⟩
  · rw [exhausted]
    exact Retains.refl _
  · cases performed with
    | unchanged same => rw [same]; exact Retains.refl _
    | moved direction candidate position picked heading translated admitted entered result =>
      rw [result]; exact add_retains world.body.inventory .food picked
    | harvested item amount result =>
      rw [result]; exact add_retains world.body.inventory item amount
    | crafted tool inventory recipe result => rw [result]; exact craft_retains _ _ _ recipe
    | ate meal result => rw [result]; exact ⟨id, id, Nat.le_refl _⟩

theorem spend_none (energy : Energy) (cost : Nat) (h : energy.spend cost = none) :
    energy.val < cost := by
  unfold Energy.spend at h
  split at h
  · contradiction
  · omega

theorem cost_le (action : Action) (night : Bool) : action.energyCost night ≤ 4 := by
  cases action <;> cases night <;> decide

theorem move_cost_le (action : Action) (night : Bool) (direction : Direction)
    (heading : action.direction = some direction) : action.energyCost night ≤ 2 := by
  cases action <;> cases night <;> first | decide | simp [Action.direction] at heading

theorem performed_energy {config : WorldConfig} (world : World config) (action : Action)
    (body : Body config) (performed : Performed world action body) :
    world.body.energy.val ≤ body.energy.val ∧
      (action ≠ .eat → body.energy = world.body.energy) := by
  cases performed with
  | unchanged same => rw [same]; exact ⟨Nat.le_refl _, fun _ => rfl⟩
  | moved direction candidate position picked heading translated admitted entered result =>
    rw [result]; exact ⟨Nat.le_refl _, fun _ => rfl⟩
  | harvested item amount result => rw [result]; exact ⟨Nat.le_refl _, fun _ => rfl⟩
  | crafted tool inventory recipe result => rw [result]; exact ⟨Nat.le_refl _, fun _ => rfl⟩
  | ate meal result =>
    rw [result]
    refine ⟨?_, fun other => absurd meal other⟩
    have capacity := world.body.energy.isLt
    change world.body.energy.val ≤
      min (world.body.energy.val + EnergyGain.eat.amount) FeatureConstants.energyMax
    omega

theorem step_energy {config : WorldConfig} (world next : World config) (action : Action)
    (events : StepResult) (h : world.step action = .ok (next, events)) :
    ∃ cost, cost ≤ 4 ∧ (∀ direction, action.direction = some direction → cost ≤ 2) ∧
      ((events.exhausted = true ∧ world.body.energy.val < cost ∧
          next.body.energy.val = world.body.energy.val + 20) ∨
        (events.exhausted = false ∧ cost ≤ world.body.energy.val ∧
          world.body.energy.val ≤ next.body.energy.val + cost ∧
          (action ≠ .eat → next.body.energy.val + cost = world.body.energy.val))) := by
  obtain ⟨active, paid, body, flag⟩ := step_active world next action events h
  obtain ⟨night, outcome⟩ := payAndAct_outcome world action active paid
  refine ⟨action.energyCost night, cost_le action night,
    fun direction heading => move_cost_le action night direction heading, ?_⟩
  have bound := cost_le action night
  rw [body, flag]
  rcases outcome with ⟨unpaid, exhausted, raised⟩ | ⟨energy, spent, performed, raised⟩
  · have short := spend_none _ _ unpaid
    refine Or.inl ⟨raised, short, ?_⟩
    rw [exhausted]
    change min (world.body.energy.val + 20) 2000 = world.body.energy.val + 20
    omega
  · have balance := Energy.spend_balance _ _ _ spent
    obtain ⟨kept, same⟩ := performed_energy _ action active.body performed
    change energy.val ≤ active.body.energy.val at kept
    refine Or.inr ⟨raised, by omega, by omega, fun other => ?_⟩
    have settled := same other
    change active.body.energy = energy at settled
    rw [settled]
    exact balance

inductive Trace {config : WorldConfig} :
    World config → List (Action × StepResult) → World config → Prop where
  | done (world : World config) : Trace world [] world
  | step {world middle final : World config} {action : Action} {events : StepResult}
      {rest : List (Action × StepResult)} (stepped : world.step action = .ok (middle, events))
      (later : Trace middle rest final) : Trace world ((action, events) :: rest) final

theorem trace_actions {config : WorldConfig} {world final : World config}
    {trace : List (Action × StepResult)} (run : Trace world trace final) :
    world.advanceActions (trace.map (·.1)) = .ok final := by
  induction run with
  | done world => rfl
  | @step world middle final action events rest stepped later ih =>
    simp only [List.map_cons, World.advanceActions, stepped, bind, Except.bind]
    exact ih

theorem actions_trace {config : WorldConfig} (world final : World config) (actions : List Action)
    (h : world.advanceActions actions = .ok final) :
    ∃ trace, Trace world trace final ∧ trace.map (·.1) = actions := by
  induction actions generalizing world with
  | nil => cases Except.ok.inj h; exact ⟨[], .done _, rfl⟩
  | cons action rest ih =>
    simp only [World.advanceActions] at h
    cases hs : world.step action with
    | error error => simp [hs, bind, Except.bind] at h
    | ok pair =>
      simp only [hs, bind, Except.bind] at h
      obtain ⟨trace, run, same⟩ := ih pair.1 h
      exact ⟨(action, pair.2) :: trace, .step hs run, by simp [same]⟩

theorem trace_retains {config : WorldConfig} {world final : World config}
    {trace : List (Action × StepResult)} (run : Trace world trace final) :
    Retains world.body.inventory final.body.inventory := by
  induction run with
  | done world => exact Retains.refl _
  | @step world middle final action events rest stepped later ih =>
    exact (step_retains _ _ _ _ stepped).trans ih

def exhausted (trace : List (Action × StepResult)) : Nat :=
  trace.countP (fun entry => entry.2.exhausted)

theorem exhausted_cons_true (action : Action) (events : StepResult)
    (rest : List (Action × StepResult)) (flag : events.exhausted = true) :
    exhausted ((action, events) :: rest) = exhausted rest + 1 := by
  simp [exhausted, flag]

theorem exhausted_cons_false (action : Action) (events : StepResult)
    (rest : List (Action × StepResult)) (flag : events.exhausted = false) :
    exhausted ((action, events) :: rest) = exhausted rest := by
  simp [exhausted, flag]

theorem trace_energy {config : WorldConfig} {world final : World config}
    {trace : List (Action × StepResult)} (run : Trace world trace final) :
    24 * exhausted trace + world.body.energy.val ≤ 4 * trace.length + final.body.energy.val := by
  induction run with
  | done world => simp [exhausted]
  | @step world middle final action events rest stepped later ih =>
    obtain ⟨cost, bound, -, outcome⟩ := step_energy _ _ _ _ stepped
    rcases outcome with ⟨flag, -, raised⟩ | ⟨flag, -, kept, -⟩
    · rw [exhausted_cons_true _ _ _ flag, List.length_cons]
      omega
    · rw [exhausted_cons_false _ _ _ flag, List.length_cons]
      omega

theorem trace_exhausted {config : WorldConfig} {world final : World config}
    {trace : List (Action × StepResult)} (run : Trace world trace final) :
    24 * exhausted trace ≤ 4 * trace.length + 2000 := by
  have ledger := trace_energy run
  have capacity : final.body.energy.val ≤ 2000 := Nat.le_of_lt_succ final.body.energy.isLt
  omega

def Moves (trace : List (Action × StepResult)) : Prop :=
  ∀ entry ∈ trace, ∃ direction, entry.1.direction = some direction

theorem trace_moves {config : WorldConfig} {world final : World config}
    {trace : List (Action × StepResult)} (run : Trace world trace final) (moves : Moves trace) :
    22 * exhausted trace + min world.body.energy.val 21 ≤
      2 * trace.length + min final.body.energy.val 21 := by
  induction run with
  | done world => simp [exhausted]
  | @step world middle final action events rest stepped later ih =>
    obtain ⟨direction, heading⟩ := moves (action, events) (List.mem_cons.mpr (Or.inl rfl))
    have ih := ih (fun entry member => moves entry (List.mem_cons.mpr (Or.inr member)))
    obtain ⟨cost, -, small, outcome⟩ := step_energy _ _ _ _ stepped
    have small := small direction heading
    have other : action ≠ .eat := by
      intro eat
      rw [eat] at heading
      simp [Action.direction] at heading
    rcases outcome with ⟨flag, short, raised⟩ | ⟨flag, -, -, balance⟩
    · rw [exhausted_cons_true _ _ _ flag, List.length_cons]
      omega
    · have balance := balance other
      rw [exhausted_cons_false _ _ _ flag, List.length_cons]
      omega

theorem moves_exhausted {config : WorldConfig} {world final : World config}
    {trace : List (Action × StepResult)} (run : Trace world trace final) (moves : Moves trace) :
    22 * exhausted trace ≤ 2 * trace.length + 21 := by
  have ledger := trace_moves run moves
  omega

theorem moves_paid_at_cap {config : WorldConfig} {world final : World config}
    {trace : List (Action × StepResult)} (run : Trace world trace final) (moves : Moves trace)
    (cap : trace.length = 3000) : 2727 ≤ trace.length - exhausted trace := by
  have bound := moves_exhausted run moves
  omega

def passable (base : TileKind) (boat : Bool) : Bool :=
  match base with
  | .water => boat
  | other => other.walkable

theorem enterable_static {config : WorldConfig} (world : World config) (position : Position) :
    world.enterable position =
      (terrain position config.raw.seed config.raw.baseScale).map
        (fun base => passable base world.body.inventory.boat) := by
  unfold World.enterable World.tileKind
  simp only [TileKind.decide_walkable]
  cases terrain position config.raw.seed config.raw.baseScale with
  | error refusal => rfl
  | ok base =>
    simp only [bind, Except.bind, pure, Except.pure, Except.map]
    cases base with
    | tree =>
      have same : (TileKind.tree == TileKind.tree) = true := rfl
      simp only [same, ↓reduceIte]
      cases harvestKey config position with
      | none => rfl
      | some key =>
        dsimp only
        cases world.harvested[key]? with
        | none => rfl
        | some time =>
          dsimp only
          by_cases growing : world.time.toNat - time.toNat < config.raw.regrow.toNat
          · rw [ite_eq_left growing]
            rfl
          · rw [ite_eq_right growing]
            rfl
    | water | sand | grass | forest | mountain | stone | ore => rfl

theorem mountain_closed {config : WorldConfig} (world : World config) (position : Position)
    (mountain : terrain position config.raw.seed config.raw.baseScale = .ok .mountain) :
    world.enterable position = .ok false := by
  rw [enterable_static, mountain]
  rfl

theorem water_needs_boat {config : WorldConfig} (world : World config) (position : Position)
    (water : terrain position config.raw.seed config.raw.baseScale = .ok .water) :
    world.enterable position = .ok world.body.inventory.boat := by
  rw [enterable_static, water]
  rfl

theorem checked_position {config : WorldConfig} (candidate : Position)
    (position : BoxPosition config)
    (admitted : BoxPosition.checked config candidate.x.val candidate.y.val = some position) :
    position.position = candidate := by
  unfold BoxPosition.checked at admitted
  split at admitted
  · rename_i hx
    split at admitted
    · rename_i hy
      cases Option.some.inj admitted
      cases candidate with
      | mk x y =>
        simp only [BoxPosition.position, Position.mk.injEq]
        exact ⟨Subtype.ext (Int.toNat_of_nonneg hx.1), Subtype.ext (Int.toNat_of_nonneg hy.1)⟩
    · contradiction
  · contradiction

theorem step_adjacent {config : WorldConfig} (world next : World config) (action : Action)
    (events : StepResult) (h : world.step action = .ok (next, events)) :
    next.body.position = world.body.position ∨
      ∃ (direction : Direction) (base : TileKind),
        world.body.position.position.translate direction.delta.1 direction.delta.2 =
          some next.body.position.position ∧
        terrain next.body.position.position config.raw.seed config.raw.baseScale = .ok base ∧
        passable base world.body.inventory.boat = true := by
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
      change ∃ (direction : Direction) (base : TileKind),
        world.body.position.position.translate direction.delta.1 direction.delta.2 =
          some position.position ∧
        terrain position.position config.raw.seed config.raw.baseScale = .ok base ∧
        passable base world.body.inventory.boat = true
      rw [checked_position candidate position admitted]
      rw [enterable_static] at entered
      cases located : terrain candidate config.raw.seed config.raw.baseScale with
      | error refusal => simp [located, Except.map] at entered
      | ok base =>
        rw [located] at entered
        exact ⟨direction, base, translated, rfl, Except.ok.inj entered⟩
    | harvested item amount result => left; rw [result]
    | crafted tool inventory recipe result => left; rw [result]
    | ate meal result => left; rw [result]

theorem step_stays {config : WorldConfig} (world next : World config) (action : Action)
    (events : StepResult) (h : world.step action = .ok (next, events))
    (still : action.direction = none) : next.body.position = world.body.position := by
  obtain ⟨active, paid, body, -⟩ := step_active world next action events h
  rw [body]
  obtain ⟨night, outcome⟩ := payAndAct_outcome world action active paid
  rcases outcome with ⟨-, exhausted, -⟩ | ⟨energy, -, performed, -⟩
  · rw [exhausted]
  · cases performed with
    | unchanged same => rw [same]
    | moved direction candidate position picked heading translated admitted entered result =>
      rw [still] at heading
      cases heading
    | harvested item amount result => rw [result]
    | crafted tool inventory recipe result => rw [result]
    | ate meal result => rw [result]

theorem step_passable {config : WorldConfig} (world next : World config) (action : Action)
    (events : StepResult) (h : world.step action = .ok (next, events)) :
    next.body.position = world.body.position ∨
      ∃ base, terrain next.body.position.position config.raw.seed config.raw.baseScale = .ok base ∧
        passable base world.body.inventory.boat = true := by
  rcases step_adjacent world next action events h with same | ⟨-, base, -, located, enters⟩
  · exact Or.inl same
  · exact Or.inr ⟨base, located, enters⟩

theorem step_terrain {config : WorldConfig} (world next : World config) (action : Action)
    (events : StepResult) (h : world.step action = .ok (next, events))
    (moved : next.body.position ≠ world.body.position) :
    terrain next.body.position.position config.raw.seed config.raw.baseScale ≠ .ok .mountain ∧
      (terrain next.body.position.position config.raw.seed config.raw.baseScale = .ok .water →
        world.body.inventory.boat = true) := by
  rcases step_passable world next action events h with same | ⟨base, located, enters⟩
  · exact absurd same moved
  · constructor
    · intro mountain
      rw [mountain] at located
      cases Except.ok.inj located
      simp [passable, TileKind.walkable] at enters
    · intro water
      rw [water] at located
      cases Except.ok.inj located
      exact enters

end AcornVerif.CurrentStep
