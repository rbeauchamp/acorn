import Acorn.Host.Microduck.Action

namespace Acorn.Host.Microduck

structure Keep where
  resend : Nat
  grace : Nat
  transit : Nat
  spaced : 0 < resend

structure Bridge where
  action : Action
  sitting : Bool
  index : Nat
  released : Instant
  sent : Instant

def Bridge.release (index : Nat) (now : Instant) (sitting : Bool) (action : Action) :
    Bridge × List Command :=
  (⟨action, sitting, index, now, now⟩, action.commands sitting)

def Bridge.next (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge) : Nat :=
  bridge.action.next pace keep.transit origin bridge.index bridge.released

def Bridge.ends (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge) : Instant :=
  pace.boundary origin (bridge.next pace keep origin + pace.latency + keep.grace)

def Bridge.tick (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge)
    (now : Instant) : Bridge × Option Command :=
  if bridge.action.velocity ≠ .zero ∧
      now.nanoseconds < (bridge.ends pace keep origin).nanoseconds ∧
      bridge.sent.nanoseconds + keep.resend ≤ now.nanoseconds then
    ({ bridge with sent := now }, some (.move bridge.action.velocity))
  else (bridge, none)

def Bridge.ticks (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge) :
    List Instant → Bridge × List (Instant × Command)
  | [] => (bridge, [])
  | now :: rest =>
    match (bridge.tick pace keep origin now).2 with
    | some command =>
      (((bridge.tick pace keep origin now).1.ticks pace keep origin rest).1,
        (now, command) :: ((bridge.tick pace keep origin now).1.ticks pace keep origin rest).2)
    | none => (bridge.tick pace keep origin now).1.ticks pace keep origin rest

def Bridge.Fresh (keep : Keep) (bridge : Bridge) (now : Instant) : Prop :=
  now.nanoseconds < bridge.sent.nanoseconds + keep.resend

def Bridge.force (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge) :
    Force Action :=
  ⟨some bridge.action, some (bridge.ends pace keep origin)⟩

theorem Bridge.release_state (index : Nat) (now : Instant) (sitting : Bool) (action : Action) :
    (Bridge.release index now sitting action).1 = ⟨action, sitting, index, now, now⟩ ∧
      (Bridge.release index now sitting action).2 = action.commands sitting :=
  ⟨rfl, rfl⟩

theorem Bridge.next_covers (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge) :
    bridge.index < bridge.next pace keep origin ∧
      bridge.released.nanoseconds + bridge.action.duration + keep.transit ≤
        (pace.boundary origin (bridge.next pace keep origin)).nanoseconds :=
  ⟨bridge.action.next_after pace keep.transit origin bridge.index bridge.released,
    bridge.action.next_covers pace keep.transit origin bridge.index bridge.released⟩

theorem Bridge.ends_held (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge) :
    (bridge.ends pace keep origin).nanoseconds =
      (pace.deadline origin (bridge.next pace keep origin)).nanoseconds +
        keep.grace * pace.cycle := by
  unfold Bridge.ends
  rw [pace.boundary_nanoseconds, pace.deadline_nanoseconds, Nat.add_mul, Nat.add_assoc]

theorem Bridge.ends_covers (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge)
    (second : Instant)
    (met : pace.meets origin (bridge.next pace keep origin) second = true) :
    second.nanoseconds < (bridge.ends pace keep origin).nanoseconds := by
  have verdict := (pace.meets_iff origin _ second).mp met
  have held := bridge.ends_held pace keep origin
  have due := pace.deadline_nanoseconds origin (bridge.next pace keep origin)
  omega

theorem Bridge.ends_bounded (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge)
    (sensed : (pace.boundary origin bridge.index).nanoseconds ≤ bridge.released.nanoseconds) :
    (bridge.ends pace keep origin).nanoseconds ≤
      bridge.released.nanoseconds + bridge.action.duration + keep.transit +
        (1 + pace.latency + keep.grace) * pace.cycle := by
  rw [pace.boundary_nanoseconds origin bridge.index] at sensed
  have started : origin.nanoseconds ≤
      bridge.released.nanoseconds + bridge.action.duration + keep.transit := by
    omega
  have within : origin.nanoseconds +
      pace.first origin
        ⟨bridge.released.nanoseconds + bridge.action.duration + keep.transit⟩ * pace.cycle <
      bridge.released.nanoseconds + bridge.action.duration + keep.transit + pace.cycle :=
    pace.first_within origin
      ⟨bridge.released.nanoseconds + bridge.action.duration + keep.transit⟩ started
  have reach : origin.nanoseconds + bridge.next pace keep origin * pace.cycle ≤
      bridge.released.nanoseconds + bridge.action.duration + keep.transit + pace.cycle := by
    unfold Bridge.next Action.next
    rcases Nat.le_total (bridge.index + 1) (pace.first origin
      ⟨bridge.released.nanoseconds + bridge.action.duration + keep.transit⟩) with later | sooner
    · rw [Nat.max_eq_right later]
      omega
    · rw [Nat.max_eq_left sooner, Nat.add_mul, Nat.one_mul]
      omega
  have split : (bridge.next pace keep origin + pace.latency + keep.grace) * pace.cycle =
      bridge.next pace keep origin * pace.cycle + (pace.latency + keep.grace) * pace.cycle := by
    rw [Nat.add_assoc, Nat.add_mul]
  have whole : (1 + pace.latency + keep.grace) * pace.cycle =
      pace.cycle + (pace.latency + keep.grace) * pace.cycle := by
    rw [Nat.add_assoc, Nat.add_mul, Nat.one_mul]
  unfold Bridge.ends
  rw [pace.boundary_nanoseconds]
  omega

theorem Bridge.release_fresh (keep : Keep) (index : Nat) (now : Instant) (sitting : Bool)
    (action : Action) : (Bridge.release index now sitting action).1.Fresh keep now :=
  Nat.lt_add_of_pos_right keep.spaced

theorem Bridge.tick_command (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge)
    (now : Instant) (command : Command)
    (sent : (bridge.tick pace keep origin now).2 = some command) :
    command = .move bridge.action.velocity ∧ bridge.action.velocity ≠ .zero ∧
      now.nanoseconds < (bridge.ends pace keep origin).nanoseconds := by
  unfold Bridge.tick at sent
  split at sent
  · rename_i due
    exact ⟨(Option.some.inj sent).symm, due.1, due.2.1⟩
  · cases sent

theorem Bridge.tick_keeps (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge)
    (now : Instant) :
    (bridge.tick pace keep origin now).1.action = bridge.action ∧
      (bridge.tick pace keep origin now).1.sitting = bridge.sitting ∧
      (bridge.tick pace keep origin now).1.next pace keep origin =
        bridge.next pace keep origin ∧
      (bridge.tick pace keep origin now).1.ends pace keep origin =
        bridge.ends pace keep origin := by
  unfold Bridge.tick
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem Bridge.tick_ended (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge)
    (now : Instant)
    (ended : (bridge.ends pace keep origin).nanoseconds ≤ now.nanoseconds) :
    bridge.tick pace keep origin now = (bridge, none) := by
  unfold Bridge.tick
  split
  · rename_i due
    exact absurd due.2.1 (Nat.not_lt.mpr ended)
  · rfl

theorem Bridge.tick_fresh (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge)
    (now : Instant) (moving : bridge.action.velocity ≠ .zero)
    (inside : now.nanoseconds < (bridge.ends pace keep origin).nanoseconds) :
    (bridge.tick pace keep origin now).1.Fresh keep now := by
  unfold Bridge.tick
  split
  · exact Nat.lt_add_of_pos_right keep.spaced
  · rename_i idle
    show now.nanoseconds < bridge.sent.nanoseconds + keep.resend
    have late : ¬bridge.sent.nanoseconds + keep.resend ≤ now.nanoseconds :=
      fun old => idle ⟨moving, inside, old⟩
    omega

theorem Bridge.Fresh.age {keep : Keep} {bridge : Bridge} {now : Instant}
    (fresh : bridge.Fresh keep now) (later : Instant) (gap limit : Nat)
    (next : later.nanoseconds ≤ now.nanoseconds + gap) (within : keep.resend + gap ≤ limit) :
    later.nanoseconds < bridge.sent.nanoseconds + limit := by
  unfold Bridge.Fresh at fresh
  omega

theorem Bridge.ticks_keeps (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge)
    (readings : List Instant) :
    (bridge.ticks pace keep origin readings).1.action = bridge.action ∧
      (bridge.ticks pace keep origin readings).1.sitting = bridge.sitting ∧
      (bridge.ticks pace keep origin readings).1.next pace keep origin =
        bridge.next pace keep origin ∧
      (bridge.ticks pace keep origin readings).1.ends pace keep origin =
        bridge.ends pace keep origin := by
  induction readings generalizing bridge with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons now rest ih =>
    have kept := bridge.tick_keeps pace keep origin now
    have later := ih (bridge.tick pace keep origin now).1
    unfold Bridge.ticks
    split
    · exact ⟨later.1.trans kept.1, later.2.1.trans kept.2.1, later.2.2.1.trans kept.2.2.1,
        later.2.2.2.trans kept.2.2.2⟩
    · exact ⟨later.1.trans kept.1, later.2.1.trans kept.2.1, later.2.2.1.trans kept.2.2.1,
        later.2.2.2.trans kept.2.2.2⟩

theorem Bridge.ticks_sent (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge)
    (readings : List Instant) (entry : Instant × Command)
    (member : entry ∈ (bridge.ticks pace keep origin readings).2) :
    entry.2 = .move bridge.action.velocity ∧ bridge.action.velocity ≠ .zero ∧
      entry.1.nanoseconds < (bridge.ends pace keep origin).nanoseconds := by
  induction readings generalizing bridge with
  | nil => cases member
  | cons now rest ih =>
    have kept := bridge.tick_keeps pace keep origin now
    unfold Bridge.ticks at member
    split at member
    · rename_i command sent
      rcases List.mem_cons.mp member with rfl | later
      · exact bridge.tick_command pace keep origin now command sent
      · have found := ih (bridge.tick pace keep origin now).1 later
        rw [kept.1, kept.2.2.2] at found
        exact found
    · have found := ih (bridge.tick pace keep origin now).1 member
      rw [kept.1, kept.2.2.2] at found
      exact found

theorem Bridge.force_named (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge)
    (rest : Option Action) (now : Instant) :
    (bridge.force pace keep origin).named rest now =
      if now.nanoseconds < (bridge.ends pace keep origin).nanoseconds then some bridge.action
      else rest :=
  (bridge.force pace keep origin).named_lapse rest now (bridge.ends pace keep origin) rfl

theorem Bridge.release_named (pace : Pace) (keep : Keep) (origin : Instant)
    (rest : Option Action) (prior : Force Action) (index : Nat) (now : Instant)
    (sitting : Bool) (action : Action) (later : Instant)
    (after : now.nanoseconds < later.nanoseconds)
    (inside : later.nanoseconds <
      ((Bridge.release index now sitting action).1.ends pace keep origin).nanoseconds) :
    (pace.outcome origin rest (Standing.during prior index now
      ((Bridge.release index now sitting action).1.force pace keep origin) later)
        later).action = some action := by
  rw [pace.step_action origin rest prior index now _ later]
  split
  · rename_i early
    exact absurd early (Nat.not_le.mpr after)
  · rw [Bridge.force_named]
    split
    · rfl
    · rename_i ended
      exact absurd inside ended

theorem Bridge.ticks_named (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge)
    (rest : Option Action) (readings : List Instant) (entry : Instant × Command)
    (member : entry ∈ (bridge.ticks pace keep origin readings).2) :
    (pace.outcome origin rest (Standing.idle (bridge.force pace keep origin))
        entry.1).action = some bridge.action ∧
      entry.2 = .move bridge.action.velocity := by
  have sent := bridge.ticks_sent pace keep origin readings entry member
  rw [pace.outcome_action origin rest]
  show (bridge.force pace keep origin).named rest entry.1 = some bridge.action ∧ _
  rw [Bridge.force_named]
  split
  · exact ⟨rfl, sent.1⟩
  · rename_i ended
    exact absurd sent.2.2 ended

theorem Bridge.tick_lapsed (pace : Pace) (keep : Keep) (origin : Instant) (bridge : Bridge)
    (rest : Option Action) (now : Instant)
    (ended : (bridge.ends pace keep origin).nanoseconds ≤ now.nanoseconds) :
    (pace.outcome origin rest (Standing.idle (bridge.force pace keep origin)) now).action =
        rest ∧
      bridge.tick pace keep origin now = (bridge, none) := by
  rw [pace.outcome_action origin rest]
  show (bridge.force pace keep origin).named rest now = rest ∧ _
  rw [Bridge.force_named]
  split
  · rename_i inside
    exact absurd inside (Nat.not_lt.mpr ended)
  · exact ⟨rfl, bridge.tick_ended pace keep origin now ended⟩

theorem Bridge.fault_named (pace : Pace) (keep : Keep) (origin : Instant)
    (rest : Option Action) (bridge : Bridge) (index : Nat) (released : Instant)
    (chosen : Force Action) (now : Instant)
    (fault : (pace.outcome origin rest
      (Standing.during (bridge.force pace keep origin) index released chosen now)
        now).fault = true) :
    (pace.outcome origin rest
        (Standing.during (bridge.force pace keep origin) index released chosen now)
          now).action =
      if now.nanoseconds < (bridge.ends pace keep origin).nanoseconds then some bridge.action
      else rest := by
  have awaited := ((pace.step_fault origin rest (bridge.force pace keep origin) index
    released chosen now).mp fault).2
  rw [pace.step_action origin rest (bridge.force pace keep origin) index released chosen now]
  split
  · exact bridge.force_named pace keep origin rest now
  · rename_i passed
    exact absurd awaited passed

inductive Reply where
  | pending
  | accepted
  | refused
  deriving DecidableEq

inductive Outcome where
  | executed
  | unchanged
  | refused
  | unexecuted
  | unanswered
  deriving DecidableEq

def Action.outcome (action : Action) (sitting : Bool) (reply : Reply) (shown : Bool) :
    Outcome :=
  match reply with
  | .refused => .refused
  | .pending => .unanswered
  | .accepted =>
    if shown then
      if action.intent = .posture sitting then .unchanged else .executed
    else .unexecuted

def Bridge.outcome (bridge : Bridge) (reply : Reply) (shown : Bool) : Outcome :=
  bridge.action.outcome bridge.sitting reply shown

def Action.Postural (action : Action) : Prop :=
  action.intent = .posture true ∨ action.intent = .posture false

def Action.Judged (action : Action) (sitting : Bool) (reply : Reply) (shown : Bool)
    (outcome : Outcome) : Prop :=
  (outcome = .refused ∧ reply = .refused) ∨
    (outcome = .unanswered ∧ reply = .pending) ∨
    (outcome = .unexecuted ∧ reply = .accepted ∧ shown = false) ∨
    (outcome = .unchanged ∧ reply = .accepted ∧ shown = true ∧
      action.Postural ∧ Command.perform .sitToggle ∉ action.commands sitting) ∨
    (outcome = .executed ∧ reply = .accepted ∧ shown = true ∧
      ¬(action.Postural ∧ Command.perform .sitToggle ∉ action.commands sitting))

theorem Action.outcome_judged (action : Action) (sitting : Bool) (reply : Reply)
    (shown : Bool) (outcome : Outcome) :
    action.outcome sitting reply shown = outcome ↔
      action.Judged sitting reply shown outcome := by
  unfold Action.Judged Action.Postural
  cases action <;> cases sitting <;> cases reply <;> cases shown <;> cases outcome <;> decide

theorem Action.outcome_accepted (action : Action) (sitting : Bool) (reply : Reply)
    (shown : Bool) :
    (action.outcome sitting reply shown ≠ .refused ∧
        action.outcome sitting reply shown ≠ .unanswered) ↔ reply = .accepted := by
  cases action <;> cases sitting <;> cases reply <;> cases shown <;> decide

theorem Action.outcome_reply (action : Action) (sitting : Bool) (reply : Reply)
    (shown : Bool) :
    (action.outcome sitting reply shown = .refused ↔ reply = .refused) ∧
      (action.outcome sitting reply shown = .unanswered ↔ reply = .pending) := by
  cases action <;> cases sitting <;> cases reply <;> cases shown <;> decide

theorem Bridge.release_outcome (index : Nat) (now : Instant) (sitting : Bool)
    (action : Action) (reply : Reply) (shown : Bool) (outcome : Outcome) :
    (Bridge.release index now sitting action).1.outcome reply shown = outcome ↔
      action.Judged sitting reply shown outcome :=
  action.outcome_judged sitting reply shown outcome

namespace Declared

def pace : Pace := ⟨200000000, 1, by decide, by decide⟩

def keep : Keep := ⟨100000000, 2, 10000000, by decide⟩

def expiry : Nat := 500000000

def gap : Nat := 50000000

def rest : Action := .still

end Declared

theorem keep_declared :
    Declared.keep.resend + Declared.gap + Declared.keep.transit < Declared.expiry := by
  decide

theorem rest_declared :
    Declared.rest.velocity = .zero ∧ Declared.rest.duration = 0 := by
  decide

end Acorn.Host.Microduck
