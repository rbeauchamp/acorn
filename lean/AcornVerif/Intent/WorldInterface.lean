/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.LeanIntentBridge

/-!
# Intent record: the interface every world meets

Contract 1 of Acorn's mission contract (`docs/mission-contract.md`, section "Contract 1: the
interface every world meets") opens with eight plain sentences that the owner confirmed on
2026-11-03 as the statement of the agent's interface with a world. That restatement is this
record's only source. The agents that work on Acorn wrote it from a research report on the research
of Rich Sutton, Khurram Javed and Oak Lab, and the owner adopted it by confirming it; the owners'
log keeps whose words they are (`AcornVerif.Intent.Decisions.ownersLog`). The record's writer had
read the executing interface's types (`Acorn.Features.Interface`, `Acorn.Features.Percept`) and the
verification kernel (`AcornVerif.Kernel`) before writing it, and none of the host's runs; the record
imports nothing of Acorn's but the bridge to lean-intent, `AcornVerif.LeanIntentBridge`.

The subject, `System`, is one world, one agent and the run that couples them, each world bringing
its own types in `Type`: the world's states, what it shows the agent, its actions, the agent's
memories, and what hosts, viewers and tools may send the run; the reward is a rational number. So
one record speaks of every world, the tile world, an ARC-AGI-3 game and the Microduck alike, and no
field names a type of any one of them. The run is described at each of the places a host could
interpose: what it gives the agent (`given`), which action it hands the world (`applied`), how the
world moves (`moved`), which memory the agent keeps (`kept`), and whether it takes another step
(`goesOn`). A run in which, at some step it takes, a host gives the agent anything but the world's
observation and reward, hands the world anything but the agent's action, moves the world otherwise
than by its dynamics, or begins the next step with any memory but the one the agent's answer
produced, is a subject of this type, and the record refutes it. An intervention whose result
coincides with the faithful run's, or that is written into the world's or the agent's own fields, is
invisible to the record: that those fields are the world's and the agent's is trusted.

The nine properties are the record's reading of sentences 1 to 7: six hold at every step a run takes
under every sequence of outside inputs; `fixedActions` holds at every two of the world's states,
reached or not; `viewerCanStop` holds under every sequence of inputs that is the stop request at
every step from some time on; and `canBegin` asks for one input that lets the run begin. `canBegin`,
the eventual reading of `viewerCanStop` and `fixedActions` at states no run reaches were decided on
the owner's behalf. Sentence 8, that every world Acorn runs meets this one interface, is carried by
the record as a whole: it is one record whose subject admits a world of any types, and that the
system of a world Acorn runs, with Acorn's agent and host, meets it is to be proved world by world,
for the tile world by the fifth step of rbeauchamp/acorn#213 and for ARC-AGI-3 games and Microduck
scenes with their classes (obligation 13 of `docs/mission-contract.md`). Sentence 4's first half
permits and requires nothing: the record carries it by requiring nothing of how much of the state an
observation shows, and `hiddenState_holds` proves that some system that meets the record has a world
showing nothing of its state.

The plain words of each property and consequence were written from the finished predicates; they are
trusted, not proved. The explanation in `AcornVerif.Intent.WorldInterfaceConsequences` records every
consequence it shows as derived from the confirmed restatement; the properties, the consequence, and
the choices of the subject's type and shape, of how sentence 8 is carried and of what the initial
memory holds, decided on the owner's behalf, are recorded with their reasons in the record's
confirmation file, `lean/AcornVerif/Intent/WorldInterface.md`. What the owner confirmed is the eight
sentences; that this record carries them is the agents' judgment, and the owners' log attaches the
owner's answer to this record's revision on that judgment.
-/

namespace AcornVerif.Intent.WorldInterface

open LeanIntent

/-- One world, one agent and the run that couples them. The world is a deterministic state machine
over its own types; the agent turns its memory and what it is given into an action and its next
memory; and the run says, at each step and for each outside input, what it gives the agent, which
action it hands the world, how the world moves, which memory the agent keeps, and whether it takes
the step at all. -/
structure System where
  /-- The world's states: everything its future depends on. -/
  State : Type
  /-- What the world shows the agent. -/
  Obs : Type
  /-- The actions. -/
  Act : Type
  /-- The agent's memories. -/
  Memory : Type
  /-- What hosts, viewers and tools may send the run at a step. -/
  Input : Type
  /-- The world's state when the run begins. -/
  start : State
  /-- The world's observation at a state. -/
  observe : State → Obs
  /-- The reward the world generates at a state, as a rational number. -/
  reward : State → Rat
  /-- Whether the world makes an action available at a state. -/
  available : State → Act → Prop
  /-- The world's own dynamics: its next state after an action, restarts included. -/
  step : State → Act → State
  /-- The agent's memory when the run begins. -/
  initial : Memory
  /-- The agent's answer, from its memory and an observation with a reward: an action and its next
  memory. -/
  act : Memory → Obs × Rat → Act × Memory
  /-- What the viewer sends to ask the run to stop. -/
  stopRequest : Input
  /-- Whether the run takes a step from a state and a memory when sent an input. -/
  goesOn : State → Memory → Input → Bool
  /-- What the run gives the agent to answer, from the world's state, the agent's memory and the
  input. -/
  given : State → Memory → Input → Obs × Rat
  /-- The action the run hands the world, from the state, the memory, the input and the agent's
  answer. -/
  applied : State → Memory → Input → Act → Act
  /-- The world's state after the step, from the state, the memory, the input and the action handed
  to it. -/
  moved : State → Memory → Input → Act → State
  /-- The memory the agent begins the next step with, from the state, the memory, the input and the
  memory its answer produced. -/
  kept : State → Memory → Input → Memory → Memory

namespace System

variable (w : System)

/-- The agent's answer at a step: what it answers when the run gives it what `given` gives. -/
def answer (s : w.State) (m : w.Memory) (e : w.Input) : w.Act × w.Memory :=
  w.act m (w.given s m e)

/-- `w.Reaches ins t s m`: under the outside inputs `ins`, one per step, the run took each of the
first `t` steps and holds the world's state `s` and the agent's memory `m` after them. -/
inductive Reaches (ins : Nat → w.Input) : Nat → w.State → w.Memory → Prop where
  /-- Before any step, the world is at its start and the agent has its initial memory. -/
  | start : Reaches ins 0 w.start w.initial
  /-- A step the run takes leads to the state `moved` gives for the action `applied` hands the
  world, and to the memory `kept` gives for the memory the agent's answer produced. -/
  | next {t : Nat} {s : w.State} {m : w.Memory} :
      Reaches ins t s m → w.goesOn s m (ins t) = true →
      Reaches ins (t + 1) (w.moved s m (ins t) (w.applied s m (ins t) (w.answer s m (ins t)).1))
        (w.kept s m (ins t) (w.answer s m (ins t)).2)

/-- `w.Takes ins t s m`: under the outside inputs `ins`, the run reaches the state `s` and the
memory `m` after `t` steps and takes the next step from them. -/
def Takes (ins : Nat → w.Input) (t : Nat) (s : w.State) (m : w.Memory) : Prop :=
  w.Reaches ins t s m ∧ w.goesOn s m (ins t) = true

end System

/-! ## The properties -/

/-- At every step a run takes, under every sequence of outside inputs, the agent is given the
world's observation of its current state. -/
def seesObservation : Clause System :=
  ⟨"each step, the agent is given the world's observation of its current state", fun w =>
    ∀ ins t s m, w.Takes ins t s m → (w.given s m (ins t)).1 = w.observe s⟩

/-- At every step a run takes, under every sequence of outside inputs, the agent is given the
reward the world generates at its current state. -/
def getsWorldReward : Clause System :=
  ⟨"each step, the agent is given the reward the world generates at its current state", fun w =>
    ∀ ins t s m, w.Takes ins t s m → (w.given s m (ins t)).2 = w.reward s⟩

/-- At every step a run takes, under every sequence of outside inputs, the agent's answer is an
action the world makes available at its current state. -/
def answersAvailable : Clause System :=
  ⟨"each step, the agent answers with an action the world makes available", fun w =>
    ∀ ins t s m, w.Takes ins t s m → w.available s (w.answer s m (ins t)).1⟩

/-- The world makes the same actions available at every one of its states. -/
def fixedActions : Clause System :=
  ⟨"the world makes the same actions available at every one of its states", fun w =>
    ∀ s s' a, w.available s a ↔ w.available s' a⟩

/-- At every step a run takes, under every sequence of outside inputs, the run hands the world the
action the agent answered. -/
def worldGetsAnswer : Clause System :=
  ⟨"each step, the world is handed the action the agent answered", fun w =>
    ∀ ins t s m, w.Takes ins t s m →
      w.applied s m (ins t) (w.answer s m (ins t)).1 = (w.answer s m (ins t)).1⟩

/-- At every step a run takes, under every sequence of outside inputs, the world's next state is
what its own dynamics give, from its current state, for the action the run hands it. -/
def worldMovesByItself : Clause System :=
  ⟨"each step, the world moves by its own dynamics", fun w =>
    ∀ ins t s m, w.Takes ins t s m →
      w.moved s m (ins t) (w.applied s m (ins t) (w.answer s m (ins t)).1) =
        w.step s (w.applied s m (ins t) (w.answer s m (ins t)).1)⟩

/-- At every step a run takes, under every sequence of outside inputs, the agent begins the next
step with the memory its own answer produced. -/
def keepsOwnMemory : Clause System :=
  ⟨"each step, the agent keeps the memory its own answer produced", fun w =>
    ∀ ins t s m, w.Takes ins t s m →
      w.kept s m (ins t) (w.answer s m (ins t)).2 = (w.answer s m (ins t)).2⟩

/-- Under every sequence of outside inputs that, from some step on, sends the viewer's stop request
at every step, there is a time at or after that step at which the run takes no step, having stopped
there or before. -/
def viewerCanStop : Clause System :=
  ⟨"a run the viewer keeps asking to stop stops", fun w =>
    ∀ ins t₀, (∀ t, t₀ ≤ t → ins t = w.stopRequest) →
      ∃ t, t₀ ≤ t ∧ ∀ s m, ¬ w.Takes ins t s m⟩

/-- Some input lets the run take its first step, from the world's start and the agent's initial
memory. -/
def canBegin : Clause System :=
  ⟨"the run can take its first step", fun w => ∃ e, w.goesOn w.start w.initial e = true⟩

/-- A configuration of a run: a system, its outside inputs, a time, a state and a memory. -/
abbrev Configuration : Type 1 :=
  (w : System) × (Nat → w.Input) × Nat × w.State × w.Memory

/-- The intent record of the interface every world meets. -/
def worldInterface : IntentRecord System where
  shape := .value _
  dom := []
  props := [seesObservation, getsWorldReward, answersAvailable, fixedActions, worldGetsAnswer,
    worldMovesByItself, keepsOwnMemory, viewerCanStop, canBegin]
  vocab := [⟨"the run takes a step", Configuration, fun c => c.1.Takes c.2.1 c.2.2.1 c.2.2.2.1
    c.2.2.2.2⟩]

/-- A system meets the record exactly when each of the nine properties holds of it. -/
theorem worldInterface_meets {w : System} :
    worldInterface.Meets w ↔
      seesObservation.holds w ∧ getsWorldReward.holds w ∧ answersAvailable.holds w ∧
        fixedActions.holds w ∧ worldGetsAnswer.holds w ∧ worldMovesByItself.holds w ∧
          keepsOwnMemory.holds w ∧ viewerCanStop.holds w ∧ canBegin.holds w := by
  constructor
  · intro hm
    have h := hm.2
    exact ⟨h _ (by simp [worldInterface]), h _ (by simp [worldInterface]),
      h _ (by simp [worldInterface]), h _ (by simp [worldInterface]),
      h _ (by simp [worldInterface]), h _ (by simp [worldInterface]),
      h _ (by simp [worldInterface]), h _ (by simp [worldInterface]),
      h _ (by simp [worldInterface])⟩
  · intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    refine ⟨(fun d hd => nomatch hd), fun p hp => ?_⟩
    simp only [worldInterface, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
    · exact h8
    · exact h9

/-! ## Worlds, agents and the faithful run -/

/-- A world: its states, what it shows, its actions, its start, observation, reward, available
actions and dynamics. -/
structure World where
  /-- The world's states. -/
  State : Type
  /-- What the world shows the agent. -/
  Obs : Type
  /-- The actions. -/
  Act : Type
  /-- The world's state when a run begins. -/
  start : State
  /-- The world's observation at a state. -/
  observe : State → Obs
  /-- The reward the world generates at a state. -/
  reward : State → Rat
  /-- Whether the world makes an action available at a state. -/
  available : State → Act → Prop
  /-- The world's next state after an action. -/
  step : State → Act → State

/-- An agent for a world whose observations are `Obs` and whose actions are `Act`: its memories,
its initial memory and its answer. -/
structure Agent (Obs Act : Type) where
  /-- The agent's memories. -/
  Memory : Type
  /-- The agent's memory when a run begins. -/
  initial : Memory
  /-- The agent's answer to an observation with a reward, from a memory: an action and its next
  memory. -/
  act : Memory → Obs × Rat → Act × Memory

/-- The faithful run of a world and an agent: it gives the agent the world's observation and reward,
hands the world the agent's action, moves the world by its own dynamics, keeps the memory the
agent's answer produced, and goes on at each step unless the viewer sends `true`, its stop
request. -/
def couple (W : World) (A : Agent W.Obs W.Act) : System where
  State := W.State
  Obs := W.Obs
  Act := W.Act
  Memory := A.Memory
  Input := Bool
  start := W.start
  observe := W.observe
  reward := W.reward
  available := W.available
  step := W.step
  initial := A.initial
  act := A.act
  stopRequest := true
  goesOn _ _ e := !e
  given s _ _ := (W.observe s, W.reward s)
  applied _ _ _ a := a
  moved s _ _ a := W.step s a
  kept _ _ _ m := m

/-- The faithful run of a world that makes the same actions available everywhere and an agent that
always answers with one of them meets the record. -/
theorem couple_meets (W : World) (A : Agent W.Obs W.Act)
    (hfixed : ∀ s s' a, W.available s a ↔ W.available s' a)
    (hanswer : ∀ s m o, W.available s (A.act m o).1) : worldInterface.Meets (couple W A) := by
  refine worldInterface_meets.mpr ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ _ s m _ => hanswer s m _, hfixed, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ _ _ => rfl, fun ins t₀ hstop => ⟨t₀, Nat.le_refl _, fun s m h => ?_⟩,
    ⟨false, rfl⟩⟩
  have hgo : (couple W A).goesOn s m (ins t₀) = true := h.2
  rw [hstop t₀ (Nat.le_refl _)] at hgo
  exact Bool.noConfusion hgo

/-! ## Adequacy -/

/-- A world of two states that moves to the state named by the action, shows its state and gives
reward 0, with both actions available everywhere. -/
def mirror : World where
  State := Bool
  Obs := Bool
  Act := Bool
  start := false
  observe s := s
  reward _ := 0
  available _ _ := True
  step _ a := a

/-- An agent that answers with what it sees and counts its steps. -/
def echo : Agent Bool Bool where
  Memory := Nat
  initial := 0
  act m o := (o.1, m + 1)

/-- The faithful run of `mirror` and `echo`, from which each refuting subject below changes one
part. -/
def base : System := couple mirror echo

theorem base_meets : worldInterface.Meets base :=
  couple_meets mirror echo (fun _ _ _ => Iff.rfl) (fun _ _ _ => trivial)

/-- The outside inputs that never ask the run to stop. -/
def neverStop : Nat → Bool := fun _ => false

/-- Every system takes its first step, from its start and its initial memory, under inputs whose
first one lets it go on there. -/
theorem takes_first {w : System} {ins : Nat → w.Input}
    (hgo : w.goesOn w.start w.initial (ins 0) = true) :
    w.Takes ins 0 w.start w.initial :=
  ⟨.start, hgo⟩

/-- O2: the record has no domain hypothesis, and `base` takes its first step, an instance of its
vocabulary predicate. -/
theorem worldInterface_o2 : O2 worldInterface := by
  refine (o2_correct _).mpr ⟨⟨base, fun _ h => nomatch h⟩, fun p hp => ?_⟩
  simp only [worldInterface, List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp
  exact ⟨⟨base, neverStop, 0, false, (0 : Nat)⟩, takes_first (w := base) rfl⟩

/-- O2 before running: `base` meets the whole record. -/
theorem worldInterface_o2Run : O2Run worldInterface :=
  (o2Run_correct _).mpr ⟨base, base_meets.1, base_meets.2⟩

/-- The run of `base` that gives the agent the negation of the world's state as its observation:
`true` at the start, where the world shows `false`. -/
def showsOther : System := { base with given := fun s _ _ => (!s, 0) }

/-- The run of `base` that gives the agent reward 1, while the world generates 0. -/
def otherReward : System := { base with given := fun s _ _ => (s, 1) }

/-- `base` with no action available. -/
def nothingAvailable : System := { base with available := fun _ _ => False }

/-- `base` with both actions available only at the state `true`. -/
def availableAtTrue : System := { base with available := fun s _ => s = true }

/-- The run of `base` that hands the world the other action than the agent answered. -/
def overridesAction : System := { base with applied := fun _ _ _ a => !a }

/-- The run of `base` that moves the world to the other state than its dynamics give. -/
def movesOtherwise : System := { base with moved := fun _ _ _ a => !a }

/-- The run of `base` that gives the agent back memory 0 after every step. -/
def resetsMemory : System := { base with kept := fun _ _ _ _ => (0 : Nat) }

/-- The run of `base` that takes every step, whatever the viewer sends. -/
def neverStops : System := { base with goesOn := fun _ _ _ => true }

/-- The run of `base` that takes no step, whatever it is sent. -/
def neverBegins : System := { base with goesOn := fun _ _ _ => false }

/-- The run of `neverStops` reaches some state and memory after any number of steps. -/
theorem neverStops_reaches (ins : Nat → Bool) : ∀ t, ∃ s m, neverStops.Reaches ins t s m
  | 0 => ⟨_, _, .start⟩
  | t + 1 =>
    let ⟨_, _, h⟩ := neverStops_reaches ins t
    ⟨_, _, .next h rfl⟩

/-- O3: each property fails of the subject that changes one part of `base`. -/
theorem worldInterface_o3 : O3 worldInterface := by
  refine (o3_correct _).mpr fun p hp => ?_
  simp only [worldInterface, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨showsOther, fun h => Bool.noConfusion (h neverStop 0 _ _ (takes_first rfl))⟩
  · exact ⟨otherReward, fun h => absurd (h neverStop 0 _ _ (takes_first rfl)) (by decide)⟩
  · exact ⟨nothingAvailable, fun h => h neverStop 0 _ _ (takes_first rfl)⟩
  · exact ⟨availableAtTrue, fun h => Bool.noConfusion ((h false true false).mpr rfl)⟩
  · exact ⟨overridesAction, fun h => Bool.noConfusion (h neverStop 0 _ _ (takes_first rfl))⟩
  · exact ⟨movesOtherwise, fun h => Bool.noConfusion (h neverStop 0 _ _ (takes_first rfl))⟩
  · exact ⟨resetsMemory, fun h => Nat.noConfusion (h neverStop 0 _ _ (takes_first rfl))⟩
  · refine ⟨neverStops, fun h => ?_⟩
    obtain ⟨t, -, ht⟩ := h (fun _ => true) 0 (fun _ _ => rfl)
    obtain ⟨s, m, hr⟩ := neverStops_reaches (fun _ => true) t
    exact ht s m ⟨hr, rfl⟩
  · exact ⟨neverBegins, fun ⟨_, h⟩ => Bool.noConfusion h⟩

/-- O4: the subject is declared a plain value, of which O4 asks nothing. Why that shape is chosen is
recorded in the record's confirmation file. -/
theorem worldInterface_o4 : O4 worldInterface := (o4_correct _).mpr trivial

/-- O5 with the widest freedom, which every record meets. -/
theorem worldInterface_o5_widest : O5 worldInterface .widest := o5_widest _

/-- `mirror` with reward 1 everywhere. -/
def mirrorRewardOne : World := { mirror with reward := fun _ => 1 }

/-- The faithful run of `mirrorRewardOne` and `echo`: a second model of the record. -/
def baseRewardOne : System := couple mirrorRewardOne echo

/-- The pair obligation of each property's pair whose only input is trivial, in the class of every
subject: `base` fulfils each property. -/
theorem worldInterface_pairs :
    ∀ c ∈ worldInterface.props, OPair (Pair.whole worldInterface c) (fun _ => True) :=
  fun c hc => (oPair_whole_iff _ _ _).mpr ⟨base, trivial, fun _ => base_meets.2 c hc⟩

/-- An agent that answers every observation with the action `a` and keeps nothing. -/
def always {Obs Act : Type} (a : Act) : Agent Obs Act where
  Memory := Unit
  initial := ()
  act _ _ := (a, ())

/-- **Every world with fixed, nonempty actions can be served.** For every world that makes the same
actions available at every state and makes some action available, an agent exists whose faithful run
with it meets the record: the agent that always answers with that action. -/
theorem every_world_served (W : World) (hfixed : ∀ s s' a, W.available s a ↔ W.available s' a)
    (a₀ : W.Act) (ha₀ : ∀ s, W.available s a₀) :
    ∃ A : Agent W.Obs W.Act, worldInterface.Meets (couple W A) :=
  ⟨always a₀, couple_meets W _ hfixed fun s _ _ => ha₀ s⟩

/-- O5 does not hold with equality: `base` and `baseRewardOne` both meet the record and differ. -/
theorem worldInterface_not_o5_eq : ¬ O5 worldInterface .eq := by
  refine not_o5_eq base_meets
    (couple_meets mirrorRewardOne echo (fun _ _ _ => Iff.rfl) (fun _ _ _ => trivial)) fun h => ?_
  have hr : HEq base.reward baseRewardOne.reward := by rw [h]; rfl
  have hr' : base.reward = baseRewardOne.reward := eq_of_heq hr
  exact absurd (congrFun hr' false) (by decide)

end AcornVerif.Intent.WorldInterface
