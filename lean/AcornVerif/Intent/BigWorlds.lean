/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.WorldInterface
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Embedding.Basic

/-!
# Intent record: what makes a class of worlds big

Contract 2 of Acorn's mission contract (`docs/mission-contract.md`, section "Contract 2: what makes
a class of worlds big") opens with seven plain sentences that the owner confirmed on 2026-11-03 as
the statement of what makes a class of worlds big. That restatement is this record's only source.
The agents that work on Acorn wrote it from a research report on the research of Rich Sutton,
Khurram Javed and Oak Lab, and the owner adopted it by confirming it; the owners' log keeps whose
words they are (`AcornVerif.Intent.Decisions.ownersLog`). The record's writer had read the mission
contract's design of the contract, the verification kernel's definitions of a class, a visit,
concealment, covering and a campaign (`AcornVerif.Kernel.WorldClass`, `AcornVerif.Kernel.visits`,
`AcornVerif.Kernel.Conceals`, `AcornVerif.Kernel.Covered`, `AcornVerif.Kernel.campaign`) and the
statement of `AcornVerif.Kernel.witness_big`, before writing it; the record imports nothing of
Acorn's but contract 1's record, `AcornVerif.Intent.WorldInterface`, and the bridge to lean-intent.

The subject, `Pairing`, is a class of worlds together with an agent, because bigness belongs to the
pair (sentence 2). The class brings its own types in `Type`: what its worlds show the agent, the
actions, and the index of its members; each member is a world of contract 1's interface over those
types, with every action available at every state, and with its goal; the class fixes how many
steps an attempt takes and how many members it presents in turn in one stream, the slots of its
campaign. The agent is an agent of contract 1's interface for those types. Each member, run with
the agent in attempts that restart at the member's start while the agent keeps its memory, is a
system that contract 1's record admits (`Pairing.system_meets`), so the record speaks of any class
of such worlds, the tile world's, an ARC-AGI-3 game's or the Microduck's, and names no type of any
of them.

The six properties are the record's reading of the seven sentences. Conditions (a) to (d) of
sentence 4 are `goalsReachable`, `goalsConcealed`, `frozenShareSmall` and `beyondCapacity`;
sentence 6 is `successShows` and `learningPays`. Sentences 1, 2, 3, 5 and 7 state no requirement of
their own beyond these: sentence 1's agent that can neither fully perceive the world nor represent a
solution everywhere, and that is smaller than its task needs, is what (b), (c) and (d) require;
sentence 2's pair is the subject, and (d) reads the agent; sentence 3's continued learning that does
better than every fixed solution is what `learningPays` requires; sentence 4's conditions are the
four properties named above; sentence 5's today's class meets three of them, and (d) is the target
every class must meet before the record calls it big; and sentence 7 is the record's scope, one
record over every class of contract 1's worlds. Which consequence of the record carries each of
those sentences is proved in `AcornVerif.Intent.BigWorldsConsequences`.

The plain words of each property and consequence were written from the finished predicates; they are
trusted, not proved. The explanation in `AcornVerif.Intent.BigWorldsConsequences` records every
consequence it shows as derived from the confirmed restatement; the choices decided on the owner's
behalf (the subject's type and shape, how each sentence is carried, the threshold of (c) and the
counting form of (d)) are recorded with their reasons in the record's confirmation file,
`lean/AcornVerif/Intent/BigWorlds.md`. What the owner confirmed is the seven sentences; that this
record carries them is the agents' judgment, and the owners' log attaches the owner's answer to this
record's revision on that judgment.
-/

namespace AcornVerif.Intent.BigWorlds

open LeanIntent
open AcornVerif.Intent.WorldInterface (World Agent System couple worldInterface)

/-- A world of a class, over the class's observations `Obs` and actions `Act`: its states, its
start, what it shows the agent, the reward it generates, its dynamics, and its goal. Every action is
available at every one of its states. -/
structure Member (Obs Act : Type) where
  /-- The world's states. -/
  State : Type
  /-- The state every attempt starts from. -/
  start : State
  /-- The world's observation at a state. -/
  observe : State → Obs
  /-- The reward the world generates at a state, as a rational number. -/
  reward : State → Rat
  /-- The world's own dynamics: its next state after an action. -/
  step : State → Act → State
  /-- The states that reach the member's goal. -/
  goal : State → Prop

/-- A class of worlds and the agent that faces it: what the worlds show and the actions, the index
of the members and each member's world, how many steps an attempt takes, how many members the class
presents in turn in one stream (the slots of its campaign), and the agent. -/
structure Pairing where
  /-- What the class's worlds show the agent. -/
  Obs : Type
  /-- The actions. -/
  Act : Type
  /-- The members of the class. -/
  Index : Type
  /-- Each member's world and goal. -/
  member : Index → Member Obs Act
  /-- How many steps an attempt takes: the goal must be reached after one to `length` steps. -/
  length : Nat
  /-- How many members the class presents in turn in one stream. -/
  slots : Nat
  /-- The agent. -/
  agent : Agent Obs Act

namespace Member

variable {Obs Act : Type} (w : Member Obs Act)

/-- What the agent perceives at a state: the world's observation and its reward. -/
def percept (s : w.State) : Obs × Rat := (w.observe s, w.reward s)

/-- The state after `t` steps from the start, under the actions `actions`, one per step. -/
def path (actions : Nat → Act) : Nat → w.State
  | 0 => w.start
  | t + 1 => w.step (path actions t) (actions t)

/-- One action sequence reaches the goal within an attempt of `len` steps: after one to `len` of its
steps from the start. -/
def MetBy (len : Nat) (actions : Nat → Act) : Prop :=
  ∃ t, 1 ≤ t ∧ t ≤ len ∧ w.goal (w.path actions t)

/-- One decision from the state and memory `x`: the agent answers what it perceives at the state,
the world moves by its own dynamics on that action, and the agent keeps the memory its answer
produced. -/
def turn (A : Agent Obs Act) (x : w.State × A.Memory) : w.State × A.Memory :=
  (w.step x.1 (A.act x.2 (w.percept x.1)).1, (A.act x.2 (w.percept x.1)).2)

/-- The state and the agent's memory after `t` decisions of an attempt that starts at the world's
start with the agent's memory `memory`, each decision as `turn` takes it. -/
def within (A : Agent Obs Act) (memory : A.Memory) : Nat → w.State × A.Memory
  | 0 => (w.start, memory)
  | t + 1 => w.turn A (within A memory t)

/-- The agent reaches the goal in an attempt of `len` steps that it starts with the memory `memory`:
after one to `len` of its decisions. -/
def Reached (len : Nat) (A : Agent Obs Act) (memory : A.Memory) : Prop :=
  ∃ t, 1 ≤ t ∧ t ≤ len ∧ w.goal (w.within A memory t).1

/-- The agent's memory after an attempt of `len` steps that it starts with the memory `memory`:
the attempt takes `len + 1` decisions, the last at the attempt's last state, and the world then
returns to its start while the agent keeps that memory. -/
def after (len : Nat) (A : Agent Obs Act) (memory : A.Memory) : A.Memory :=
  (w.within A memory (len + 1)).2

/-- The member's world of contract 1's interface in attempts of `len` steps: its state is the
member's state with the number of steps taken in the current attempt; it shows the member's
observation and reward, makes every action available, moves by the member's dynamics within an
attempt and returns to the member's start, by its own dynamics, after the attempt's last
decision. -/
def world (len : Nat) : World where
  State := w.State × Nat
  Obs := Obs
  Act := Act
  start := (w.start, 0)
  observe s := w.observe s.1
  reward s := w.reward s.1
  available _ _ := True
  step s a := if s.2 < len then (w.step s.1 a, s.2 + 1) else (w.start, 0)

end Member

namespace Pairing

variable (p : Pairing)

/-- The run of member `i` with the agent, as a system of contract 1's interface: the faithful run of
the member's world in attempts and the agent. -/
def system (i : p.Index) : System := couple ((p.member i).world p.length) p.agent

/-- **Every member is a world of contract 1's interface.** Each member, run with the agent in
attempts, is a system that contract 1's record admits. -/
theorem system_meets (i : p.Index) : worldInterface.Meets (p.system i) :=
  WorldInterface.couple_meets _ _ (fun _ _ _ => Iff.rfl) (fun _ _ _ => trivial)

/-- The agent `A`'s memory at the start of its attempt number `n` (counting from 0) in member `i`:
its initial memory before the first, and after each attempt the memory it kept. -/
def memoryAt (A : Agent p.Obs p.Act) (i : p.Index) : Nat → A.Memory
  | 0 => A.initial
  | n + 1 => (p.member i).after p.length A (memoryAt A i n)

/-- The agent `A` solves member `i` on its attempt number `n`: in that attempt of the agent's run in
that member, it reaches the member's goal. -/
def SolvesOn (A : Agent p.Obs p.Act) (i : p.Index) (n : Nat) : Prop :=
  (p.member i).Reached p.length A (p.memoryAt A i n)

/-- One action sequence reaches the goals of at most `k` members within one attempt: every finite
set of members whose goals it reaches has at most `k` elements. -/
def Covered (k : Nat) : Prop :=
  ∀ (actions : Nat → p.Act) (T : Finset p.Index),
    (∀ i ∈ T, (p.member i).MetBy p.length actions) → T.card ≤ k

end Pairing

/-- An agent that keeps nothing from its experience: its next memory is a function of its memory
alone, whatever it perceives, though its action may read what it perceives. -/
def KeepsNothing {Obs Act : Type} (A : Agent Obs Act) : Prop :=
  ∃ advance : A.Memory → A.Memory, ∀ m o, (A.act m o).2 = advance m

/-- The agent's memory takes at most `2 ^ b` values: it embeds in the bit strings of width `b`. -/
def MemoryWithin {Obs Act : Type} (A : Agent Obs Act) (b : Nat) : Prop :=
  Nonempty (A.Memory ↪ Fin (2 ^ b))

namespace Pairing

variable (p : Pairing)

/-- The agent `A`'s memory after it meets, in turn, one attempt in each member of `members`,
starting with the memory `memory` and keeping its memory from one attempt to the next. -/
def through (A : Agent p.Obs p.Act) (members : List p.Index) (memory : A.Memory) : A.Memory :=
  members.foldl (fun m i => (p.member i).after p.length A m) memory

/-- The class's campaign under the assignment `σ` of a member to each slot: one stream in which the
agent `A` meets the slots' members in turn, one attempt each, cycle after cycle, never restarting.
`p.cycleStart A σ c` is the agent's memory at the start of cycle `c` (counting from 0). -/
def cycleStart (A : Agent p.Obs p.Act) (σ : Fin p.slots → p.Index) : Nat → A.Memory
  | 0 => A.initial
  | c + 1 => p.through A (List.ofFn σ) (cycleStart A σ c)

/-- In the campaign under `σ`, the agent `A` solves slot `s` on cycle `c`: in that slot's attempt of
that cycle, it reaches the goal of the member assigned to the slot. -/
def SolvesSlot (A : Agent p.Obs p.Act) (σ : Fin p.slots → p.Index) (c : Nat) (s : Fin p.slots) :
    Prop :=
  (p.member (σ s)).Reached p.length A (p.through A ((List.ofFn σ).take s) (p.cycleStart A σ c))

end Pairing

/-! ## The properties -/

/-- (a) Every member's goal can be reached within one attempt from where its attempt starts: some
action sequence reaches it after one to `length` steps from the member's start. -/
def goalsReachable : Clause Pairing :=
  ⟨"(a) every goal can be reached within one attempt from where the attempt starts", fun p =>
    ∀ i, ∃ actions, (p.member i).MetBy p.length actions⟩

/-- (b) Until a goal is first reached, nothing the agent perceives tells it which member it faces:
for every two members and every action sequence, at every time of an attempt before either member's
goal is reached, the two members show the same observation and reward. -/
def goalsConcealed : Clause Pairing :=
  ⟨"(b) until a goal is first reached, nothing the agent perceives tells it which member it faces",
    fun p => ∀ i j (actions : Nat → p.Act) t, t ≤ p.length →
      (∀ t', 1 ≤ t' → t' ≤ t → ¬ (p.member i).goal ((p.member i).path actions t') ∧
        ¬ (p.member j).goal ((p.member j).path actions t')) →
      (p.member i).percept ((p.member i).path actions t) =
        (p.member j).percept ((p.member j).path actions t)⟩

/-- (c) An agent that keeps nothing from its experience solves only a small share of the class on
any attempt: there is a number `k`, smaller than the size of some finite set of members, such that
every agent that keeps nothing solves at most `k` members on each of its attempts. -/
def frozenShareSmall : Clause Pairing :=
  ⟨"(c) an agent that keeps nothing solves on any attempt at most a number of members smaller \
    than the class", fun p =>
    ∃ k, (∃ S : Finset p.Index, k < S.card) ∧
      ∀ F : Agent p.Obs p.Act, KeepsNothing F → ∀ n (T : Finset p.Index),
        (∀ i ∈ T, p.SolvesOn F i n) → T.card ≤ k⟩

/-- (d) The class poses more separate problems than the agent's memory can hold solutions to at
once, in Acorn's counting form: for some width `b` of the agent's memory, some number `k` of members
whose goals one action sequence can reach within an attempt at most, and some finite set `S` of
members, `2 ^ b * k ^ slots < card S ^ slots`. -/
def beyondCapacity : Clause Pairing :=
  ⟨"(d) the class poses more separate problems than the agent's memory can hold solutions to at \
    once", fun p =>
    ∃ (b k : Nat) (S : Finset p.Index), MemoryWithin p.agent b ∧ p.Covered k ∧
      2 ^ b * k ^ p.slots < S.card ^ p.slots⟩

/-- Success shows in what the agent perceives: one test of what the agent perceives, the same for
every member, tells at every state of an attempt whether the member's goal is reached there. -/
def successShows : Clause Pairing :=
  ⟨"success shows in what the agent perceives", fun p =>
    ∃ signal : p.Obs × Rat → Prop, ∀ i (actions : Nat → p.Act) t, t ≤ p.length →
      (signal ((p.member i).percept ((p.member i).path actions t)) ↔
        (p.member i).goal ((p.member i).path actions t))⟩

/-- Continued learning can do better than any fixed solution: some agent solves, on one of its
attempts, more members than any agent that keeps nothing solves on any attempt. -/
def learningPays : Clause Pairing :=
  ⟨"continued learning can do better than every agent that keeps nothing", fun p =>
    ∃ (A : Agent p.Obs p.Act) (n : Nat) (T : Finset p.Index), (∀ i ∈ T, p.SolvesOn A i n) ∧
      ∀ F : Agent p.Obs p.Act, KeepsNothing F → ∀ n' (T' : Finset p.Index),
        (∀ i ∈ T', p.SolvesOn F i n') → T'.card < T.card⟩

/-- An agent's attempt in a member: a class, an agent for it, a member and an attempt's number. -/
abbrev Attempt : Type 1 := (p : Pairing) × Agent p.Obs p.Act × p.Index × Nat

/-- An action sequence tried in a member: a class, an action sequence and a member. -/
abbrev Trial : Type 1 := (p : Pairing) × (Nat → p.Act) × p.Index

/-- An agent of a class. -/
abbrev AgentOf : Type 1 := (p : Pairing) × Agent p.Obs p.Act

/-- The intent record of what makes a class of worlds big. -/
def bigWorlds : IntentRecord Pairing where
  shape := .value _
  dom := []
  props := [goalsReachable, goalsConcealed, frozenShareSmall, beyondCapacity, successShows,
    learningPays]
  vocab := [
    ⟨"the agent solves a member on an attempt", Attempt,
      fun c => c.1.SolvesOn c.2.1 c.2.2.1 c.2.2.2⟩,
    ⟨"an action sequence reaches a member's goal within an attempt", Trial,
      fun c => (c.1.member c.2.2).MetBy c.1.length c.2.1⟩,
    ⟨"the agent keeps nothing from its experience", AgentOf, fun c => KeepsNothing c.2⟩]

/-- A pairing meets the record exactly when each of the six properties holds of it. -/
theorem bigWorlds_meets {p : Pairing} :
    bigWorlds.Meets p ↔
      goalsReachable.holds p ∧ goalsConcealed.holds p ∧ frozenShareSmall.holds p ∧
        beyondCapacity.holds p ∧ successShows.holds p ∧ learningPays.holds p := by
  constructor
  · intro hm
    have h := hm.2
    exact ⟨h _ (by simp [bigWorlds]), h _ (by simp [bigWorlds]), h _ (by simp [bigWorlds]),
      h _ (by simp [bigWorlds]), h _ (by simp [bigWorlds]), h _ (by simp [bigWorlds])⟩
  · intro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨(fun d hd => nomatch hd), fun c hc => ?_⟩
    simp only [bigWorlds, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6

/-! ## What concealment and covering give every agent -/

namespace Member

variable {Obs Act : Type} (w : Member Obs Act)

/-- The actions the agent `A` takes in an attempt it starts with the memory `memory`. -/
def actions (A : Agent Obs Act) (memory : A.Memory) (t : Nat) : Act :=
  (A.act (w.within A memory t).2 (w.percept (w.within A memory t).1)).1

/-- An attempt's states are the path of the actions the agent takes in it. -/
theorem within_path (A : Agent Obs Act) (memory : A.Memory) :
    ∀ t, (w.within A memory t).1 = w.path (w.actions A memory) t
  | 0 => rfl
  | t + 1 => by
    change w.step (w.within A memory t).1 (w.actions A memory t) =
      w.step (w.path (w.actions A memory) t) (w.actions A memory t)
    rw [within_path A memory t]

/-- An agent whose next memory reads nothing it perceives has, after `t` decisions of an attempt,
the memory its advance gives `t` times, in every member. -/
theorem within_keepsNothing {A : Agent Obs Act} {advance : A.Memory → A.Memory}
    (law : ∀ m o, (A.act m o).2 = advance m) (memory : A.Memory) :
    ∀ t, (w.within A memory t).2 = advance^[t] memory
  | 0 => rfl
  | t + 1 => by
    change (A.act (w.within A memory t).2 _).2 = advance^[t + 1] memory
    rw [law, within_keepsNothing law memory t, Function.iterate_succ_apply']

end Member

namespace Pairing

variable {p : Pairing}

/-- **Agreement before success.** Under concealment, an agent that starts an attempt with the same
memory in two members takes the same actions and keeps the same memories in both, at every
decision up to one past the attempt's last state, as long as neither member's goal has been
reached. -/
theorem within_agree (hb : goalsConcealed.holds p) (i j : p.Index) (A : Agent p.Obs p.Act)
    (memory : A.Memory) :
    ∀ t, t ≤ p.length + 1 →
      (∀ t', 1 ≤ t' → t' < t → ¬ (p.member i).goal ((p.member i).within A memory t').1 ∧
        ¬ (p.member j).goal ((p.member j).within A memory t').1) →
      ∀ t' ≤ t, (p.member j).within A memory t' =
        ((p.member j).path ((p.member i).actions A memory) t',
          ((p.member i).within A memory t').2)
  | 0, _, _, t', ht' => by
    obtain rfl : t' = 0 := Nat.le_zero.mp ht'
    rfl
  | t + 1, hlen, hun, t', ht' => by
    have ih := within_agree hb i j A memory t (by omega)
      (fun t'' h1 h2 => hun t'' h1 (by omega))
    rcases Nat.lt_or_ge t' (t + 1) with hlt | hge
    · exact ih t' (by omega)
    obtain rfl : t' = t + 1 := by omega
    have hcur := ih t le_rfl
    have hpercept := hb i j ((p.member i).actions A memory) t (by omega) (fun t'' h1 h2 => by
      have hu := hun t'' h1 (by omega)
      rw [(p.member i).within_path A memory t'', ih t'' h2] at hu
      exact hu)
    rw [← (p.member i).within_path A memory t] at hpercept
    change (p.member j).turn A ((p.member j).within A memory t) = _
    rw [hcur]
    change ((p.member j).step _ (A.act _ ((p.member j).percept _)).1,
      (A.act _ ((p.member j).percept _)).2) = _
    rw [← hpercept]
    rfl

/-- **Covering from one memory.** Under concealment, if one action sequence reaches the goals of at
most `k` members within an attempt, an agent that starts an attempt with one memory reaches, in
that attempt, the goals of at most `k` members, whatever it has learned before. -/
theorem covered_from (hb : goalsConcealed.holds p) {k : Nat} (hk : p.Covered k)
    (A : Agent p.Obs p.Act) (memory : A.Memory) (T : Finset p.Index)
    (hT : ∀ i ∈ T, (p.member i).Reached p.length A memory) : T.card ≤ k := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | hne
  · exact Nat.zero_le _
  let first : p.Index → Nat := fun i =>
    if h : (p.member i).Reached p.length A memory then Nat.find h else 0
  obtain ⟨i₀, hi₀, hmax⟩ := T.exists_max_image first hne
  apply hk ((p.member i₀).actions A memory) T
  intro i hi
  have hr := hT i hi
  have hfirst : first i = Nat.find hr := dite_eq_left hr
  obtain ⟨h1, h2, hgoal⟩ := Nat.find_spec hr
  have hr₀ := hT i₀ hi₀
  have hfirst₀ : first i₀ = Nat.find hr₀ := dite_eq_left hr₀
  have hle : Nat.find hr ≤ Nat.find hr₀ := hfirst ▸ hfirst₀ ▸ hmax i hi
  have hagree := within_agree hb i₀ i A memory (Nat.find hr) (by omega) (fun t' h1' h2' =>
    ⟨fun hg => Nat.find_min hr₀ (by omega) ⟨h1', by omega, hg⟩,
      fun hg => Nat.find_min hr h2' ⟨h1', by omega, hg⟩⟩) (Nat.find hr) le_rfl
  refine ⟨Nat.find hr, h1, h2, ?_⟩
  rw [hagree] at hgoal
  exact hgoal

/-- An agent that keeps nothing starts each attempt with the same memory in every member. -/
theorem memoryAt_keepsNothing {A : Agent p.Obs p.Act} (hA : KeepsNothing A) (i j : p.Index) :
    ∀ n, p.memoryAt A i n = p.memoryAt A j n
  | 0 => rfl
  | n + 1 => by
    have ih := memoryAt_keepsNothing hA i j n
    obtain ⟨advance, law⟩ := hA
    change ((p.member i).within A (p.memoryAt A i n) (p.length + 1)).2 =
      ((p.member j).within A (p.memoryAt A j n) (p.length + 1)).2
    rw [(p.member i).within_keepsNothing law, (p.member j).within_keepsNothing law, ih]

/-- **Frozen agents are covered.** Under concealment, with one action sequence reaching the goals of
at most `k` members within an attempt, every agent that keeps nothing solves at most `k` members on
each of its attempts. -/
theorem keepsNothing_covered (hb : goalsConcealed.holds p) {k : Nat} (hk : p.Covered k)
    {F : Agent p.Obs p.Act} (hF : KeepsNothing F) (n : Nat) (T : Finset p.Index)
    (hT : ∀ i ∈ T, p.SolvesOn F i n) : T.card ≤ k := by
  rcases T.eq_empty_or_nonempty with rfl | ⟨i₀, -⟩
  · exact Nat.zero_le _
  refine covered_from hb hk F (p.memoryAt F i₀ n) T fun i hi => ?_
  have h := hT i hi
  unfold SolvesOn at h
  rwa [memoryAt_keepsNothing hF i i₀ n] at h

end Pairing

/-! ## A class that meets the record -/

/-- The three spots of the fork's worlds. -/
inductive Spot where
  /-- Where every attempt starts. -/
  | start
  /-- The goal. -/
  | goal
  /-- The trap: no action leaves it. -/
  | trap
  deriving DecidableEq

/-- Member `i` of the fork: from its start the action `i` reaches the goal and the other action
falls into the trap, and no action leaves the goal or the trap. It shows whether the goal is
reached, and gives reward 0 everywhere. -/
def forkMember (i : Bool) : Member Bool Bool where
  State := Spot
  start := .start
  observe s := decide (s = .goal)
  reward _ := 0
  step s a := match s with
    | .start => if a = i then .goal else .trap
    | s => s
  goal s := s = .goal

/-- The agent that always answers `false` and keeps nothing, whose memory takes one value. -/
def stays : Agent Bool Bool := WorldInterface.always false

/-- The fork: two members, `false` and `true`, each reached by the action of its name, in attempts
of one step, presented `n + 1` at a time in a campaign, with the agent `stays`. -/
def fork (n : Nat) : Pairing where
  Obs := Bool
  Act := Bool
  Index := Bool
  member := forkMember
  length := 1
  slots := n + 1
  agent := stays

/-- The learner: its memory is the action it tries and whether it has just tried it. It tries its
action at an attempt's start, and at the attempt's last state keeps the action if it sees the goal
and switches to the other action otherwise. -/
def learner : Agent Bool Bool where
  Memory := Bool × Bool
  initial := (false, false)
  act m o := if m.2 then (m.1, (if o.1 then m.1 else !m.1, false)) else (m.1, (m.1, true))

theorem forkMember_metBy {i : Bool} {actions : Nat → Bool}
    (h : (forkMember i).MetBy 1 actions) : actions 0 = i := by
  obtain ⟨t, h1, h2, hg⟩ := h
  obtain rfl : t = 1 := by omega
  change (if actions 0 = i then Spot.goal else Spot.trap) = Spot.goal at hg
  by_contra hne
  rw [ite_eq_right hne] at hg
  exact Spot.noConfusion hg

theorem fork_covered (n : Nat) : (fork n).Covered 1 := fun _ _ hT =>
  Finset.card_le_one.mpr fun a ha b hb =>
    (forkMember_metBy (hT a ha)).symm.trans (forkMember_metBy (hT b hb))

/-- Where the goal is not reached, a fork member shows `false` and reward 0. -/
theorem forkMember_percept {i : Bool} {s : Spot} (h : ¬ s = Spot.goal) :
    (forkMember i).percept s = (false, 0) := by
  cases s
  · rfl
  · exact absurd rfl h
  · rfl

/-- A fork member's state after `t` steps is not its goal if its goal was reached at none of the
steps 1 to `t`. -/
theorem forkMember_path_ne {i : Bool} {actions : Nat → Bool} {t : Nat}
    (hk : ∀ t', 1 ≤ t' → t' ≤ t → ¬ (forkMember i).goal ((forkMember i).path actions t')) :
    ¬ ((forkMember i).path actions t : Spot) = Spot.goal := by
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · exact fun h => Spot.noConfusion h
  · exact hk t hpos le_rfl

theorem fork_concealed (n : Nat) : goalsConcealed.holds (fork n) := by
  intro (i : Bool) (j : Bool) (actions : Nat → Bool) t _ hun
  change (forkMember i).percept ((forkMember i).path actions t) =
    (forkMember j).percept ((forkMember j).path actions t)
  rw [forkMember_percept (forkMember_path_ne fun t' h1 h2 => (hun t' h1 h2).1),
    forkMember_percept (forkMember_path_ne fun t' h1 h2 => (hun t' h1 h2).2)]

/-- A fork member shows `true` exactly at its goal. -/
theorem forkMember_observe (i : Bool) (s : Spot) :
    (forkMember i).observe s = true ↔ s = Spot.goal := by
  cases s <;> simp [forkMember]

theorem fork_keepsNothing_covered (n : Nat) {F : Agent Bool Bool} (hF : KeepsNothing F)
    (n' : Nat) (T : Finset Bool) (hT : ∀ i ∈ T, (fork n).SolvesOn F i n') : T.card ≤ 1 :=
  Pairing.keepsNothing_covered (fork_concealed n) (fork_covered n) hF n' T hT

theorem learner_solves (n : Nat) (i : Bool) : (fork n).SolvesOn learner i 1 := by
  refine ⟨1, le_rfl, le_rfl, ?_⟩
  cases i <;> rfl

/-- Both of `Bool`'s values. -/
theorem card_univ_bool : (Finset.univ : Finset Bool).card = 2 := rfl

theorem fork_meets (n : Nat) : bigWorlds.Meets (fork n) := by
  refine bigWorlds_meets.mpr ⟨fun (i : Bool) => ⟨fun _ => i, 1, le_rfl, le_rfl, by
      change (if i = i then Spot.goal else Spot.trap) = Spot.goal
      rw [ite_eq_left rfl]⟩, fork_concealed n, ⟨1, ⟨(Finset.univ : Finset Bool), by
        change 1 < (Finset.univ : Finset Bool).card
        rw [card_univ_bool]; decide⟩,
      fun _ hF n' T hT => fork_keepsNothing_covered n hF n' T hT⟩,
    ⟨0, 1, (Finset.univ : Finset Bool), ⟨⟨fun _ => 0, fun _ _ _ => rfl⟩⟩, fork_covered n, ?_⟩,
    ⟨fun o => o.1 = true, fun (i : Bool) (actions : Nat → Bool) t _ =>
      forkMember_observe i ((forkMember i).path actions t)⟩,
    ⟨learner, 1, (Finset.univ : Finset Bool), fun i _ => learner_solves n i,
      fun _ hF n' T' hT' => (fork_keepsNothing_covered n hF n' T' hT').trans_lt (by
        change 1 < (Finset.univ : Finset Bool).card
        rw [card_univ_bool]; decide)⟩⟩
  change 2 ^ 0 * 1 ^ (n + 1) < (Finset.univ : Finset Bool).card ^ (n + 1)
  rw [Nat.one_pow, Nat.pow_zero, Nat.one_mul, card_univ_bool]
  exact Nat.one_lt_two_pow (Nat.succ_ne_zero n)

/-! ## Adequacy -/

/-- O2: the record has no domain hypothesis, and the fork gives an instance of each predicate of its
vocabulary: the learner solves a member on an attempt, an action sequence reaches a member's goal,
and the agent `stays` keeps nothing. -/
theorem bigWorlds_o2 : O2 bigWorlds := by
  refine (o2_correct _).mpr ⟨⟨fork 0, fun _ h => nomatch h⟩, fun q hq => ?_⟩
  simp only [bigWorlds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨⟨fork 0, learner, false, 1⟩, learner_solves 0 false⟩
  · exact ⟨⟨fork 0, fun _ => false, false⟩, 1, le_rfl, le_rfl, rfl⟩
  · exact ⟨⟨fork 0, stays⟩, id, fun _ _ => rfl⟩

/-- O2 before running: the fork meets the whole record. -/
theorem bigWorlds_o2Run : O2Run bigWorlds :=
  (o2Run_correct _).mpr ⟨fork 0, (fork_meets 0).1, (fork_meets 0).2⟩

/-- The fork whose members' goals are never reached. -/
def noGoal : Pairing :=
  { fork 0 with member := fun i => { forkMember i with goal := fun _ => False } }

/-- The fork whose member `true` shows `true` at its start, where member `false` shows `false`. -/
def startTells : Pairing :=
  { fork 0 with member := fun i => { forkMember i with
      observe := fun (s : Spot) => decide (s = Spot.goal) || (decide (s = Spot.start) && i) } }

/-- The class of the one member `true` of the fork, with the agent `stays`. -/
def single : Pairing where
  Obs := Bool
  Act := Bool
  Index := Unit
  member _ := forkMember true
  length := 1
  slots := 1
  agent := stays

/-- The agent that always answers `true` and keeps nothing. -/
def goesTrue : Agent Bool Bool := WorldInterface.always true

/-- The agent `goesTrue` solves the one member of `single` on its first attempt. -/
theorem goesTrue_solves : single.SolvesOn goesTrue () 0 := ⟨1, le_rfl, le_rfl, rfl⟩

/-- The fork presented with no slots. -/
def noSlots : Pairing := { fork 0 with slots := 0 }

/-- The fork whose members show `false` everywhere, the goal included. -/
def silent : Pairing :=
  { fork 0 with member := fun i => { forkMember i with observe := fun _ => false } }

/-- O3: each property fails of a class that changes one part of the fork, or of `single`. -/
theorem bigWorlds_o3 : O3 bigWorlds := by
  refine (o3_correct _).mpr fun c hc => ?_
  simp only [bigWorlds, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨noGoal, fun h => by
      obtain ⟨_, _, _, _, hg⟩ := h false
      exact hg⟩
  · refine ⟨startTells, fun h => ?_⟩
    have := h false true (fun _ => false) 0 (Nat.zero_le _) (fun t' h1 h2 => by omega)
    have hfst := congrArg Prod.fst this
    change false = true at hfst
    exact Bool.noConfusion hfst
  · refine ⟨single, fun ⟨k, ⟨S, hS⟩, hF⟩ => ?_⟩
    have h1 : ({()} : Finset Unit).card ≤ k :=
      hF goesTrue ⟨id, fun _ _ => rfl⟩ 0 {()} fun i _ => goesTrue_solves
    have h2 : S.card ≤ 1 := Finset.card_le_one.mpr fun _ _ _ _ => rfl
    simp only [Finset.card_singleton] at h1
    omega
  · refine ⟨noSlots, fun ⟨b, k, S, _, _, h⟩ => ?_⟩
    change 2 ^ b * k ^ 0 < S.card ^ 0 at h
    rw [Nat.pow_zero, Nat.pow_zero, Nat.mul_one] at h
    exact absurd h (Nat.not_lt.mpr (Nat.one_le_two_pow))
  · refine ⟨silent, fun ⟨signal, h⟩ => ?_⟩
    have hstart := (h false (fun _ => false) 0 (Nat.zero_le _))
    have hgoal := (h false (fun _ => false) 1 le_rfl)
    have hg : (silent.member false).goal ((silent.member false).path (fun _ => false) 1) := rfl
    have hns : ¬ (silent.member false).goal ((silent.member false).path (fun _ => false) 0) :=
      fun h => Spot.noConfusion h
    exact hns (hstart.mp (hgoal.mpr hg))
  · refine ⟨single, fun ⟨A, n, T, _, hF⟩ => ?_⟩
    have h1 : ({()} : Finset Unit).card < T.card :=
      hF goesTrue ⟨id, fun _ _ => rfl⟩ 0 {()} fun i _ => goesTrue_solves
    have h2 : T.card ≤ 1 := Finset.card_le_one.mpr fun _ _ _ _ => rfl
    simp only [Finset.card_singleton] at h1
    omega

/-- O4: the subject is declared a plain value, of which O4 asks nothing. Why that shape is chosen is
recorded in the record's confirmation file. -/
theorem bigWorlds_o4 : O4 bigWorlds := (o4_correct _).mpr trivial

/-- O5 with the widest freedom, which every record meets. -/
theorem bigWorlds_o5_widest : O5 bigWorlds .widest := o5_widest _

/-- O5 does not hold with equality: the fork presented one at a time and the fork presented two at a
time both meet the record and differ. -/
theorem bigWorlds_not_o5_eq : ¬ O5 bigWorlds .eq :=
  not_o5_eq (fork_meets 0) (fork_meets 1) fun h => absurd (congrArg Pairing.slots h) (by decide)

/-- The pair obligation of each property's pair whose only input is trivial, in the class of every
subject: the fork fulfils each property. -/
theorem bigWorlds_pairs :
    ∀ c ∈ bigWorlds.props, OPair (Pair.whole bigWorlds c) (fun _ => True) :=
  fun c hc => (oPair_whole_iff _ _ _).mpr ⟨fork 0, trivial, fun _ => (fork_meets 0).2 c hc⟩

end AcornVerif.Intent.BigWorlds
