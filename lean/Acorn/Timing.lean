/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

/-!
# Time between an agent and a world

A step of the agent has two parts. The first selects the action. The second completes
the step from the value the first returned. `StepOrder` declares which of two orders
an agent and its host run.

Under `learnThenAct` both parts run before the world receives the action, and the
first part plans at a free boundary before it draws. Under `planAfterAct` the host
releases the action between the two parts, and planning is the first work of the
second part: at a free boundary the meta action is drawn from the meta-controller
before that frame's planning. The name says what the order does and no more. An option
that starts still draws its first action after the terminal credit and the settlement
that this percept causes, so this order is not a complete "act, then learn".

Releasing the action before the learning update is the reordering of Travnik,
Mathewson, Sutton & Pilarski, *Reactive Reinforcement Learning in Asynchronous
Environments*, Frontiers in Robotics and AI 5:79 (2018), section 3. Its Algorithm 1
(SARSA) takes the action it chose at the start of the next iteration, after the
update; its Algorithm 2 (Reactive SARSA) takes the action directly after choosing it,
before the update. Both listings choose the action before the update; the source has
no planning. Moving planning after the action is Acorn's own change of PAR-14's
schedule, declared in PAR-19.
-/
namespace Acorn

/-- The order of the agent's two step parts, planning and the world's transition. -/
inductive StepOrder where
  /-- Both parts run before the world receives the action, and a free boundary plans
  before its meta draw. -/
  | learnThenAct
  /-- The world receives the action after the first part. Planning is the first work
  of the second part, which runs after the world's transition. -/
  | planAfterAct
  deriving DecidableEq

/-- Canonical spelling of each order; the single text vocabulary shared by command
admission and run provenance. -/
def StepOrder.name : StepOrder → String
  | .learnThenAct => "learn-then-act"
  | .planAfterAct => "plan-after-act"

/-- The single closed textual admission rule: exactly the two canonical spellings
parse; every other string is refused and never substituted. -/
def StepOrder.parse (text : String) : Option StepOrder :=
  if text = "learn-then-act" then some .learnThenAct
  else if text = "plan-after-act" then some .planAfterAct
  else none

/-- Stored word of each order in a checkpoint header. -/
def StepOrder.tag : StepOrder → UInt32
  | .learnThenAct => 0
  | .planAfterAct => 1

/-- Two orders with one stored word are one order. -/
theorem StepOrder.tag_injective (first second : StepOrder) (same : first.tag = second.tag) :
    first = second := by
  cases first <;> cases second <;> first | rfl | cases same

/-- The specification of the stored word of a step order, written with no executed
function: word 0 is learn-then-act and word 1 is plan-after-act. -/
def StepOrder.Stored (word : UInt32) (order : StepOrder) : Prop :=
  (word = 0 ∧ order = .learnThenAct) ∨ (word = 1 ∧ order = .planAfterAct)

/-- **The stored word of an order is exactly its specified word.** For every order and
word, `tag` gives the word exactly when the word is stored for the order. -/
theorem StepOrder.tag_stored (order : StepOrder) (word : UInt32) :
    order.tag = word ↔ StepOrder.Stored word order := by
  cases order <;> simp [StepOrder.tag, StepOrder.Stored, eq_comm]

/-- One stored word is the word of one order. -/
theorem StepOrder.stored_injective (word : UInt32) (first second : StepOrder)
    (one : StepOrder.Stored word first) (other : StepOrder.Stored word second) :
    first = second :=
  StepOrder.tag_injective first second
    (((StepOrder.tag_stored first word).mpr one).trans
      ((StepOrder.tag_stored second word).mpr other).symm)

/-- The specification of the spelling of a step order, written with no executed function:
a text spells an order when it is that order's one word. -/
def StepOrder.Spelled (text : String) (order : StepOrder) : Prop :=
  (text = "learn-then-act" ∧ order = .learnThenAct) ∨
    (text = "plan-after-act" ∧ order = .planAfterAct)

/-- **The parser accepts exactly the spelled orders.** For every string and order, the
parser returns the order exactly when the text spells it. -/
theorem StepOrder.parse_spelled (text : String) (order : StepOrder) :
    StepOrder.parse text = some order ↔ StepOrder.Spelled text order := by
  cases order <;> by_cases first : text = "learn-then-act" <;>
    by_cases second : text = "plan-after-act" <;>
    simp_all [StepOrder.parse, StepOrder.Spelled]

/-- **The parser refuses exactly the texts that spell no order.** -/
theorem StepOrder.parse_refused (text : String) :
    StepOrder.parse text = none ↔ ∀ order, ¬ StepOrder.Spelled text order := by
  constructor
  · intro refused order spelled
    rw [(StepOrder.parse_spelled text order).mpr spelled] at refused
    cases refused
  · intro unspelled
    cases parsed : StepOrder.parse text with
    | none => rfl
    | some order => exact (unspelled order ((StepOrder.parse_spelled text order).mp parsed)).elim

/-- The word that run provenance prints for an order spells that order, and no other. -/
theorem StepOrder.name_spelled (order other : StepOrder) :
    StepOrder.Spelled order.name other ↔ other = order := by
  cases order <;> cases other <;> simp [StepOrder.Spelled, StepOrder.name]

/-- Accepted spelling identifies exactly the selected constructor over the entire
string domain. -/
theorem StepOrder.parse_accepted (text : String) (order : StepOrder) :
    StepOrder.parse text = some order ↔ text = StepOrder.name order := by
  cases order <;> by_cases first : text = "learn-then-act" <;>
    by_cases second : text = "plan-after-act" <;>
    simp_all [StepOrder.parse, StepOrder.name]

end Acorn
