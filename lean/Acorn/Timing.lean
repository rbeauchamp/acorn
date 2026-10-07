/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

/-!
# Time between an agent and a world

A step of the agent has two parts. The first selects the action. The second completes
the step from the value the first returned. `StepOrder` declares which of three orders
an agent and its host run.

Under `learnThenAct` both parts run before the world receives the action, and the
first part plans at a free boundary before it draws. Under `planAfterAct` the host
releases the action between the two parts, and planning is the first work of the
second part: at a free boundary the meta action is drawn from the meta-controller
before that frame's planning. The name says what the order does and no more. An option
that starts still draws its first action after the terminal credit and the settlement
that this percept causes, so this order is not a complete "act, then learn".

Under `actThenLearn` the first part makes every draw of the step and takes no reward
word, and every write that reads the reward of the percept is in the second part, with
the planning of a free boundary after it. An option that starts draws its first action
from its policy as the preceding step left it. The first part still reads the frame's
achievement event (D8), on which an executing option ends.

Releasing the action before the learning update is the reordering of Travnik,
Mathewson, Sutton & Pilarski, *Reactive Reinforcement Learning in Asynchronous
Environments*, Frontiers in Robotics and AI 5:79 (2018), sections 2 and 3. Its
Algorithm 1 (SARSA, section 2) takes the action it chose at the start of the next
iteration, after the update; its Algorithm 2 (Reactive SARSA, section 3) takes the
action directly after choosing it, before the update. Both listings choose the action
before the update; the source has no planning. Moving planning after the action is Acorn's own change of PAR-14's
schedule, declared in PAR-19. Drawing the first action of an option before the credit
that the same percept causes is the source's order of choice and update applied to that
option's learner, and is declared with its other consequences in PAR-20.
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
  /-- The world receives the action after the first part, which makes every draw and
  takes no reward. Every write that reads the reward, and then planning, is in the
  second part, which runs after the world's transition. -/
  | actThenLearn
  deriving DecidableEq

/-- Canonical spelling of each order; the single text vocabulary shared by command
admission and run provenance. -/
def StepOrder.name : StepOrder → String
  | .learnThenAct => "learn-then-act"
  | .planAfterAct => "plan-after-act"
  | .actThenLearn => "act-then-learn"

/-- The single closed textual admission rule: exactly the three canonical spellings
parse; every other string is refused and never substituted. -/
def StepOrder.parse (text : String) : Option StepOrder :=
  if text = "learn-then-act" then some .learnThenAct
  else if text = "plan-after-act" then some .planAfterAct
  else if text = "act-then-learn" then some .actThenLearn
  else none

/-- Stored word of each order in a checkpoint header. -/
def StepOrder.tag : StepOrder → UInt32
  | .learnThenAct => 0
  | .planAfterAct => 1
  | .actThenLearn => 2

/-- Two orders with one stored word are one order. -/
theorem StepOrder.tag_injective (first second : StepOrder) (same : first.tag = second.tag) :
    first = second := by
  cases first <;> cases second <;> first | rfl | cases same

/-- The stored word of every order is below 256: it occupies one byte of its four. -/
theorem StepOrder.tag_small (order : StepOrder) : order.tag.toNat < 256 := by
  cases order <;> decide

/-- The specification of the stored word of a step order, written with no executed
function: word 0 is learn-then-act, word 1 is plan-after-act and word 2 is
act-then-learn. -/
def StepOrder.Stored (word : UInt32) (order : StepOrder) : Prop :=
  (word = 0 ∧ order = .learnThenAct) ∨ (word = 1 ∧ order = .planAfterAct) ∨
    (word = 2 ∧ order = .actThenLearn)

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
    (text = "plan-after-act" ∧ order = .planAfterAct) ∨
    (text = "act-then-learn" ∧ order = .actThenLearn)

/-- **The parser accepts exactly the spelled orders.** For every string and order, the
parser returns the order exactly when the text spells it. -/
theorem StepOrder.parse_spelled (text : String) (order : StepOrder) :
    StepOrder.parse text = some order ↔ StepOrder.Spelled text order := by
  cases order <;> by_cases first : text = "learn-then-act" <;>
    by_cases second : text = "plan-after-act" <;>
    by_cases third : text = "act-then-learn" <;>
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
    by_cases third : text = "act-then-learn" <;>
    simp_all [StepOrder.parse, StepOrder.name]

/-- An order whose host loop releases the action between the two parts of a step: every
order but the default. A host loop that releases takes the callbacks of such an order. -/
def StepOrder.Releases (order : StepOrder) : Prop := order ≠ .learnThenAct

end Acorn
