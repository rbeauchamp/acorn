import AcornVerif.LeanIntentBridge

namespace AcornVerif.Intent.Hash

open LeanIntent

abbrev Inputs := UInt64 × UInt64 × UInt64

structure Hashes where
  hash2 : Inputs → UInt64
  hash3 : Inputs → UInt64

inductive Order where
  | abc
  | bac
  | acb
  | cba
  | bca
  | cab

def Order.apply : Order → Inputs → Inputs
  | .abc, (a, b, c) => (a, b, c)
  | .bac, (a, b, c) => (b, a, c)
  | .acb, (a, b, c) => (a, c, b)
  | .cba, (a, b, c) => (c, b, a)
  | .bca, (a, b, c) => (b, c, a)
  | .cab, (a, b, c) => (c, a, b)

inductive Shift where
  | flip
  | add

def Shift.apply : Shift → UInt64 → UInt64 → UInt64
  | .flip, x, d => x ^^^ d
  | .add, x, d => x + d

structure Rule where
  order : Order
  shift : Shift
  amount : Inputs

def Rule.apply (r : Rule) (x : Inputs) : Inputs :=
  let (a, b, c) := r.order.apply x
  (r.shift.apply a r.amount.1, r.shift.apply b r.amount.2.1, r.shift.apply c r.amount.2.2)

def Rule.Moves (r : Rule) : Prop := ¬ (r.order = .abc ∧ r.amount = (0, 0, 0))

def OneInputMoves (f : Inputs → UInt64) : Prop :=
  (∀ a a' b c, f (a, b, c) = f (a', b, c) → a = a') ∧
    (∀ a b b' c, f (a, b, c) = f (a, b', c) → b = b') ∧
    (∀ a b c c', f (a, b, c) = f (a, b, c') → c = c')

def NoRuleKeepsSpots (f : Inputs → UInt64) : Prop :=
  ∀ r : Rule, r.Moves → ∃ x, f (r.apply x) ≠ f x

def oneInputMoves : Clause Hashes :=
  ⟨"changing any one input always moves the spot", fun w =>
    OneInputMoves w.hash2 ∧ OneInputMoves w.hash3⟩

def noRuleKeepsSpots : Clause Hashes :=
  ⟨"no fixed rule of reordering and shifting the inputs keeps every spot", fun w =>
    NoRuleKeepsSpots w.hash2 ∧ NoRuleKeepsSpots w.hash3⟩

def hashes : IntentRecord Hashes where
  shape := .value _
  dom := []
  props := [oneInputMoves, noRuleKeepsSpots]
  vocab := [⟨"same spot", UInt64 × UInt64, fun p => p.1 = p.2⟩]

theorem hashes_meets {w : Hashes} :
    hashes.Meets w ↔
      (OneInputMoves w.hash2 ∧ OneInputMoves w.hash3) ∧
      (NoRuleKeepsSpots w.hash2 ∧ NoRuleKeepsSpots w.hash3) := by
  constructor
  · intro h
    exact ⟨h.2 _ (List.mem_cons_self ..),
      h.2 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩
  · intro ⟨h1, h2⟩
    refine ⟨(fun d hd => nomatch hd), fun p hp => ?_⟩
    simp only [hashes, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact h1
    · exact h2

def constantZero : Hashes := ⟨fun _ => 0, fun _ => 0⟩

theorem hashes_o2 : O2 hashes := by
  refine (o2_correct _).mpr ⟨⟨constantZero, fun _ h => nomatch h⟩, ?_⟩
  intro p hp
  simp only [hashes, List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp
  exact ⟨(0, 0), rfl⟩

theorem hashes_o3 : O3 hashes := by
  refine (o3_correct _).mpr fun p hp => ?_
  simp only [hashes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨constantZero, fun h => absurd (h.1.1 0 1 0 0 rfl) (by decide)⟩
  · refine ⟨constantZero, fun h => ?_⟩
    obtain ⟨x, hx⟩ := h.1 ⟨.abc, .add, (1, 0, 0)⟩ (fun h => absurd (congrArg (·.1) h.2) (by decide))
    exact hx rfl

theorem hashes_o4 : O4 hashes := (o4_correct _).mpr trivial

theorem hashes_o5_widest : O5 hashes .widest := o5_widest _

end AcornVerif.Intent.Hash
