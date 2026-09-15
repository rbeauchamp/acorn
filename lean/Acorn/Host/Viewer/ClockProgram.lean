/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

/-!
# Shared capture-order predicates

Native admission and generated browser replay admission use these exact
programs. Native counters enter as naturals. Browser counters must first pass
safe-integer admission; JavaScript integer arithmetic remains the host boundary.
-/
namespace Acorn.Host.Viewer.ClockProgram

variable {n : Nat}

/-- Bounded natural-valued references with successor as the only arithmetic. -/
inductive Term (n : Nat) where
  /-- Closed natural. -/
  | constant (value : Nat)
  /-- Reference owned by the input environment. -/
  | input (index : Fin n)
  /-- Mathematical successor, without machine overflow. -/
  | successor (value : Term n)

/-- Closed predicate language for identity-independent capture ordering. -/
inductive Predicate (n : Nat) where
  /-- Equality of natural-valued terms. -/
  | equal (left right : Term n)
  /-- Strict natural order. -/
  | less (left right : Term n)
  /-- Both claims hold. -/
  | both (left right : Predicate n)
  /-- At least one claim holds. -/
  | either (left right : Predicate n)

/-- Total natural semantics. -/
def Term.eval (values : Fin n → Nat) : Term n → Nat
  | .constant value => value
  | .input index => values index
  | .successor value => value.eval values + 1

/-- Total Boolean semantics used directly by native admission. -/
def Predicate.eval (values : Fin n → Nat) : Predicate n → Bool
  | .equal a b => a.eval values == b.eval values
  | .less a b => a.eval values < b.eval values
  | .both a b => a.eval values && b.eval values
  | .either a b => a.eval values || b.eval values

/-- Structural numeric backend. -/
def Term.javascript (values : Fin n → String) : Term n → String
  | .constant value => toString value
  | .input index => values index
  | .successor value => "(" ++ value.javascript values ++ "+1)"

/-- Structural Boolean backend; no independent ordering algorithm is emitted. -/
def Predicate.javascript (values : Fin n → String) : Predicate n → String
  | .equal a b => "(" ++ a.javascript values ++ "===" ++ b.javascript values ++ ")"
  | .less a b => "(" ++ a.javascript values ++ "<" ++ b.javascript values ++ ")"
  | .both a b => "(" ++ a.javascript values ++ "&&" ++ b.javascript values ++ ")"
  | .either a b => "(" ++ a.javascript values ++ "||" ++ b.javascript values ++ ")"

/-- Lexicographic order over next timestamp/lifetime/world, then previous fields. -/
def after : Predicate 6 :=
  .either (.less (.input 3) (.input 0))
    (.both (.equal (.input 0) (.input 3))
      (.either (.less (.input 4) (.input 1))
        (.both (.equal (.input 1) (.input 4)) (.less (.input 5) (.input 2)))))

/-- Next lifetime/world/terminal, then previous fields; terminal flags are zero or one. -/
def follows : Predicate 6 :=
  .either (.less (.input 3) (.input 0))
    (.both (.equal (.input 0) (.input 3))
      (.both (.equal (.input 2) (.constant 1))
        (.both (.equal (.input 5) (.constant 0))
          (.equal (.input 1) (.successor (.input 4))))))

/-- One environment transition separates the next and previous observation. -/
def worldSuccessor : Predicate 2 :=
  .equal (.input 0) (.successor (.input 1))

/-- Next process/clock/stopped and previous process/clock/stopped. A final
same-clock censor snapshot advances once; process markers are monotonic OS times. -/
def agreementFollows : Predicate 6 :=
  .either (.less (.input 3) (.input 0))
    (.both (.equal (.input 0) (.input 3))
      (.both (.equal (.input 5) (.constant 0))
        (.either (.less (.input 4) (.input 1))
          (.both (.equal (.input 1) (.input 4)) (.equal (.input 2) (.constant 1))))))

/-- An accepted same-process snapshot cannot regress its clock or follow a stop. -/
theorem agreementFollows_same (values : Fin 6 → Nat)
    (same : values 0 = values 3) (accepted : agreementFollows.eval values = true) :
    values 5 = 0 ∧ (values 4 < values 1 ∨ (values 1 = values 4 ∧ values 2 = 1)) := by
  simp [agreementFollows, Predicate.eval, Term.eval, same] at accepted
  refine ⟨accepted.1, ?_⟩
  cases accepted.2 with
  | inl later => exact Or.inl (of_decide_eq_true later)
  | inr final => exact Or.inr final

/-- Joint process snapshots also advance on goal boundaries with zero agent
steps. Fields are process/clock/stopped/cycle/resolved/attempt/invalid for the
next snapshot, followed by the same seven fields for its predecessor. -/
def snapshotFollows : Predicate 14 :=
  .either (.less (.input 7) (.input 0))
    (.both (.equal (.input 0) (.input 7))
      (.both (.equal (.input 9) (.constant 0))
        (.either (.less (.input 8) (.input 1))
          (.both (.equal (.input 1) (.input 8))
            (.either (.equal (.input 2) (.constant 1))
              (.either
                (.both (.equal (.input 6) (.constant 1)) (.equal (.input 13) (.constant 0)))
                (.either (.less (.input 10) (.input 3))
                  (.both (.equal (.input 3) (.input 10))
                    (.either (.less (.input 11) (.input 4))
                      (.both (.equal (.input 4) (.input 11))
                        (.less (.input 12) (.input 5))))))))))))

/-- Same-process outcome updates never regress the learning clock or follow stop. -/
theorem snapshotFollows_same (values : Fin 14 → Nat) (same : values 0 = values 7)
    (accepted : snapshotFollows.eval values = true) :
    values 9 = 0 ∧ values 8 ≤ values 1 := by
  simp [snapshotFollows, Predicate.eval, Term.eval, same] at accepted
  refine ⟨accepted.1, ?_⟩
  rcases accepted.2 with later | equal
  · have bound : values 8 < values 1 := of_decide_eq_true later
    omega
  · rw [equal.1]
    exact Nat.le_refl _

/-- A resolved goal is admitted immediately even when it executes zero actions. -/
theorem snapshotFollows_goal (values : Fin 14 → Nat)
    (process : values 0 = values 7) (clock : values 1 = values 8)
    (running : values 9 = 0) (cycle : values 3 = values 10)
    (resolved : values 11 < values 4) : snapshotFollows.eval values = true := by
  simp [snapshotFollows, Predicate.eval, Term.eval, process, clock, running, cycle, resolved]

/-- The same counter programs are exported to the replay adapter. -/
def javascript : String :=
  let environment := fun (i : Fin 6) => s!"p[{i.val}]"
  "const observerSnapshotFollows=(...p)=>" ++ snapshotFollows.javascript
    (fun (i : Fin 14) => s!"p[{i.val}]") ++ ";\n" ++
    "const observerAfter=(...p)=>" ++ after.javascript environment ++ ";\n" ++
    "const observerAgreementFollows=(...p)=>" ++ agreementFollows.javascript environment ++ ";\n" ++
    "const observerFollows=(...p)=>" ++ follows.javascript environment ++ ";\n" ++
    "const observerWorldSuccessor=(...p)=>" ++ worldSuccessor.javascript
      (fun (i : Fin 2) => s!"p[{i.val}]") ++ ";\n"

end Acorn.Host.Viewer.ClockProgram
