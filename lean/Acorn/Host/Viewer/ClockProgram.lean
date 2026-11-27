namespace Acorn.Host.Viewer.ClockProgram

variable {n : Nat}

inductive Term (n : Nat) where
  | constant (value : Nat)
  | input (index : Fin n)
  | successor (value : Term n)

inductive Predicate (n : Nat) where
  | equal (left right : Term n)
  | less (left right : Term n)
  | both (left right : Predicate n)
  | either (left right : Predicate n)

def Term.eval (values : Fin n → Nat) : Term n → Nat
  | .constant value => value
  | .input index => values index
  | .successor value => value.eval values + 1

def Predicate.eval (values : Fin n → Nat) : Predicate n → Bool
  | .equal a b => a.eval values == b.eval values
  | .less a b => a.eval values < b.eval values
  | .both a b => a.eval values && b.eval values
  | .either a b => a.eval values || b.eval values

def Term.javascript (values : Fin n → String) : Term n → String
  | .constant value => toString value
  | .input index => values index
  | .successor value => "(" ++ value.javascript values ++ "+1)"

def Predicate.javascript (values : Fin n → String) : Predicate n → String
  | .equal a b => "(" ++ a.javascript values ++ "===" ++ b.javascript values ++ ")"
  | .less a b => "(" ++ a.javascript values ++ "<" ++ b.javascript values ++ ")"
  | .both a b => "(" ++ a.javascript values ++ "&&" ++ b.javascript values ++ ")"
  | .either a b => "(" ++ a.javascript values ++ "||" ++ b.javascript values ++ ")"

def after : Predicate 6 :=
  .either (.less (.input 3) (.input 0))
    (.both (.equal (.input 0) (.input 3))
      (.either (.less (.input 4) (.input 1))
        (.both (.equal (.input 1) (.input 4)) (.less (.input 5) (.input 2)))))

def follows : Predicate 6 :=
  .either (.less (.input 3) (.input 0))
    (.both (.equal (.input 0) (.input 3))
      (.both (.equal (.input 2) (.constant 1))
        (.both (.equal (.input 5) (.constant 0))
          (.equal (.input 1) (.successor (.input 4))))))

def worldSuccessor : Predicate 2 :=
  .equal (.input 0) (.successor (.input 1))

def agreementFollows : Predicate 6 :=
  .either (.less (.input 3) (.input 0))
    (.both (.equal (.input 0) (.input 3))
      (.both (.equal (.input 5) (.constant 0))
        (.either (.less (.input 4) (.input 1))
          (.both (.equal (.input 1) (.input 4)) (.equal (.input 2) (.constant 1))))))

theorem agreementFollows_same (values : Fin 6 → Nat)
    (same : values 0 = values 3) (accepted : agreementFollows.eval values = true) :
    values 5 = 0 ∧ (values 4 < values 1 ∨ (values 1 = values 4 ∧ values 2 = 1)) := by
  simp [agreementFollows, Predicate.eval, Term.eval, same] at accepted
  refine ⟨accepted.1, ?_⟩
  cases accepted.2 with
  | inl later => exact Or.inl (of_decide_eq_true later)
  | inr final => exact Or.inr final

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

theorem snapshotFollows_goal (values : Fin 14 → Nat)
    (process : values 0 = values 7) (clock : values 1 = values 8)
    (running : values 9 = 0) (cycle : values 3 = values 10)
    (resolved : values 11 < values 4) : snapshotFollows.eval values = true := by
  simp [snapshotFollows, Predicate.eval, Term.eval, process, clock, running, cycle, resolved]

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
