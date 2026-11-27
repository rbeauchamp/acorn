namespace Acorn.Digits

def read (text : String) : Option Nat :=
  match text.toList with
  | [] => none
  | digits@(_ :: _) => digits.foldlM (fun total c =>
      if '0' ≤ c && c ≤ '9' then some (10 * total + (c.toNat - 48)) else none) 0

def natural (text : String) : Option Nat :=
  match text.toList with
  | '+' :: digits => read (String.ofList digits)
  | _ => read text

def integer (text : String) : Option Int :=
  match text.toList with
  | '-' :: digits => (read (String.ofList digits)).map fun n : Nat => -(n : Int)
  | '+' :: digits => (read (String.ofList digits)).map fun n : Nat => (n : Int)
  | _ => (read text).map fun n : Nat => (n : Int)

def usage : String :=
  "A number is the digits 0 to 9 with an optional leading +; no other sign, separator or space."

def Spelled (text : String) (n : Nat) : Prop :=
  text.toList ≠ [] ∧ (∀ c ∈ text.toList, 48 ≤ c.toNat ∧ c.toNat ≤ 57) ∧
    n = (text.toList.reverse.zipIdx.map fun place => (place.1.toNat - 48) * 10 ^ place.2).sum

def Natural (text : String) (n : Nat) : Prop :=
  ∃ sign digits : List Char, (sign = [] ∨ sign = ['+']) ∧ digits ≠ [] ∧
    (∀ c ∈ digits, 48 ≤ c.toNat ∧ c.toNat ≤ 57) ∧ text.toList = sign ++ digits ∧
    n = (digits.reverse.zipIdx.map fun place => (place.1.toNat - 48) * 10 ^ place.2).sum

def Integer (text : String) (z : Int) : Prop :=
  ∃ sign digits : List Char, (sign = [] ∨ sign = ['+'] ∨ sign = ['-']) ∧ digits ≠ [] ∧
    (∀ c ∈ digits, 48 ≤ c.toNat ∧ c.toNat ≤ 57) ∧ text.toList = sign ++ digits ∧
    z = (if sign = ['-'] then -1 else 1) *
      ((digits.reverse.zipIdx.map fun place => (place.1.toNat - 48) * 10 ^ place.2).sum : Nat)

end Acorn.Digits
