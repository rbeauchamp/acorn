import Mathlib.Tactic.Primality.Lucas
import Mathlib.Tactic.NormNum.Prime

namespace XoshiroPrimes
open Mathlib.Tactic.Primality

theorem p3 : Nat.Prime 3 := by norm_num

theorem p5 : Nat.Prime 5 := by norm_num

theorem p7 : Nat.Prime 7 := by norm_num

theorem p11 : Nat.Prime 11 := by norm_num

theorem p17 : Nat.Prime 17 := by norm_num

theorem p47 : Nat.Prime 47 := by norm_num

theorem p71 : Nat.Prime 71 := by norm_num

theorem p139 : Nat.Prime 139 := by norm_num

theorem p181 : Nat.Prime 181 := by norm_num

theorem p257 : Nat.Prime 257 := by norm_num

theorem p347 : Nat.Prime 347 := by norm_num

theorem p367 : Nat.Prime 367 := by norm_num

theorem p373 : Nat.Prime 373 := by norm_num

theorem p449 : Nat.Prime 449 := by norm_num

theorem p641 : Nat.Prime 641 := by norm_num

theorem p727 : Nat.Prime 727 := by norm_num

theorem p823 : Nat.Prime 823 := by norm_num

theorem p1783 : Nat.Prime 1783 :=
  prime_of_lucasCheck (a := 10) (factorization := [(2, 1), (3, 4), (11, 1)])
    (List.forall_mem_cons.2 ⟨Nat.prime_two, List.forall_mem_cons.2 ⟨p3, List.forall_mem_cons.2 ⟨p11, List.forall_mem_nil _⟩⟩⟩)
    (by decide +kernel)

theorem p2203 : Nat.Prime 2203 :=
  prime_of_lucasCheck (a := 5) (factorization := [(2, 1), (3, 1), (367, 1)])
    (List.forall_mem_cons.2 ⟨Nat.prime_two, List.forall_mem_cons.2 ⟨p3, List.forall_mem_cons.2 ⟨p367, List.forall_mem_nil _⟩⟩⟩)
    (by decide +kernel)

theorem p12497 : Nat.Prime 12497 :=
  prime_of_lucasCheck (a := 3) (factorization := [(2, 4), (11, 1), (71, 1)])
    (List.forall_mem_cons.2 ⟨Nat.prime_two, List.forall_mem_cons.2 ⟨p11, List.forall_mem_cons.2 ⟨p71, List.forall_mem_nil _⟩⟩⟩)
    (by decide +kernel)

theorem p16657 : Nat.Prime 16657 :=
  prime_of_lucasCheck (a := 5) (factorization := [(2, 4), (3, 1), (347, 1)])
    (List.forall_mem_cons.2 ⟨Nat.prime_two, List.forall_mem_cons.2 ⟨p3, List.forall_mem_cons.2 ⟨p347, List.forall_mem_nil _⟩⟩⟩)
    (by decide +kernel)

theorem p17449 : Nat.Prime 17449 :=
  prime_of_lucasCheck (a := 14) (factorization := [(2, 3), (3, 1), (727, 1)])
    (List.forall_mem_cons.2 ⟨Nat.prime_two, List.forall_mem_cons.2 ⟨p3, List.forall_mem_cons.2 ⟨p727, List.forall_mem_nil _⟩⟩⟩)
    (by decide +kernel)

theorem p52673 : Nat.Prime 52673 :=
  prime_of_lucasCheck (a := 3) (factorization := [(2, 6), (823, 1)])
    (List.forall_mem_cons.2 ⟨Nat.prime_two, List.forall_mem_cons.2 ⟨p823, List.forall_mem_nil _⟩⟩)
    (by decide +kernel)

theorem p65537 : Nat.Prime 65537 :=
  prime_of_lucasCheck (a := 3) (factorization := [(2, 16)])
    (List.forall_mem_cons.2 ⟨Nat.prime_two, List.forall_mem_nil _⟩)
    (by decide +kernel)

theorem p166571 : Nat.Prime 166571 :=
  prime_of_lucasCheck (a := 2) (factorization := [(2, 1), (5, 1), (16657, 1)])
    (List.forall_mem_cons.2 ⟨Nat.prime_two, List.forall_mem_cons.2 ⟨p5, List.forall_mem_cons.2 ⟨p16657, List.forall_mem_nil _⟩⟩⟩)
    (by decide +kernel)

theorem p274177 : Nat.Prime 274177 :=
  prime_of_lucasCheck (a := 5) (factorization := [(2, 8), (3, 2), (7, 1), (17, 1)])
    (List.forall_mem_cons.2 ⟨Nat.prime_two, List.forall_mem_cons.2 ⟨p3, List.forall_mem_cons.2 ⟨p7, List.forall_mem_cons.2 ⟨p17, List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel)

theorem p1896229 : Nat.Prime 1896229 :=
  prime_of_lucasCheck (a := 2) (factorization := [(2, 2), (3, 2), (52673, 1)])
    (List.forall_mem_cons.2 ⟨Nat.prime_two, List.forall_mem_cons.2 ⟨p3, List.forall_mem_cons.2 ⟨p52673, List.forall_mem_nil _⟩⟩⟩)
    (by decide +kernel)

theorem p2998279 : Nat.Prime 2998279 :=
  prime_of_lucasCheck (a := 3) (factorization := [(2, 1), (3, 2), (166571, 1)])
    (List.forall_mem_cons.2 ⟨Nat.prime_two, List.forall_mem_cons.2 ⟨p3, List.forall_mem_cons.2 ⟨p166571, List.forall_mem_nil _⟩⟩⟩)
    (by decide +kernel)

theorem p6700417 : Nat.Prime 6700417 :=
  prime_of_lucasCheck (a := 5) (factorization := [(2, 7), (3, 1), (17449, 1)])
    (List.forall_mem_cons.2 ⟨Nat.prime_two, List.forall_mem_cons.2 ⟨p3, List.forall_mem_cons.2 ⟨p17449, List.forall_mem_nil _⟩⟩⟩)
    (by decide +kernel)

theorem p6939437 : Nat.Prime 6939437 :=
  prime_of_lucasCheck (a := 2) (factorization := [(2, 2), (7, 1), (139, 1), (1783, 1)])
    (List.forall_mem_cons.2 ⟨Nat.prime_two, List.forall_mem_cons.2 ⟨p7, List.forall_mem_cons.2 ⟨p139, List.forall_mem_cons.2 ⟨p1783, List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel)

theorem p55515497 : Nat.Prime 55515497 :=
  prime_of_lucasCheck (a := 3) (factorization := [(2, 3), (6939437, 1)])
    (List.forall_mem_cons.2 ⟨Nat.prime_two, List.forall_mem_cons.2 ⟨p6939437, List.forall_mem_nil _⟩⟩)
    (by decide +kernel)

theorem p18533742247 : Nat.Prime 18533742247 :=
  prime_of_lucasCheck (a := 6) (factorization := [(2, 1), (3, 3), (181, 1), (1896229, 1)])
    (List.forall_mem_cons.2 ⟨Nat.prime_two, List.forall_mem_cons.2 ⟨p3, List.forall_mem_cons.2 ⟨p181, List.forall_mem_cons.2 ⟨p1896229, List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel)

theorem p733803839347 : Nat.Prime 733803839347 :=
  prime_of_lucasCheck (a := 2) (factorization := [(2, 1), (3, 1), (2203, 1), (55515497, 1)])
    (List.forall_mem_cons.2 ⟨Nat.prime_two, List.forall_mem_cons.2 ⟨p3, List.forall_mem_cons.2 ⟨p2203, List.forall_mem_cons.2 ⟨p55515497, List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel)

theorem p67280421310721 : Nat.Prime 67280421310721 :=
  prime_of_lucasCheck (a := 3) (factorization := [(2, 8), (5, 1), (47, 1), (373, 1), (2998279, 1)])
    (List.forall_mem_cons.2 ⟨Nat.prime_two, List.forall_mem_cons.2 ⟨p5, List.forall_mem_cons.2 ⟨p47, List.forall_mem_cons.2 ⟨p373, List.forall_mem_cons.2 ⟨p2998279, List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel)

theorem p116503103764643 : Nat.Prime 116503103764643 :=
  prime_of_lucasCheck (a := 2) (factorization := [(2, 1), (7, 1), (449, 1), (18533742247, 1)])
    (List.forall_mem_cons.2 ⟨Nat.prime_two, List.forall_mem_cons.2 ⟨p7, List.forall_mem_cons.2 ⟨p449, List.forall_mem_cons.2 ⟨p18533742247, List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel)

theorem p59649589127497217 : Nat.Prime 59649589127497217 :=
  prime_of_lucasCheck (a := 3) (factorization := [(2, 9), (116503103764643, 1)])
    (List.forall_mem_cons.2 ⟨Nat.prime_two, List.forall_mem_cons.2 ⟨p116503103764643, List.forall_mem_nil _⟩⟩)
    (by decide +kernel)

theorem p5704689200685129054721 : Nat.Prime 5704689200685129054721 :=
  prime_of_lucasCheck (a := 21) (factorization := [(2, 9), (3, 5), (5, 1), (12497, 1), (733803839347, 1)])
    (List.forall_mem_cons.2 ⟨Nat.prime_two, List.forall_mem_cons.2 ⟨p3, List.forall_mem_cons.2 ⟨p5, List.forall_mem_cons.2 ⟨p12497, List.forall_mem_cons.2 ⟨p733803839347, List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel)

end XoshiroPrimes
