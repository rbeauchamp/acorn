import Acorn.Rng

namespace XoshiroCertificates
open Acorn.Rng

def poly : Nat := 0x10003c03c3f3ecb1904b4edcf26259f850280002bcefd1a5e9d116f2bb0f0f001

def mulx (y : Nat) : Nat :=
  let z := y <<< 1
  bif Nat.beq (z >>> 256) 1 then z ^^^ poly else z

def chain : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, c => c :: chain k (mulx (mulx c))

def table : List Nat := chain 256 1

def frobL : List Nat → Nat → Nat → Nat
  | [], _, acc => acc
  | c :: cs, y, acc => frobL cs (y >>> 1) (bif Nat.beq (y % 2) 1 then acc ^^^ c else acc)

def frob (y : Nat) : Nat := frobL table y 0

def powAux : Nat → Nat → Nat → Nat
  | 0, _, y => y
  | k + 1, e, y => powAux k e (let s := frob y; bif Nat.beq ((e >>> k) % 2) 1 then mulx s else s)

def powx (e : Nat) : Nat := powAux 256 e 1

def sxor (a b : Xoshiro256) : Xoshiro256 :=
  ⟨a.s0 ^^^ b.s0, a.s1 ^^^ b.s1, a.s2 ^^^ b.s2, a.s3 ^^^ b.s3⟩

def pe : Nat → Nat → Xoshiro256 → Xoshiro256
  | 0, _, _ => Xoshiro256.zero
  | n + 1, f, v => sxor (bif Nat.beq (f % 2) 1 then v else Xoshiro256.zero) (pe n (f >>> 1) v.next.2)

def v0 : Xoshiro256 := ⟨1, 0, 0, 0⟩


def iter : Nat → Nat → Nat
  | 0, y => y
  | k + 1, y => iter k (frob y)

theorem annihilates : pe 257 poly v0 = Xoshiro256.zero := by decide +kernel
theorem cycle : iter 256 2 = 2 := by decide +kernel
theorem o3 : pe 257 (powx ((2 ^ 256 - 1) / 3)) v0 ≠ v0 := by decide +kernel
theorem o5 : pe 257 (powx ((2 ^ 256 - 1) / 5)) v0 ≠ v0 := by decide +kernel
theorem o17 : pe 257 (powx ((2 ^ 256 - 1) / 17)) v0 ≠ v0 := by decide +kernel
theorem o257 : pe 257 (powx ((2 ^ 256 - 1) / 257)) v0 ≠ v0 := by decide +kernel
theorem o641 : pe 257 (powx ((2 ^ 256 - 1) / 641)) v0 ≠ v0 := by decide +kernel
theorem o65537 : pe 257 (powx ((2 ^ 256 - 1) / 65537)) v0 ≠ v0 := by decide +kernel
theorem o274177 : pe 257 (powx ((2 ^ 256 - 1) / 274177)) v0 ≠ v0 := by decide +kernel
theorem o6700417 : pe 257 (powx ((2 ^ 256 - 1) / 6700417)) v0 ≠ v0 := by decide +kernel
theorem o67280421310721 : pe 257 (powx ((2 ^ 256 - 1) / 67280421310721)) v0 ≠ v0 := by
  decide +kernel
theorem o59649589127497217 : pe 257 (powx ((2 ^ 256 - 1) / 59649589127497217)) v0 ≠ v0 := by
  decide +kernel
theorem o5704689200685129054721 :
    pe 257 (powx ((2 ^ 256 - 1) / 5704689200685129054721)) v0 ≠ v0 := by
  decide +kernel

end XoshiroCertificates
