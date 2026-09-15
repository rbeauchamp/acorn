/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

/-! # Machine-word constants

Exact IEEE-754 words and numeric parameters shared by the executing modules.
Algorithm owners state their citations and semantic contracts. Consumers import
these definitions directly, so changing a word changes every use by construction.
-/
namespace Acorn.Constants

/-- Binary64 reduction constant `ln2HiBits`. -/
def ln2HiBits : UInt64 := 0x3fe62e42fee00000

/-- Binary64 reduction constant `ln2LoBits`. -/
def ln2LoBits : UInt64 := 0x3dea39ef35793c77

/-- Binary64 reduction constant `log2eBits`. -/
def log2eBits : UInt64 := 0x3ff71547652b82fe

/-- Binary64 reduction constant `sqrt2Bits`. -/
def sqrt2Bits : UInt64 := 0x3ff6a09e667f3bcd

/-- Binary32 exponential bound `expOverflowBits`. -/
def expOverflowBits : UInt32 := 0x42b20000

/-- Binary32 exponential bound `expUnderflowBits`. -/
def expUnderflowBits : UInt32 := 0xc2d00000

/-- Host reward-rate lag budget in transitions. -/
def gainTrackingHorizon : UInt32 := 20000

/-- Exact f32 bits of the configured decimal value (`0.3`). -/
def band030Bits : UInt32 := 0x3e99999a

/-- Exact f32 bits of the configured decimal value (`0.335`). -/
def band0335Bits : UInt32 := 0x3eab851f

/-- Exact f32 bits of the configured decimal value (`0.6`). -/
def band060Bits : UInt32 := 0x3f19999a

/-- Exact f32 bits of the configured decimal value (`0.72`). -/
def band072Bits : UInt32 := 0x3f3851ec

/-- Exact f32 bits of the configured decimal value (`0.8`). -/
def band080Bits : UInt32 := 0x3f4ccccd

/-- Exact f32 bits of the configured decimal value (`0.4`). -/
def moist040Bits : UInt32 := 0x3ecccccd

/-- Exact f32 bits of the configured decimal value (`0.9`). -/
def gamma90Bits : UInt32 := 0x3f666666

/-- Exact f32 bits of the configured decimal value (`0.95`). -/
def gamma95Bits : UInt32 := 0x3f733333

/-- Exact f32 bits of the configured decimal value (`0.99`). -/
def gamma99Bits : UInt32 := 0x3f7d70a4

/-- Exact f32 bits of the configured decimal value (`0.00005`). -/
def alphaInit5e5Bits : UInt32 := 0x3851b717

/-- Exact f32 bits of the configured decimal value (`0.0001`). -/
def alphaInit1e4Bits : UInt32 := 0x38d1b717

/-- Exact f32 bits of the configured decimal value (`0.00001`). -/
def epsilon1e5Bits : UInt32 := 0x3727c5ac

/-- Exact f32 bits of the configured decimal value (`0.1`). -/
def eta01Bits : UInt32 := 0x3dcccccd

/-- Exact f32 bits of the configured decimal value (`0.25`). -/
def eta025Bits : UInt32 := 0x3e800000

/-- Exact f32 bits of the configured decimal value (`0.0000000001`). -/
def etaMin1e10Bits : UInt32 := 0x2edbe6ff

/-- Exact f32 bits of the configured decimal value (`0.999`). -/
def decay0999Bits : UInt32 := 0x3f7fbe77

/-- Exact f32 bits of the configured decimal value (`0.001`). -/
def meta1e3Bits : UInt32 := 0x3a83126f

/-- Exact f32 bits of the configured decimal value (`0.03`). -/
def meta3e2Bits : UInt32 := 0x3cf5c28f

/-- Exact f32 bits of the configured decimal value (`0.000001`). -/
def tie1e6Bits : UInt32 := 0x358637bd

/-- Exact f32 bits of the configured decimal value (`0.5`). -/
def epsStartBits : UInt32 := 0x3f000000

/-- Exact f32 bits of the configured decimal value (`0.05`). -/
def epsMinBits : UInt32 := 0x3d4ccccd

/-- Exact f32 bits of the configured decimal value (`0.99999`). -/
def epsDecayBits : UInt32 := 0x3f7fff58

/-- Exact f32 bits of the configured decimal value (`0.1`). -/
def optionEpsilonBits : UInt32 := 0x3dcccccd

end Acorn.Constants
