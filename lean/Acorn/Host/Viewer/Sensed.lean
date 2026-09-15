/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.Wire
import Acorn.Host.Viewer.WorldMemory

/-!
# Exact sensed-window admission

The map consumes the strict parsed document. Every coordinate is admitted
against that document's side, and all 121 terrain values belong to the closed
terrain domain before any observation is written. Agent epoch does not form
part of the durable world key.
-/
namespace Acorn.Host.Viewer

/-- A sensed window names its world, legal pose and complete terrain window. -/
structure Sensed where
  /-- Durable world and admitted allocation shape. -/
  key : MapKey
  /-- Horizontal pose lies inside the named world. -/
  x : Fin key.side.val
  /-- Vertical pose lies inside the named world. -/
  y : Fin key.side.val
  /-- Complete row-major sensor window. -/
  tiles : Vector (Fin 8) 121

/-- Decode a terrain kind without casts or truncation. -/
def terrainFromJson (value : Json.Value) : Except String (Fin 8) := do
  let kind ← value.natural
  if h : kind < 8 then return ⟨kind, h⟩ else throw "invalid sensed terrain kind"

/-- All shape and domain checks precede construction of a writable observation. -/
def sensedFromJson (value : Json.Value) : Except String Sensed := do
  let run ← runWord (← jsonField value "run_id")
  let side ← (← jsonField value "side").natural
  let side : MapSide ← if bound : 0 < side ∧ side ≤ mapSideCapacity then
    pure ⟨side, bound⟩ else throw "unsupported map side"
  let seed ← jsonWord (← jsonField value "seed")
  let key : MapKey := ⟨run, seed, side⟩
  let x ← (← jsonField value "x").natural
  let y ← (← jsonField value "y").natural
  let x : Fin side.val ← if hx : x < side.val then pure ⟨x, hx⟩
    else throw "sensed x outside world"
  let y : Fin side.val ← if hy : y < side.val then pure ⟨y, hy⟩
    else throw "sensed y outside world"
  let values ← (← jsonField value "tiles").list
  unless values.length == 121 do throw "incomplete sensed window"
  let tiles := (← values.mapM terrainFromJson).toArray
  if shape : tiles.size = 121 then
    return ⟨key, x, y, ⟨tiles, shape⟩⟩
  else throw "incomplete sensed window"

/-- A map observation cannot be substituted independently of the actual parsed wire text. -/
structure SensedEnvelope where
  /-- The original bounded input. -/
  source : WireText
  /-- The strict syntax tree. -/
  value : Json.Value
  /-- Exact source-to-syntax linkage. -/
  parsed : Json.parse source.val = .ok value
  /-- Complete typed observation. -/
  sensed : Sensed
  /-- Exact syntax-to-observation linkage. -/
  decoded : sensedFromJson value = .ok sensed

/-- Parse and admit the executing input before publishing sensed observations. -/
def SensedEnvelope.parse (source : WireText) : Except String SensedEnvelope :=
  match parsed : Json.parse source.val with
  | .error message => .error message
  | .ok value =>
    match decoded : sensedFromJson value with
    | .error message => .error message
    | .ok sensed => .ok ⟨source, value, parsed, sensed, decoded⟩

/-- A different world replaces the retained map instead of painting onto it. -/
def Sensed.absorb (sensed : Sensed) (previous : Option ((key : MapKey) × WorldMemory key)) :
    (key : MapKey) × WorldMemory key :=
  let memory := match previous with
    | none => WorldMemory.empty sensed.key
    | some ⟨key, memory⟩ =>
      if same : key = sensed.key then same ▸ memory else WorldMemory.empty sensed.key
  ⟨sensed.key, memory.absorb sensed.x sensed.y sensed.tiles⟩

/-- Every retained result belongs to the admitted observation's durable world. -/
theorem Sensed.absorb_key (sensed : Sensed) (previous : Option ((key : MapKey) × WorldMemory key)) :
    (sensed.absorb previous).1 = sensed.key := rfl

end Acorn.Host.Viewer
