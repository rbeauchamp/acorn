import Acorn.Host.Viewer.Wire
import Acorn.Host.Viewer.WorldMemory

namespace Acorn.Host.Viewer

structure Sensed where
  key : MapKey
  x : Fin key.side.val
  y : Fin key.side.val
  tiles : Vector (Fin 8) 121

def terrainFromJson (value : Json.Value) : Except String (Fin 8) := do
  let kind ← value.natural
  if h : kind < 8 then return ⟨kind, h⟩ else throw "invalid sensed terrain kind"

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

structure SensedEnvelope where
  source : WireText
  value : Json.Value
  parsed : Json.parse source.val = .ok value
  sensed : Sensed
  decoded : sensedFromJson value = .ok sensed

def SensedEnvelope.parse (source : WireText) : Except String SensedEnvelope :=
  match parsed : Json.parse source.val with
  | .error message => .error message
  | .ok value =>
    match decoded : sensedFromJson value with
    | .error message => .error message
    | .ok sensed => .ok ⟨source, value, parsed, sensed, decoded⟩

def Sensed.absorb (sensed : Sensed) (previous : Option ((key : MapKey) × WorldMemory key)) :
    (key : MapKey) × WorldMemory key :=
  let memory := match previous with
    | none => WorldMemory.empty sensed.key
    | some ⟨key, memory⟩ =>
      if same : key = sensed.key then same ▸ memory else WorldMemory.empty sensed.key
  ⟨sensed.key, memory.absorb sensed.x sensed.y sensed.tiles⟩

theorem Sensed.absorb_key (sensed : Sensed) (previous : Option ((key : MapKey) × WorldMemory key)) :
    (sensed.absorb previous).1 = sensed.key := rfl

end Acorn.Host.Viewer
