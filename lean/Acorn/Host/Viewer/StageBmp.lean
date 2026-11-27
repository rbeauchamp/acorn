import Acorn.Host.Viewer.WorldMemory
import Acorn.Host.Viewer.ServerFrame
import Acorn.Host.Viewer.BrowserNat

namespace Acorn.Host.Viewer.StageBmp

def bmpWidth : Nat := 288

def bmpHeight : Nat := 160

private def terrainRgb : Nat → UInt8 × UInt8 × UInt8
  | 0 => (0x3a, 0x6e, 0xa5)
  | 1 => (0xd9, 0xc5, 0x8b)
  | 2 => (0x7d, 0xa0, 0x5e)
  | 3 => (0x5c, 0x8a, 0x3f)
  | 4 => (0x2e, 0x6b, 0x2f)
  | 5 => (0x8a, 0x8a, 0x8a)
  | 6 => (0xb0, 0xb0, 0xb0)
  | 7 => (0xd4, 0xa0, 0x17)
  | _ => (0x0a, 0x0e, 0x14)

private def pushU16LE (buf : ByteArray) (v : Nat) : ByteArray :=
  (buf.push (v % 256).toUInt8).push ((v / 256) % 256).toUInt8

private def pushU32LE (buf : ByteArray) (v : Nat) : ByteArray :=
  let b0 := (v % 256).toUInt8
  let b1 := ((v / 256) % 256).toUInt8
  let b2 := ((v / 65536) % 256).toUInt8
  let b3 := ((v / 16777216) % 256).toUInt8
  (((buf.push b0).push b1).push b2).push b3

private def nightTint (phase : Nat) (rgb : UInt8 × UInt8 × UInt8) : UInt8 × UInt8 × UInt8 :=
  if phase < 4 then rgb
  else
    let depth := if phase == 4 || phase == 7 then 3 else 5
    let r := (rgb.1.toNat * (10 - depth) + 8 * depth) / 10
    let g := (rgb.2.1.toNat * (10 - depth) + 18 * depth) / 10
    let b := (rgb.2.2.toNat * (10 - depth) + 48 * depth) / 10
    (r.toUInt8, g.toUInt8, b.toUInt8)

private def tileColor (world : Option ((key : MapKey) × WorldMemory key))
    (frame : Option ServerFrame) (wx wy : Int) (phase : Nat) : UInt8 × UInt8 × UInt8 :=
  match frame with
  | none => (0x0a, 0x0e, 0x14)
  | some f =>
    let side : Int := f.summary.side
    let inWorld := 0 ≤ wx && wx < side && 0 ≤ wy && wy < side
    let dx := wx - f.summary.x
    let dy := wy - f.summary.y
    let isAgent := dx == 0 && dy == 0
    let isFacing := match f.summary.facing with
      | 0 => dx == 0 && dy == -1
      | 1 => dx == 0 && dy == 1
      | 2 => dx == 1 && dy == 0
      | _ => dx == -1 && dy == 0
    let isReachTarget := f.gkind == 1 && (wx - f.gx).natAbs ≤ 1 && (wy - f.gy).natAbs ≤ 1
    if isAgent then (0xff, 0xff, 0xff)
    else if isFacing then (0x79, 0xc0, 0xff)
    else if isReachTarget then (0xff, 0xd2, 0x4a)
    else if !inWorld then (0x04, 0x06, 0x09)
    else
      let inSensor := -5 ≤ dx && dx ≤ 5 && -5 ≤ dy && dy ≤ 5
      let base :=
        if inSensor then
          let idx := ((dy + 5).toNat) * 11 + (dx + 5).toNat
          let extra := f.tileExtra[idx]?.getD 0
          if extra % 2 == 1 then (0xf0, 0x88, 0x3e)
          else if (extra / 2) % 2 == 1 then (0x8b, 0x5a, 0x2b)
          else terrainRgb (f.tiles[idx]?.getD 255)
        else
          match world with
          | some ⟨key, mem⟩ =>
            match mapIndex key.side wx wy with
            | some mapIdx =>
              let byte := mem.observations.bytes[mapIdx.val]'(by
                rw [mem.observations.size]; exact mapIdx.isLt)
              if byte == 255 then (0x0a, 0x0e, 0x14)
              else terrainRgb byte.toNat
            | none => (0x0a, 0x0e, 0x14)
          | none => (0x0a, 0x0e, 0x14)
      let isBorder := inSensor && (dx == -5 || dx == 5 || dy == -5 || dy == 5)
      let tinted := nightTint phase base
      if isBorder then
        let r := min 255 (tinted.1.toNat + 36)
        let g := min 255 (tinted.2.1.toNat + 44)
        let b := min 255 (tinted.2.2.toNat + 56)
        (r.toUInt8, g.toUInt8, b.toUInt8)
      else tinted

def render (world : Option ((key : MapKey) × WorldMemory key))
    (frame : Option ServerFrame) : ByteArray := Id.run do
  let rowBytes := bmpWidth * 3
  let pixelBytes := rowBytes * bmpHeight
  let fileSize := 54 + pixelBytes
  let mut out := ByteArray.emptyWithCapacity fileSize
  out := (out.push 0x42).push 0x4d
  out := pushU32LE out fileSize
  out := pushU32LE out 0
  out := pushU32LE out 54
  out := pushU32LE out 40
  out := pushU32LE out bmpWidth
  out := pushU32LE out bmpHeight
  out := pushU16LE out 1
  out := pushU16LE out 24
  out := pushU32LE out 0
  out := pushU32LE out pixelBytes
  out := pushU32LE out 2835
  out := pushU32LE out 2835
  out := pushU32LE out 0
  out := pushU32LE out 0
  let centerX : Int := match frame with | some f => f.summary.x | none => 0
  let centerY : Int := match frame with | some f => f.summary.y | none => 0
  let phase : Nat := match frame with
    | some f =>
      if f.summary.dayLength > 0 then
        BrowserNat.dayPhase.eval (BrowserNat.dayArguments f.summary.worldStep f.summary.dayLength)
      else 0
    | none => 0
  let tilesW := bmpWidth / 2
  let tilesH := bmpHeight / 2
  let halfW : Int := (tilesW / 2 : Nat)
  let halfH : Int := (tilesH / 2 : Nat)
  for rowFromBottom in [:bmpHeight] do
    let py := bmpHeight - 1 - rowFromBottom
    let ty : Int := (py / 2 : Nat)
    let wy := centerY - halfH + ty
    for tx in [:tilesW] do
      let wx := centerX - halfW + (tx : Int)
      let (r, g, b) := tileColor world frame wx wy phase
      out := (((((out.push b).push g).push r).push b).push g).push r
  return out

end Acorn.Host.Viewer.StageBmp
