import Acorn.Host.Viewer.WorldMemory
import Acorn.Host.Viewer.ServerFrame
import Acorn.Host.Viewer.BrowserNat
import Acorn.Host.Viewer.Broadcast
import Acorn.Host.Viewer.BrowserKernel

namespace Acorn.Host.Viewer.StageBmp

def bmpWidth : Nat := 288

def bmpHeight : Nat := 160

inductive StageState where
  | unavailable (headline : String) (detail : String) (fault : Bool)
  | available (world : Option ((key : MapKey) × WorldMemory key)) (frame : ServerFrame)
      (banner : Option (String × Bool))

def fromSnapshot (snapshot : BroadcastSnapshot) (nowMonoMs : Nat) : StageState :=
  let lifecycle := snapshot.lifecycle
  let unaskedStop := match snapshot.detail with
    | some d => unaskedStops.contains d.transition
    | none => false
  let termWarning := snapshot.detail.bind (controlWarning lifecycle)
  let liveness := snapshot.observer.streamLiveness lifecycle unaskedStop
    snapshot.runningSinceMonoMs nowMonoMs
  let (statusText, isFault) : String × Bool :=
    match liveness with
    | .fault true => ("CORE FAILED - EXHAUSTED", true)
    | .fault false => ("CORE FAILED - RESTARTING", true)
    | .stale true => ("STREAM STALE - NO FRESH FRAMES", true)
    | .stale false => ("STREAM STALE - NO CAPTURE", true)
    | .waitingForCapture => ("AWAITING FIRST FRAME", false)
    | .busy _ =>
      match lifecycle.phaseValue with
      | .starting _ => ("CORE STARTING", false)
      | .stopping _ => ("CORE STOPPING", false)
      | .archiving => ("CORE CLEARING", false)
      | _ => ("CORE BUSY", false)
    | .idle =>
      if termWarning.isSome then ("CORE STOPPED - WARNING", true)
      else ("CORE STOPPED", false)
    | .live => ("LIVE", false)
  match snapshot.observer.latest with
  | none => .unavailable "NO TELEMETRY" statusText isFault
  | some frame =>
    let banner := if liveness == .live then none else some (statusText, isFault)
    .available snapshot.world frame banner

private def glyphRows (c : Char) : Array Nat :=
  match c.toUpper with
  | 'A' => #[0x0e, 0x11, 0x11, 0x1f, 0x11, 0x11, 0x11]
  | 'B' => #[0x1e, 0x11, 0x11, 0x1e, 0x11, 0x11, 0x1e]
  | 'C' => #[0x0e, 0x11, 0x10, 0x10, 0x10, 0x11, 0x0e]
  | 'D' => #[0x1c, 0x12, 0x11, 0x11, 0x11, 0x12, 0x1c]
  | 'E' => #[0x1f, 0x10, 0x10, 0x1e, 0x10, 0x10, 0x1f]
  | 'F' => #[0x1f, 0x10, 0x10, 0x1e, 0x10, 0x10, 0x10]
  | 'G' => #[0x0e, 0x11, 0x10, 0x17, 0x11, 0x11, 0x0f]
  | 'H' => #[0x11, 0x11, 0x11, 0x1f, 0x11, 0x11, 0x11]
  | 'I' => #[0x0e, 0x04, 0x04, 0x04, 0x04, 0x04, 0x0e]
  | 'J' => #[0x07, 0x02, 0x02, 0x02, 0x12, 0x12, 0x0c]
  | 'K' => #[0x11, 0x12, 0x14, 0x18, 0x14, 0x12, 0x11]
  | 'L' => #[0x10, 0x10, 0x10, 0x10, 0x10, 0x10, 0x1f]
  | 'M' => #[0x11, 0x1b, 0x15, 0x15, 0x11, 0x11, 0x11]
  | 'N' => #[0x11, 0x19, 0x15, 0x13, 0x11, 0x11, 0x11]
  | 'O' => #[0x0e, 0x11, 0x11, 0x11, 0x11, 0x11, 0x0e]
  | 'P' => #[0x1e, 0x11, 0x11, 0x1e, 0x10, 0x10, 0x10]
  | 'Q' => #[0x0e, 0x11, 0x11, 0x11, 0x15, 0x12, 0x0d]
  | 'R' => #[0x1e, 0x11, 0x11, 0x1e, 0x14, 0x12, 0x11]
  | 'S' => #[0x0f, 0x10, 0x10, 0x0e, 0x01, 0x01, 0x1e]
  | 'T' => #[0x1f, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04]
  | 'U' => #[0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x0e]
  | 'V' => #[0x11, 0x11, 0x11, 0x11, 0x11, 0x0a, 0x04]
  | 'W' => #[0x11, 0x11, 0x11, 0x15, 0x15, 0x1b, 0x11]
  | 'X' => #[0x11, 0x11, 0x0a, 0x04, 0x0a, 0x11, 0x11]
  | 'Y' => #[0x11, 0x11, 0x0a, 0x04, 0x04, 0x04, 0x04]
  | 'Z' => #[0x1f, 0x01, 0x02, 0x04, 0x08, 0x10, 0x1f]
  | '0' => #[0x0e, 0x11, 0x13, 0x15, 0x19, 0x11, 0x0e]
  | '1' => #[0x04, 0x0c, 0x04, 0x04, 0x04, 0x04, 0x0e]
  | '2' => #[0x0e, 0x11, 0x01, 0x06, 0x08, 0x10, 0x1f]
  | '3' => #[0x1e, 0x01, 0x01, 0x0e, 0x01, 0x01, 0x1e]
  | '4' => #[0x02, 0x06, 0x0a, 0x12, 0x1f, 0x02, 0x02]
  | '5' => #[0x1f, 0x10, 0x1e, 0x01, 0x01, 0x11, 0x0e]
  | '6' => #[0x0e, 0x10, 0x1e, 0x11, 0x11, 0x11, 0x0e]
  | '7' => #[0x1f, 0x01, 0x02, 0x04, 0x08, 0x08, 0x08]
  | '8' => #[0x0e, 0x11, 0x11, 0x0e, 0x11, 0x11, 0x0e]
  | '9' => #[0x0e, 0x11, 0x11, 0x0f, 0x01, 0x01, 0x0e]
  | '-' => #[0x00, 0x00, 0x00, 0x1f, 0x00, 0x00, 0x00]
  | ':' => #[0x00, 0x04, 0x04, 0x00, 0x04, 0x04, 0x00]
  | '/' => #[0x01, 0x02, 0x02, 0x04, 0x08, 0x08, 0x10]
  | '.' => #[0x00, 0x00, 0x00, 0x00, 0x00, 0x0c, 0x0c]
  | _ => #[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

private def textBit (chars : Array Char) (scale x0 y0 px py : Nat) : Bool :=
  if px < x0 || py < y0 then false
  else
    let dy := (py - y0) / scale
    if dy ≥ 7 then false
    else
      let dx := (px - x0) / scale
      let charIdx := dx / 6
      let col := dx % 6
      if col ≥ 5 then false
      else
        match chars[charIdx]? with
        | none => false
        | some c =>
          let bits := (glyphRows c)[dy]?.getD 0
          ((bits >>> (4 - col)) &&& 1) == 1

private def centeredX (charCount scale : Nat) : Nat :=
  let totalW := charCount * 6 * scale
  if totalW < bmpWidth then (bmpWidth - totalW) / 2 else 4

def unavailablePixel (headChars detailChars : Array Char) (fault : Bool)
    (px py : Nat) : UInt8 × UInt8 × UInt8 :=
  let inCard := 16 ≤ px && px < 272 && 36 ≤ py && py < 124
  let onBorder := inCard && (px < 18 || px ≥ 270 || py < 38 || py ≥ 122)
  if onBorder then
    if fault then (0xff, 0x7b, 0x72) else (0x48, 0x58, 0x6e)
  else if !inCard then
    (0x0a, 0x0e, 0x14)
  else
    let hx0 := centeredX headChars.size 2
    let dx0 := centeredX detailChars.size 1
    if textBit headChars 2 hx0 54 px py then
      if fault then (0xff, 0x7b, 0x72) else (0xe6, 0xed, 0xf3)
    else if textBit detailChars 1 dx0 86 px py then
      if fault then (0xff, 0x7b, 0x72) else (0xf0, 0x88, 0x3e)
    else
      (0x11, 0x16, 0x1d)

private def bannerPixel (chars : Array Char) (fault : Bool)
    (px py : Nat) : UInt8 × UInt8 × UInt8 :=
  if py == 13 then
    if fault then (0x5a, 0x2a, 0x28) else (0x4a, 0x34, 0x17)
  else
    let x0 := centeredX chars.size 1
    if textBit chars 1 x0 3 px py then
      if fault then (0xff, 0x7b, 0x72) else (0xf0, 0x88, 0x3e)
    else
      if fault then (0x23, 0x12, 0x12) else (0x20, 0x17, 0x0c)

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
    (f : ServerFrame) (wx wy : Int) (phase : Nat) : UInt8 × UInt8 × UInt8 :=
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

def render (state : StageState) : ByteArray := Id.run do
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
  match state with
  | .unavailable headline detail fault =>
    let headChars := headline.toList.toArray
    let detailChars := detail.toList.toArray
    for rowFromBottom in [:bmpHeight] do
      let py := bmpHeight - 1 - rowFromBottom
      for px in [:bmpWidth] do
        let (r, g, b) := unavailablePixel headChars detailChars fault px py
        out := ((out.push b).push g).push r
  | .available world f banner =>
    let centerX : Int := f.summary.x
    let centerY : Int := f.summary.y
    let phase : Nat :=
      if f.summary.dayLength > 0 then
        BrowserNat.dayPhase.eval (BrowserNat.dayArguments f.summary.worldStep f.summary.dayLength)
      else 0
    let tilesW := bmpWidth / 2
    let tilesH := bmpHeight / 2
    let halfW : Int := (tilesW / 2 : Nat)
    let halfH : Int := (tilesH / 2 : Nat)
    let bannerInfo := banner.map fun (text, fault) => (text.toList.toArray, fault)
    for rowFromBottom in [:bmpHeight] do
      let py := bmpHeight - 1 - rowFromBottom
      match bannerInfo with
      | some (bChars, bFault) =>
        if py < 14 then
          for px in [:bmpWidth] do
            let (r, g, b) := bannerPixel bChars bFault px py
            out := ((out.push b).push g).push r
        else
          let ty : Int := (py / 2 : Nat)
          let wy := centerY - halfH + ty
          for tx in [:tilesW] do
            let wx := centerX - halfW + (tx : Int)
            let (r, g, b) := tileColor world f wx wy phase
            out := (((((out.push b).push g).push r).push b).push g).push r
      | none =>
        let ty : Int := (py / 2 : Nat)
        let wy := centerY - halfH + ty
        for tx in [:tilesW] do
          let wx := centerX - halfW + (tx : Int)
          let (r, g, b) := tileColor world f wx wy phase
          out := (((((out.push b).push g).push r).push b).push g).push r
  return out

theorem fromSnapshot_none_unavailable (snapshot : BroadcastSnapshot) (nowMonoMs : Nat)
    (hNone : snapshot.observer.latest = none) :
    ∃ h d f, fromSnapshot snapshot nowMonoMs = .unavailable h d f := by
  unfold fromSnapshot
  dsimp only
  rw [hNone]
  exact ⟨_, _, _, rfl⟩

end Acorn.Host.Viewer.StageBmp
