/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornSpec.World
import AcornSpec.StudySchema

/-!
# Static Reach-solvability: an optimistic necessary condition

For each held-out world, both curriculum Reach
targets must have a goal-region tile (Chebyshev radius 3, inside the
campaign box) in the same optimistic-passability component as the spawn
tile. The passability graph is **optimistic** — every tile that could ever
be entered under any action sequence counts as passable, which here is
every non-Mountain tile (trees are choppable, water is boatable) — so
component connectivity is a *necessary* condition for Reach success,
independent of budgets, policies and stream continuity: an agent cannot
cross a component boundary of the optimistic graph by any action sequence.

A failing world dooms the Reach-success conjunct's contribution from that
target. This executable graph calculation is not itself a theorem relating
every world transition to graph connectivity.
-/

namespace AcornSpec

/-- Whether a base tile can ever be entered under any action sequence:
everything but mountains (trees are choppable, water is boatable, and the
harvest log only ever turns trees into walkable forest). -/
@[inline]
def TileKind.optimisticallyPassable : TileKind → Bool
  | .mountain => false
  | _ => true

/-- Flood fill (iterative frontier BFS) over the optimistic passability
graph inside the campaign box, from the spawn tile. Returns the visited
bitmap (one byte per box tile, row-major). -/
def floodFill (w : World) : ByteArray :=
  let side := w.side.toNat
  let idx (x y : Nat) : Nat := y * side + x
  let passable (x y : Nat) : Bool :=
    (w.baseKind (x : Int) (y : Int)).optimisticallyPassable
  let rec
    /-- Process the frontier queue: `fuel` bounds work at one dequeue per
    box tile, which a monotone visited set never exceeds. -/
    go (visited : ByteArray) (queue : Array (Nat × Nat)) (head : Nat) :
        Nat → ByteArray
      | 0 => visited
      | fuel + 1 =>
        if h : head < queue.size then
          let (x, y) := queue[head]
          let step (visited : ByteArray) (queue : Array (Nat × Nat))
              (nx ny : Int) : ByteArray × Array (Nat × Nat) :=
            if 0 ≤ nx ∧ nx < (side : Int) ∧ 0 ≤ ny ∧ ny < (side : Int) then
              let (ux, uy) := (nx.toNat, ny.toNat)
              if visited.get! (idx ux uy) == 0 ∧ passable ux uy then
                (visited.set! (idx ux uy) 1, queue.push (ux, uy))
              else (visited, queue)
            else (visited, queue)
          let (visited, queue) := step visited queue ((x : Int) + 1) (y : Int)
          let (visited, queue) := step visited queue ((x : Int) - 1) (y : Int)
          let (visited, queue) := step visited queue (x : Int) ((y : Int) + 1)
          let (visited, queue) := step visited queue (x : Int) ((y : Int) - 1)
          go visited queue (head + 1) fuel
        else visited
  let visited := ByteArray.mk (Array.replicate (side * side) 0)
  let sx := w.bx.toNat
  let sy := w.by'.toNat
  let visited := visited.set! (idx sx sy) 1
  go visited #[(sx, sy)] 0 (side * side)

/-- Whether some campaign-box tile within the Reach completion radius of
`(tx, ty)` is reachable in the optimistic graph. -/
def regionReachable (w : World) (visited : ByteArray) (tx ty : Int) : Bool :=
  let side := w.side.toNat
  let r : Int := 3
  (Array.range 7).any fun dy =>
    (Array.range 7).any fun dx =>
      let x := tx + (dx : Int) - r
      let y := ty + (dy : Int) - r
      if 0 ≤ x ∧ x < (side : Int) ∧ 0 ≤ y ∧ y < (side : Int) then
        visited.get! (y.toNat * side + x.toNat) == 1
      else false

/-- The static necessary condition for one held-out seed: both curriculum
Reach targets have a reachable goal-region tile. -/
def reachTargetsConnected (seed : UInt64) : Bool :=
  let w := World.new seed studyWorldSide
  let visited := floodFill w
  let curriculum := standardCurriculum seed studyWorldSide
  (Array.range studyGoals).all fun g =>
    match curriculum[g]! with
    | .reach tx ty => regionReachable w visited tx ty
    | _ => true

end AcornSpec
