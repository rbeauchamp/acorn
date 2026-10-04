/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.CertificateSearch
import Acorn.Host.Curriculum

/-!
# Native certificate tool

For each listed seed the tool generates the standard world, proposes
certificates with `Acorn.Host.CertificateSearch` and prints what the checkers of
`Acorn.Host.Certificate` accepted: for each of the two reach goals a replay
certificate from the spawn or a blocked certificate, and for wood, stone and gold
a stance and a replay certificate that collects one item from the spawn.

A printed `feasible`, `blocked` or `certified` verdict is rendered from a
certificate value, which exists only when its checker accepted it;
`AcornVerif.CurrentCertificates` states what that establishes. `uncertified`
establishes nothing. Every certificate concerns the generated world at its spawn,
before any step: it is not a statement about the world a campaign leaves at the
start of a later attempt.

The tool's import closure holds neither the agent composition, the campaign
runner nor the random-policy comparator; the boundary audit refuses such an
import. Its only world steps replay candidate action lists: each candidate once
while it is settled, and at most once more by the replay checker. A candidate the
checker rejects, for instance one longer than the cap, has been replayed and is
not printed. Its counts are over the listed seeds and do not estimate a fraction
of the 2^64 seeds.
-/
namespace Acorn.Host.CertificateDriver
open CertificateSearch

/-- The most tiles a proposed blocked region may hold. The checker's work is quadratic
in the region size. -/
def regionBudget : Nat := 4096

/-- What the tool established about one reach goal from a world. A `feasible` or
`blocked` value holds a certificate its checker accepted. -/
inductive ReachFinding {config : WorldConfig} (world : World config) (target : Position)
    (cap : Nat) where
  /-- A replay certificate: the goal box is reached within the cap. -/
  | feasible (certificate : ReplayCertificate world (.reach target) cap)
  /-- A blocked certificate, for any body when `boat` is true and otherwise for a body
  that owns no boat. -/
  | blocked (boat : Bool)
      (certificate : BlockedCertificate config boat target world.body.position.position)
  /-- No proposed certificate was accepted. -/
  | uncertified

/-- Propose and check certificates for one reach goal: a replay of the searched path,
then a region of mountains alone, then a region of mountains and water. -/
def certifyReach {config : WorldConfig} (world : World config) (target : Position) (cap : Nat)
    (path : Option (List Action)) : ReachFinding world target cap :=
  let goal := Goal.reach target
  let start := world.body.position.position
  let replay := path.bind fun moves =>
    ReplayCertificate.check world goal cap
      (settle (world.setGoal goal) (if moves.isEmpty then [.wait] else moves))
  match replay with
  | some certificate => .feasible certificate
  | none =>
    match (region config true target regionBudget).bind
        (BlockedCertificate.check config true target start) with
    | some certificate => .blocked true certificate
    | none =>
      match (region config false target regionBudget).bind
          (BlockedCertificate.check config false target start) with
      | some certificate => .blocked false certificate
      | none => .uncertified

/-- What the tool established about one harvested item from a world: a stance, and a
replay that collects one item. Each present value holds a certificate its checker
accepted. -/
structure ItemFinding {config : WorldConfig} (world : World config) (item : Item)
    (cap : Nat) where
  /-- A stance facing a tile that yields the item. -/
  stance : Option (StanceCertificate config item)
  /-- A replay from the world that ends holding one item. -/
  obtained : Option (ReplayCertificate world (.collect item 1) cap)

/-- Propose and check the stance one move from a searched approach tile, and the replay
of the path to it followed by that move and a harvest. -/
def certifyItem {config : WorldConfig} (world : World config) (arrival : Array UInt8)
    (item : Item) (cap : Nat) (approach : Option (BoxPosition config × Direction)) :
    ItemFinding world item cap :=
  match approach with
  | none => ⟨none, none⟩
  | some (tile, direction) =>
    let goal := Goal.collect item 1
    let planned := pathTo config arrival tile ++ [direction.action, .harvest]
    ⟨(neighbor config tile direction).bind fun stance =>
        StanceCertificate.check config item stance direction,
      ReplayCertificate.check world goal cap (settle (world.setGoal goal) planned)⟩

/-- An action list as one digit per action, the action's index. -/
def actionText (actions : List Action) : String :=
  String.join (actions.map fun action => toString action.index.val)

/-- A tile as its two signed coordinates. -/
def positionText (tile : Position) : String := s!"{tile.x.val},{tile.y.val}"

/-- Direction names. -/
def directionText : Direction → String
  | .north => "north" | .south => "south" | .east => "east" | .west => "west"

/-- Item names. -/
def itemText : Item → String
  | .wood => "wood" | .stone => "stone" | .food => "food" | .gold => "gold"

/-- One seed's output lines, and the verdict labels the summary counts. -/
structure Report where
  /-- Lines in print order. -/
  lines : List String
  /-- One label per verdict. -/
  labels : List String

/-- The line and label of a reach finding. -/
def reachLine {config : WorldConfig} {world : World config} {target : Position} {cap : Nat}
    (seed : UInt64) (goal : Nat) (finding : ReachFinding world target cap) : String × String :=
  let head := s!"reach seed={seed} goal={goal} target={positionText target}"
  match finding with
  | .feasible certificate =>
    (s!"{head} verdict=feasible steps={certificate.actions.length} " ++
      s!"actions={actionText certificate.actions}", s!"reach{goal}=feasible")
  | .blocked boat certificate =>
    let scope := if boat then "any-body" else "no-boat"
    (s!"{head} verdict=blocked scope={scope} cells={certificate.cells.length} region=" ++
      ";".intercalate (certificate.cells.map positionText), s!"reach{goal}=blocked-{scope}")
  | .uncertified => (s!"{head} verdict=uncertified", s!"reach{goal}=uncertified")

/-- The lines and labels of an item finding. -/
def itemLines {config : WorldConfig} {world : World config} {item : Item} {cap : Nat}
    (seed : UInt64) (finding : ItemFinding world item cap) : List String × List String :=
  let name := itemText item
  let stance := match finding.stance with
    | some certificate =>
      (s!"stance seed={seed} item={name} verdict=certified " ++
        s!"tile={positionText certificate.stance.position} " ++
        s!"facing={directionText certificate.direction}", s!"stance-{name}=certified")
    | none => (s!"stance seed={seed} item={name} verdict=uncertified",
        s!"stance-{name}=uncertified")
  let obtained := match finding.obtained with
    | some certificate =>
      (s!"obtain seed={seed} item={name} count=1 verdict=feasible " ++
        s!"steps={certificate.actions.length} actions={actionText certificate.actions}",
        s!"obtain-{name}=feasible")
    | none => (s!"obtain seed={seed} item={name} count=1 verdict=uncertified",
        s!"obtain-{name}=uncertified")
  ([stance.1, obtained.1], [stance.2, obtained.2])

/-- Generate one seed's standard world, search it once and check every proposal. No
agent, comparator or attempt is constructed. -/
@[noinline] def execute (seed : UInt64) (side : Coordinate) (cap : Nat) :
    Except String Report := do
  let config ← (WorldConfig.standard seed side).mapError fun _ => "world configuration refused"
  let world ← (World.initial config).mapError fun _ => "world generation refused"
  let curriculum := standardCurriculum config config.raw.seed
  let some (Goal.reach near, _) := curriculum[3]?
    | throw "curriculum goal 3 is not a reach goal"
  let some (Goal.reach far, _) := curriculum[7]?
    | throw "curriculum goal 7 is not a reach goal"
  let (found, arrival) := explore config world.body.position near far
  let nearLine := reachLine seed 3
    (certifyReach world near cap (found.near.map (pathTo config arrival)))
  let farLine := reachLine seed 7
    (certifyReach world far cap (found.far.map (pathTo config arrival)))
  let wood := itemLines seed (certifyItem world arrival .wood cap found.wood)
  let stone := itemLines seed (certifyItem world arrival .stone cap found.stone)
  let gold := itemLines seed (certifyItem world arrival .gold cap found.gold)
  return {
    lines := [s!"world seed={seed} side={side.val} cap={cap} " ++
      s!"spawn={positionText world.body.position.position}", nearLine.1, farLine.1] ++
      wood.1 ++ stone.1 ++ gold.1
    labels := [nearLine.2, farLine.2] ++ wood.2 ++ stone.2 ++ gold.2 }

/-- Decimal digits only; no sign, separator or other notation. -/
def natural (text : String) : Option Nat :=
  if text.isEmpty || !text.toList.all (fun c => '0' ≤ c && c ≤ '9') then none else text.toNat?

/-- Add one to a label's count, keeping first-seen order. -/
def count (tally : List (String × Nat)) (label : String) : List (String × Nat) :=
  if tally.any (·.1 == label) then
    tally.map fun entry => if entry.1 == label then (entry.1, entry.2 + 1) else entry
  else tally ++ [(label, 1)]

/-- Admit every argument before generating any world, then print each seed's lines as
they are produced and the counts over the list. -/
def dispatch (arguments : List String) : IO UInt32 := do
  let usage := "usage: world-certificates SIDE CAP SEED [SEED ...]"
  let sideText :: capText :: seedTexts := arguments | throw (IO.userError usage)
  let some side := (natural sideText).bind fun value => Coordinate.checked (value : Int)
    | throw (IO.userError s!"invalid side: {sideText}")
  let some cap := natural capText | throw (IO.userError s!"invalid cap: {capText}")
  if seedTexts.isEmpty then throw (IO.userError usage)
  let seeds ← seedTexts.mapM fun text =>
    match natural text with
    | some value =>
      if value < 2 ^ 64 then pure value.toUInt64
      else throw (IO.userError s!"seed overflow: {text}")
    | none => throw (IO.userError s!"invalid seed: {text}")
  let output ← IO.getStdout
  let mut tally : List (String × Nat) := []
  for seed in seeds do
    match execute seed side cap with
    | .error refusal =>
      IO.println s!"world seed={seed} side={side.val} cap={cap} refused={refusal}"
      tally := count tally "world=refused"
    | .ok report =>
      for line in report.lines do IO.println line
      for label in report.labels do tally := count tally label
    output.flush
  for (label, seen) in tally do
    IO.println s!"summary {label} count={seen} of={seeds.length}"
  IO.println ("note counts are over the listed seeds only and do not estimate a fraction " ++
    "of the 2^64 seeds; every certificate is from the spawn of the generated world")
  return 0

end Acorn.Host.CertificateDriver

/-- Native admission failure produces a failing exit status. -/
def main (arguments : List String) : IO UInt32 := do
  try Acorn.Host.CertificateDriver.dispatch arguments
  catch error =>
    try IO.eprintln s!"world-certificates: {error}" catch _ => pure ()
    return 1
