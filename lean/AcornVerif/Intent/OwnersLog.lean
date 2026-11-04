/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.LeanIntentBridge

/-!
# The owners' log

Acorn's owners' log, the one value of `LeanIntent.OwnersLog` that lean-intent's confirmation check
reads from the build (`LeanIntent.Confirmation.Read.check`): each statement as the text
`LeanIntent.Statement.print` writes, in a string literal broken across source lines by string gaps,
which add nothing to the text. It holds, in order:

* the owners declaration, naming the principal `owner`;
* the owner's delegation `agents-below-intent`, of 2026-10-29, of every decision below their intent
  on the day and hash records to the principal `agents`, which may confirm, decline and retract and
  may not pass it on;
* the agents' eleven answers of 2026-10-29 under that delegation, which named the record's revision
  by a commit and its predicates in a short form;
* the agents' retraction of each of them on 2026-11-03, since the confirmation check compares an
  answer's revision and predicate with the texts it computes from the build;
* and the answers the agents gave again on 2026-11-03, with the same verdicts, against those texts:
  for each record, the question every revision asks, whether its rendering restates the intent, and
  each decision on a consequence. `LeanIntent.Confirmation.Read.answerStatement` wrote each, from a
  process that imports the modules `intent-check` reads, so that its texts are the checker's;
* for the record of contract 1 of Acorn's mission contract, the interface every world meets
  (`AcornVerif.Intent.WorldInterface.worldInterface`), the origin statement `contract-1-origin`,
  which says that the agents wrote the plain restatement the record was written from and that the
  owner adopted it, and the owner's answer `contract-1-restatement`, which attaches the owner's
  confirmation of that restatement, given on 2026-11-03 in the words the two statements hold as
  their source, to the record's current revision. The owner saw the restatement, not the record or
  its rendering; the record's confirmation file, `lean/AcornVerif/Intent/WorldInterface.md`, says
  so, and gives the status of every consequence of the record.

The statements that are the owner's are the declaration, the delegation, and the origin and answer
of 2026-11-03 for the interface record; every other answer names the agents, acting under the
delegation, as its author. The decisions on the day and hash records and their reasons are
described in `AcornVerif.Intent.Decisions` and the pilot report, `docs/spec-first-pilot.md`.
-/

namespace AcornVerif.Intent.Decisions

open LeanIntent

/-- The owners' log of the day and hash records, each statement as `LeanIntent.Statement.print`
writes it. -/
def ownersLog : OwnersLog := ⟨[
  "lean-intent statement 1\n\
    kind owners\n\
    project acorn\n\
    id owners\n\
    date 2026-10-29\n\
    reference https://github.com/rbeauchamp/acorn\n\
    principals 1\n\
    principal owner\n\
    keys 0\n\
    no threshold\n\
    ",
  "lean-intent statement 1\n\
    kind delegation\n\
    project acorn\n\
    id agents-below-intent\n\
    date 2026-10-29\n\
    words 1\n\
    | Yes, apply it\n\
    by owner\n\
    as owner\n\
    delegate agents\n\
    keys 0\n\
    records 2\n\
    record AcornVerif.Intent.DayCycle.dayCycle\n\
    record AcornVerif.Intent.Hash.hashes\n\
    may confirm yes\n\
    may decline yes\n\
    may retract yes\n\
    may pass on no\n\
    ",
  "lean-intent statement 1\n\
    kind answer\n\
    project acorn\n\
    id day-1\n\
    date 2026-10-29\n\
    reference docs/spec-first-pilot.md, The decisions made on the owner's behalf\n\
    by agents\n\
    under agents-below-intent\n\
    record AcornVerif.Intent.DayCycle.dayCycle\n\
    revision 1\n\
    | commit 50051c749d9b94ea577bba2bde577552337df271\n\
    consequence every day lasts the same even number of ticks, at least two, placed alike\n\
    shown as entailment\n\
    predicate 1\n\
    | fun w => 2 ≤ w.length ∧ w.length % 2 = 0 ∧ ∀ t, w.night (t + w.length) = w.night t\n\
    verdict confirmed\n\
    ",
  "lean-intent statement 1\n\
    kind answer\n\
    project acorn\n\
    id day-2\n\
    date 2026-10-29\n\
    reference docs/spec-first-pilot.md, The decisions made on the owner's behalf\n\
    by agents\n\
    under agents-below-intent\n\
    record AcornVerif.Intent.DayCycle.dayCycle\n\
    revision 1\n\
    | commit 50051c749d9b94ea577bba2bde577552337df271\n\
    consequence every action costs more at any night moment than at any daytime moment\n\
    shown as entailment\n\
    predicate 1\n\
    | fun w => ∀ c a t t', w.night t = true → w.night t' = false → w.cost t' c a < w.cost t c \
    a\n\
    verdict confirmed\n\
    ",
  "lean-intent statement 1\n\
    kind answer\n\
    project acorn\n\
    id day-3\n\
    date 2026-10-29\n\
    reference docs/spec-first-pilot.md, The decisions made on the owner's behalf\n\
    by agents\n\
    under agents-below-intent\n\
    record AcornVerif.Intent.DayCycle.dayCycle\n\
    revision 1\n\
    | commit 50051c749d9b94ea577bba2bde577552337df271\n\
    consequence what the agent sees always tells day from night\n\
    shown as entailment\n\
    predicate 1\n\
    | fun w => ∀ t t' c c', w.sees t c = w.sees t' c' → w.night t = w.night t'\n\
    verdict confirmed\n\
    ",
  "lean-intent statement 1\n\
    kind answer\n\
    project acorn\n\
    id day-4\n\
    date 2026-10-29\n\
    reference docs/spec-first-pilot.md, The decisions made on the owner's behalf\n\
    by agents\n\
    under agents-below-intent\n\
    record AcornVerif.Intent.DayCycle.dayCycle\n\
    revision 1\n\
    | commit 50051c749d9b94ea577bba2bde577552337df271\n\
    consequence a day may last 1000 ticks\n\
    shown as possibility\n\
    predicate 1\n\
    | fun w => w.length = 1000\n\
    verdict confirmed\n\
    ",
  "lean-intent statement 1\n\
    kind answer\n\
    project acorn\n\
    id day-5a\n\
    date 2026-10-29\n\
    reference docs/spec-first-pilot.md, The decisions made on the owner's behalf\n\
    by agents\n\
    under agents-below-intent\n\
    record AcornVerif.Intent.DayCycle.dayCycle\n\
    revision 1\n\
    | commit 50051c749d9b94ea577bba2bde577552337df271\n\
    consequence what the agent sees always tells it which quarter of the day it is in\n\
    shown as entailment\n\
    predicate 1\n\
    | fun w => ∃ start, ∀ t t' c c', w.sees t c = w.sees t' c' → quarter w.length start t = qu\
    arter w.length start t'\n\
    verdict confirmed\n\
    ",
  "lean-intent statement 1\n\
    kind answer\n\
    project acorn\n\
    id day-5b\n\
    date 2026-10-29\n\
    reference docs/spec-first-pilot.md, The decisions made on the owner's behalf\n\
    by agents\n\
    under agents-below-intent\n\
    record AcornVerif.Intent.DayCycle.dayCycle\n\
    revision 1\n\
    | commit 50051c749d9b94ea577bba2bde577552337df271\n\
    consequence the agent may see only whether it is day or night\n\
    shown as possibility\n\
    predicate 1\n\
    | fun w => w = dayOrNightOnly lo hi o₁ o₂\n\
    verdict declined\n\
    ",
  "lean-intent statement 1\n\
    kind answer\n\
    project acorn\n\
    id day-6\n\
    date 2026-10-29\n\
    reference docs/spec-first-pilot.md, The decisions made on the owner's behalf\n\
    by agents\n\
    under agents-below-intent\n\
    record AcornVerif.Intent.DayCycle.dayCycle\n\
    revision 1\n\
    | commit 50051c749d9b94ea577bba2bde577552337df271\n\
    consequence an action may cost more at one night moment than at another\n\
    shown as possibility\n\
    predicate 1\n\
    | fun w => ∃ c a t t', w.night t = true ∧ w.night t' = true ∧ w.cost t c a ≠ w.cost t' c a\
    \n\
    verdict confirmed\n\
    ",
  "lean-intent statement 1\n\
    kind answer\n\
    project acorn\n\
    id hash-1\n\
    date 2026-10-29\n\
    reference docs/spec-first-pilot.md, The decisions made on the owner's behalf\n\
    by agents\n\
    under agents-below-intent\n\
    record AcornVerif.Intent.Hash.hashes\n\
    revision 1\n\
    | commit 50051c749d9b94ea577bba2bde577552337df271\n\
    consequence changing any one input always moves the spot\n\
    shown as entailment\n\
    predicate 1\n\
    | fun w => OneInputMoves w.hash2 ∧ OneInputMoves w.hash3\n\
    verdict confirmed\n\
    ",
  "lean-intent statement 1\n\
    kind answer\n\
    project acorn\n\
    id hash-2\n\
    date 2026-10-29\n\
    reference docs/spec-first-pilot.md, The decisions made on the owner's behalf\n\
    by agents\n\
    under agents-below-intent\n\
    record AcornVerif.Intent.Hash.hashes\n\
    revision 1\n\
    | commit 50051c749d9b94ea577bba2bde577552337df271\n\
    consequence no fixed rule of reordering and shifting the inputs keeps every spot\n\
    shown as entailment\n\
    predicate 1\n\
    | fun w => NoRuleKeepsSpots w.hash2 ∧ NoRuleKeepsSpots w.hash3\n\
    verdict confirmed\n\
    ",
  "lean-intent statement 1\n\
    kind answer\n\
    project acorn\n\
    id hash-3\n\
    date 2026-10-29\n\
    reference docs/spec-first-pilot.md, The decisions made on the owner's behalf\n\
    by agents\n\
    under agents-below-intent\n\
    record AcornVerif.Intent.Hash.hashes\n\
    revision 1\n\
    | commit 50051c749d9b94ea577bba2bde577552337df271\n\
    consequence neither function combines its inputs by plain exclusive or or plain addition\n\
    shown as entailment\n\
    predicate 1\n\
    | fun w => w.hash2 ≠ xorAll ∧ w.hash2 ≠ addAll ∧ w.hash3 ≠ xorAll ∧ w.hash3 ≠ addAll\n\
    verdict confirmed\n\
    ",
  "lean-intent statement 1\n\
    kind answer\n\
    project acorn\n\
    id hash-6\n\
    date 2026-10-29\n\
    reference docs/spec-first-pilot.md, The decisions made on the owner's behalf\n\
    by agents\n\
    under agents-below-intent\n\
    record AcornVerif.Intent.Hash.hashes\n\
    revision 1\n\
    | commit 50051c749d9b94ea577bba2bde577552337df271\n\
    consequence the same inputs always give the same spot\n\
    shown as entailment\n\
    predicate 1\n\
    | fun w => ∀ x y, x = y → w.hash2 x = w.hash2 y ∧ w.hash3 x = w.hash3 y\n\
    verdict confirmed\n\
    ",
  "lean-intent statement 1\n\
    kind retraction\n\
    project acorn\n\
    id day-1-retracted\n\
    date 2026-11-03\n\
    words 1\n\
    | lean-intent's confirmation check, as of lean-intent commit 9502fbe, compares an answer's\
    \x20revision and predicate with the texts it computes from the build, and this answer hold\
    s an earlier short form of each; the agents give it again against those texts, with the sa\
    me verdict.\n\
    by agents\n\
    under agents-below-intent\n\
    retracts day-1\n\
    ",
  "lean-intent statement 1\n\
    kind retraction\n\
    project acorn\n\
    id day-2-retracted\n\
    date 2026-11-03\n\
    words 1\n\
    | lean-intent's confirmation check, as of lean-intent commit 9502fbe, compares an answer's\
    \x20revision and predicate with the texts it computes from the build, and this answer hold\
    s an earlier short form of each; the agents give it again against those texts, with the sa\
    me verdict.\n\
    by agents\n\
    under agents-below-intent\n\
    retracts day-2\n\
    ",
  "lean-intent statement 1\n\
    kind retraction\n\
    project acorn\n\
    id day-3-retracted\n\
    date 2026-11-03\n\
    words 1\n\
    | lean-intent's confirmation check, as of lean-intent commit 9502fbe, compares an answer's\
    \x20revision and predicate with the texts it computes from the build, and this answer hold\
    s an earlier short form of each; the agents give it again against those texts, with the sa\
    me verdict.\n\
    by agents\n\
    under agents-below-intent\n\
    retracts day-3\n\
    ",
  "lean-intent statement 1\n\
    kind retraction\n\
    project acorn\n\
    id day-4-retracted\n\
    date 2026-11-03\n\
    words 1\n\
    | lean-intent's confirmation check, as of lean-intent commit 9502fbe, compares an answer's\
    \x20revision and predicate with the texts it computes from the build, and this answer hold\
    s an earlier short form of each; the agents give it again against those texts, with the sa\
    me verdict.\n\
    by agents\n\
    under agents-below-intent\n\
    retracts day-4\n\
    ",
  "lean-intent statement 1\n\
    kind retraction\n\
    project acorn\n\
    id day-5a-retracted\n\
    date 2026-11-03\n\
    words 1\n\
    | lean-intent's confirmation check, as of lean-intent commit 9502fbe, compares an answer's\
    \x20revision and predicate with the texts it computes from the build, and this answer hold\
    s an earlier short form of each; the agents give it again against those texts, with the sa\
    me verdict.\n\
    by agents\n\
    under agents-below-intent\n\
    retracts day-5a\n\
    ",
  "lean-intent statement 1\n\
    kind retraction\n\
    project acorn\n\
    id day-5b-retracted\n\
    date 2026-11-03\n\
    words 1\n\
    | lean-intent's confirmation check, as of lean-intent commit 9502fbe, compares an answer's\
    \x20revision and predicate with the texts it computes from the build, and this answer hold\
    s an earlier short form of each; the agents give it again against those texts, with the sa\
    me verdict.\n\
    by agents\n\
    under agents-below-intent\n\
    retracts day-5b\n\
    ",
  "lean-intent statement 1\n\
    kind retraction\n\
    project acorn\n\
    id day-6-retracted\n\
    date 2026-11-03\n\
    words 1\n\
    | lean-intent's confirmation check, as of lean-intent commit 9502fbe, compares an answer's\
    \x20revision and predicate with the texts it computes from the build, and this answer hold\
    s an earlier short form of each; the agents give it again against those texts, with the sa\
    me verdict.\n\
    by agents\n\
    under agents-below-intent\n\
    retracts day-6\n\
    ",
  "lean-intent statement 1\n\
    kind retraction\n\
    project acorn\n\
    id hash-1-retracted\n\
    date 2026-11-03\n\
    words 1\n\
    | lean-intent's confirmation check, as of lean-intent commit 9502fbe, compares an answer's\
    \x20revision and predicate with the texts it computes from the build, and this answer hold\
    s an earlier short form of each; the agents give it again against those texts, with the sa\
    me verdict.\n\
    by agents\n\
    under agents-below-intent\n\
    retracts hash-1\n\
    ",
  "lean-intent statement 1\n\
    kind retraction\n\
    project acorn\n\
    id hash-2-retracted\n\
    date 2026-11-03\n\
    words 1\n\
    | lean-intent's confirmation check, as of lean-intent commit 9502fbe, compares an answer's\
    \x20revision and predicate with the texts it computes from the build, and this answer hold\
    s an earlier short form of each; the agents give it again against those texts, with the sa\
    me verdict.\n\
    by agents\n\
    under agents-below-intent\n\
    retracts hash-2\n\
    ",
  "lean-intent statement 1\n\
    kind retraction\n\
    project acorn\n\
    id hash-3-retracted\n\
    date 2026-11-03\n\
    words 1\n\
    | lean-intent's confirmation check, as of lean-intent commit 9502fbe, compares an answer's\
    \x20revision and predicate with the texts it computes from the build, and this answer hold\
    s an earlier short form of each; the agents give it again against those texts, with the sa\
    me verdict.\n\
    by agents\n\
    under agents-below-intent\n\
    retracts hash-3\n\
    ",
  "lean-intent statement 1\n\
    kind retraction\n\
    project acorn\n\
    id hash-6-retracted\n\
    date 2026-11-03\n\
    words 1\n\
    | lean-intent's confirmation check, as of lean-intent commit 9502fbe, compares an answer's\
    \x20revision and predicate with the texts it computes from the build, and this answer hold\
    s an earlier short form of each; the agents give it again against those texts, with the sa\
    me verdict.\n\
    by agents\n\
    under agents-below-intent\n\
    retracts hash-6\n\
    ",
  "lean-intent statement 1\n\
    kind answer\n\
    project acorn\n\
    id day-restatement\n\
    date 2026-11-03\n\
    reference docs/spec-first-pilot.md, The records and their adequacy\n\
    by agents\n\
    under agents-below-intent\n\
    record AcornVerif.Intent.DayCycle.dayCycle\n\
    revision 610\n\
    | # The intent record @AcornVerif.Intent.DayCycle.dayCycleFor Unit Acorn.Host.Action UInt8\
    \x20Nat instLTNat\n\
    | \n\
    | Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term \
    its kernel checks, binder names and metadata aside, from the root namespace with nothing o\
    pened. The plain words after it are written by a model and are trusted, not proved.\n\
    | \n\
    | ## Shape\n\
    | \n\
    | ### The subject\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Shape.value.{0} (AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action U\
    Int8 Nat)\n\
    | ```\n\
    | \n\
    | - **Requires:** The subject is a description of a world's day: how many ticks a day last\
    s, which ticks are night, what each action costs at each tick in each situation, and what \
    the agent sees at each tick in each situation. Time is counted in whole ticks from the sta\
    rt of a run, and one clock serves the whole world.\n\
    | - **Rules out:** Nothing by itself; it fixes only what the statements below talk about.\
    \n\
    | - **Still allows:** Any world's situations, actions, sights and energy amounts.\n\
    | - **Freedom O5 leaves:** None of its own. It carries no state from one tick to the next,\
    \x20so it is declared a plain value, of which obligation O4 asks nothing.\n\
    | \n\
    | ## Domain hypotheses\n\
    | \n\
    | None.\n\
    | \n\
    | ## Properties\n\
    | \n\
    | ### each day has a daytime half and a night half of equal length\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => And (@\
    LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w)) (And (@Eq.{1\
    } Nat (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@AcornVerif.Inten\
    t.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) (@OfNat.ofNat.{0} Nat (nat_\
    lit 2) (instOfNatNat (nat_lit 2)))) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_l\
    it 0)))) (@Exists.{1} Nat (fun (start : Nat) => ∀ (t : Nat), Iff (@Eq.{1} Bool (@AcornVeri\
    f.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true) (AcornVe\
    rif.Intent.DayCycle.NightHalf (@AcornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host\
    .Action UInt8 Nat w) start t))))\n\
    | ```\n\
    | \n\
    | - **Requires:** A day lasts a fixed, even number of ticks, at least two. The night is on\
    e unbroken stretch of exactly half of them and the daytime the other half, and every day i\
    s the same.\n\
    | - **Rules out:** A world with no night or no daytime; a day of an odd number of ticks; a\
    \x20night broken into several stretches; days of different lengths.\n\
    | - **Still allows:** Any even day length, and a night that starts at any tick of the day.\
    \n\
    | - **Freedom O5 leaves:** How long a day is and where in it the night starts.\n\
    | \n\
    | ### at night every action costs more energy\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (c :\
    \x20Unit), ∀ (a : Acorn.Host.Action), ∀ (t : Nat), ∀ (t' : Nat), @Eq.{1} Bool (@AcornVerif\
    .Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true → @Eq.{1} \
    Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t') Bo\
    ol.false → @LT.lt.{0} Nat instLTNat (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.\
    Host.Action UInt8 Nat w t' c a) (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.Host\
    .Action UInt8 Nat w t c a)\n\
    | ```\n\
    | \n\
    | - **Requires:** For every action and every situation, the action costs strictly more ene\
    rgy at every night tick than at every daytime tick, waiting included.\n\
    | - **Rules out:** Any action that, in some situation, costs as much or less at some night\
    \x20tick than at some daytime tick.\n\
    | - **Still allows:** Any amount more at night, and a night cost that changes during the n\
    ight, as long as it stays above every daytime cost.\n\
    | - **Freedom O5 leaves:** How much more the night costs, and whether that extra changes d\
    uring the night.\n\
    | \n\
    | ### the agent can always tell day from night\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (t :\
    \x20Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @Eq.{1} UInt8 (@AcornVerif.Intent.Day\
    Cycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t c) (@AcornVerif.Intent.DayCycle.D\
    ayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') → @Eq.{1} Bool (@AcornVerif.Intent.\
    DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) (@AcornVerif.Intent.DayCycle\
    .DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t')\n\
    | ```\n\
    | \n\
    | - **Requires:** Whatever the agent sees always tells it whether it is day or night.\n\
    | - **Rules out:** An agent that sees a day moment and a night moment alike.\n\
    | - **Still allows:** An agent that sees more than that.\n\
    | - **Freedom O5 leaves:** How much more it sees.\n\
    | \n\
    | ### the agent can always see where in the day it is, at least to a quarter of the day\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Exist\
    s.{1} Nat (fun (start : Nat) => ∀ (t : Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @E\
    q.{1} UInt8 (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w \
    t c) (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') \
    → @Eq.{1} Nat (AcornVerif.Intent.DayCycle.quarter (@AcornVerif.Intent.DayCycle.DayWorld.le\
    ngth Unit Acorn.Host.Action UInt8 Nat w) start t) (AcornVerif.Intent.DayCycle.quarter (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) start t'))\n\
    | ```\n\
    | \n\
    | - **Requires:** Whatever the agent sees always tells it which quarter of the day it is i\
    n.\n\
    | - **Rules out:** An agent that sees only whether it is day or night, in a day longer tha\
    n two ticks.\n\
    | - **Still allows:** An agent that sees the quarter, a finer part of the day, or the exac\
    t tick.\n\
    | - **Freedom O5 leaves:** How much more finely than a quarter the agent sees the time of \
    day.\n\
    | \n\
    | ## Vocabulary\n\
    | \n\
    | ### night half, a predicate over `Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) => AcornVerif.Intent.DayCycle.NightHalf \
    (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat Nat) p) (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0}\
    \x20Nat (Prod.{0, 0} Nat Nat) p)) (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0\
    , 0} Nat Nat) p))\n\
    | ```\n\
    | \n\
    | - **Requires:** Tick t is in the night when, counted around a day of the given length fr\
    om where the night starts, it falls in the first half.\n\
    | - **Rules out:** Tick 1 in a day of two ticks whose night starts at tick 0.\n\
    | - **Still allows:** Tick 0 in that day.\n\
    | - **Freedom O5 leaves:** None: it is a definition.\n\
    | \n\
    | ### costs less, a predicate over `Prod.{0, 0} Nat Nat`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} Nat Nat) => @LT.lt.{0} Nat instLTNat (@Prod.fst.{0, 0} Nat Nat p) (\
    @Prod.snd.{0, 0} Nat Nat p)\n\
    | ```\n\
    | \n\
    | - **Requires:** The world's own order on energy amounts.\n\
    | - **Rules out:** Whatever that order rules out.\n\
    | - **Still allows:** Whatever that order allows.\n\
    | - **Freedom O5 leaves:** None of its own.\n\
    | \n\
    | ### in quarter, a predicate over `Prod.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)\
    )`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))) => @Eq.{1} Nat (AcornV\
    erif.Intent.DayCycle.quarter (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))\
    \x20p) (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat Nat) (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat \
    (Prod.{0, 0} Nat Nat)) p)) (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Na\
    t Nat) (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) p)))) (@Prod.snd.{0, \
    0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat Nat) (@Prod.snd.{0, 0} Nat (Prod.{0, 0} \
    Nat (Prod.{0, 0} Nat Nat)) p)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Tick t lies in the given quarter of a day of the given length, counted f\
    rom the given start.\n\
    | - **Rules out:** Tick 0 in quarter 1 of a day of four ticks counted from tick 0.\n\
    | - **Still allows:** Tick 0 in quarter 0 of that day.\n\
    | - **Freedom O5 leaves:** None: it is a definition.\n\
    | \n\
    | ## Consequences\n\
    | \n\
    | ### every day lasts the same even number of ticks, at least two, placed alike, an entail\
    ment: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => And (@\
    LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w)) (And (@Eq.{1\
    } Nat (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@AcornVerif.Inten\
    t.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) (@OfNat.ofNat.{0} Nat (nat_\
    lit 2) (instOfNatNat (nat_lit 2)))) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_l\
    it 0)))) (∀ (t : Nat), @Eq.{1} Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn\
    .Host.Action UInt8 Nat w (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) \
    t (@AcornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w))) (@Aco\
    rnVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Every day lasts the same even number of ticks, at least two, and each da\
    y's night falls at the same ticks of the day.\n\
    | - **Rules out:** Days of different lengths.\n\
    | - **Still allows:** Any one day length shared by all days.\n\
    | - **Freedom O5 leaves:** The length itself.\n\
    | \n\
    | ### every action costs more at any night moment than at any daytime moment, an entailmen\
    t: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (c :\
    \x20Unit), ∀ (a : Acorn.Host.Action), ∀ (t : Nat), ∀ (t' : Nat), @Eq.{1} Bool (@AcornVerif\
    .Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true → @Eq.{1} \
    Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t') Bo\
    ol.false → @LT.lt.{0} Nat instLTNat (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.\
    Host.Action UInt8 Nat w t' c a) (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.Host\
    .Action UInt8 Nat w t c a)\n\
    | ```\n\
    | \n\
    | - **Requires:** Even the cheapest action costs more at any night moment than at any dayt\
    ime moment, in the same situation.\n\
    | - **Rules out:** Any action that is no dearer at some night moment.\n\
    | - **Still allows:** Any extra amount.\n\
    | - **Freedom O5 leaves:** How much more.\n\
    | \n\
    | ### what the agent sees always tells day from night, an entailment: every subject that m\
    eets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (t :\
    \x20Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @Eq.{1} UInt8 (@AcornVerif.Intent.Day\
    Cycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t c) (@AcornVerif.Intent.DayCycle.D\
    ayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') → @Eq.{1} Bool (@AcornVerif.Intent.\
    DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) (@AcornVerif.Intent.DayCycle\
    .DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t')\n\
    | ```\n\
    | \n\
    | - **Requires:** From what it sees, the agent can always tell whether it is day or night.\
    \n\
    | - **Rules out:** An agent that cannot tell day from night at some moment.\n\
    | - **Still allows:** An agent that sees more than that.\n\
    | - **Freedom O5 leaves:** How much more it sees.\n\
    | \n\
    | ### what the agent sees always tells it which quarter of the day it is in, an entailment\
    : every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Exist\
    s.{1} Nat (fun (start : Nat) => ∀ (t : Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @E\
    q.{1} UInt8 (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w \
    t c) (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') \
    → @Eq.{1} Nat (AcornVerif.Intent.DayCycle.quarter (@AcornVerif.Intent.DayCycle.DayWorld.le\
    ngth Unit Acorn.Host.Action UInt8 Nat w) start t) (AcornVerif.Intent.DayCycle.quarter (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) start t'))\n\
    | ```\n\
    | \n\
    | - **Requires:** From what it sees, the agent can always tell which quarter of the day it\
    \x20is in.\n\
    | - **Rules out:** An agent that sees only day or night.\n\
    | - **Still allows:** Seeing a finer part of the day, or the exact tick.\n\
    | - **Freedom O5 leaves:** How much finer than a quarter.\n\
    | \n\
    | ### a day may last 1000 ticks, a possibility: some subject that meets the record satisfi\
    es it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Eq.{1\
    } Nat (@AcornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) (@O\
    fNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Nothing more: a world whose day lasts 1000 ticks can meet the record.\n\
    | - **Rules out:** Nothing.\n\
    | - **Still allows:** Short days and long days alike.\n\
    | - **Freedom O5 leaves:** The day's length.\n\
    | \n\
    | ### an action may cost more at one night moment than at another, a possibility: some sub\
    ject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Exist\
    s.{1} Unit (fun (c : Unit) => @Exists.{1} Acorn.Host.Action (fun (a : Acorn.Host.Action) =\
    > @Exists.{1} Nat (fun (t : Nat) => @Exists.{1} Nat (fun (t' : Nat) => And (@Eq.{1} Bool (\
    @AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true\
    ) (And (@Eq.{1} Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UI\
    nt8 Nat w t') Bool.true) (@Ne.{1} Nat (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acor\
    n.Host.Action UInt8 Nat w t c a) (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.Hos\
    t.Action UInt8 Nat w t' c a)))))))\n\
    | ```\n\
    | \n\
    | - **Requires:** Nothing more: an action may cost more at one night moment than at anothe\
    r, as long as every night cost is above every daytime cost.\n\
    | - **Rules out:** Nothing.\n\
    | - **Still allows:** A night that is dearer at midnight than at dusk.\n\
    | - **Freedom O5 leaves:** Whether the night's extra changes during the night.\n\
    | \n\
    | ## Definitions the record's meaning reaches\n\
    | \n\
    | These are not statements of the record: each is a declaration that a statement above dep\
    ends on, or that says what it is for a subject to meet the record and for a consequence to\
    \x20hold of it as shown, with everything those depend on in turn. Each is printed in full:\
    \x20its type, a definition's value, or for a definition by structural or well-founded recu\
    rsion the equation that determines it, and an inductive type's constructors, which for a s\
    tructure are its fields; a theorem's proof and an opaque constant's value are not, since n\
    o term that uses them depends on more than their types. Their plain words are those of the\
    \x20statements that use them.\n\
    | \n\
    | ### Acorn.Host.Action\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### Acorn.Host.Action.north\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.south\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.east\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.west\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.wait\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.harvest\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftAxe\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftBoat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.eat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Shape\n\
    | \n\
    | An inductive type. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type u → Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Shape.value\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.function\n\
    | \n\
    | ```lean\n\
    | ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.step\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.stepOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.action\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.actionOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u\
    } O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.bundle\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀\
    \x20(rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Member\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Member.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → \
    Out), LeanIntent.Member.{u} W\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (Ctx : Type), ∀ (Act : Type), ∀ (Obs : Type), ∀ (E : Type), Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 4 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.DayCycle.DayWorld.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (length : Nat), ∀ (night\
    \x20: Nat → Bool), ∀ (cost : Nat → Ctx → Act → E), ∀ (sees : Nat → Ctx → Obs), AcornVerif.\
    Intent.DayCycle.DayWorld Ctx Act Obs E\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.length\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 1, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.night\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 2, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Bool\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.NightHalf\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (length : Nat), ∀ (start : Nat), ∀ (t : Nat), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (length : Nat) => fun (start : Nat) => fun (t : Nat) => @LT.lt.{0} Nat instLTNat (@H\
    Mod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@HAdd.hAdd.{0, 0, 0} Nat N\
    at Nat (@instHAdd.{0} Nat instAddNat) t start) length) (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (\
    @instHDiv.{0} Nat Nat.instDiv) length (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat\
    _lit 2))))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.cost\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 3, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Ctx → Act → E\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.sees\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 4, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Ctx → Obs\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.quarter\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (length : Nat), ∀ (start : Nat), ∀ (t : Nat), Nat\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (length : Nat) => fun (start : Nat) => fun (t : Nat) => @HDiv.hDiv.{0, 0, 0} Nat Nat\
    \x20Nat (@instHDiv.{0} Nat Nat.instDiv) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} N\
    at instMulNat) (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@HAdd.hA\
    dd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t start) length) (@OfNat.ofNat.{0}\
    \x20Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) length\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Meets\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@Lean\
    Intent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.IntentRecord.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause\
    .{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanInte\
    nt.Pred.{u}), LeanIntent.IntentRecord.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Clause.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Pred\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Pred.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Dom\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.dom\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Cla\
    use's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Props\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.props\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.HoldsOf\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (c : LeanIntent.Consequence.{u} W), ∀ (r : LeanIntent.IntentRecord.{u}\
    \x20W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (c : LeanIntent.Consequence.{u} W) => fun (r : LeanIntent.Intent\
    Record.{u} W) => LeanIntent.Consequence.HoldsOf.match_1.{1} (fun (x : LeanIntent.Consequen\
    ce.Kind) => Prop) (@LeanIntent.Consequence.kind.{u} W c) (fun («_» : Unit) => ∀ (w : W), @\
    LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W c w) (fun («\
    _» : Unit) => @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRec\
    ord.Meets.{u} W r w) (@LeanIntent.Consequence.holds.{u} W c w)))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W \
    → Prop), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.entailment\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.possibility\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.HoldsOf.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : LeanIntent.Consequence.Kind → Sort u_1), ∀ (x : LeanIntent.Consequence.Kind)\
    , ∀ (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment), ∀ (h_2 : ∀ («_»\
    \x20: Unit), motive LeanIntent.Consequence.Kind.possibility), motive x\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : LeanIntent.Consequence.Kind → Sort u_1) => fun (x : LeanIntent.Consequence\
    .Kind) => fun (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment) => fun\
    \x20(h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.\
    Consequence.Kind.casesOn.{u_1} (fun (x_1 : LeanIntent.Consequence.Kind) => motive x_1) x (\
    h_1 Unit.unit) (h_2 Unit.unit)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.\
    Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : mo\
    tive LeanIntent.Consequence.Kind.possibility), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Conseq\
    uence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (po\
    ssibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kin\
    d.rec.{u} motive entailment possibility t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.kind\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.HasInstance\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)\n\
    | ```\n\
    | \n\
    | ## Lean's own libraries\n\
    | \n\
    | The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: the\
    y are those of Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, which made th\
    is text. A declaration is counted as Lean's own when Lean found the module that declares i\
    t in that release's library directory.\n\
    | \n\
    consequence the record's plain restatement\n\
    shown as entailment\n\
    predicate 1\n\
    | the record, as its revision prints it\n\
    verdict confirmed\n\
    ",
  "lean-intent statement 1\n\
    kind answer\n\
    project acorn\n\
    id hash-restatement\n\
    date 2026-11-03\n\
    reference docs/spec-first-pilot.md, The records and their adequacy\n\
    by agents\n\
    under agents-below-intent\n\
    record AcornVerif.Intent.Hash.hashes\n\
    revision 740\n\
    | # The intent record AcornVerif.Intent.Hash.hashes\n\
    | \n\
    | Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term \
    its kernel checks, binder names and metadata aside, from the root namespace with nothing o\
    pened. The plain words after it are written by a model and are trusted, not proved.\n\
    | \n\
    | ## Shape\n\
    | \n\
    | ### The subject\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Shape.value.{0} AcornVerif.Intent.Hash.Hashes\n\
    | ```\n\
    | \n\
    | - **Requires:** The subject is the pair of hash functions, each taking three 64-bit inpu\
    ts to one 64-bit spot.\n\
    | - **Rules out:** Nothing by itself.\n\
    | - **Still allows:** Any pair of such functions, until the properties narrow it.\n\
    | - **Freedom O5 leaves:** None of its own. The pair carries no state from one call to the\
    \x20next, so it is declared a plain value, of which obligation O4 asks nothing.\n\
    | \n\
    | ## Domain hypotheses\n\
    | \n\
    | None.\n\
    | \n\
    | ## Properties\n\
    | \n\
    | ### changing any one input always moves the spot\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => And (AcornVerif.Intent.Hash.OneInputMoves (Ac\
    ornVerif.Intent.Hash.Hashes.hash2 w)) (AcornVerif.Intent.Hash.OneInputMoves (AcornVerif.In\
    tent.Hash.Hashes.hash3 w))\n\
    | ```\n\
    | \n\
    | - **Requires:** In each function, changing exactly one input, the others kept, always ch\
    anges the spot: never the same spot, not merely rarely.\n\
    | - **Rules out:** A function that ignores an input, and one where two values of one input\
    \x20share a spot for some values of the others.\n\
    | - **Still allows:** Any amount of sharing between inputs that differ in two or three pla\
    ces.\n\
    | - **Freedom O5 leaves:** Everything about inputs that differ in more than one place.\n\
    | \n\
    | ### no fixed rule of reordering and shifting the inputs keeps every spot\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => And (AcornVerif.Intent.Hash.NoRuleKeepsSpots \
    (AcornVerif.Intent.Hash.Hashes.hash2 w)) (AcornVerif.Intent.Hash.NoRuleKeepsSpots (AcornVe\
    rif.Intent.Hash.Hashes.hash3 w))\n\
    | ```\n\
    | \n\
    | - **Requires:** No fixed rule moves every input to a different input in the same spot. A\
    \x20rule here puts the three inputs in some order, then adds a fixed amount to each, or fl\
    ips fixed bits of each.\n\
    | - **Rules out:** Combining the inputs by plain exclusive or or plain addition, where swa\
    pping two inputs keeps the spot; and any function where adding the same amounts, or flippi\
    ng the same bits, keeps every spot.\n\
    | - **Still allows:** Rules of other kinds, such as multiplying the inputs by fixed number\
    s; and any number of inputs sharing spots without a fixed rule behind it.\n\
    | - **Freedom O5 leaves:** How often inputs share spots overall: the record bounds no rate\
    .\n\
    | \n\
    | ## Vocabulary\n\
    | \n\
    | ### same spot, a predicate over `Prod.{0, 0} UInt64 UInt64`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} UInt64 UInt64) => @Eq.{1} UInt64 (@Prod.fst.{0, 0} UInt64 UInt64 p)\
    \x20(@Prod.snd.{0, 0} UInt64 UInt64 p)\n\
    | ```\n\
    | \n\
    | - **Requires:** Two spots are the same 64-bit value.\n\
    | - **Rules out:** Spots 0 and 1.\n\
    | - **Still allows:** Spots 0 and 0.\n\
    | - **Freedom O5 leaves:** None: it is equality.\n\
    | \n\
    | ## Consequences\n\
    | \n\
    | ### changing any one input always moves the spot, an entailment: every subject that meet\
    s the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => And (AcornVerif.Intent.Hash.OneInputMoves (Ac\
    ornVerif.Intent.Hash.Hashes.hash2 w)) (AcornVerif.Intent.Hash.OneInputMoves (AcornVerif.In\
    tent.Hash.Hashes.hash3 w))\n\
    | ```\n\
    | \n\
    | - **Requires:** Changing any one input always moves the spot, in both functions.\n\
    | - **Rules out:** Any single changed input landing in the same spot.\n\
    | - **Still allows:** Inputs that differ in two or three places sharing a spot.\n\
    | - **Freedom O5 leaves:** None beyond the property's.\n\
    | \n\
    | ### no fixed rule of reordering and shifting the inputs keeps every spot, an entailment:\
    \x20every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => And (AcornVerif.Intent.Hash.NoRuleKeepsSpots \
    (AcornVerif.Intent.Hash.Hashes.hash2 w)) (AcornVerif.Intent.Hash.NoRuleKeepsSpots (AcornVe\
    rif.Intent.Hash.Hashes.hash3 w))\n\
    | ```\n\
    | \n\
    | - **Requires:** No fixed reordering and shifting of the inputs keeps every spot.\n\
    | - **Rules out:** Systematic sharing by any such rule.\n\
    | - **Still allows:** Sharing by rules of other kinds, and sharing with no fixed rule.\n\
    | - **Freedom O5 leaves:** Which rules count as systematic beyond these.\n\
    | \n\
    | ### neither function combines its inputs by plain exclusive or or plain addition, an ent\
    ailment: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => And (@Ne.{1} (AcornVerif.Intent.Hash.Inputs →\
    \x20UInt64) (AcornVerif.Intent.Hash.Hashes.hash2 w) AcornVerif.Intent.Hash.xorAll) (And (@\
    Ne.{1} (AcornVerif.Intent.Hash.Inputs → UInt64) (AcornVerif.Intent.Hash.Hashes.hash2 w) Ac\
    ornVerif.Intent.Hash.addAll) (And (@Ne.{1} (AcornVerif.Intent.Hash.Inputs → UInt64) (Acorn\
    Verif.Intent.Hash.Hashes.hash3 w) AcornVerif.Intent.Hash.xorAll) (@Ne.{1} (AcornVerif.Inte\
    nt.Hash.Inputs → UInt64) (AcornVerif.Intent.Hash.Hashes.hash3 w) AcornVerif.Intent.Hash.ad\
    dAll)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Neither function combines its three inputs by plain exclusive or or by p\
    lain addition.\n\
    | - **Rules out:** Those two combinations, since swapping two inputs keeps their spot.\n\
    | - **Still allows:** Combinations that mix the inputs before combining them.\n\
    | - **Freedom O5 leaves:** None that this consequence adds.\n\
    | \n\
    | ### the same inputs always give the same spot, an entailment: every subject that meets t\
    he record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => ∀ (x : AcornVerif.Intent.Hash.Inputs), ∀ (y :\
    \x20AcornVerif.Intent.Hash.Inputs), @Eq.{1} AcornVerif.Intent.Hash.Inputs x y → And (@Eq.{\
    1} UInt64 (AcornVerif.Intent.Hash.Hashes.hash2 w x) (AcornVerif.Intent.Hash.Hashes.hash2 w\
    \x20y)) (@Eq.{1} UInt64 (AcornVerif.Intent.Hash.Hashes.hash3 w x) (AcornVerif.Intent.Hash.\
    Hashes.hash3 w y))\n\
    | ```\n\
    | \n\
    | - **Requires:** The same inputs always give the same spot, so a run can be replayed.\n\
    | - **Rules out:** Nothing: every function of this type meets it.\n\
    | - **Still allows:** Every pair of functions.\n\
    | - **Freedom O5 leaves:** None. It holds by construction; replay further trusts the compi\
    ler and the machine to compute 64-bit words alike everywhere.\n\
    | \n\
    | ## Definitions the record's meaning reaches\n\
    | \n\
    | These are not statements of the record: each is a declaration that a statement above dep\
    ends on, or that says what it is for a subject to meet the record and for a consequence to\
    \x20hold of it as shown, with everything those depend on in turn. Each is printed in full:\
    \x20its type, a definition's value, or for a definition by structural or well-founded recu\
    rsion the equation that determines it, and an inductive type's constructors, which for a s\
    tructure are its fields; a theorem's proof and an opaque constant's value are not, since n\
    o term that uses them depends on more than their types. Their plain words are those of the\
    \x20statements that use them.\n\
    | \n\
    | ### LeanIntent.Shape\n\
    | \n\
    | An inductive type. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type u → Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Shape.value\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.function\n\
    | \n\
    | ```lean\n\
    | ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.step\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.stepOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.action\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.actionOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u\
    } O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.bundle\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀\
    \x20(rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Member\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Member.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → \
    Out), LeanIntent.Member.{u} W\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Hashes\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Hashes.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (hash2 : AcornVerif.Intent.Hash.Inputs → UInt64), ∀ (hash3 : AcornVerif.Intent.Hash.In\
    puts → UInt64), AcornVerif.Intent.Hash.Hashes\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Inputs\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | Prod.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.OneInputMoves\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (f : AcornVerif.Intent.Hash.Inputs → UInt64), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (f : AcornVerif.Intent.Hash.Inputs → UInt64) => And (∀ (a : UInt64), ∀ (a' : UInt64)\
    , ∀ (b : UInt64), ∀ (c : UInt64), @Eq.{1} UInt64 (f (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} U\
    Int64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) (f (@Prod.mk.{0, 0} UInt64 (Prod.{0,\
    \x200} UInt64 UInt64) a' (@Prod.mk.{0, 0} UInt64 UInt64 b c))) → @Eq.{1} UInt64 a a') (And\
    \x20(∀ (a : UInt64), ∀ (b : UInt64), ∀ (b' : UInt64), ∀ (c : UInt64), @Eq.{1} UInt64 (f (@\
    Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) \
    (f (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b'\
    \x20c))) → @Eq.{1} UInt64 b b') (∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), ∀ (c' : U\
    Int64), @Eq.{1} UInt64 (f (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.\
    {0, 0} UInt64 UInt64 b c))) (f (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Pro\
    d.mk.{0, 0} UInt64 UInt64 b c'))) → @Eq.{1} UInt64 c c'))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Hashes.hash2\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 1, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Hashes's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash\
    .Hashes. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Hashes), AcornVerif.Intent.Hash.Inputs → UInt64\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Hashes.hash3\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 2, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Hashes's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash\
    .Hashes. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Hashes), AcornVerif.Intent.Hash.Inputs → UInt64\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.NoRuleKeepsSpots\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (f : AcornVerif.Intent.Hash.Inputs → UInt64), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (f : AcornVerif.Intent.Hash.Inputs → UInt64) => ∀ (r : AcornVerif.Intent.Hash.Rule),\
    \x20AcornVerif.Intent.Hash.Rule.Moves r → @Exists.{1} AcornVerif.Intent.Hash.Inputs (fun (\
    x : AcornVerif.Intent.Hash.Inputs) => @Ne.{1} UInt64 (f (AcornVerif.Intent.Hash.Rule.apply\
    \x20r x)) (f x))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Rule.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (order : AcornVerif.Intent.Hash.Order), ∀ (shift : AcornVerif.Intent.Hash.Shift), ∀ (a\
    mount : AcornVerif.Intent.Hash.Inputs), AcornVerif.Intent.Hash.Rule\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Order\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.abc\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.bac\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.acb\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.cba\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.bca\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.cab\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Shift\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Shift.flip\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Shift\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Shift.add\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Shift\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.Moves\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (r : AcornVerif.Intent.Hash.Rule), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (r : AcornVerif.Intent.Hash.Rule) => Not (And (@Eq.{1} AcornVerif.Intent.Hash.Order \
    (AcornVerif.Intent.Hash.Rule.order r) AcornVerif.Intent.Hash.Order.abc) (@Eq.{1} AcornVeri\
    f.Intent.Hash.Inputs (AcornVerif.Intent.Hash.Rule.amount r) (@Prod.mk.{0, 0} UInt64 (Prod.\
    {0, 0} UInt64 UInt64) (@OfNat.ofNat.{0} UInt64 (nat_lit 0) (@UInt64.instOfNat (nat_lit 0))\
    ) (@Prod.mk.{0, 0} UInt64 UInt64 (@OfNat.ofNat.{0} UInt64 (nat_lit 0) (@UInt64.instOfNat (\
    nat_lit 0))) (@OfNat.ofNat.{0} UInt64 (nat_lit 0) (@UInt64.instOfNat (nat_lit 0)))))))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.order\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 1, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Rule's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash.R\
    ule. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Rule), AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.amount\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 3, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Rule's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash.R\
    ule. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Rule), AcornVerif.Intent.Hash.Inputs\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.apply\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (r : AcornVerif.Intent.Hash.Rule), ∀ (x : AcornVerif.Intent.Hash.Inputs), AcornVerif.I\
    ntent.Hash.Inputs\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (r : AcornVerif.Intent.Hash.Rule) => fun (x : AcornVerif.Intent.Hash.Inputs) => Acor\
    nVerif.Intent.Hash.Rule.apply.match_1.{1} (fun (x_1 : AcornVerif.Intent.Hash.Inputs) => Ac\
    ornVerif.Intent.Hash.Inputs) (AcornVerif.Intent.Hash.Order.apply (AcornVerif.Intent.Hash.R\
    ule.order r) x) (fun (a : UInt64) => fun (b : UInt64) => fun (c : UInt64) => @Prod.mk.{0, \
    0} UInt64 (Prod.{0, 0} UInt64 UInt64) (AcornVerif.Intent.Hash.Shift.apply (AcornVerif.Inte\
    nt.Hash.Rule.shift r) a (@Prod.fst.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (AcornVerif.I\
    ntent.Hash.Rule.amount r))) (@Prod.mk.{0, 0} UInt64 UInt64 (AcornVerif.Intent.Hash.Shift.a\
    pply (AcornVerif.Intent.Hash.Rule.shift r) b (@Prod.fst.{0, 0} UInt64 UInt64 (@Prod.snd.{0\
    , 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (AcornVerif.Intent.Hash.Rule.amount r)))) (AcornVe\
    rif.Intent.Hash.Shift.apply (AcornVerif.Intent.Hash.Rule.shift r) c (@Prod.snd.{0, 0} UInt\
    64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (AcornVerif.Intent.Hash.Rul\
    e.amount r))))))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.apply.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : AcornVerif.Intent.Hash.Inputs → Sort u_1), ∀ (x : AcornVerif.Intent.Hash.Inp\
    uts), ∀ (h_1 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive (@Prod.mk.{0, 0} UIn\
    t64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))), motive x\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : AcornVerif.Intent.Hash.Inputs → Sort u_1) => fun (x : AcornVerif.Intent.Ha\
    sh.Inputs) => fun (h_1 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive (@Prod.mk.\
    {0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) => @Prod\
    .casesOn.{u_1, 0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (fun (x_1 : AcornVerif.Intent.Hash\
    .Inputs) => motive x_1) x (fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => \
    @Prod.casesOn.{u_1, 0, 0} UInt64 UInt64 (fun (x_1 : Prod.{0, 0} UInt64 UInt64) => motive (\
    @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_1)) snd (fun (x_1 : UInt64) => fu\
    n (x_2 : UInt64) => h_1 fst x_1 x_2))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Order.apply\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order → AcornVerif.Intent.Hash.Inputs → AcornVerif.Intent.Hash.In\
    puts\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (x : AcornVerif.Intent.Hash.Order) => fun (x_1 : AcornVerif.Intent.Hash.Inputs) => A\
    cornVerif.Intent.Hash.Order.apply.match_1.{1} (fun (x_2 : AcornVerif.Intent.Hash.Order) =>\
    \x20fun (x_3 : AcornVerif.Intent.Hash.Inputs) => AcornVerif.Intent.Hash.Inputs) x x_1 (fun\
    \x20(a : UInt64) => fun (b : UInt64) => fun (c : UInt64) => @Prod.mk.{0, 0} UInt64 (Prod.{\
    0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c)) (fun (a : UInt64) => fun (b : \
    UInt64) => fun (c : UInt64) => @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) b (@Prod\
    .mk.{0, 0} UInt64 UInt64 a c)) (fun (a : UInt64) => fun (b : UInt64) => fun (c : UInt64) =\
    > @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 c b)\
    ) (fun (a : UInt64) => fun (b : UInt64) => fun (c : UInt64) => @Prod.mk.{0, 0} UInt64 (Pro\
    d.{0, 0} UInt64 UInt64) c (@Prod.mk.{0, 0} UInt64 UInt64 b a)) (fun (a : UInt64) => fun (b\
    \x20: UInt64) => fun (c : UInt64) => @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) b \
    (@Prod.mk.{0, 0} UInt64 UInt64 c a)) (fun (a : UInt64) => fun (b : UInt64) => fun (c : UIn\
    t64) => @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) c (@Prod.mk.{0, 0} UInt64 UInt6\
    4 a b))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Order.apply.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : AcornVerif.Intent.Hash.Order → AcornVerif.Intent.Hash.Inputs → Sort u_1), ∀ \
    (x : AcornVerif.Intent.Hash.Order), ∀ (x_1 : AcornVerif.Intent.Hash.Inputs), ∀ (h_1 : ∀ (a\
    \x20: UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Order.abc (@P\
    rod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))), \
    ∀ (h_2 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Ord\
    er.bac (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt6\
    4 b c))), ∀ (h_3 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Inten\
    t.Hash.Order.acb (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UI\
    nt64 UInt64 b c))), ∀ (h_4 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornV\
    erif.Intent.Hash.Order.cba (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk\
    .{0, 0} UInt64 UInt64 b c))), ∀ (h_5 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), mot\
    ive AcornVerif.Intent.Hash.Order.bca (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a\
    \x20(@Prod.mk.{0, 0} UInt64 UInt64 b c))), ∀ (h_6 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c :\
    \x20UInt64), motive AcornVerif.Intent.Hash.Order.cab (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} \
    UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))), motive x x_1\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : AcornVerif.Intent.Hash.Order → AcornVerif.Intent.Hash.Inputs → Sort u_1) =\
    > fun (x : AcornVerif.Intent.Hash.Order) => fun (x_1 : AcornVerif.Intent.Hash.Inputs) => f\
    un (h_1 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Or\
    der.abc (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt\
    64 b c))) => fun (h_2 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.\
    Intent.Hash.Order.bac (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, \
    0} UInt64 UInt64 b c))) => fun (h_3 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), moti\
    ve AcornVerif.Intent.Hash.Order.acb (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a \
    (@Prod.mk.{0, 0} UInt64 UInt64 b c))) => fun (h_4 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c :\
    \x20UInt64), motive AcornVerif.Intent.Hash.Order.cba (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} \
    UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) => fun (h_5 : ∀ (a : UInt64), ∀ (b \
    : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Order.bca (@Prod.mk.{0, 0} UInt64\
    \x20(Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) => fun (h_6 : ∀ (a\
    \x20: UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Order.cab (@P\
    rod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) =\
    > @AcornVerif.Intent.Hash.Order.casesOn.{u_1} (fun (x_2 : AcornVerif.Intent.Hash.Order) =>\
    \x20motive x_2 x_1) x (@Prod.casesOn.{u_1, 0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (fun (\
    x_2 : AcornVerif.Intent.Hash.Inputs) => motive AcornVerif.Intent.Hash.Order.abc x_2) x_1 (\
    fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => @Prod.casesOn.{u_1, 0, 0} U\
    Int64 UInt64 (fun (x_2 : Prod.{0, 0} UInt64 UInt64) => motive AcornVerif.Intent.Hash.Order\
    .abc (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_2)) snd (fun (x_2 : UInt64)\
    \x20=> fun (x_3 : UInt64) => h_1 fst x_2 x_3))) (@Prod.casesOn.{u_1, 0, 0} UInt64 (Prod.{0\
    , 0} UInt64 UInt64) (fun (x_2 : AcornVerif.Intent.Hash.Inputs) => motive AcornVerif.Intent\
    .Hash.Order.bac x_2) x_1 (fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => @\
    Prod.casesOn.{u_1, 0, 0} UInt64 UInt64 (fun (x_2 : Prod.{0, 0} UInt64 UInt64) => motive Ac\
    ornVerif.Intent.Hash.Order.bac (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_2\
    )) snd (fun (x_2 : UInt64) => fun (x_3 : UInt64) => h_2 fst x_2 x_3))) (@Prod.casesOn.{u_1\
    , 0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (fun (x_2 : AcornVerif.Intent.Hash.Inputs) => m\
    otive AcornVerif.Intent.Hash.Order.acb x_2) x_1 (fun (fst : UInt64) => fun (snd : Prod.{0,\
    \x200} UInt64 UInt64) => @Prod.casesOn.{u_1, 0, 0} UInt64 UInt64 (fun (x_2 : Prod.{0, 0} U\
    Int64 UInt64) => motive AcornVerif.Intent.Hash.Order.acb (@Prod.mk.{0, 0} UInt64 (Prod.{0,\
    \x200} UInt64 UInt64) fst x_2)) snd (fun (x_2 : UInt64) => fun (x_3 : UInt64) => h_3 fst x\
    _2 x_3))) (@Prod.casesOn.{u_1, 0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (fun (x_2 : AcornV\
    erif.Intent.Hash.Inputs) => motive AcornVerif.Intent.Hash.Order.cba x_2) x_1 (fun (fst : U\
    Int64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => @Prod.casesOn.{u_1, 0, 0} UInt64 UInt64\
    \x20(fun (x_2 : Prod.{0, 0} UInt64 UInt64) => motive AcornVerif.Intent.Hash.Order.cba (@Pr\
    od.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_2)) snd (fun (x_2 : UInt64) => fun (\
    x_3 : UInt64) => h_4 fst x_2 x_3))) (@Prod.casesOn.{u_1, 0, 0} UInt64 (Prod.{0, 0} UInt64 \
    UInt64) (fun (x_2 : AcornVerif.Intent.Hash.Inputs) => motive AcornVerif.Intent.Hash.Order.\
    bca x_2) x_1 (fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => @Prod.casesOn\
    .{u_1, 0, 0} UInt64 UInt64 (fun (x_2 : Prod.{0, 0} UInt64 UInt64) => motive AcornVerif.Int\
    ent.Hash.Order.bca (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_2)) snd (fun \
    (x_2 : UInt64) => fun (x_3 : UInt64) => h_5 fst x_2 x_3))) (@Prod.casesOn.{u_1, 0, 0} UInt\
    64 (Prod.{0, 0} UInt64 UInt64) (fun (x_2 : AcornVerif.Intent.Hash.Inputs) => motive AcornV\
    erif.Intent.Hash.Order.cab x_2) x_1 (fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 U\
    Int64) => @Prod.casesOn.{u_1, 0, 0} UInt64 UInt64 (fun (x_2 : Prod.{0, 0} UInt64 UInt64) =\
    > motive AcornVerif.Intent.Hash.Order.cab (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt\
    64) fst x_2)) snd (fun (x_2 : UInt64) => fun (x_3 : UInt64) => h_6 fst x_2 x_3)))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Order.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : AcornVerif.Intent.Hash.Order), Sort u}, ∀ (t : AcornVerif.Intent.Hash\
    .Order), ∀ (abc : motive AcornVerif.Intent.Hash.Order.abc), ∀ (bac : motive AcornVerif.Int\
    ent.Hash.Order.bac), ∀ (acb : motive AcornVerif.Intent.Hash.Order.acb), ∀ (cba : motive Ac\
    ornVerif.Intent.Hash.Order.cba), ∀ (bca : motive AcornVerif.Intent.Hash.Order.bca), ∀ (cab\
    \x20: motive AcornVerif.Intent.Hash.Order.cab), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : AcornVerif.Intent.Hash.Order), Sort u} => fun (t : AcornVerif.Inten\
    t.Hash.Order) => fun (abc : motive AcornVerif.Intent.Hash.Order.abc) => fun (bac : motive \
    AcornVerif.Intent.Hash.Order.bac) => fun (acb : motive AcornVerif.Intent.Hash.Order.acb) =\
    > fun (cba : motive AcornVerif.Intent.Hash.Order.cba) => fun (bca : motive AcornVerif.Inte\
    nt.Hash.Order.bca) => fun (cab : motive AcornVerif.Intent.Hash.Order.cab) => @AcornVerif.I\
    ntent.Hash.Order.rec.{u} motive abc bac acb cba bca cab t\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Shift.apply\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Shift → UInt64 → UInt64 → UInt64\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (x : AcornVerif.Intent.Hash.Shift) => fun (x_1 : UInt64) => fun (x_2 : UInt64) => Ac\
    ornVerif.Intent.Hash.Shift.apply.match_1.{1} (fun (x_3 : AcornVerif.Intent.Hash.Shift) => \
    fun (x_4 : UInt64) => fun (x_5 : UInt64) => UInt64) x x_1 x_2 (fun (x_3 : UInt64) => fun (\
    d : UInt64) => @HXor.hXor.{0, 0, 0} UInt64 UInt64 UInt64 (@instHXorOfXorOp.{0} UInt64 inst\
    XorOpUInt64) x_3 d) (fun (x_3 : UInt64) => fun (d : UInt64) => @HAdd.hAdd.{0, 0, 0} UInt64\
    \x20UInt64 UInt64 (@instHAdd.{0} UInt64 instAddUInt64) x_3 d)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Shift.apply.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : AcornVerif.Intent.Hash.Shift → UInt64 → UInt64 → Sort u_1), ∀ (x : AcornVeri\
    f.Intent.Hash.Shift), ∀ (x_1 : UInt64), ∀ (x_2 : UInt64), ∀ (h_1 : ∀ (x_3 : UInt64), ∀ (d \
    : UInt64), motive AcornVerif.Intent.Hash.Shift.flip x_3 d), ∀ (h_2 : ∀ (x_3 : UInt64), ∀ (\
    d : UInt64), motive AcornVerif.Intent.Hash.Shift.add x_3 d), motive x x_1 x_2\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : AcornVerif.Intent.Hash.Shift → UInt64 → UInt64 → Sort u_1) => fun (x : Aco\
    rnVerif.Intent.Hash.Shift) => fun (x_1 : UInt64) => fun (x_2 : UInt64) => fun (h_1 : ∀ (x_\
    3 : UInt64), ∀ (d : UInt64), motive AcornVerif.Intent.Hash.Shift.flip x_3 d) => fun (h_2 :\
    \x20∀ (x_3 : UInt64), ∀ (d : UInt64), motive AcornVerif.Intent.Hash.Shift.add x_3 d) => @A\
    cornVerif.Intent.Hash.Shift.casesOn.{u_1} (fun (x_3 : AcornVerif.Intent.Hash.Shift) => mot\
    ive x_3 x_1 x_2) x (h_1 x_1 x_2) (h_2 x_1 x_2)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Shift.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : AcornVerif.Intent.Hash.Shift), Sort u}, ∀ (t : AcornVerif.Intent.Hash\
    .Shift), ∀ (flip : motive AcornVerif.Intent.Hash.Shift.flip), ∀ (add : motive AcornVerif.I\
    ntent.Hash.Shift.add), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : AcornVerif.Intent.Hash.Shift), Sort u} => fun (t : AcornVerif.Inten\
    t.Hash.Shift) => fun (flip : motive AcornVerif.Intent.Hash.Shift.flip) => fun (add : motiv\
    e AcornVerif.Intent.Hash.Shift.add) => @AcornVerif.Intent.Hash.Shift.rec.{u} motive flip a\
    dd t\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.shift\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 2, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Rule's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash.R\
    ule. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Rule), AcornVerif.Intent.Hash.Shift\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.xorAll\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (x : AcornVerif.Intent.Hash.Inputs), UInt64\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (x : AcornVerif.Intent.Hash.Inputs) => @HXor.hXor.{0, 0, 0} UInt64 UInt64 UInt64 (@i\
    nstHXorOfXorOp.{0} UInt64 instXorOpUInt64) (@HXor.hXor.{0, 0, 0} UInt64 UInt64 UInt64 (@in\
    stHXorOfXorOp.{0} UInt64 instXorOpUInt64) (@Prod.fst.{0, 0} UInt64 (Prod.{0, 0} UInt64 UIn\
    t64) x) (@Prod.fst.{0, 0} UInt64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt6\
    4) x))) (@Prod.snd.{0, 0} UInt64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt6\
    4) x))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.addAll\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (x : AcornVerif.Intent.Hash.Inputs), UInt64\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (x : AcornVerif.Intent.Hash.Inputs) => @HAdd.hAdd.{0, 0, 0} UInt64 UInt64 UInt64 (@i\
    nstHAdd.{0} UInt64 instAddUInt64) (@HAdd.hAdd.{0, 0, 0} UInt64 UInt64 UInt64 (@instHAdd.{0\
    } UInt64 instAddUInt64) (@Prod.fst.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) x) (@Prod.fst\
    .{0, 0} UInt64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) x))) (@Prod.snd\
    .{0, 0} UInt64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) x))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Meets\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@Lean\
    Intent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.IntentRecord.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause\
    .{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanInte\
    nt.Pred.{u}), LeanIntent.IntentRecord.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Clause.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Pred\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Pred.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Dom\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.dom\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Cla\
    use's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Props\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.props\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.HoldsOf\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (c : LeanIntent.Consequence.{u} W), ∀ (r : LeanIntent.IntentRecord.{u}\
    \x20W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (c : LeanIntent.Consequence.{u} W) => fun (r : LeanIntent.Intent\
    Record.{u} W) => LeanIntent.Consequence.HoldsOf.match_1.{1} (fun (x : LeanIntent.Consequen\
    ce.Kind) => Prop) (@LeanIntent.Consequence.kind.{u} W c) (fun («_» : Unit) => ∀ (w : W), @\
    LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W c w) (fun («\
    _» : Unit) => @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRec\
    ord.Meets.{u} W r w) (@LeanIntent.Consequence.holds.{u} W c w)))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W \
    → Prop), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.entailment\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.possibility\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.HoldsOf.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : LeanIntent.Consequence.Kind → Sort u_1), ∀ (x : LeanIntent.Consequence.Kind)\
    , ∀ (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment), ∀ (h_2 : ∀ («_»\
    \x20: Unit), motive LeanIntent.Consequence.Kind.possibility), motive x\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : LeanIntent.Consequence.Kind → Sort u_1) => fun (x : LeanIntent.Consequence\
    .Kind) => fun (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment) => fun\
    \x20(h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.\
    Consequence.Kind.casesOn.{u_1} (fun (x_1 : LeanIntent.Consequence.Kind) => motive x_1) x (\
    h_1 Unit.unit) (h_2 Unit.unit)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.\
    Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : mo\
    tive LeanIntent.Consequence.Kind.possibility), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Conseq\
    uence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (po\
    ssibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kin\
    d.rec.{u} motive entailment possibility t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.kind\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.HasInstance\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)\n\
    | ```\n\
    | \n\
    | ## Lean's own libraries\n\
    | \n\
    | The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: the\
    y are those of Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, which made th\
    is text. A declaration is counted as Lean's own when Lean found the module that declares i\
    t in that release's library directory.\n\
    | \n\
    consequence the record's plain restatement\n\
    shown as entailment\n\
    predicate 1\n\
    | the record, as its revision prints it\n\
    verdict confirmed\n\
    ",
  "lean-intent statement 1\n\
    kind answer\n\
    project acorn\n\
    id day-1-r2\n\
    date 2026-11-03\n\
    reference docs/spec-first-pilot.md, The decisions made on the owner's behalf\n\
    by agents\n\
    under agents-below-intent\n\
    record AcornVerif.Intent.DayCycle.dayCycle\n\
    revision 610\n\
    | # The intent record @AcornVerif.Intent.DayCycle.dayCycleFor Unit Acorn.Host.Action UInt8\
    \x20Nat instLTNat\n\
    | \n\
    | Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term \
    its kernel checks, binder names and metadata aside, from the root namespace with nothing o\
    pened. The plain words after it are written by a model and are trusted, not proved.\n\
    | \n\
    | ## Shape\n\
    | \n\
    | ### The subject\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Shape.value.{0} (AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action U\
    Int8 Nat)\n\
    | ```\n\
    | \n\
    | - **Requires:** The subject is a description of a world's day: how many ticks a day last\
    s, which ticks are night, what each action costs at each tick in each situation, and what \
    the agent sees at each tick in each situation. Time is counted in whole ticks from the sta\
    rt of a run, and one clock serves the whole world.\n\
    | - **Rules out:** Nothing by itself; it fixes only what the statements below talk about.\
    \n\
    | - **Still allows:** Any world's situations, actions, sights and energy amounts.\n\
    | - **Freedom O5 leaves:** None of its own. It carries no state from one tick to the next,\
    \x20so it is declared a plain value, of which obligation O4 asks nothing.\n\
    | \n\
    | ## Domain hypotheses\n\
    | \n\
    | None.\n\
    | \n\
    | ## Properties\n\
    | \n\
    | ### each day has a daytime half and a night half of equal length\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => And (@\
    LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w)) (And (@Eq.{1\
    } Nat (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@AcornVerif.Inten\
    t.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) (@OfNat.ofNat.{0} Nat (nat_\
    lit 2) (instOfNatNat (nat_lit 2)))) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_l\
    it 0)))) (@Exists.{1} Nat (fun (start : Nat) => ∀ (t : Nat), Iff (@Eq.{1} Bool (@AcornVeri\
    f.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true) (AcornVe\
    rif.Intent.DayCycle.NightHalf (@AcornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host\
    .Action UInt8 Nat w) start t))))\n\
    | ```\n\
    | \n\
    | - **Requires:** A day lasts a fixed, even number of ticks, at least two. The night is on\
    e unbroken stretch of exactly half of them and the daytime the other half, and every day i\
    s the same.\n\
    | - **Rules out:** A world with no night or no daytime; a day of an odd number of ticks; a\
    \x20night broken into several stretches; days of different lengths.\n\
    | - **Still allows:** Any even day length, and a night that starts at any tick of the day.\
    \n\
    | - **Freedom O5 leaves:** How long a day is and where in it the night starts.\n\
    | \n\
    | ### at night every action costs more energy\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (c :\
    \x20Unit), ∀ (a : Acorn.Host.Action), ∀ (t : Nat), ∀ (t' : Nat), @Eq.{1} Bool (@AcornVerif\
    .Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true → @Eq.{1} \
    Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t') Bo\
    ol.false → @LT.lt.{0} Nat instLTNat (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.\
    Host.Action UInt8 Nat w t' c a) (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.Host\
    .Action UInt8 Nat w t c a)\n\
    | ```\n\
    | \n\
    | - **Requires:** For every action and every situation, the action costs strictly more ene\
    rgy at every night tick than at every daytime tick, waiting included.\n\
    | - **Rules out:** Any action that, in some situation, costs as much or less at some night\
    \x20tick than at some daytime tick.\n\
    | - **Still allows:** Any amount more at night, and a night cost that changes during the n\
    ight, as long as it stays above every daytime cost.\n\
    | - **Freedom O5 leaves:** How much more the night costs, and whether that extra changes d\
    uring the night.\n\
    | \n\
    | ### the agent can always tell day from night\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (t :\
    \x20Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @Eq.{1} UInt8 (@AcornVerif.Intent.Day\
    Cycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t c) (@AcornVerif.Intent.DayCycle.D\
    ayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') → @Eq.{1} Bool (@AcornVerif.Intent.\
    DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) (@AcornVerif.Intent.DayCycle\
    .DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t')\n\
    | ```\n\
    | \n\
    | - **Requires:** Whatever the agent sees always tells it whether it is day or night.\n\
    | - **Rules out:** An agent that sees a day moment and a night moment alike.\n\
    | - **Still allows:** An agent that sees more than that.\n\
    | - **Freedom O5 leaves:** How much more it sees.\n\
    | \n\
    | ### the agent can always see where in the day it is, at least to a quarter of the day\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Exist\
    s.{1} Nat (fun (start : Nat) => ∀ (t : Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @E\
    q.{1} UInt8 (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w \
    t c) (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') \
    → @Eq.{1} Nat (AcornVerif.Intent.DayCycle.quarter (@AcornVerif.Intent.DayCycle.DayWorld.le\
    ngth Unit Acorn.Host.Action UInt8 Nat w) start t) (AcornVerif.Intent.DayCycle.quarter (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) start t'))\n\
    | ```\n\
    | \n\
    | - **Requires:** Whatever the agent sees always tells it which quarter of the day it is i\
    n.\n\
    | - **Rules out:** An agent that sees only whether it is day or night, in a day longer tha\
    n two ticks.\n\
    | - **Still allows:** An agent that sees the quarter, a finer part of the day, or the exac\
    t tick.\n\
    | - **Freedom O5 leaves:** How much more finely than a quarter the agent sees the time of \
    day.\n\
    | \n\
    | ## Vocabulary\n\
    | \n\
    | ### night half, a predicate over `Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) => AcornVerif.Intent.DayCycle.NightHalf \
    (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat Nat) p) (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0}\
    \x20Nat (Prod.{0, 0} Nat Nat) p)) (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0\
    , 0} Nat Nat) p))\n\
    | ```\n\
    | \n\
    | - **Requires:** Tick t is in the night when, counted around a day of the given length fr\
    om where the night starts, it falls in the first half.\n\
    | - **Rules out:** Tick 1 in a day of two ticks whose night starts at tick 0.\n\
    | - **Still allows:** Tick 0 in that day.\n\
    | - **Freedom O5 leaves:** None: it is a definition.\n\
    | \n\
    | ### costs less, a predicate over `Prod.{0, 0} Nat Nat`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} Nat Nat) => @LT.lt.{0} Nat instLTNat (@Prod.fst.{0, 0} Nat Nat p) (\
    @Prod.snd.{0, 0} Nat Nat p)\n\
    | ```\n\
    | \n\
    | - **Requires:** The world's own order on energy amounts.\n\
    | - **Rules out:** Whatever that order rules out.\n\
    | - **Still allows:** Whatever that order allows.\n\
    | - **Freedom O5 leaves:** None of its own.\n\
    | \n\
    | ### in quarter, a predicate over `Prod.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)\
    )`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))) => @Eq.{1} Nat (AcornV\
    erif.Intent.DayCycle.quarter (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))\
    \x20p) (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat Nat) (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat \
    (Prod.{0, 0} Nat Nat)) p)) (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Na\
    t Nat) (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) p)))) (@Prod.snd.{0, \
    0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat Nat) (@Prod.snd.{0, 0} Nat (Prod.{0, 0} \
    Nat (Prod.{0, 0} Nat Nat)) p)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Tick t lies in the given quarter of a day of the given length, counted f\
    rom the given start.\n\
    | - **Rules out:** Tick 0 in quarter 1 of a day of four ticks counted from tick 0.\n\
    | - **Still allows:** Tick 0 in quarter 0 of that day.\n\
    | - **Freedom O5 leaves:** None: it is a definition.\n\
    | \n\
    | ## Consequences\n\
    | \n\
    | ### every day lasts the same even number of ticks, at least two, placed alike, an entail\
    ment: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => And (@\
    LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w)) (And (@Eq.{1\
    } Nat (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@AcornVerif.Inten\
    t.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) (@OfNat.ofNat.{0} Nat (nat_\
    lit 2) (instOfNatNat (nat_lit 2)))) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_l\
    it 0)))) (∀ (t : Nat), @Eq.{1} Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn\
    .Host.Action UInt8 Nat w (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) \
    t (@AcornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w))) (@Aco\
    rnVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Every day lasts the same even number of ticks, at least two, and each da\
    y's night falls at the same ticks of the day.\n\
    | - **Rules out:** Days of different lengths.\n\
    | - **Still allows:** Any one day length shared by all days.\n\
    | - **Freedom O5 leaves:** The length itself.\n\
    | \n\
    | ### every action costs more at any night moment than at any daytime moment, an entailmen\
    t: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (c :\
    \x20Unit), ∀ (a : Acorn.Host.Action), ∀ (t : Nat), ∀ (t' : Nat), @Eq.{1} Bool (@AcornVerif\
    .Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true → @Eq.{1} \
    Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t') Bo\
    ol.false → @LT.lt.{0} Nat instLTNat (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.\
    Host.Action UInt8 Nat w t' c a) (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.Host\
    .Action UInt8 Nat w t c a)\n\
    | ```\n\
    | \n\
    | - **Requires:** Even the cheapest action costs more at any night moment than at any dayt\
    ime moment, in the same situation.\n\
    | - **Rules out:** Any action that is no dearer at some night moment.\n\
    | - **Still allows:** Any extra amount.\n\
    | - **Freedom O5 leaves:** How much more.\n\
    | \n\
    | ### what the agent sees always tells day from night, an entailment: every subject that m\
    eets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (t :\
    \x20Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @Eq.{1} UInt8 (@AcornVerif.Intent.Day\
    Cycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t c) (@AcornVerif.Intent.DayCycle.D\
    ayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') → @Eq.{1} Bool (@AcornVerif.Intent.\
    DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) (@AcornVerif.Intent.DayCycle\
    .DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t')\n\
    | ```\n\
    | \n\
    | - **Requires:** From what it sees, the agent can always tell whether it is day or night.\
    \n\
    | - **Rules out:** An agent that cannot tell day from night at some moment.\n\
    | - **Still allows:** An agent that sees more than that.\n\
    | - **Freedom O5 leaves:** How much more it sees.\n\
    | \n\
    | ### what the agent sees always tells it which quarter of the day it is in, an entailment\
    : every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Exist\
    s.{1} Nat (fun (start : Nat) => ∀ (t : Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @E\
    q.{1} UInt8 (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w \
    t c) (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') \
    → @Eq.{1} Nat (AcornVerif.Intent.DayCycle.quarter (@AcornVerif.Intent.DayCycle.DayWorld.le\
    ngth Unit Acorn.Host.Action UInt8 Nat w) start t) (AcornVerif.Intent.DayCycle.quarter (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) start t'))\n\
    | ```\n\
    | \n\
    | - **Requires:** From what it sees, the agent can always tell which quarter of the day it\
    \x20is in.\n\
    | - **Rules out:** An agent that sees only day or night.\n\
    | - **Still allows:** Seeing a finer part of the day, or the exact tick.\n\
    | - **Freedom O5 leaves:** How much finer than a quarter.\n\
    | \n\
    | ### a day may last 1000 ticks, a possibility: some subject that meets the record satisfi\
    es it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Eq.{1\
    } Nat (@AcornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) (@O\
    fNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Nothing more: a world whose day lasts 1000 ticks can meet the record.\n\
    | - **Rules out:** Nothing.\n\
    | - **Still allows:** Short days and long days alike.\n\
    | - **Freedom O5 leaves:** The day's length.\n\
    | \n\
    | ### an action may cost more at one night moment than at another, a possibility: some sub\
    ject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Exist\
    s.{1} Unit (fun (c : Unit) => @Exists.{1} Acorn.Host.Action (fun (a : Acorn.Host.Action) =\
    > @Exists.{1} Nat (fun (t : Nat) => @Exists.{1} Nat (fun (t' : Nat) => And (@Eq.{1} Bool (\
    @AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true\
    ) (And (@Eq.{1} Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UI\
    nt8 Nat w t') Bool.true) (@Ne.{1} Nat (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acor\
    n.Host.Action UInt8 Nat w t c a) (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.Hos\
    t.Action UInt8 Nat w t' c a)))))))\n\
    | ```\n\
    | \n\
    | - **Requires:** Nothing more: an action may cost more at one night moment than at anothe\
    r, as long as every night cost is above every daytime cost.\n\
    | - **Rules out:** Nothing.\n\
    | - **Still allows:** A night that is dearer at midnight than at dusk.\n\
    | - **Freedom O5 leaves:** Whether the night's extra changes during the night.\n\
    | \n\
    | ## Definitions the record's meaning reaches\n\
    | \n\
    | These are not statements of the record: each is a declaration that a statement above dep\
    ends on, or that says what it is for a subject to meet the record and for a consequence to\
    \x20hold of it as shown, with everything those depend on in turn. Each is printed in full:\
    \x20its type, a definition's value, or for a definition by structural or well-founded recu\
    rsion the equation that determines it, and an inductive type's constructors, which for a s\
    tructure are its fields; a theorem's proof and an opaque constant's value are not, since n\
    o term that uses them depends on more than their types. Their plain words are those of the\
    \x20statements that use them.\n\
    | \n\
    | ### Acorn.Host.Action\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### Acorn.Host.Action.north\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.south\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.east\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.west\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.wait\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.harvest\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftAxe\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftBoat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.eat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Shape\n\
    | \n\
    | An inductive type. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type u → Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Shape.value\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.function\n\
    | \n\
    | ```lean\n\
    | ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.step\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.stepOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.action\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.actionOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u\
    } O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.bundle\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀\
    \x20(rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Member\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Member.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → \
    Out), LeanIntent.Member.{u} W\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (Ctx : Type), ∀ (Act : Type), ∀ (Obs : Type), ∀ (E : Type), Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 4 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.DayCycle.DayWorld.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (length : Nat), ∀ (night\
    \x20: Nat → Bool), ∀ (cost : Nat → Ctx → Act → E), ∀ (sees : Nat → Ctx → Obs), AcornVerif.\
    Intent.DayCycle.DayWorld Ctx Act Obs E\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.length\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 1, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.night\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 2, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Bool\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.NightHalf\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (length : Nat), ∀ (start : Nat), ∀ (t : Nat), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (length : Nat) => fun (start : Nat) => fun (t : Nat) => @LT.lt.{0} Nat instLTNat (@H\
    Mod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@HAdd.hAdd.{0, 0, 0} Nat N\
    at Nat (@instHAdd.{0} Nat instAddNat) t start) length) (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (\
    @instHDiv.{0} Nat Nat.instDiv) length (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat\
    _lit 2))))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.cost\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 3, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Ctx → Act → E\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.sees\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 4, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Ctx → Obs\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.quarter\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (length : Nat), ∀ (start : Nat), ∀ (t : Nat), Nat\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (length : Nat) => fun (start : Nat) => fun (t : Nat) => @HDiv.hDiv.{0, 0, 0} Nat Nat\
    \x20Nat (@instHDiv.{0} Nat Nat.instDiv) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} N\
    at instMulNat) (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@HAdd.hA\
    dd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t start) length) (@OfNat.ofNat.{0}\
    \x20Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) length\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Meets\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@Lean\
    Intent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.IntentRecord.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause\
    .{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanInte\
    nt.Pred.{u}), LeanIntent.IntentRecord.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Clause.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Pred\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Pred.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Dom\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.dom\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Cla\
    use's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Props\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.props\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.HoldsOf\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (c : LeanIntent.Consequence.{u} W), ∀ (r : LeanIntent.IntentRecord.{u}\
    \x20W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (c : LeanIntent.Consequence.{u} W) => fun (r : LeanIntent.Intent\
    Record.{u} W) => LeanIntent.Consequence.HoldsOf.match_1.{1} (fun (x : LeanIntent.Consequen\
    ce.Kind) => Prop) (@LeanIntent.Consequence.kind.{u} W c) (fun («_» : Unit) => ∀ (w : W), @\
    LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W c w) (fun («\
    _» : Unit) => @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRec\
    ord.Meets.{u} W r w) (@LeanIntent.Consequence.holds.{u} W c w)))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W \
    → Prop), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.entailment\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.possibility\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.HoldsOf.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : LeanIntent.Consequence.Kind → Sort u_1), ∀ (x : LeanIntent.Consequence.Kind)\
    , ∀ (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment), ∀ (h_2 : ∀ («_»\
    \x20: Unit), motive LeanIntent.Consequence.Kind.possibility), motive x\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : LeanIntent.Consequence.Kind → Sort u_1) => fun (x : LeanIntent.Consequence\
    .Kind) => fun (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment) => fun\
    \x20(h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.\
    Consequence.Kind.casesOn.{u_1} (fun (x_1 : LeanIntent.Consequence.Kind) => motive x_1) x (\
    h_1 Unit.unit) (h_2 Unit.unit)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.\
    Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : mo\
    tive LeanIntent.Consequence.Kind.possibility), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Conseq\
    uence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (po\
    ssibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kin\
    d.rec.{u} motive entailment possibility t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.kind\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.HasInstance\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)\n\
    | ```\n\
    | \n\
    | ## Lean's own libraries\n\
    | \n\
    | The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: the\
    y are those of Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, which made th\
    is text. A declaration is counted as Lean's own when Lean found the module that declares i\
    t in that release's library directory.\n\
    | \n\
    consequence every day lasts the same even number of ticks, at least two, placed alike\n\
    shown as entailment\n\
    predicate 472\n\
    | # A consequence's predicate\n\
    | \n\
    | Printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks,\
    \x20binder names and metadata aside, from the root namespace with nothing opened.\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => And (@\
    LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w)) (And (@Eq.{1\
    } Nat (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@AcornVerif.Inten\
    t.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) (@OfNat.ofNat.{0} Nat (nat_\
    lit 2) (instOfNatNat (nat_lit 2)))) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_l\
    it 0)))) (∀ (t : Nat), @Eq.{1} Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn\
    .Host.Action UInt8 Nat w (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) \
    t (@AcornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w))) (@Aco\
    rnVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t)))\n\
    | ```\n\
    | \n\
    | ## Definitions the predicate reaches\n\
    | \n\
    | Each is printed in full, as in the rendering of a record, with what an answer to it asks\
    \x20of every later revision (`LeanIntent.Answer.KeptBy`).\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (Ctx : Type), ∀ (Act : Type), ∀ (Obs : Type), ∀ (E : Type), Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 4 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.DayCycle.DayWorld.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (length : Nat), ∀ (night\
    \x20: Nat → Bool), ∀ (cost : Nat → Ctx → Act → E), ∀ (sees : Nat → Ctx → Obs), AcornVerif.\
    Intent.DayCycle.DayWorld Ctx Act Obs E\n\
    | ```\n\
    | \n\
    | ### Acorn.Host.Action\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### Acorn.Host.Action.north\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.south\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.east\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.west\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.wait\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.harvest\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftAxe\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftBoat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.eat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.length\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 1, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.night\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 2, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Bool\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.KeptBy\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (a : LeanIntent.Answer.{u} W), ∀ (r : LeanIntent.IntentRecord.{u} W), \
    Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (a : LeanIntent.Answer.{u} W) => fun (r : LeanIntent.IntentRecor\
    d.{u} W) => LeanIntent.Answer.KeptBy.match_1.{1} (fun (x : LeanIntent.Consequence.Kind) =>\
    \x20fun (x_1 : LeanIntent.Verdict) => Prop) (@LeanIntent.Consequence.kind.{u} W (@LeanInte\
    nt.Answer.consequence.{u} W a)) (@LeanIntent.Answer.verdict.{u} W a) (fun («_» : Unit) => \
    ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W \
    (@LeanIntent.Answer.consequence.{u} W a) w) (fun («_» : Unit) => @LeanIntent.HasInstance.{\
    u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u} W r w) (Not (@LeanIntent.\
    Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w)))) (fun («_» : Unit) =\
    > @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u\
    } W r w) (@LeanIntent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w))\
    ) (fun («_» : Unit) => ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → Not (@LeanInt\
    ent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Answer.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (consequence : LeanIntent.Consequence.{u} W), ∀ (verdict : LeanIntent.\
    Verdict), LeanIntent.Answer.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W \
    → Prop), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.entailment\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.possibility\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Verdict\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Verdict.confirmed\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Verdict.declined\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.IntentRecord.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause\
    .{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanInte\
    nt.Pred.{u}), LeanIntent.IntentRecord.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Shape\n\
    | \n\
    | An inductive type. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type u → Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Shape.value\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.function\n\
    | \n\
    | ```lean\n\
    | ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.step\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.stepOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.action\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.actionOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u\
    } O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.bundle\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀\
    \x20(rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Member\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Member.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → \
    Out), LeanIntent.Member.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Clause.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Pred\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Pred.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.KeptBy.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : LeanIntent.Consequence.Kind → LeanIntent.Verdict → Sort u_1), ∀ (x : LeanInt\
    ent.Consequence.Kind), ∀ (x_1 : LeanIntent.Verdict), ∀ (h_1 : ∀ («_» : Unit), motive LeanI\
    ntent.Consequence.Kind.entailment LeanIntent.Verdict.confirmed), ∀ (h_2 : ∀ («_» : Unit), \
    motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.declined), ∀ (h_3 : ∀ («_\
    » : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdict.confirmed), ∀\
    \x20(h_4 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdi\
    ct.declined), motive x x_1\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : LeanIntent.Consequence.Kind → LeanIntent.Verdict → Sort u_1) => fun (x : L\
    eanIntent.Consequence.Kind) => fun (x_1 : LeanIntent.Verdict) => fun (h_1 : ∀ («_» : Unit)\
    , motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.confirmed) => fun (h_2 \
    : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.decline\
    d) => fun (h_3 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent\
    .Verdict.confirmed) => fun (h_4 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possi\
    bility LeanIntent.Verdict.declined) => @LeanIntent.Consequence.Kind.casesOn.{u_1} (fun (x_\
    2 : LeanIntent.Consequence.Kind) => motive x_2 x_1) x (@LeanIntent.Verdict.casesOn.{u_1} (\
    fun (x_2 : LeanIntent.Verdict) => motive LeanIntent.Consequence.Kind.entailment x_2) x_1 (\
    h_1 Unit.unit) (h_2 Unit.unit)) (@LeanIntent.Verdict.casesOn.{u_1} (fun (x_2 : LeanIntent.\
    Verdict) => motive LeanIntent.Consequence.Kind.possibility x_2) x_1 (h_3 Unit.unit) (h_4 U\
    nit.unit))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.\
    Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : mo\
    tive LeanIntent.Consequence.Kind.possibility), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Conseq\
    uence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (po\
    ssibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kin\
    d.rec.{u} motive entailment possibility t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Verdict.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Verdict), Sort u}, ∀ (t : LeanIntent.Verdict), ∀ (confirme\
    d : motive LeanIntent.Verdict.confirmed), ∀ (declined : motive LeanIntent.Verdict.declined\
    ), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Verdict), Sort u} => fun (t : LeanIntent.Verdict) => fun\
    \x20(confirmed : motive LeanIntent.Verdict.confirmed) => fun (declined : motive LeanIntent\
    .Verdict.declined) => @LeanIntent.Verdict.rec.{u} motive confirmed declined t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.kind\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.consequence\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 1, counted after the parameters in the type of LeanIntent.Ans\
    wer's constructor, of its argument number 2, a value of LeanIntent.Answer. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Answer.{u} W), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.verdict\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Ans\
    wer's constructor, of its argument number 2, a value of LeanIntent.Answer. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Answer.{u} W), LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Meets\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@Lean\
    Intent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Dom\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.dom\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Cla\
    use's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Props\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.props\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.HasInstance\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)\n\
    | ```\n\
    | \n\
    | ## Lean's own libraries\n\
    | \n\
    | The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: the\
    y are those of Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, which made th\
    is text. A declaration is counted as Lean's own when Lean found the module that declares i\
    t in that release's library directory.\n\
    | \n\
    verdict confirmed\n\
    ",
  "lean-intent statement 1\n\
    kind answer\n\
    project acorn\n\
    id day-2-r2\n\
    date 2026-11-03\n\
    reference docs/spec-first-pilot.md, The decisions made on the owner's behalf\n\
    by agents\n\
    under agents-below-intent\n\
    record AcornVerif.Intent.DayCycle.dayCycle\n\
    revision 610\n\
    | # The intent record @AcornVerif.Intent.DayCycle.dayCycleFor Unit Acorn.Host.Action UInt8\
    \x20Nat instLTNat\n\
    | \n\
    | Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term \
    its kernel checks, binder names and metadata aside, from the root namespace with nothing o\
    pened. The plain words after it are written by a model and are trusted, not proved.\n\
    | \n\
    | ## Shape\n\
    | \n\
    | ### The subject\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Shape.value.{0} (AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action U\
    Int8 Nat)\n\
    | ```\n\
    | \n\
    | - **Requires:** The subject is a description of a world's day: how many ticks a day last\
    s, which ticks are night, what each action costs at each tick in each situation, and what \
    the agent sees at each tick in each situation. Time is counted in whole ticks from the sta\
    rt of a run, and one clock serves the whole world.\n\
    | - **Rules out:** Nothing by itself; it fixes only what the statements below talk about.\
    \n\
    | - **Still allows:** Any world's situations, actions, sights and energy amounts.\n\
    | - **Freedom O5 leaves:** None of its own. It carries no state from one tick to the next,\
    \x20so it is declared a plain value, of which obligation O4 asks nothing.\n\
    | \n\
    | ## Domain hypotheses\n\
    | \n\
    | None.\n\
    | \n\
    | ## Properties\n\
    | \n\
    | ### each day has a daytime half and a night half of equal length\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => And (@\
    LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w)) (And (@Eq.{1\
    } Nat (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@AcornVerif.Inten\
    t.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) (@OfNat.ofNat.{0} Nat (nat_\
    lit 2) (instOfNatNat (nat_lit 2)))) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_l\
    it 0)))) (@Exists.{1} Nat (fun (start : Nat) => ∀ (t : Nat), Iff (@Eq.{1} Bool (@AcornVeri\
    f.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true) (AcornVe\
    rif.Intent.DayCycle.NightHalf (@AcornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host\
    .Action UInt8 Nat w) start t))))\n\
    | ```\n\
    | \n\
    | - **Requires:** A day lasts a fixed, even number of ticks, at least two. The night is on\
    e unbroken stretch of exactly half of them and the daytime the other half, and every day i\
    s the same.\n\
    | - **Rules out:** A world with no night or no daytime; a day of an odd number of ticks; a\
    \x20night broken into several stretches; days of different lengths.\n\
    | - **Still allows:** Any even day length, and a night that starts at any tick of the day.\
    \n\
    | - **Freedom O5 leaves:** How long a day is and where in it the night starts.\n\
    | \n\
    | ### at night every action costs more energy\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (c :\
    \x20Unit), ∀ (a : Acorn.Host.Action), ∀ (t : Nat), ∀ (t' : Nat), @Eq.{1} Bool (@AcornVerif\
    .Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true → @Eq.{1} \
    Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t') Bo\
    ol.false → @LT.lt.{0} Nat instLTNat (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.\
    Host.Action UInt8 Nat w t' c a) (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.Host\
    .Action UInt8 Nat w t c a)\n\
    | ```\n\
    | \n\
    | - **Requires:** For every action and every situation, the action costs strictly more ene\
    rgy at every night tick than at every daytime tick, waiting included.\n\
    | - **Rules out:** Any action that, in some situation, costs as much or less at some night\
    \x20tick than at some daytime tick.\n\
    | - **Still allows:** Any amount more at night, and a night cost that changes during the n\
    ight, as long as it stays above every daytime cost.\n\
    | - **Freedom O5 leaves:** How much more the night costs, and whether that extra changes d\
    uring the night.\n\
    | \n\
    | ### the agent can always tell day from night\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (t :\
    \x20Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @Eq.{1} UInt8 (@AcornVerif.Intent.Day\
    Cycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t c) (@AcornVerif.Intent.DayCycle.D\
    ayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') → @Eq.{1} Bool (@AcornVerif.Intent.\
    DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) (@AcornVerif.Intent.DayCycle\
    .DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t')\n\
    | ```\n\
    | \n\
    | - **Requires:** Whatever the agent sees always tells it whether it is day or night.\n\
    | - **Rules out:** An agent that sees a day moment and a night moment alike.\n\
    | - **Still allows:** An agent that sees more than that.\n\
    | - **Freedom O5 leaves:** How much more it sees.\n\
    | \n\
    | ### the agent can always see where in the day it is, at least to a quarter of the day\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Exist\
    s.{1} Nat (fun (start : Nat) => ∀ (t : Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @E\
    q.{1} UInt8 (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w \
    t c) (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') \
    → @Eq.{1} Nat (AcornVerif.Intent.DayCycle.quarter (@AcornVerif.Intent.DayCycle.DayWorld.le\
    ngth Unit Acorn.Host.Action UInt8 Nat w) start t) (AcornVerif.Intent.DayCycle.quarter (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) start t'))\n\
    | ```\n\
    | \n\
    | - **Requires:** Whatever the agent sees always tells it which quarter of the day it is i\
    n.\n\
    | - **Rules out:** An agent that sees only whether it is day or night, in a day longer tha\
    n two ticks.\n\
    | - **Still allows:** An agent that sees the quarter, a finer part of the day, or the exac\
    t tick.\n\
    | - **Freedom O5 leaves:** How much more finely than a quarter the agent sees the time of \
    day.\n\
    | \n\
    | ## Vocabulary\n\
    | \n\
    | ### night half, a predicate over `Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) => AcornVerif.Intent.DayCycle.NightHalf \
    (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat Nat) p) (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0}\
    \x20Nat (Prod.{0, 0} Nat Nat) p)) (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0\
    , 0} Nat Nat) p))\n\
    | ```\n\
    | \n\
    | - **Requires:** Tick t is in the night when, counted around a day of the given length fr\
    om where the night starts, it falls in the first half.\n\
    | - **Rules out:** Tick 1 in a day of two ticks whose night starts at tick 0.\n\
    | - **Still allows:** Tick 0 in that day.\n\
    | - **Freedom O5 leaves:** None: it is a definition.\n\
    | \n\
    | ### costs less, a predicate over `Prod.{0, 0} Nat Nat`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} Nat Nat) => @LT.lt.{0} Nat instLTNat (@Prod.fst.{0, 0} Nat Nat p) (\
    @Prod.snd.{0, 0} Nat Nat p)\n\
    | ```\n\
    | \n\
    | - **Requires:** The world's own order on energy amounts.\n\
    | - **Rules out:** Whatever that order rules out.\n\
    | - **Still allows:** Whatever that order allows.\n\
    | - **Freedom O5 leaves:** None of its own.\n\
    | \n\
    | ### in quarter, a predicate over `Prod.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)\
    )`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))) => @Eq.{1} Nat (AcornV\
    erif.Intent.DayCycle.quarter (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))\
    \x20p) (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat Nat) (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat \
    (Prod.{0, 0} Nat Nat)) p)) (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Na\
    t Nat) (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) p)))) (@Prod.snd.{0, \
    0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat Nat) (@Prod.snd.{0, 0} Nat (Prod.{0, 0} \
    Nat (Prod.{0, 0} Nat Nat)) p)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Tick t lies in the given quarter of a day of the given length, counted f\
    rom the given start.\n\
    | - **Rules out:** Tick 0 in quarter 1 of a day of four ticks counted from tick 0.\n\
    | - **Still allows:** Tick 0 in quarter 0 of that day.\n\
    | - **Freedom O5 leaves:** None: it is a definition.\n\
    | \n\
    | ## Consequences\n\
    | \n\
    | ### every day lasts the same even number of ticks, at least two, placed alike, an entail\
    ment: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => And (@\
    LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w)) (And (@Eq.{1\
    } Nat (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@AcornVerif.Inten\
    t.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) (@OfNat.ofNat.{0} Nat (nat_\
    lit 2) (instOfNatNat (nat_lit 2)))) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_l\
    it 0)))) (∀ (t : Nat), @Eq.{1} Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn\
    .Host.Action UInt8 Nat w (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) \
    t (@AcornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w))) (@Aco\
    rnVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Every day lasts the same even number of ticks, at least two, and each da\
    y's night falls at the same ticks of the day.\n\
    | - **Rules out:** Days of different lengths.\n\
    | - **Still allows:** Any one day length shared by all days.\n\
    | - **Freedom O5 leaves:** The length itself.\n\
    | \n\
    | ### every action costs more at any night moment than at any daytime moment, an entailmen\
    t: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (c :\
    \x20Unit), ∀ (a : Acorn.Host.Action), ∀ (t : Nat), ∀ (t' : Nat), @Eq.{1} Bool (@AcornVerif\
    .Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true → @Eq.{1} \
    Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t') Bo\
    ol.false → @LT.lt.{0} Nat instLTNat (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.\
    Host.Action UInt8 Nat w t' c a) (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.Host\
    .Action UInt8 Nat w t c a)\n\
    | ```\n\
    | \n\
    | - **Requires:** Even the cheapest action costs more at any night moment than at any dayt\
    ime moment, in the same situation.\n\
    | - **Rules out:** Any action that is no dearer at some night moment.\n\
    | - **Still allows:** Any extra amount.\n\
    | - **Freedom O5 leaves:** How much more.\n\
    | \n\
    | ### what the agent sees always tells day from night, an entailment: every subject that m\
    eets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (t :\
    \x20Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @Eq.{1} UInt8 (@AcornVerif.Intent.Day\
    Cycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t c) (@AcornVerif.Intent.DayCycle.D\
    ayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') → @Eq.{1} Bool (@AcornVerif.Intent.\
    DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) (@AcornVerif.Intent.DayCycle\
    .DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t')\n\
    | ```\n\
    | \n\
    | - **Requires:** From what it sees, the agent can always tell whether it is day or night.\
    \n\
    | - **Rules out:** An agent that cannot tell day from night at some moment.\n\
    | - **Still allows:** An agent that sees more than that.\n\
    | - **Freedom O5 leaves:** How much more it sees.\n\
    | \n\
    | ### what the agent sees always tells it which quarter of the day it is in, an entailment\
    : every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Exist\
    s.{1} Nat (fun (start : Nat) => ∀ (t : Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @E\
    q.{1} UInt8 (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w \
    t c) (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') \
    → @Eq.{1} Nat (AcornVerif.Intent.DayCycle.quarter (@AcornVerif.Intent.DayCycle.DayWorld.le\
    ngth Unit Acorn.Host.Action UInt8 Nat w) start t) (AcornVerif.Intent.DayCycle.quarter (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) start t'))\n\
    | ```\n\
    | \n\
    | - **Requires:** From what it sees, the agent can always tell which quarter of the day it\
    \x20is in.\n\
    | - **Rules out:** An agent that sees only day or night.\n\
    | - **Still allows:** Seeing a finer part of the day, or the exact tick.\n\
    | - **Freedom O5 leaves:** How much finer than a quarter.\n\
    | \n\
    | ### a day may last 1000 ticks, a possibility: some subject that meets the record satisfi\
    es it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Eq.{1\
    } Nat (@AcornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) (@O\
    fNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Nothing more: a world whose day lasts 1000 ticks can meet the record.\n\
    | - **Rules out:** Nothing.\n\
    | - **Still allows:** Short days and long days alike.\n\
    | - **Freedom O5 leaves:** The day's length.\n\
    | \n\
    | ### an action may cost more at one night moment than at another, a possibility: some sub\
    ject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Exist\
    s.{1} Unit (fun (c : Unit) => @Exists.{1} Acorn.Host.Action (fun (a : Acorn.Host.Action) =\
    > @Exists.{1} Nat (fun (t : Nat) => @Exists.{1} Nat (fun (t' : Nat) => And (@Eq.{1} Bool (\
    @AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true\
    ) (And (@Eq.{1} Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UI\
    nt8 Nat w t') Bool.true) (@Ne.{1} Nat (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acor\
    n.Host.Action UInt8 Nat w t c a) (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.Hos\
    t.Action UInt8 Nat w t' c a)))))))\n\
    | ```\n\
    | \n\
    | - **Requires:** Nothing more: an action may cost more at one night moment than at anothe\
    r, as long as every night cost is above every daytime cost.\n\
    | - **Rules out:** Nothing.\n\
    | - **Still allows:** A night that is dearer at midnight than at dusk.\n\
    | - **Freedom O5 leaves:** Whether the night's extra changes during the night.\n\
    | \n\
    | ## Definitions the record's meaning reaches\n\
    | \n\
    | These are not statements of the record: each is a declaration that a statement above dep\
    ends on, or that says what it is for a subject to meet the record and for a consequence to\
    \x20hold of it as shown, with everything those depend on in turn. Each is printed in full:\
    \x20its type, a definition's value, or for a definition by structural or well-founded recu\
    rsion the equation that determines it, and an inductive type's constructors, which for a s\
    tructure are its fields; a theorem's proof and an opaque constant's value are not, since n\
    o term that uses them depends on more than their types. Their plain words are those of the\
    \x20statements that use them.\n\
    | \n\
    | ### Acorn.Host.Action\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### Acorn.Host.Action.north\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.south\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.east\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.west\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.wait\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.harvest\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftAxe\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftBoat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.eat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Shape\n\
    | \n\
    | An inductive type. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type u → Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Shape.value\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.function\n\
    | \n\
    | ```lean\n\
    | ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.step\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.stepOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.action\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.actionOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u\
    } O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.bundle\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀\
    \x20(rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Member\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Member.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → \
    Out), LeanIntent.Member.{u} W\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (Ctx : Type), ∀ (Act : Type), ∀ (Obs : Type), ∀ (E : Type), Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 4 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.DayCycle.DayWorld.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (length : Nat), ∀ (night\
    \x20: Nat → Bool), ∀ (cost : Nat → Ctx → Act → E), ∀ (sees : Nat → Ctx → Obs), AcornVerif.\
    Intent.DayCycle.DayWorld Ctx Act Obs E\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.length\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 1, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.night\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 2, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Bool\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.NightHalf\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (length : Nat), ∀ (start : Nat), ∀ (t : Nat), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (length : Nat) => fun (start : Nat) => fun (t : Nat) => @LT.lt.{0} Nat instLTNat (@H\
    Mod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@HAdd.hAdd.{0, 0, 0} Nat N\
    at Nat (@instHAdd.{0} Nat instAddNat) t start) length) (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (\
    @instHDiv.{0} Nat Nat.instDiv) length (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat\
    _lit 2))))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.cost\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 3, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Ctx → Act → E\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.sees\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 4, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Ctx → Obs\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.quarter\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (length : Nat), ∀ (start : Nat), ∀ (t : Nat), Nat\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (length : Nat) => fun (start : Nat) => fun (t : Nat) => @HDiv.hDiv.{0, 0, 0} Nat Nat\
    \x20Nat (@instHDiv.{0} Nat Nat.instDiv) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} N\
    at instMulNat) (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@HAdd.hA\
    dd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t start) length) (@OfNat.ofNat.{0}\
    \x20Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) length\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Meets\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@Lean\
    Intent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.IntentRecord.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause\
    .{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanInte\
    nt.Pred.{u}), LeanIntent.IntentRecord.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Clause.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Pred\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Pred.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Dom\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.dom\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Cla\
    use's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Props\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.props\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.HoldsOf\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (c : LeanIntent.Consequence.{u} W), ∀ (r : LeanIntent.IntentRecord.{u}\
    \x20W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (c : LeanIntent.Consequence.{u} W) => fun (r : LeanIntent.Intent\
    Record.{u} W) => LeanIntent.Consequence.HoldsOf.match_1.{1} (fun (x : LeanIntent.Consequen\
    ce.Kind) => Prop) (@LeanIntent.Consequence.kind.{u} W c) (fun («_» : Unit) => ∀ (w : W), @\
    LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W c w) (fun («\
    _» : Unit) => @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRec\
    ord.Meets.{u} W r w) (@LeanIntent.Consequence.holds.{u} W c w)))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W \
    → Prop), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.entailment\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.possibility\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.HoldsOf.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : LeanIntent.Consequence.Kind → Sort u_1), ∀ (x : LeanIntent.Consequence.Kind)\
    , ∀ (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment), ∀ (h_2 : ∀ («_»\
    \x20: Unit), motive LeanIntent.Consequence.Kind.possibility), motive x\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : LeanIntent.Consequence.Kind → Sort u_1) => fun (x : LeanIntent.Consequence\
    .Kind) => fun (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment) => fun\
    \x20(h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.\
    Consequence.Kind.casesOn.{u_1} (fun (x_1 : LeanIntent.Consequence.Kind) => motive x_1) x (\
    h_1 Unit.unit) (h_2 Unit.unit)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.\
    Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : mo\
    tive LeanIntent.Consequence.Kind.possibility), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Conseq\
    uence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (po\
    ssibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kin\
    d.rec.{u} motive entailment possibility t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.kind\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.HasInstance\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)\n\
    | ```\n\
    | \n\
    | ## Lean's own libraries\n\
    | \n\
    | The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: the\
    y are those of Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, which made th\
    is text. A declaration is counted as Lean's own when Lean found the module that declares i\
    t in that release's library directory.\n\
    | \n\
    consequence every action costs more at any night moment than at any daytime moment\n\
    shown as entailment\n\
    predicate 472\n\
    | # A consequence's predicate\n\
    | \n\
    | Printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks,\
    \x20binder names and metadata aside, from the root namespace with nothing opened.\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (c :\
    \x20Unit), ∀ (a : Acorn.Host.Action), ∀ (t : Nat), ∀ (t' : Nat), @Eq.{1} Bool (@AcornVerif\
    .Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true → @Eq.{1} \
    Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t') Bo\
    ol.false → @LT.lt.{0} Nat instLTNat (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.\
    Host.Action UInt8 Nat w t' c a) (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.Host\
    .Action UInt8 Nat w t c a)\n\
    | ```\n\
    | \n\
    | ## Definitions the predicate reaches\n\
    | \n\
    | Each is printed in full, as in the rendering of a record, with what an answer to it asks\
    \x20of every later revision (`LeanIntent.Answer.KeptBy`).\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (Ctx : Type), ∀ (Act : Type), ∀ (Obs : Type), ∀ (E : Type), Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 4 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.DayCycle.DayWorld.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (length : Nat), ∀ (night\
    \x20: Nat → Bool), ∀ (cost : Nat → Ctx → Act → E), ∀ (sees : Nat → Ctx → Obs), AcornVerif.\
    Intent.DayCycle.DayWorld Ctx Act Obs E\n\
    | ```\n\
    | \n\
    | ### Acorn.Host.Action\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### Acorn.Host.Action.north\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.south\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.east\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.west\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.wait\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.harvest\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftAxe\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftBoat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.eat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.night\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 2, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Bool\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.cost\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 3, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Ctx → Act → E\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.KeptBy\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (a : LeanIntent.Answer.{u} W), ∀ (r : LeanIntent.IntentRecord.{u} W), \
    Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (a : LeanIntent.Answer.{u} W) => fun (r : LeanIntent.IntentRecor\
    d.{u} W) => LeanIntent.Answer.KeptBy.match_1.{1} (fun (x : LeanIntent.Consequence.Kind) =>\
    \x20fun (x_1 : LeanIntent.Verdict) => Prop) (@LeanIntent.Consequence.kind.{u} W (@LeanInte\
    nt.Answer.consequence.{u} W a)) (@LeanIntent.Answer.verdict.{u} W a) (fun («_» : Unit) => \
    ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W \
    (@LeanIntent.Answer.consequence.{u} W a) w) (fun («_» : Unit) => @LeanIntent.HasInstance.{\
    u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u} W r w) (Not (@LeanIntent.\
    Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w)))) (fun («_» : Unit) =\
    > @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u\
    } W r w) (@LeanIntent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w))\
    ) (fun («_» : Unit) => ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → Not (@LeanInt\
    ent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Answer.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (consequence : LeanIntent.Consequence.{u} W), ∀ (verdict : LeanIntent.\
    Verdict), LeanIntent.Answer.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W \
    → Prop), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.entailment\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.possibility\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Verdict\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Verdict.confirmed\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Verdict.declined\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.IntentRecord.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause\
    .{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanInte\
    nt.Pred.{u}), LeanIntent.IntentRecord.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Shape\n\
    | \n\
    | An inductive type. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type u → Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Shape.value\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.function\n\
    | \n\
    | ```lean\n\
    | ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.step\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.stepOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.action\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.actionOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u\
    } O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.bundle\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀\
    \x20(rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Member\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Member.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → \
    Out), LeanIntent.Member.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Clause.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Pred\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Pred.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.KeptBy.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : LeanIntent.Consequence.Kind → LeanIntent.Verdict → Sort u_1), ∀ (x : LeanInt\
    ent.Consequence.Kind), ∀ (x_1 : LeanIntent.Verdict), ∀ (h_1 : ∀ («_» : Unit), motive LeanI\
    ntent.Consequence.Kind.entailment LeanIntent.Verdict.confirmed), ∀ (h_2 : ∀ («_» : Unit), \
    motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.declined), ∀ (h_3 : ∀ («_\
    » : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdict.confirmed), ∀\
    \x20(h_4 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdi\
    ct.declined), motive x x_1\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : LeanIntent.Consequence.Kind → LeanIntent.Verdict → Sort u_1) => fun (x : L\
    eanIntent.Consequence.Kind) => fun (x_1 : LeanIntent.Verdict) => fun (h_1 : ∀ («_» : Unit)\
    , motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.confirmed) => fun (h_2 \
    : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.decline\
    d) => fun (h_3 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent\
    .Verdict.confirmed) => fun (h_4 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possi\
    bility LeanIntent.Verdict.declined) => @LeanIntent.Consequence.Kind.casesOn.{u_1} (fun (x_\
    2 : LeanIntent.Consequence.Kind) => motive x_2 x_1) x (@LeanIntent.Verdict.casesOn.{u_1} (\
    fun (x_2 : LeanIntent.Verdict) => motive LeanIntent.Consequence.Kind.entailment x_2) x_1 (\
    h_1 Unit.unit) (h_2 Unit.unit)) (@LeanIntent.Verdict.casesOn.{u_1} (fun (x_2 : LeanIntent.\
    Verdict) => motive LeanIntent.Consequence.Kind.possibility x_2) x_1 (h_3 Unit.unit) (h_4 U\
    nit.unit))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.\
    Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : mo\
    tive LeanIntent.Consequence.Kind.possibility), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Conseq\
    uence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (po\
    ssibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kin\
    d.rec.{u} motive entailment possibility t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Verdict.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Verdict), Sort u}, ∀ (t : LeanIntent.Verdict), ∀ (confirme\
    d : motive LeanIntent.Verdict.confirmed), ∀ (declined : motive LeanIntent.Verdict.declined\
    ), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Verdict), Sort u} => fun (t : LeanIntent.Verdict) => fun\
    \x20(confirmed : motive LeanIntent.Verdict.confirmed) => fun (declined : motive LeanIntent\
    .Verdict.declined) => @LeanIntent.Verdict.rec.{u} motive confirmed declined t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.kind\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.consequence\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 1, counted after the parameters in the type of LeanIntent.Ans\
    wer's constructor, of its argument number 2, a value of LeanIntent.Answer. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Answer.{u} W), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.verdict\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Ans\
    wer's constructor, of its argument number 2, a value of LeanIntent.Answer. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Answer.{u} W), LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Meets\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@Lean\
    Intent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Dom\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.dom\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Cla\
    use's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Props\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.props\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.HasInstance\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)\n\
    | ```\n\
    | \n\
    | ## Lean's own libraries\n\
    | \n\
    | The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: the\
    y are those of Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, which made th\
    is text. A declaration is counted as Lean's own when Lean found the module that declares i\
    t in that release's library directory.\n\
    | \n\
    verdict confirmed\n\
    ",
  "lean-intent statement 1\n\
    kind answer\n\
    project acorn\n\
    id day-3-r2\n\
    date 2026-11-03\n\
    reference docs/spec-first-pilot.md, The decisions made on the owner's behalf\n\
    by agents\n\
    under agents-below-intent\n\
    record AcornVerif.Intent.DayCycle.dayCycle\n\
    revision 610\n\
    | # The intent record @AcornVerif.Intent.DayCycle.dayCycleFor Unit Acorn.Host.Action UInt8\
    \x20Nat instLTNat\n\
    | \n\
    | Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term \
    its kernel checks, binder names and metadata aside, from the root namespace with nothing o\
    pened. The plain words after it are written by a model and are trusted, not proved.\n\
    | \n\
    | ## Shape\n\
    | \n\
    | ### The subject\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Shape.value.{0} (AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action U\
    Int8 Nat)\n\
    | ```\n\
    | \n\
    | - **Requires:** The subject is a description of a world's day: how many ticks a day last\
    s, which ticks are night, what each action costs at each tick in each situation, and what \
    the agent sees at each tick in each situation. Time is counted in whole ticks from the sta\
    rt of a run, and one clock serves the whole world.\n\
    | - **Rules out:** Nothing by itself; it fixes only what the statements below talk about.\
    \n\
    | - **Still allows:** Any world's situations, actions, sights and energy amounts.\n\
    | - **Freedom O5 leaves:** None of its own. It carries no state from one tick to the next,\
    \x20so it is declared a plain value, of which obligation O4 asks nothing.\n\
    | \n\
    | ## Domain hypotheses\n\
    | \n\
    | None.\n\
    | \n\
    | ## Properties\n\
    | \n\
    | ### each day has a daytime half and a night half of equal length\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => And (@\
    LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w)) (And (@Eq.{1\
    } Nat (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@AcornVerif.Inten\
    t.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) (@OfNat.ofNat.{0} Nat (nat_\
    lit 2) (instOfNatNat (nat_lit 2)))) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_l\
    it 0)))) (@Exists.{1} Nat (fun (start : Nat) => ∀ (t : Nat), Iff (@Eq.{1} Bool (@AcornVeri\
    f.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true) (AcornVe\
    rif.Intent.DayCycle.NightHalf (@AcornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host\
    .Action UInt8 Nat w) start t))))\n\
    | ```\n\
    | \n\
    | - **Requires:** A day lasts a fixed, even number of ticks, at least two. The night is on\
    e unbroken stretch of exactly half of them and the daytime the other half, and every day i\
    s the same.\n\
    | - **Rules out:** A world with no night or no daytime; a day of an odd number of ticks; a\
    \x20night broken into several stretches; days of different lengths.\n\
    | - **Still allows:** Any even day length, and a night that starts at any tick of the day.\
    \n\
    | - **Freedom O5 leaves:** How long a day is and where in it the night starts.\n\
    | \n\
    | ### at night every action costs more energy\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (c :\
    \x20Unit), ∀ (a : Acorn.Host.Action), ∀ (t : Nat), ∀ (t' : Nat), @Eq.{1} Bool (@AcornVerif\
    .Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true → @Eq.{1} \
    Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t') Bo\
    ol.false → @LT.lt.{0} Nat instLTNat (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.\
    Host.Action UInt8 Nat w t' c a) (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.Host\
    .Action UInt8 Nat w t c a)\n\
    | ```\n\
    | \n\
    | - **Requires:** For every action and every situation, the action costs strictly more ene\
    rgy at every night tick than at every daytime tick, waiting included.\n\
    | - **Rules out:** Any action that, in some situation, costs as much or less at some night\
    \x20tick than at some daytime tick.\n\
    | - **Still allows:** Any amount more at night, and a night cost that changes during the n\
    ight, as long as it stays above every daytime cost.\n\
    | - **Freedom O5 leaves:** How much more the night costs, and whether that extra changes d\
    uring the night.\n\
    | \n\
    | ### the agent can always tell day from night\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (t :\
    \x20Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @Eq.{1} UInt8 (@AcornVerif.Intent.Day\
    Cycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t c) (@AcornVerif.Intent.DayCycle.D\
    ayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') → @Eq.{1} Bool (@AcornVerif.Intent.\
    DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) (@AcornVerif.Intent.DayCycle\
    .DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t')\n\
    | ```\n\
    | \n\
    | - **Requires:** Whatever the agent sees always tells it whether it is day or night.\n\
    | - **Rules out:** An agent that sees a day moment and a night moment alike.\n\
    | - **Still allows:** An agent that sees more than that.\n\
    | - **Freedom O5 leaves:** How much more it sees.\n\
    | \n\
    | ### the agent can always see where in the day it is, at least to a quarter of the day\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Exist\
    s.{1} Nat (fun (start : Nat) => ∀ (t : Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @E\
    q.{1} UInt8 (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w \
    t c) (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') \
    → @Eq.{1} Nat (AcornVerif.Intent.DayCycle.quarter (@AcornVerif.Intent.DayCycle.DayWorld.le\
    ngth Unit Acorn.Host.Action UInt8 Nat w) start t) (AcornVerif.Intent.DayCycle.quarter (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) start t'))\n\
    | ```\n\
    | \n\
    | - **Requires:** Whatever the agent sees always tells it which quarter of the day it is i\
    n.\n\
    | - **Rules out:** An agent that sees only whether it is day or night, in a day longer tha\
    n two ticks.\n\
    | - **Still allows:** An agent that sees the quarter, a finer part of the day, or the exac\
    t tick.\n\
    | - **Freedom O5 leaves:** How much more finely than a quarter the agent sees the time of \
    day.\n\
    | \n\
    | ## Vocabulary\n\
    | \n\
    | ### night half, a predicate over `Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) => AcornVerif.Intent.DayCycle.NightHalf \
    (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat Nat) p) (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0}\
    \x20Nat (Prod.{0, 0} Nat Nat) p)) (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0\
    , 0} Nat Nat) p))\n\
    | ```\n\
    | \n\
    | - **Requires:** Tick t is in the night when, counted around a day of the given length fr\
    om where the night starts, it falls in the first half.\n\
    | - **Rules out:** Tick 1 in a day of two ticks whose night starts at tick 0.\n\
    | - **Still allows:** Tick 0 in that day.\n\
    | - **Freedom O5 leaves:** None: it is a definition.\n\
    | \n\
    | ### costs less, a predicate over `Prod.{0, 0} Nat Nat`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} Nat Nat) => @LT.lt.{0} Nat instLTNat (@Prod.fst.{0, 0} Nat Nat p) (\
    @Prod.snd.{0, 0} Nat Nat p)\n\
    | ```\n\
    | \n\
    | - **Requires:** The world's own order on energy amounts.\n\
    | - **Rules out:** Whatever that order rules out.\n\
    | - **Still allows:** Whatever that order allows.\n\
    | - **Freedom O5 leaves:** None of its own.\n\
    | \n\
    | ### in quarter, a predicate over `Prod.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)\
    )`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))) => @Eq.{1} Nat (AcornV\
    erif.Intent.DayCycle.quarter (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))\
    \x20p) (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat Nat) (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat \
    (Prod.{0, 0} Nat Nat)) p)) (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Na\
    t Nat) (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) p)))) (@Prod.snd.{0, \
    0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat Nat) (@Prod.snd.{0, 0} Nat (Prod.{0, 0} \
    Nat (Prod.{0, 0} Nat Nat)) p)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Tick t lies in the given quarter of a day of the given length, counted f\
    rom the given start.\n\
    | - **Rules out:** Tick 0 in quarter 1 of a day of four ticks counted from tick 0.\n\
    | - **Still allows:** Tick 0 in quarter 0 of that day.\n\
    | - **Freedom O5 leaves:** None: it is a definition.\n\
    | \n\
    | ## Consequences\n\
    | \n\
    | ### every day lasts the same even number of ticks, at least two, placed alike, an entail\
    ment: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => And (@\
    LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w)) (And (@Eq.{1\
    } Nat (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@AcornVerif.Inten\
    t.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) (@OfNat.ofNat.{0} Nat (nat_\
    lit 2) (instOfNatNat (nat_lit 2)))) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_l\
    it 0)))) (∀ (t : Nat), @Eq.{1} Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn\
    .Host.Action UInt8 Nat w (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) \
    t (@AcornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w))) (@Aco\
    rnVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Every day lasts the same even number of ticks, at least two, and each da\
    y's night falls at the same ticks of the day.\n\
    | - **Rules out:** Days of different lengths.\n\
    | - **Still allows:** Any one day length shared by all days.\n\
    | - **Freedom O5 leaves:** The length itself.\n\
    | \n\
    | ### every action costs more at any night moment than at any daytime moment, an entailmen\
    t: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (c :\
    \x20Unit), ∀ (a : Acorn.Host.Action), ∀ (t : Nat), ∀ (t' : Nat), @Eq.{1} Bool (@AcornVerif\
    .Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true → @Eq.{1} \
    Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t') Bo\
    ol.false → @LT.lt.{0} Nat instLTNat (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.\
    Host.Action UInt8 Nat w t' c a) (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.Host\
    .Action UInt8 Nat w t c a)\n\
    | ```\n\
    | \n\
    | - **Requires:** Even the cheapest action costs more at any night moment than at any dayt\
    ime moment, in the same situation.\n\
    | - **Rules out:** Any action that is no dearer at some night moment.\n\
    | - **Still allows:** Any extra amount.\n\
    | - **Freedom O5 leaves:** How much more.\n\
    | \n\
    | ### what the agent sees always tells day from night, an entailment: every subject that m\
    eets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (t :\
    \x20Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @Eq.{1} UInt8 (@AcornVerif.Intent.Day\
    Cycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t c) (@AcornVerif.Intent.DayCycle.D\
    ayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') → @Eq.{1} Bool (@AcornVerif.Intent.\
    DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) (@AcornVerif.Intent.DayCycle\
    .DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t')\n\
    | ```\n\
    | \n\
    | - **Requires:** From what it sees, the agent can always tell whether it is day or night.\
    \n\
    | - **Rules out:** An agent that cannot tell day from night at some moment.\n\
    | - **Still allows:** An agent that sees more than that.\n\
    | - **Freedom O5 leaves:** How much more it sees.\n\
    | \n\
    | ### what the agent sees always tells it which quarter of the day it is in, an entailment\
    : every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Exist\
    s.{1} Nat (fun (start : Nat) => ∀ (t : Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @E\
    q.{1} UInt8 (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w \
    t c) (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') \
    → @Eq.{1} Nat (AcornVerif.Intent.DayCycle.quarter (@AcornVerif.Intent.DayCycle.DayWorld.le\
    ngth Unit Acorn.Host.Action UInt8 Nat w) start t) (AcornVerif.Intent.DayCycle.quarter (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) start t'))\n\
    | ```\n\
    | \n\
    | - **Requires:** From what it sees, the agent can always tell which quarter of the day it\
    \x20is in.\n\
    | - **Rules out:** An agent that sees only day or night.\n\
    | - **Still allows:** Seeing a finer part of the day, or the exact tick.\n\
    | - **Freedom O5 leaves:** How much finer than a quarter.\n\
    | \n\
    | ### a day may last 1000 ticks, a possibility: some subject that meets the record satisfi\
    es it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Eq.{1\
    } Nat (@AcornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) (@O\
    fNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Nothing more: a world whose day lasts 1000 ticks can meet the record.\n\
    | - **Rules out:** Nothing.\n\
    | - **Still allows:** Short days and long days alike.\n\
    | - **Freedom O5 leaves:** The day's length.\n\
    | \n\
    | ### an action may cost more at one night moment than at another, a possibility: some sub\
    ject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Exist\
    s.{1} Unit (fun (c : Unit) => @Exists.{1} Acorn.Host.Action (fun (a : Acorn.Host.Action) =\
    > @Exists.{1} Nat (fun (t : Nat) => @Exists.{1} Nat (fun (t' : Nat) => And (@Eq.{1} Bool (\
    @AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true\
    ) (And (@Eq.{1} Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UI\
    nt8 Nat w t') Bool.true) (@Ne.{1} Nat (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acor\
    n.Host.Action UInt8 Nat w t c a) (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.Hos\
    t.Action UInt8 Nat w t' c a)))))))\n\
    | ```\n\
    | \n\
    | - **Requires:** Nothing more: an action may cost more at one night moment than at anothe\
    r, as long as every night cost is above every daytime cost.\n\
    | - **Rules out:** Nothing.\n\
    | - **Still allows:** A night that is dearer at midnight than at dusk.\n\
    | - **Freedom O5 leaves:** Whether the night's extra changes during the night.\n\
    | \n\
    | ## Definitions the record's meaning reaches\n\
    | \n\
    | These are not statements of the record: each is a declaration that a statement above dep\
    ends on, or that says what it is for a subject to meet the record and for a consequence to\
    \x20hold of it as shown, with everything those depend on in turn. Each is printed in full:\
    \x20its type, a definition's value, or for a definition by structural or well-founded recu\
    rsion the equation that determines it, and an inductive type's constructors, which for a s\
    tructure are its fields; a theorem's proof and an opaque constant's value are not, since n\
    o term that uses them depends on more than their types. Their plain words are those of the\
    \x20statements that use them.\n\
    | \n\
    | ### Acorn.Host.Action\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### Acorn.Host.Action.north\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.south\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.east\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.west\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.wait\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.harvest\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftAxe\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftBoat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.eat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Shape\n\
    | \n\
    | An inductive type. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type u → Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Shape.value\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.function\n\
    | \n\
    | ```lean\n\
    | ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.step\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.stepOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.action\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.actionOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u\
    } O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.bundle\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀\
    \x20(rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Member\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Member.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → \
    Out), LeanIntent.Member.{u} W\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (Ctx : Type), ∀ (Act : Type), ∀ (Obs : Type), ∀ (E : Type), Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 4 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.DayCycle.DayWorld.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (length : Nat), ∀ (night\
    \x20: Nat → Bool), ∀ (cost : Nat → Ctx → Act → E), ∀ (sees : Nat → Ctx → Obs), AcornVerif.\
    Intent.DayCycle.DayWorld Ctx Act Obs E\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.length\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 1, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.night\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 2, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Bool\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.NightHalf\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (length : Nat), ∀ (start : Nat), ∀ (t : Nat), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (length : Nat) => fun (start : Nat) => fun (t : Nat) => @LT.lt.{0} Nat instLTNat (@H\
    Mod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@HAdd.hAdd.{0, 0, 0} Nat N\
    at Nat (@instHAdd.{0} Nat instAddNat) t start) length) (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (\
    @instHDiv.{0} Nat Nat.instDiv) length (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat\
    _lit 2))))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.cost\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 3, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Ctx → Act → E\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.sees\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 4, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Ctx → Obs\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.quarter\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (length : Nat), ∀ (start : Nat), ∀ (t : Nat), Nat\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (length : Nat) => fun (start : Nat) => fun (t : Nat) => @HDiv.hDiv.{0, 0, 0} Nat Nat\
    \x20Nat (@instHDiv.{0} Nat Nat.instDiv) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} N\
    at instMulNat) (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@HAdd.hA\
    dd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t start) length) (@OfNat.ofNat.{0}\
    \x20Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) length\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Meets\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@Lean\
    Intent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.IntentRecord.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause\
    .{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanInte\
    nt.Pred.{u}), LeanIntent.IntentRecord.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Clause.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Pred\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Pred.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Dom\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.dom\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Cla\
    use's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Props\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.props\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.HoldsOf\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (c : LeanIntent.Consequence.{u} W), ∀ (r : LeanIntent.IntentRecord.{u}\
    \x20W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (c : LeanIntent.Consequence.{u} W) => fun (r : LeanIntent.Intent\
    Record.{u} W) => LeanIntent.Consequence.HoldsOf.match_1.{1} (fun (x : LeanIntent.Consequen\
    ce.Kind) => Prop) (@LeanIntent.Consequence.kind.{u} W c) (fun («_» : Unit) => ∀ (w : W), @\
    LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W c w) (fun («\
    _» : Unit) => @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRec\
    ord.Meets.{u} W r w) (@LeanIntent.Consequence.holds.{u} W c w)))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W \
    → Prop), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.entailment\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.possibility\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.HoldsOf.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : LeanIntent.Consequence.Kind → Sort u_1), ∀ (x : LeanIntent.Consequence.Kind)\
    , ∀ (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment), ∀ (h_2 : ∀ («_»\
    \x20: Unit), motive LeanIntent.Consequence.Kind.possibility), motive x\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : LeanIntent.Consequence.Kind → Sort u_1) => fun (x : LeanIntent.Consequence\
    .Kind) => fun (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment) => fun\
    \x20(h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.\
    Consequence.Kind.casesOn.{u_1} (fun (x_1 : LeanIntent.Consequence.Kind) => motive x_1) x (\
    h_1 Unit.unit) (h_2 Unit.unit)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.\
    Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : mo\
    tive LeanIntent.Consequence.Kind.possibility), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Conseq\
    uence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (po\
    ssibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kin\
    d.rec.{u} motive entailment possibility t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.kind\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.HasInstance\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)\n\
    | ```\n\
    | \n\
    | ## Lean's own libraries\n\
    | \n\
    | The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: the\
    y are those of Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, which made th\
    is text. A declaration is counted as Lean's own when Lean found the module that declares i\
    t in that release's library directory.\n\
    | \n\
    consequence what the agent sees always tells day from night\n\
    shown as entailment\n\
    predicate 472\n\
    | # A consequence's predicate\n\
    | \n\
    | Printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks,\
    \x20binder names and metadata aside, from the root namespace with nothing opened.\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (t :\
    \x20Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @Eq.{1} UInt8 (@AcornVerif.Intent.Day\
    Cycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t c) (@AcornVerif.Intent.DayCycle.D\
    ayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') → @Eq.{1} Bool (@AcornVerif.Intent.\
    DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) (@AcornVerif.Intent.DayCycle\
    .DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t')\n\
    | ```\n\
    | \n\
    | ## Definitions the predicate reaches\n\
    | \n\
    | Each is printed in full, as in the rendering of a record, with what an answer to it asks\
    \x20of every later revision (`LeanIntent.Answer.KeptBy`).\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (Ctx : Type), ∀ (Act : Type), ∀ (Obs : Type), ∀ (E : Type), Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 4 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.DayCycle.DayWorld.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (length : Nat), ∀ (night\
    \x20: Nat → Bool), ∀ (cost : Nat → Ctx → Act → E), ∀ (sees : Nat → Ctx → Obs), AcornVerif.\
    Intent.DayCycle.DayWorld Ctx Act Obs E\n\
    | ```\n\
    | \n\
    | ### Acorn.Host.Action\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### Acorn.Host.Action.north\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.south\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.east\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.west\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.wait\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.harvest\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftAxe\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftBoat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.eat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.sees\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 4, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Ctx → Obs\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.night\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 2, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Bool\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.KeptBy\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (a : LeanIntent.Answer.{u} W), ∀ (r : LeanIntent.IntentRecord.{u} W), \
    Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (a : LeanIntent.Answer.{u} W) => fun (r : LeanIntent.IntentRecor\
    d.{u} W) => LeanIntent.Answer.KeptBy.match_1.{1} (fun (x : LeanIntent.Consequence.Kind) =>\
    \x20fun (x_1 : LeanIntent.Verdict) => Prop) (@LeanIntent.Consequence.kind.{u} W (@LeanInte\
    nt.Answer.consequence.{u} W a)) (@LeanIntent.Answer.verdict.{u} W a) (fun («_» : Unit) => \
    ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W \
    (@LeanIntent.Answer.consequence.{u} W a) w) (fun («_» : Unit) => @LeanIntent.HasInstance.{\
    u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u} W r w) (Not (@LeanIntent.\
    Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w)))) (fun («_» : Unit) =\
    > @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u\
    } W r w) (@LeanIntent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w))\
    ) (fun («_» : Unit) => ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → Not (@LeanInt\
    ent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Answer.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (consequence : LeanIntent.Consequence.{u} W), ∀ (verdict : LeanIntent.\
    Verdict), LeanIntent.Answer.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W \
    → Prop), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.entailment\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.possibility\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Verdict\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Verdict.confirmed\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Verdict.declined\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.IntentRecord.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause\
    .{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanInte\
    nt.Pred.{u}), LeanIntent.IntentRecord.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Shape\n\
    | \n\
    | An inductive type. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type u → Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Shape.value\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.function\n\
    | \n\
    | ```lean\n\
    | ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.step\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.stepOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.action\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.actionOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u\
    } O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.bundle\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀\
    \x20(rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Member\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Member.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → \
    Out), LeanIntent.Member.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Clause.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Pred\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Pred.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.KeptBy.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : LeanIntent.Consequence.Kind → LeanIntent.Verdict → Sort u_1), ∀ (x : LeanInt\
    ent.Consequence.Kind), ∀ (x_1 : LeanIntent.Verdict), ∀ (h_1 : ∀ («_» : Unit), motive LeanI\
    ntent.Consequence.Kind.entailment LeanIntent.Verdict.confirmed), ∀ (h_2 : ∀ («_» : Unit), \
    motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.declined), ∀ (h_3 : ∀ («_\
    » : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdict.confirmed), ∀\
    \x20(h_4 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdi\
    ct.declined), motive x x_1\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : LeanIntent.Consequence.Kind → LeanIntent.Verdict → Sort u_1) => fun (x : L\
    eanIntent.Consequence.Kind) => fun (x_1 : LeanIntent.Verdict) => fun (h_1 : ∀ («_» : Unit)\
    , motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.confirmed) => fun (h_2 \
    : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.decline\
    d) => fun (h_3 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent\
    .Verdict.confirmed) => fun (h_4 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possi\
    bility LeanIntent.Verdict.declined) => @LeanIntent.Consequence.Kind.casesOn.{u_1} (fun (x_\
    2 : LeanIntent.Consequence.Kind) => motive x_2 x_1) x (@LeanIntent.Verdict.casesOn.{u_1} (\
    fun (x_2 : LeanIntent.Verdict) => motive LeanIntent.Consequence.Kind.entailment x_2) x_1 (\
    h_1 Unit.unit) (h_2 Unit.unit)) (@LeanIntent.Verdict.casesOn.{u_1} (fun (x_2 : LeanIntent.\
    Verdict) => motive LeanIntent.Consequence.Kind.possibility x_2) x_1 (h_3 Unit.unit) (h_4 U\
    nit.unit))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.\
    Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : mo\
    tive LeanIntent.Consequence.Kind.possibility), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Conseq\
    uence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (po\
    ssibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kin\
    d.rec.{u} motive entailment possibility t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Verdict.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Verdict), Sort u}, ∀ (t : LeanIntent.Verdict), ∀ (confirme\
    d : motive LeanIntent.Verdict.confirmed), ∀ (declined : motive LeanIntent.Verdict.declined\
    ), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Verdict), Sort u} => fun (t : LeanIntent.Verdict) => fun\
    \x20(confirmed : motive LeanIntent.Verdict.confirmed) => fun (declined : motive LeanIntent\
    .Verdict.declined) => @LeanIntent.Verdict.rec.{u} motive confirmed declined t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.kind\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.consequence\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 1, counted after the parameters in the type of LeanIntent.Ans\
    wer's constructor, of its argument number 2, a value of LeanIntent.Answer. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Answer.{u} W), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.verdict\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Ans\
    wer's constructor, of its argument number 2, a value of LeanIntent.Answer. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Answer.{u} W), LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Meets\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@Lean\
    Intent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Dom\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.dom\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Cla\
    use's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Props\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.props\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.HasInstance\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)\n\
    | ```\n\
    | \n\
    | ## Lean's own libraries\n\
    | \n\
    | The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: the\
    y are those of Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, which made th\
    is text. A declaration is counted as Lean's own when Lean found the module that declares i\
    t in that release's library directory.\n\
    | \n\
    verdict confirmed\n\
    ",
  "lean-intent statement 1\n\
    kind answer\n\
    project acorn\n\
    id day-4-r2\n\
    date 2026-11-03\n\
    reference docs/spec-first-pilot.md, The decisions made on the owner's behalf\n\
    by agents\n\
    under agents-below-intent\n\
    record AcornVerif.Intent.DayCycle.dayCycle\n\
    revision 610\n\
    | # The intent record @AcornVerif.Intent.DayCycle.dayCycleFor Unit Acorn.Host.Action UInt8\
    \x20Nat instLTNat\n\
    | \n\
    | Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term \
    its kernel checks, binder names and metadata aside, from the root namespace with nothing o\
    pened. The plain words after it are written by a model and are trusted, not proved.\n\
    | \n\
    | ## Shape\n\
    | \n\
    | ### The subject\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Shape.value.{0} (AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action U\
    Int8 Nat)\n\
    | ```\n\
    | \n\
    | - **Requires:** The subject is a description of a world's day: how many ticks a day last\
    s, which ticks are night, what each action costs at each tick in each situation, and what \
    the agent sees at each tick in each situation. Time is counted in whole ticks from the sta\
    rt of a run, and one clock serves the whole world.\n\
    | - **Rules out:** Nothing by itself; it fixes only what the statements below talk about.\
    \n\
    | - **Still allows:** Any world's situations, actions, sights and energy amounts.\n\
    | - **Freedom O5 leaves:** None of its own. It carries no state from one tick to the next,\
    \x20so it is declared a plain value, of which obligation O4 asks nothing.\n\
    | \n\
    | ## Domain hypotheses\n\
    | \n\
    | None.\n\
    | \n\
    | ## Properties\n\
    | \n\
    | ### each day has a daytime half and a night half of equal length\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => And (@\
    LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w)) (And (@Eq.{1\
    } Nat (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@AcornVerif.Inten\
    t.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) (@OfNat.ofNat.{0} Nat (nat_\
    lit 2) (instOfNatNat (nat_lit 2)))) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_l\
    it 0)))) (@Exists.{1} Nat (fun (start : Nat) => ∀ (t : Nat), Iff (@Eq.{1} Bool (@AcornVeri\
    f.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true) (AcornVe\
    rif.Intent.DayCycle.NightHalf (@AcornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host\
    .Action UInt8 Nat w) start t))))\n\
    | ```\n\
    | \n\
    | - **Requires:** A day lasts a fixed, even number of ticks, at least two. The night is on\
    e unbroken stretch of exactly half of them and the daytime the other half, and every day i\
    s the same.\n\
    | - **Rules out:** A world with no night or no daytime; a day of an odd number of ticks; a\
    \x20night broken into several stretches; days of different lengths.\n\
    | - **Still allows:** Any even day length, and a night that starts at any tick of the day.\
    \n\
    | - **Freedom O5 leaves:** How long a day is and where in it the night starts.\n\
    | \n\
    | ### at night every action costs more energy\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (c :\
    \x20Unit), ∀ (a : Acorn.Host.Action), ∀ (t : Nat), ∀ (t' : Nat), @Eq.{1} Bool (@AcornVerif\
    .Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true → @Eq.{1} \
    Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t') Bo\
    ol.false → @LT.lt.{0} Nat instLTNat (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.\
    Host.Action UInt8 Nat w t' c a) (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.Host\
    .Action UInt8 Nat w t c a)\n\
    | ```\n\
    | \n\
    | - **Requires:** For every action and every situation, the action costs strictly more ene\
    rgy at every night tick than at every daytime tick, waiting included.\n\
    | - **Rules out:** Any action that, in some situation, costs as much or less at some night\
    \x20tick than at some daytime tick.\n\
    | - **Still allows:** Any amount more at night, and a night cost that changes during the n\
    ight, as long as it stays above every daytime cost.\n\
    | - **Freedom O5 leaves:** How much more the night costs, and whether that extra changes d\
    uring the night.\n\
    | \n\
    | ### the agent can always tell day from night\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (t :\
    \x20Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @Eq.{1} UInt8 (@AcornVerif.Intent.Day\
    Cycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t c) (@AcornVerif.Intent.DayCycle.D\
    ayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') → @Eq.{1} Bool (@AcornVerif.Intent.\
    DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) (@AcornVerif.Intent.DayCycle\
    .DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t')\n\
    | ```\n\
    | \n\
    | - **Requires:** Whatever the agent sees always tells it whether it is day or night.\n\
    | - **Rules out:** An agent that sees a day moment and a night moment alike.\n\
    | - **Still allows:** An agent that sees more than that.\n\
    | - **Freedom O5 leaves:** How much more it sees.\n\
    | \n\
    | ### the agent can always see where in the day it is, at least to a quarter of the day\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Exist\
    s.{1} Nat (fun (start : Nat) => ∀ (t : Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @E\
    q.{1} UInt8 (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w \
    t c) (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') \
    → @Eq.{1} Nat (AcornVerif.Intent.DayCycle.quarter (@AcornVerif.Intent.DayCycle.DayWorld.le\
    ngth Unit Acorn.Host.Action UInt8 Nat w) start t) (AcornVerif.Intent.DayCycle.quarter (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) start t'))\n\
    | ```\n\
    | \n\
    | - **Requires:** Whatever the agent sees always tells it which quarter of the day it is i\
    n.\n\
    | - **Rules out:** An agent that sees only whether it is day or night, in a day longer tha\
    n two ticks.\n\
    | - **Still allows:** An agent that sees the quarter, a finer part of the day, or the exac\
    t tick.\n\
    | - **Freedom O5 leaves:** How much more finely than a quarter the agent sees the time of \
    day.\n\
    | \n\
    | ## Vocabulary\n\
    | \n\
    | ### night half, a predicate over `Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) => AcornVerif.Intent.DayCycle.NightHalf \
    (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat Nat) p) (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0}\
    \x20Nat (Prod.{0, 0} Nat Nat) p)) (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0\
    , 0} Nat Nat) p))\n\
    | ```\n\
    | \n\
    | - **Requires:** Tick t is in the night when, counted around a day of the given length fr\
    om where the night starts, it falls in the first half.\n\
    | - **Rules out:** Tick 1 in a day of two ticks whose night starts at tick 0.\n\
    | - **Still allows:** Tick 0 in that day.\n\
    | - **Freedom O5 leaves:** None: it is a definition.\n\
    | \n\
    | ### costs less, a predicate over `Prod.{0, 0} Nat Nat`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} Nat Nat) => @LT.lt.{0} Nat instLTNat (@Prod.fst.{0, 0} Nat Nat p) (\
    @Prod.snd.{0, 0} Nat Nat p)\n\
    | ```\n\
    | \n\
    | - **Requires:** The world's own order on energy amounts.\n\
    | - **Rules out:** Whatever that order rules out.\n\
    | - **Still allows:** Whatever that order allows.\n\
    | - **Freedom O5 leaves:** None of its own.\n\
    | \n\
    | ### in quarter, a predicate over `Prod.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)\
    )`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))) => @Eq.{1} Nat (AcornV\
    erif.Intent.DayCycle.quarter (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))\
    \x20p) (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat Nat) (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat \
    (Prod.{0, 0} Nat Nat)) p)) (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Na\
    t Nat) (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) p)))) (@Prod.snd.{0, \
    0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat Nat) (@Prod.snd.{0, 0} Nat (Prod.{0, 0} \
    Nat (Prod.{0, 0} Nat Nat)) p)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Tick t lies in the given quarter of a day of the given length, counted f\
    rom the given start.\n\
    | - **Rules out:** Tick 0 in quarter 1 of a day of four ticks counted from tick 0.\n\
    | - **Still allows:** Tick 0 in quarter 0 of that day.\n\
    | - **Freedom O5 leaves:** None: it is a definition.\n\
    | \n\
    | ## Consequences\n\
    | \n\
    | ### every day lasts the same even number of ticks, at least two, placed alike, an entail\
    ment: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => And (@\
    LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w)) (And (@Eq.{1\
    } Nat (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@AcornVerif.Inten\
    t.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) (@OfNat.ofNat.{0} Nat (nat_\
    lit 2) (instOfNatNat (nat_lit 2)))) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_l\
    it 0)))) (∀ (t : Nat), @Eq.{1} Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn\
    .Host.Action UInt8 Nat w (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) \
    t (@AcornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w))) (@Aco\
    rnVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Every day lasts the same even number of ticks, at least two, and each da\
    y's night falls at the same ticks of the day.\n\
    | - **Rules out:** Days of different lengths.\n\
    | - **Still allows:** Any one day length shared by all days.\n\
    | - **Freedom O5 leaves:** The length itself.\n\
    | \n\
    | ### every action costs more at any night moment than at any daytime moment, an entailmen\
    t: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (c :\
    \x20Unit), ∀ (a : Acorn.Host.Action), ∀ (t : Nat), ∀ (t' : Nat), @Eq.{1} Bool (@AcornVerif\
    .Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true → @Eq.{1} \
    Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t') Bo\
    ol.false → @LT.lt.{0} Nat instLTNat (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.\
    Host.Action UInt8 Nat w t' c a) (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.Host\
    .Action UInt8 Nat w t c a)\n\
    | ```\n\
    | \n\
    | - **Requires:** Even the cheapest action costs more at any night moment than at any dayt\
    ime moment, in the same situation.\n\
    | - **Rules out:** Any action that is no dearer at some night moment.\n\
    | - **Still allows:** Any extra amount.\n\
    | - **Freedom O5 leaves:** How much more.\n\
    | \n\
    | ### what the agent sees always tells day from night, an entailment: every subject that m\
    eets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (t :\
    \x20Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @Eq.{1} UInt8 (@AcornVerif.Intent.Day\
    Cycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t c) (@AcornVerif.Intent.DayCycle.D\
    ayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') → @Eq.{1} Bool (@AcornVerif.Intent.\
    DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) (@AcornVerif.Intent.DayCycle\
    .DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t')\n\
    | ```\n\
    | \n\
    | - **Requires:** From what it sees, the agent can always tell whether it is day or night.\
    \n\
    | - **Rules out:** An agent that cannot tell day from night at some moment.\n\
    | - **Still allows:** An agent that sees more than that.\n\
    | - **Freedom O5 leaves:** How much more it sees.\n\
    | \n\
    | ### what the agent sees always tells it which quarter of the day it is in, an entailment\
    : every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Exist\
    s.{1} Nat (fun (start : Nat) => ∀ (t : Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @E\
    q.{1} UInt8 (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w \
    t c) (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') \
    → @Eq.{1} Nat (AcornVerif.Intent.DayCycle.quarter (@AcornVerif.Intent.DayCycle.DayWorld.le\
    ngth Unit Acorn.Host.Action UInt8 Nat w) start t) (AcornVerif.Intent.DayCycle.quarter (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) start t'))\n\
    | ```\n\
    | \n\
    | - **Requires:** From what it sees, the agent can always tell which quarter of the day it\
    \x20is in.\n\
    | - **Rules out:** An agent that sees only day or night.\n\
    | - **Still allows:** Seeing a finer part of the day, or the exact tick.\n\
    | - **Freedom O5 leaves:** How much finer than a quarter.\n\
    | \n\
    | ### a day may last 1000 ticks, a possibility: some subject that meets the record satisfi\
    es it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Eq.{1\
    } Nat (@AcornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) (@O\
    fNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Nothing more: a world whose day lasts 1000 ticks can meet the record.\n\
    | - **Rules out:** Nothing.\n\
    | - **Still allows:** Short days and long days alike.\n\
    | - **Freedom O5 leaves:** The day's length.\n\
    | \n\
    | ### an action may cost more at one night moment than at another, a possibility: some sub\
    ject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Exist\
    s.{1} Unit (fun (c : Unit) => @Exists.{1} Acorn.Host.Action (fun (a : Acorn.Host.Action) =\
    > @Exists.{1} Nat (fun (t : Nat) => @Exists.{1} Nat (fun (t' : Nat) => And (@Eq.{1} Bool (\
    @AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true\
    ) (And (@Eq.{1} Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UI\
    nt8 Nat w t') Bool.true) (@Ne.{1} Nat (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acor\
    n.Host.Action UInt8 Nat w t c a) (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.Hos\
    t.Action UInt8 Nat w t' c a)))))))\n\
    | ```\n\
    | \n\
    | - **Requires:** Nothing more: an action may cost more at one night moment than at anothe\
    r, as long as every night cost is above every daytime cost.\n\
    | - **Rules out:** Nothing.\n\
    | - **Still allows:** A night that is dearer at midnight than at dusk.\n\
    | - **Freedom O5 leaves:** Whether the night's extra changes during the night.\n\
    | \n\
    | ## Definitions the record's meaning reaches\n\
    | \n\
    | These are not statements of the record: each is a declaration that a statement above dep\
    ends on, or that says what it is for a subject to meet the record and for a consequence to\
    \x20hold of it as shown, with everything those depend on in turn. Each is printed in full:\
    \x20its type, a definition's value, or for a definition by structural or well-founded recu\
    rsion the equation that determines it, and an inductive type's constructors, which for a s\
    tructure are its fields; a theorem's proof and an opaque constant's value are not, since n\
    o term that uses them depends on more than their types. Their plain words are those of the\
    \x20statements that use them.\n\
    | \n\
    | ### Acorn.Host.Action\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### Acorn.Host.Action.north\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.south\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.east\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.west\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.wait\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.harvest\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftAxe\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftBoat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.eat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Shape\n\
    | \n\
    | An inductive type. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type u → Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Shape.value\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.function\n\
    | \n\
    | ```lean\n\
    | ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.step\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.stepOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.action\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.actionOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u\
    } O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.bundle\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀\
    \x20(rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Member\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Member.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → \
    Out), LeanIntent.Member.{u} W\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (Ctx : Type), ∀ (Act : Type), ∀ (Obs : Type), ∀ (E : Type), Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 4 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.DayCycle.DayWorld.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (length : Nat), ∀ (night\
    \x20: Nat → Bool), ∀ (cost : Nat → Ctx → Act → E), ∀ (sees : Nat → Ctx → Obs), AcornVerif.\
    Intent.DayCycle.DayWorld Ctx Act Obs E\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.length\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 1, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.night\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 2, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Bool\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.NightHalf\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (length : Nat), ∀ (start : Nat), ∀ (t : Nat), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (length : Nat) => fun (start : Nat) => fun (t : Nat) => @LT.lt.{0} Nat instLTNat (@H\
    Mod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@HAdd.hAdd.{0, 0, 0} Nat N\
    at Nat (@instHAdd.{0} Nat instAddNat) t start) length) (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (\
    @instHDiv.{0} Nat Nat.instDiv) length (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat\
    _lit 2))))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.cost\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 3, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Ctx → Act → E\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.sees\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 4, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Ctx → Obs\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.quarter\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (length : Nat), ∀ (start : Nat), ∀ (t : Nat), Nat\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (length : Nat) => fun (start : Nat) => fun (t : Nat) => @HDiv.hDiv.{0, 0, 0} Nat Nat\
    \x20Nat (@instHDiv.{0} Nat Nat.instDiv) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} N\
    at instMulNat) (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@HAdd.hA\
    dd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t start) length) (@OfNat.ofNat.{0}\
    \x20Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) length\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Meets\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@Lean\
    Intent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.IntentRecord.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause\
    .{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanInte\
    nt.Pred.{u}), LeanIntent.IntentRecord.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Clause.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Pred\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Pred.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Dom\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.dom\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Cla\
    use's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Props\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.props\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.HoldsOf\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (c : LeanIntent.Consequence.{u} W), ∀ (r : LeanIntent.IntentRecord.{u}\
    \x20W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (c : LeanIntent.Consequence.{u} W) => fun (r : LeanIntent.Intent\
    Record.{u} W) => LeanIntent.Consequence.HoldsOf.match_1.{1} (fun (x : LeanIntent.Consequen\
    ce.Kind) => Prop) (@LeanIntent.Consequence.kind.{u} W c) (fun («_» : Unit) => ∀ (w : W), @\
    LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W c w) (fun («\
    _» : Unit) => @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRec\
    ord.Meets.{u} W r w) (@LeanIntent.Consequence.holds.{u} W c w)))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W \
    → Prop), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.entailment\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.possibility\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.HoldsOf.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : LeanIntent.Consequence.Kind → Sort u_1), ∀ (x : LeanIntent.Consequence.Kind)\
    , ∀ (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment), ∀ (h_2 : ∀ («_»\
    \x20: Unit), motive LeanIntent.Consequence.Kind.possibility), motive x\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : LeanIntent.Consequence.Kind → Sort u_1) => fun (x : LeanIntent.Consequence\
    .Kind) => fun (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment) => fun\
    \x20(h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.\
    Consequence.Kind.casesOn.{u_1} (fun (x_1 : LeanIntent.Consequence.Kind) => motive x_1) x (\
    h_1 Unit.unit) (h_2 Unit.unit)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.\
    Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : mo\
    tive LeanIntent.Consequence.Kind.possibility), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Conseq\
    uence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (po\
    ssibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kin\
    d.rec.{u} motive entailment possibility t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.kind\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.HasInstance\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)\n\
    | ```\n\
    | \n\
    | ## Lean's own libraries\n\
    | \n\
    | The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: the\
    y are those of Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, which made th\
    is text. A declaration is counted as Lean's own when Lean found the module that declares i\
    t in that release's library directory.\n\
    | \n\
    consequence a day may last 1000 ticks\n\
    shown as possibility\n\
    predicate 464\n\
    | # A consequence's predicate\n\
    | \n\
    | Printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks,\
    \x20binder names and metadata aside, from the root namespace with nothing opened.\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Eq.{1\
    } Nat (@AcornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) (@O\
    fNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))\n\
    | ```\n\
    | \n\
    | ## Definitions the predicate reaches\n\
    | \n\
    | Each is printed in full, as in the rendering of a record, with what an answer to it asks\
    \x20of every later revision (`LeanIntent.Answer.KeptBy`).\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (Ctx : Type), ∀ (Act : Type), ∀ (Obs : Type), ∀ (E : Type), Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 4 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.DayCycle.DayWorld.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (length : Nat), ∀ (night\
    \x20: Nat → Bool), ∀ (cost : Nat → Ctx → Act → E), ∀ (sees : Nat → Ctx → Obs), AcornVerif.\
    Intent.DayCycle.DayWorld Ctx Act Obs E\n\
    | ```\n\
    | \n\
    | ### Acorn.Host.Action\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### Acorn.Host.Action.north\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.south\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.east\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.west\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.wait\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.harvest\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftAxe\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftBoat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.eat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.length\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 1, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.KeptBy\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (a : LeanIntent.Answer.{u} W), ∀ (r : LeanIntent.IntentRecord.{u} W), \
    Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (a : LeanIntent.Answer.{u} W) => fun (r : LeanIntent.IntentRecor\
    d.{u} W) => LeanIntent.Answer.KeptBy.match_1.{1} (fun (x : LeanIntent.Consequence.Kind) =>\
    \x20fun (x_1 : LeanIntent.Verdict) => Prop) (@LeanIntent.Consequence.kind.{u} W (@LeanInte\
    nt.Answer.consequence.{u} W a)) (@LeanIntent.Answer.verdict.{u} W a) (fun («_» : Unit) => \
    ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W \
    (@LeanIntent.Answer.consequence.{u} W a) w) (fun («_» : Unit) => @LeanIntent.HasInstance.{\
    u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u} W r w) (Not (@LeanIntent.\
    Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w)))) (fun («_» : Unit) =\
    > @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u\
    } W r w) (@LeanIntent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w))\
    ) (fun («_» : Unit) => ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → Not (@LeanInt\
    ent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Answer.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (consequence : LeanIntent.Consequence.{u} W), ∀ (verdict : LeanIntent.\
    Verdict), LeanIntent.Answer.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W \
    → Prop), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.entailment\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.possibility\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Verdict\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Verdict.confirmed\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Verdict.declined\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.IntentRecord.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause\
    .{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanInte\
    nt.Pred.{u}), LeanIntent.IntentRecord.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Shape\n\
    | \n\
    | An inductive type. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type u → Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Shape.value\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.function\n\
    | \n\
    | ```lean\n\
    | ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.step\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.stepOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.action\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.actionOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u\
    } O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.bundle\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀\
    \x20(rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Member\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Member.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → \
    Out), LeanIntent.Member.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Clause.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Pred\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Pred.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.KeptBy.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : LeanIntent.Consequence.Kind → LeanIntent.Verdict → Sort u_1), ∀ (x : LeanInt\
    ent.Consequence.Kind), ∀ (x_1 : LeanIntent.Verdict), ∀ (h_1 : ∀ («_» : Unit), motive LeanI\
    ntent.Consequence.Kind.entailment LeanIntent.Verdict.confirmed), ∀ (h_2 : ∀ («_» : Unit), \
    motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.declined), ∀ (h_3 : ∀ («_\
    » : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdict.confirmed), ∀\
    \x20(h_4 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdi\
    ct.declined), motive x x_1\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : LeanIntent.Consequence.Kind → LeanIntent.Verdict → Sort u_1) => fun (x : L\
    eanIntent.Consequence.Kind) => fun (x_1 : LeanIntent.Verdict) => fun (h_1 : ∀ («_» : Unit)\
    , motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.confirmed) => fun (h_2 \
    : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.decline\
    d) => fun (h_3 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent\
    .Verdict.confirmed) => fun (h_4 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possi\
    bility LeanIntent.Verdict.declined) => @LeanIntent.Consequence.Kind.casesOn.{u_1} (fun (x_\
    2 : LeanIntent.Consequence.Kind) => motive x_2 x_1) x (@LeanIntent.Verdict.casesOn.{u_1} (\
    fun (x_2 : LeanIntent.Verdict) => motive LeanIntent.Consequence.Kind.entailment x_2) x_1 (\
    h_1 Unit.unit) (h_2 Unit.unit)) (@LeanIntent.Verdict.casesOn.{u_1} (fun (x_2 : LeanIntent.\
    Verdict) => motive LeanIntent.Consequence.Kind.possibility x_2) x_1 (h_3 Unit.unit) (h_4 U\
    nit.unit))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.\
    Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : mo\
    tive LeanIntent.Consequence.Kind.possibility), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Conseq\
    uence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (po\
    ssibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kin\
    d.rec.{u} motive entailment possibility t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Verdict.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Verdict), Sort u}, ∀ (t : LeanIntent.Verdict), ∀ (confirme\
    d : motive LeanIntent.Verdict.confirmed), ∀ (declined : motive LeanIntent.Verdict.declined\
    ), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Verdict), Sort u} => fun (t : LeanIntent.Verdict) => fun\
    \x20(confirmed : motive LeanIntent.Verdict.confirmed) => fun (declined : motive LeanIntent\
    .Verdict.declined) => @LeanIntent.Verdict.rec.{u} motive confirmed declined t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.kind\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.consequence\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 1, counted after the parameters in the type of LeanIntent.Ans\
    wer's constructor, of its argument number 2, a value of LeanIntent.Answer. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Answer.{u} W), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.verdict\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Ans\
    wer's constructor, of its argument number 2, a value of LeanIntent.Answer. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Answer.{u} W), LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Meets\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@Lean\
    Intent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Dom\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.dom\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Cla\
    use's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Props\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.props\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.HasInstance\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)\n\
    | ```\n\
    | \n\
    | ## Lean's own libraries\n\
    | \n\
    | The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: the\
    y are those of Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, which made th\
    is text. A declaration is counted as Lean's own when Lean found the module that declares i\
    t in that release's library directory.\n\
    | \n\
    verdict confirmed\n\
    ",
  "lean-intent statement 1\n\
    kind answer\n\
    project acorn\n\
    id day-5a-r2\n\
    date 2026-11-03\n\
    reference docs/spec-first-pilot.md, The decisions made on the owner's behalf\n\
    by agents\n\
    under agents-below-intent\n\
    record AcornVerif.Intent.DayCycle.dayCycle\n\
    revision 610\n\
    | # The intent record @AcornVerif.Intent.DayCycle.dayCycleFor Unit Acorn.Host.Action UInt8\
    \x20Nat instLTNat\n\
    | \n\
    | Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term \
    its kernel checks, binder names and metadata aside, from the root namespace with nothing o\
    pened. The plain words after it are written by a model and are trusted, not proved.\n\
    | \n\
    | ## Shape\n\
    | \n\
    | ### The subject\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Shape.value.{0} (AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action U\
    Int8 Nat)\n\
    | ```\n\
    | \n\
    | - **Requires:** The subject is a description of a world's day: how many ticks a day last\
    s, which ticks are night, what each action costs at each tick in each situation, and what \
    the agent sees at each tick in each situation. Time is counted in whole ticks from the sta\
    rt of a run, and one clock serves the whole world.\n\
    | - **Rules out:** Nothing by itself; it fixes only what the statements below talk about.\
    \n\
    | - **Still allows:** Any world's situations, actions, sights and energy amounts.\n\
    | - **Freedom O5 leaves:** None of its own. It carries no state from one tick to the next,\
    \x20so it is declared a plain value, of which obligation O4 asks nothing.\n\
    | \n\
    | ## Domain hypotheses\n\
    | \n\
    | None.\n\
    | \n\
    | ## Properties\n\
    | \n\
    | ### each day has a daytime half and a night half of equal length\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => And (@\
    LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w)) (And (@Eq.{1\
    } Nat (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@AcornVerif.Inten\
    t.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) (@OfNat.ofNat.{0} Nat (nat_\
    lit 2) (instOfNatNat (nat_lit 2)))) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_l\
    it 0)))) (@Exists.{1} Nat (fun (start : Nat) => ∀ (t : Nat), Iff (@Eq.{1} Bool (@AcornVeri\
    f.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true) (AcornVe\
    rif.Intent.DayCycle.NightHalf (@AcornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host\
    .Action UInt8 Nat w) start t))))\n\
    | ```\n\
    | \n\
    | - **Requires:** A day lasts a fixed, even number of ticks, at least two. The night is on\
    e unbroken stretch of exactly half of them and the daytime the other half, and every day i\
    s the same.\n\
    | - **Rules out:** A world with no night or no daytime; a day of an odd number of ticks; a\
    \x20night broken into several stretches; days of different lengths.\n\
    | - **Still allows:** Any even day length, and a night that starts at any tick of the day.\
    \n\
    | - **Freedom O5 leaves:** How long a day is and where in it the night starts.\n\
    | \n\
    | ### at night every action costs more energy\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (c :\
    \x20Unit), ∀ (a : Acorn.Host.Action), ∀ (t : Nat), ∀ (t' : Nat), @Eq.{1} Bool (@AcornVerif\
    .Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true → @Eq.{1} \
    Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t') Bo\
    ol.false → @LT.lt.{0} Nat instLTNat (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.\
    Host.Action UInt8 Nat w t' c a) (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.Host\
    .Action UInt8 Nat w t c a)\n\
    | ```\n\
    | \n\
    | - **Requires:** For every action and every situation, the action costs strictly more ene\
    rgy at every night tick than at every daytime tick, waiting included.\n\
    | - **Rules out:** Any action that, in some situation, costs as much or less at some night\
    \x20tick than at some daytime tick.\n\
    | - **Still allows:** Any amount more at night, and a night cost that changes during the n\
    ight, as long as it stays above every daytime cost.\n\
    | - **Freedom O5 leaves:** How much more the night costs, and whether that extra changes d\
    uring the night.\n\
    | \n\
    | ### the agent can always tell day from night\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (t :\
    \x20Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @Eq.{1} UInt8 (@AcornVerif.Intent.Day\
    Cycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t c) (@AcornVerif.Intent.DayCycle.D\
    ayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') → @Eq.{1} Bool (@AcornVerif.Intent.\
    DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) (@AcornVerif.Intent.DayCycle\
    .DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t')\n\
    | ```\n\
    | \n\
    | - **Requires:** Whatever the agent sees always tells it whether it is day or night.\n\
    | - **Rules out:** An agent that sees a day moment and a night moment alike.\n\
    | - **Still allows:** An agent that sees more than that.\n\
    | - **Freedom O5 leaves:** How much more it sees.\n\
    | \n\
    | ### the agent can always see where in the day it is, at least to a quarter of the day\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Exist\
    s.{1} Nat (fun (start : Nat) => ∀ (t : Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @E\
    q.{1} UInt8 (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w \
    t c) (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') \
    → @Eq.{1} Nat (AcornVerif.Intent.DayCycle.quarter (@AcornVerif.Intent.DayCycle.DayWorld.le\
    ngth Unit Acorn.Host.Action UInt8 Nat w) start t) (AcornVerif.Intent.DayCycle.quarter (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) start t'))\n\
    | ```\n\
    | \n\
    | - **Requires:** Whatever the agent sees always tells it which quarter of the day it is i\
    n.\n\
    | - **Rules out:** An agent that sees only whether it is day or night, in a day longer tha\
    n two ticks.\n\
    | - **Still allows:** An agent that sees the quarter, a finer part of the day, or the exac\
    t tick.\n\
    | - **Freedom O5 leaves:** How much more finely than a quarter the agent sees the time of \
    day.\n\
    | \n\
    | ## Vocabulary\n\
    | \n\
    | ### night half, a predicate over `Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) => AcornVerif.Intent.DayCycle.NightHalf \
    (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat Nat) p) (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0}\
    \x20Nat (Prod.{0, 0} Nat Nat) p)) (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0\
    , 0} Nat Nat) p))\n\
    | ```\n\
    | \n\
    | - **Requires:** Tick t is in the night when, counted around a day of the given length fr\
    om where the night starts, it falls in the first half.\n\
    | - **Rules out:** Tick 1 in a day of two ticks whose night starts at tick 0.\n\
    | - **Still allows:** Tick 0 in that day.\n\
    | - **Freedom O5 leaves:** None: it is a definition.\n\
    | \n\
    | ### costs less, a predicate over `Prod.{0, 0} Nat Nat`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} Nat Nat) => @LT.lt.{0} Nat instLTNat (@Prod.fst.{0, 0} Nat Nat p) (\
    @Prod.snd.{0, 0} Nat Nat p)\n\
    | ```\n\
    | \n\
    | - **Requires:** The world's own order on energy amounts.\n\
    | - **Rules out:** Whatever that order rules out.\n\
    | - **Still allows:** Whatever that order allows.\n\
    | - **Freedom O5 leaves:** None of its own.\n\
    | \n\
    | ### in quarter, a predicate over `Prod.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)\
    )`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))) => @Eq.{1} Nat (AcornV\
    erif.Intent.DayCycle.quarter (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))\
    \x20p) (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat Nat) (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat \
    (Prod.{0, 0} Nat Nat)) p)) (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Na\
    t Nat) (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) p)))) (@Prod.snd.{0, \
    0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat Nat) (@Prod.snd.{0, 0} Nat (Prod.{0, 0} \
    Nat (Prod.{0, 0} Nat Nat)) p)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Tick t lies in the given quarter of a day of the given length, counted f\
    rom the given start.\n\
    | - **Rules out:** Tick 0 in quarter 1 of a day of four ticks counted from tick 0.\n\
    | - **Still allows:** Tick 0 in quarter 0 of that day.\n\
    | - **Freedom O5 leaves:** None: it is a definition.\n\
    | \n\
    | ## Consequences\n\
    | \n\
    | ### every day lasts the same even number of ticks, at least two, placed alike, an entail\
    ment: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => And (@\
    LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w)) (And (@Eq.{1\
    } Nat (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@AcornVerif.Inten\
    t.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) (@OfNat.ofNat.{0} Nat (nat_\
    lit 2) (instOfNatNat (nat_lit 2)))) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_l\
    it 0)))) (∀ (t : Nat), @Eq.{1} Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn\
    .Host.Action UInt8 Nat w (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) \
    t (@AcornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w))) (@Aco\
    rnVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Every day lasts the same even number of ticks, at least two, and each da\
    y's night falls at the same ticks of the day.\n\
    | - **Rules out:** Days of different lengths.\n\
    | - **Still allows:** Any one day length shared by all days.\n\
    | - **Freedom O5 leaves:** The length itself.\n\
    | \n\
    | ### every action costs more at any night moment than at any daytime moment, an entailmen\
    t: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (c :\
    \x20Unit), ∀ (a : Acorn.Host.Action), ∀ (t : Nat), ∀ (t' : Nat), @Eq.{1} Bool (@AcornVerif\
    .Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true → @Eq.{1} \
    Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t') Bo\
    ol.false → @LT.lt.{0} Nat instLTNat (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.\
    Host.Action UInt8 Nat w t' c a) (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.Host\
    .Action UInt8 Nat w t c a)\n\
    | ```\n\
    | \n\
    | - **Requires:** Even the cheapest action costs more at any night moment than at any dayt\
    ime moment, in the same situation.\n\
    | - **Rules out:** Any action that is no dearer at some night moment.\n\
    | - **Still allows:** Any extra amount.\n\
    | - **Freedom O5 leaves:** How much more.\n\
    | \n\
    | ### what the agent sees always tells day from night, an entailment: every subject that m\
    eets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (t :\
    \x20Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @Eq.{1} UInt8 (@AcornVerif.Intent.Day\
    Cycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t c) (@AcornVerif.Intent.DayCycle.D\
    ayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') → @Eq.{1} Bool (@AcornVerif.Intent.\
    DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) (@AcornVerif.Intent.DayCycle\
    .DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t')\n\
    | ```\n\
    | \n\
    | - **Requires:** From what it sees, the agent can always tell whether it is day or night.\
    \n\
    | - **Rules out:** An agent that cannot tell day from night at some moment.\n\
    | - **Still allows:** An agent that sees more than that.\n\
    | - **Freedom O5 leaves:** How much more it sees.\n\
    | \n\
    | ### what the agent sees always tells it which quarter of the day it is in, an entailment\
    : every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Exist\
    s.{1} Nat (fun (start : Nat) => ∀ (t : Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @E\
    q.{1} UInt8 (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w \
    t c) (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') \
    → @Eq.{1} Nat (AcornVerif.Intent.DayCycle.quarter (@AcornVerif.Intent.DayCycle.DayWorld.le\
    ngth Unit Acorn.Host.Action UInt8 Nat w) start t) (AcornVerif.Intent.DayCycle.quarter (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) start t'))\n\
    | ```\n\
    | \n\
    | - **Requires:** From what it sees, the agent can always tell which quarter of the day it\
    \x20is in.\n\
    | - **Rules out:** An agent that sees only day or night.\n\
    | - **Still allows:** Seeing a finer part of the day, or the exact tick.\n\
    | - **Freedom O5 leaves:** How much finer than a quarter.\n\
    | \n\
    | ### a day may last 1000 ticks, a possibility: some subject that meets the record satisfi\
    es it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Eq.{1\
    } Nat (@AcornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) (@O\
    fNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Nothing more: a world whose day lasts 1000 ticks can meet the record.\n\
    | - **Rules out:** Nothing.\n\
    | - **Still allows:** Short days and long days alike.\n\
    | - **Freedom O5 leaves:** The day's length.\n\
    | \n\
    | ### an action may cost more at one night moment than at another, a possibility: some sub\
    ject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Exist\
    s.{1} Unit (fun (c : Unit) => @Exists.{1} Acorn.Host.Action (fun (a : Acorn.Host.Action) =\
    > @Exists.{1} Nat (fun (t : Nat) => @Exists.{1} Nat (fun (t' : Nat) => And (@Eq.{1} Bool (\
    @AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true\
    ) (And (@Eq.{1} Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UI\
    nt8 Nat w t') Bool.true) (@Ne.{1} Nat (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acor\
    n.Host.Action UInt8 Nat w t c a) (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.Hos\
    t.Action UInt8 Nat w t' c a)))))))\n\
    | ```\n\
    | \n\
    | - **Requires:** Nothing more: an action may cost more at one night moment than at anothe\
    r, as long as every night cost is above every daytime cost.\n\
    | - **Rules out:** Nothing.\n\
    | - **Still allows:** A night that is dearer at midnight than at dusk.\n\
    | - **Freedom O5 leaves:** Whether the night's extra changes during the night.\n\
    | \n\
    | ## Definitions the record's meaning reaches\n\
    | \n\
    | These are not statements of the record: each is a declaration that a statement above dep\
    ends on, or that says what it is for a subject to meet the record and for a consequence to\
    \x20hold of it as shown, with everything those depend on in turn. Each is printed in full:\
    \x20its type, a definition's value, or for a definition by structural or well-founded recu\
    rsion the equation that determines it, and an inductive type's constructors, which for a s\
    tructure are its fields; a theorem's proof and an opaque constant's value are not, since n\
    o term that uses them depends on more than their types. Their plain words are those of the\
    \x20statements that use them.\n\
    | \n\
    | ### Acorn.Host.Action\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### Acorn.Host.Action.north\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.south\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.east\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.west\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.wait\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.harvest\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftAxe\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftBoat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.eat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Shape\n\
    | \n\
    | An inductive type. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type u → Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Shape.value\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.function\n\
    | \n\
    | ```lean\n\
    | ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.step\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.stepOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.action\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.actionOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u\
    } O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.bundle\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀\
    \x20(rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Member\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Member.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → \
    Out), LeanIntent.Member.{u} W\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (Ctx : Type), ∀ (Act : Type), ∀ (Obs : Type), ∀ (E : Type), Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 4 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.DayCycle.DayWorld.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (length : Nat), ∀ (night\
    \x20: Nat → Bool), ∀ (cost : Nat → Ctx → Act → E), ∀ (sees : Nat → Ctx → Obs), AcornVerif.\
    Intent.DayCycle.DayWorld Ctx Act Obs E\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.length\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 1, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.night\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 2, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Bool\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.NightHalf\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (length : Nat), ∀ (start : Nat), ∀ (t : Nat), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (length : Nat) => fun (start : Nat) => fun (t : Nat) => @LT.lt.{0} Nat instLTNat (@H\
    Mod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@HAdd.hAdd.{0, 0, 0} Nat N\
    at Nat (@instHAdd.{0} Nat instAddNat) t start) length) (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (\
    @instHDiv.{0} Nat Nat.instDiv) length (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat\
    _lit 2))))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.cost\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 3, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Ctx → Act → E\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.sees\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 4, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Ctx → Obs\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.quarter\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (length : Nat), ∀ (start : Nat), ∀ (t : Nat), Nat\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (length : Nat) => fun (start : Nat) => fun (t : Nat) => @HDiv.hDiv.{0, 0, 0} Nat Nat\
    \x20Nat (@instHDiv.{0} Nat Nat.instDiv) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} N\
    at instMulNat) (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@HAdd.hA\
    dd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t start) length) (@OfNat.ofNat.{0}\
    \x20Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) length\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Meets\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@Lean\
    Intent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.IntentRecord.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause\
    .{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanInte\
    nt.Pred.{u}), LeanIntent.IntentRecord.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Clause.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Pred\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Pred.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Dom\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.dom\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Cla\
    use's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Props\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.props\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.HoldsOf\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (c : LeanIntent.Consequence.{u} W), ∀ (r : LeanIntent.IntentRecord.{u}\
    \x20W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (c : LeanIntent.Consequence.{u} W) => fun (r : LeanIntent.Intent\
    Record.{u} W) => LeanIntent.Consequence.HoldsOf.match_1.{1} (fun (x : LeanIntent.Consequen\
    ce.Kind) => Prop) (@LeanIntent.Consequence.kind.{u} W c) (fun («_» : Unit) => ∀ (w : W), @\
    LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W c w) (fun («\
    _» : Unit) => @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRec\
    ord.Meets.{u} W r w) (@LeanIntent.Consequence.holds.{u} W c w)))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W \
    → Prop), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.entailment\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.possibility\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.HoldsOf.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : LeanIntent.Consequence.Kind → Sort u_1), ∀ (x : LeanIntent.Consequence.Kind)\
    , ∀ (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment), ∀ (h_2 : ∀ («_»\
    \x20: Unit), motive LeanIntent.Consequence.Kind.possibility), motive x\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : LeanIntent.Consequence.Kind → Sort u_1) => fun (x : LeanIntent.Consequence\
    .Kind) => fun (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment) => fun\
    \x20(h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.\
    Consequence.Kind.casesOn.{u_1} (fun (x_1 : LeanIntent.Consequence.Kind) => motive x_1) x (\
    h_1 Unit.unit) (h_2 Unit.unit)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.\
    Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : mo\
    tive LeanIntent.Consequence.Kind.possibility), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Conseq\
    uence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (po\
    ssibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kin\
    d.rec.{u} motive entailment possibility t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.kind\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.HasInstance\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)\n\
    | ```\n\
    | \n\
    | ## Lean's own libraries\n\
    | \n\
    | The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: the\
    y are those of Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, which made th\
    is text. A declaration is counted as Lean's own when Lean found the module that declares i\
    t in that release's library directory.\n\
    | \n\
    consequence what the agent sees always tells it which quarter of the day it is in\n\
    shown as entailment\n\
    predicate 486\n\
    | # A consequence's predicate\n\
    | \n\
    | Printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks,\
    \x20binder names and metadata aside, from the root namespace with nothing opened.\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Exist\
    s.{1} Nat (fun (start : Nat) => ∀ (t : Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @E\
    q.{1} UInt8 (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w \
    t c) (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') \
    → @Eq.{1} Nat (AcornVerif.Intent.DayCycle.quarter (@AcornVerif.Intent.DayCycle.DayWorld.le\
    ngth Unit Acorn.Host.Action UInt8 Nat w) start t) (AcornVerif.Intent.DayCycle.quarter (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) start t'))\n\
    | ```\n\
    | \n\
    | ## Definitions the predicate reaches\n\
    | \n\
    | Each is printed in full, as in the rendering of a record, with what an answer to it asks\
    \x20of every later revision (`LeanIntent.Answer.KeptBy`).\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (Ctx : Type), ∀ (Act : Type), ∀ (Obs : Type), ∀ (E : Type), Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 4 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.DayCycle.DayWorld.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (length : Nat), ∀ (night\
    \x20: Nat → Bool), ∀ (cost : Nat → Ctx → Act → E), ∀ (sees : Nat → Ctx → Obs), AcornVerif.\
    Intent.DayCycle.DayWorld Ctx Act Obs E\n\
    | ```\n\
    | \n\
    | ### Acorn.Host.Action\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### Acorn.Host.Action.north\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.south\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.east\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.west\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.wait\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.harvest\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftAxe\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftBoat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.eat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.sees\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 4, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Ctx → Obs\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.quarter\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (length : Nat), ∀ (start : Nat), ∀ (t : Nat), Nat\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (length : Nat) => fun (start : Nat) => fun (t : Nat) => @HDiv.hDiv.{0, 0, 0} Nat Nat\
    \x20Nat (@instHDiv.{0} Nat Nat.instDiv) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} N\
    at instMulNat) (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@HAdd.hA\
    dd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t start) length) (@OfNat.ofNat.{0}\
    \x20Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) length\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.length\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 1, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.KeptBy\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (a : LeanIntent.Answer.{u} W), ∀ (r : LeanIntent.IntentRecord.{u} W), \
    Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (a : LeanIntent.Answer.{u} W) => fun (r : LeanIntent.IntentRecor\
    d.{u} W) => LeanIntent.Answer.KeptBy.match_1.{1} (fun (x : LeanIntent.Consequence.Kind) =>\
    \x20fun (x_1 : LeanIntent.Verdict) => Prop) (@LeanIntent.Consequence.kind.{u} W (@LeanInte\
    nt.Answer.consequence.{u} W a)) (@LeanIntent.Answer.verdict.{u} W a) (fun («_» : Unit) => \
    ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W \
    (@LeanIntent.Answer.consequence.{u} W a) w) (fun («_» : Unit) => @LeanIntent.HasInstance.{\
    u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u} W r w) (Not (@LeanIntent.\
    Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w)))) (fun («_» : Unit) =\
    > @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u\
    } W r w) (@LeanIntent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w))\
    ) (fun («_» : Unit) => ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → Not (@LeanInt\
    ent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Answer.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (consequence : LeanIntent.Consequence.{u} W), ∀ (verdict : LeanIntent.\
    Verdict), LeanIntent.Answer.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W \
    → Prop), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.entailment\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.possibility\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Verdict\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Verdict.confirmed\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Verdict.declined\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.IntentRecord.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause\
    .{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanInte\
    nt.Pred.{u}), LeanIntent.IntentRecord.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Shape\n\
    | \n\
    | An inductive type. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type u → Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Shape.value\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.function\n\
    | \n\
    | ```lean\n\
    | ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.step\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.stepOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.action\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.actionOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u\
    } O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.bundle\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀\
    \x20(rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Member\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Member.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → \
    Out), LeanIntent.Member.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Clause.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Pred\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Pred.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.KeptBy.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : LeanIntent.Consequence.Kind → LeanIntent.Verdict → Sort u_1), ∀ (x : LeanInt\
    ent.Consequence.Kind), ∀ (x_1 : LeanIntent.Verdict), ∀ (h_1 : ∀ («_» : Unit), motive LeanI\
    ntent.Consequence.Kind.entailment LeanIntent.Verdict.confirmed), ∀ (h_2 : ∀ («_» : Unit), \
    motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.declined), ∀ (h_3 : ∀ («_\
    » : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdict.confirmed), ∀\
    \x20(h_4 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdi\
    ct.declined), motive x x_1\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : LeanIntent.Consequence.Kind → LeanIntent.Verdict → Sort u_1) => fun (x : L\
    eanIntent.Consequence.Kind) => fun (x_1 : LeanIntent.Verdict) => fun (h_1 : ∀ («_» : Unit)\
    , motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.confirmed) => fun (h_2 \
    : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.decline\
    d) => fun (h_3 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent\
    .Verdict.confirmed) => fun (h_4 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possi\
    bility LeanIntent.Verdict.declined) => @LeanIntent.Consequence.Kind.casesOn.{u_1} (fun (x_\
    2 : LeanIntent.Consequence.Kind) => motive x_2 x_1) x (@LeanIntent.Verdict.casesOn.{u_1} (\
    fun (x_2 : LeanIntent.Verdict) => motive LeanIntent.Consequence.Kind.entailment x_2) x_1 (\
    h_1 Unit.unit) (h_2 Unit.unit)) (@LeanIntent.Verdict.casesOn.{u_1} (fun (x_2 : LeanIntent.\
    Verdict) => motive LeanIntent.Consequence.Kind.possibility x_2) x_1 (h_3 Unit.unit) (h_4 U\
    nit.unit))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.\
    Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : mo\
    tive LeanIntent.Consequence.Kind.possibility), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Conseq\
    uence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (po\
    ssibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kin\
    d.rec.{u} motive entailment possibility t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Verdict.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Verdict), Sort u}, ∀ (t : LeanIntent.Verdict), ∀ (confirme\
    d : motive LeanIntent.Verdict.confirmed), ∀ (declined : motive LeanIntent.Verdict.declined\
    ), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Verdict), Sort u} => fun (t : LeanIntent.Verdict) => fun\
    \x20(confirmed : motive LeanIntent.Verdict.confirmed) => fun (declined : motive LeanIntent\
    .Verdict.declined) => @LeanIntent.Verdict.rec.{u} motive confirmed declined t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.kind\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.consequence\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 1, counted after the parameters in the type of LeanIntent.Ans\
    wer's constructor, of its argument number 2, a value of LeanIntent.Answer. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Answer.{u} W), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.verdict\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Ans\
    wer's constructor, of its argument number 2, a value of LeanIntent.Answer. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Answer.{u} W), LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Meets\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@Lean\
    Intent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Dom\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.dom\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Cla\
    use's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Props\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.props\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.HasInstance\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)\n\
    | ```\n\
    | \n\
    | ## Lean's own libraries\n\
    | \n\
    | The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: the\
    y are those of Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, which made th\
    is text. A declaration is counted as Lean's own when Lean found the module that declares i\
    t in that release's library directory.\n\
    | \n\
    verdict confirmed\n\
    ",
  "lean-intent statement 1\n\
    kind answer\n\
    project acorn\n\
    id day-5b-r2\n\
    date 2026-11-03\n\
    reference docs/spec-first-pilot.md, The decisions made on the owner's behalf\n\
    by agents\n\
    under agents-below-intent\n\
    record AcornVerif.Intent.DayCycle.dayCycle\n\
    revision 610\n\
    | # The intent record @AcornVerif.Intent.DayCycle.dayCycleFor Unit Acorn.Host.Action UInt8\
    \x20Nat instLTNat\n\
    | \n\
    | Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term \
    its kernel checks, binder names and metadata aside, from the root namespace with nothing o\
    pened. The plain words after it are written by a model and are trusted, not proved.\n\
    | \n\
    | ## Shape\n\
    | \n\
    | ### The subject\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Shape.value.{0} (AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action U\
    Int8 Nat)\n\
    | ```\n\
    | \n\
    | - **Requires:** The subject is a description of a world's day: how many ticks a day last\
    s, which ticks are night, what each action costs at each tick in each situation, and what \
    the agent sees at each tick in each situation. Time is counted in whole ticks from the sta\
    rt of a run, and one clock serves the whole world.\n\
    | - **Rules out:** Nothing by itself; it fixes only what the statements below talk about.\
    \n\
    | - **Still allows:** Any world's situations, actions, sights and energy amounts.\n\
    | - **Freedom O5 leaves:** None of its own. It carries no state from one tick to the next,\
    \x20so it is declared a plain value, of which obligation O4 asks nothing.\n\
    | \n\
    | ## Domain hypotheses\n\
    | \n\
    | None.\n\
    | \n\
    | ## Properties\n\
    | \n\
    | ### each day has a daytime half and a night half of equal length\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => And (@\
    LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w)) (And (@Eq.{1\
    } Nat (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@AcornVerif.Inten\
    t.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) (@OfNat.ofNat.{0} Nat (nat_\
    lit 2) (instOfNatNat (nat_lit 2)))) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_l\
    it 0)))) (@Exists.{1} Nat (fun (start : Nat) => ∀ (t : Nat), Iff (@Eq.{1} Bool (@AcornVeri\
    f.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true) (AcornVe\
    rif.Intent.DayCycle.NightHalf (@AcornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host\
    .Action UInt8 Nat w) start t))))\n\
    | ```\n\
    | \n\
    | - **Requires:** A day lasts a fixed, even number of ticks, at least two. The night is on\
    e unbroken stretch of exactly half of them and the daytime the other half, and every day i\
    s the same.\n\
    | - **Rules out:** A world with no night or no daytime; a day of an odd number of ticks; a\
    \x20night broken into several stretches; days of different lengths.\n\
    | - **Still allows:** Any even day length, and a night that starts at any tick of the day.\
    \n\
    | - **Freedom O5 leaves:** How long a day is and where in it the night starts.\n\
    | \n\
    | ### at night every action costs more energy\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (c :\
    \x20Unit), ∀ (a : Acorn.Host.Action), ∀ (t : Nat), ∀ (t' : Nat), @Eq.{1} Bool (@AcornVerif\
    .Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true → @Eq.{1} \
    Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t') Bo\
    ol.false → @LT.lt.{0} Nat instLTNat (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.\
    Host.Action UInt8 Nat w t' c a) (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.Host\
    .Action UInt8 Nat w t c a)\n\
    | ```\n\
    | \n\
    | - **Requires:** For every action and every situation, the action costs strictly more ene\
    rgy at every night tick than at every daytime tick, waiting included.\n\
    | - **Rules out:** Any action that, in some situation, costs as much or less at some night\
    \x20tick than at some daytime tick.\n\
    | - **Still allows:** Any amount more at night, and a night cost that changes during the n\
    ight, as long as it stays above every daytime cost.\n\
    | - **Freedom O5 leaves:** How much more the night costs, and whether that extra changes d\
    uring the night.\n\
    | \n\
    | ### the agent can always tell day from night\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (t :\
    \x20Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @Eq.{1} UInt8 (@AcornVerif.Intent.Day\
    Cycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t c) (@AcornVerif.Intent.DayCycle.D\
    ayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') → @Eq.{1} Bool (@AcornVerif.Intent.\
    DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) (@AcornVerif.Intent.DayCycle\
    .DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t')\n\
    | ```\n\
    | \n\
    | - **Requires:** Whatever the agent sees always tells it whether it is day or night.\n\
    | - **Rules out:** An agent that sees a day moment and a night moment alike.\n\
    | - **Still allows:** An agent that sees more than that.\n\
    | - **Freedom O5 leaves:** How much more it sees.\n\
    | \n\
    | ### the agent can always see where in the day it is, at least to a quarter of the day\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Exist\
    s.{1} Nat (fun (start : Nat) => ∀ (t : Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @E\
    q.{1} UInt8 (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w \
    t c) (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') \
    → @Eq.{1} Nat (AcornVerif.Intent.DayCycle.quarter (@AcornVerif.Intent.DayCycle.DayWorld.le\
    ngth Unit Acorn.Host.Action UInt8 Nat w) start t) (AcornVerif.Intent.DayCycle.quarter (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) start t'))\n\
    | ```\n\
    | \n\
    | - **Requires:** Whatever the agent sees always tells it which quarter of the day it is i\
    n.\n\
    | - **Rules out:** An agent that sees only whether it is day or night, in a day longer tha\
    n two ticks.\n\
    | - **Still allows:** An agent that sees the quarter, a finer part of the day, or the exac\
    t tick.\n\
    | - **Freedom O5 leaves:** How much more finely than a quarter the agent sees the time of \
    day.\n\
    | \n\
    | ## Vocabulary\n\
    | \n\
    | ### night half, a predicate over `Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) => AcornVerif.Intent.DayCycle.NightHalf \
    (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat Nat) p) (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0}\
    \x20Nat (Prod.{0, 0} Nat Nat) p)) (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0\
    , 0} Nat Nat) p))\n\
    | ```\n\
    | \n\
    | - **Requires:** Tick t is in the night when, counted around a day of the given length fr\
    om where the night starts, it falls in the first half.\n\
    | - **Rules out:** Tick 1 in a day of two ticks whose night starts at tick 0.\n\
    | - **Still allows:** Tick 0 in that day.\n\
    | - **Freedom O5 leaves:** None: it is a definition.\n\
    | \n\
    | ### costs less, a predicate over `Prod.{0, 0} Nat Nat`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} Nat Nat) => @LT.lt.{0} Nat instLTNat (@Prod.fst.{0, 0} Nat Nat p) (\
    @Prod.snd.{0, 0} Nat Nat p)\n\
    | ```\n\
    | \n\
    | - **Requires:** The world's own order on energy amounts.\n\
    | - **Rules out:** Whatever that order rules out.\n\
    | - **Still allows:** Whatever that order allows.\n\
    | - **Freedom O5 leaves:** None of its own.\n\
    | \n\
    | ### in quarter, a predicate over `Prod.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)\
    )`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))) => @Eq.{1} Nat (AcornV\
    erif.Intent.DayCycle.quarter (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))\
    \x20p) (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat Nat) (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat \
    (Prod.{0, 0} Nat Nat)) p)) (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Na\
    t Nat) (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) p)))) (@Prod.snd.{0, \
    0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat Nat) (@Prod.snd.{0, 0} Nat (Prod.{0, 0} \
    Nat (Prod.{0, 0} Nat Nat)) p)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Tick t lies in the given quarter of a day of the given length, counted f\
    rom the given start.\n\
    | - **Rules out:** Tick 0 in quarter 1 of a day of four ticks counted from tick 0.\n\
    | - **Still allows:** Tick 0 in quarter 0 of that day.\n\
    | - **Freedom O5 leaves:** None: it is a definition.\n\
    | \n\
    | ## Consequences\n\
    | \n\
    | ### every day lasts the same even number of ticks, at least two, placed alike, an entail\
    ment: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => And (@\
    LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w)) (And (@Eq.{1\
    } Nat (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@AcornVerif.Inten\
    t.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) (@OfNat.ofNat.{0} Nat (nat_\
    lit 2) (instOfNatNat (nat_lit 2)))) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_l\
    it 0)))) (∀ (t : Nat), @Eq.{1} Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn\
    .Host.Action UInt8 Nat w (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) \
    t (@AcornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w))) (@Aco\
    rnVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Every day lasts the same even number of ticks, at least two, and each da\
    y's night falls at the same ticks of the day.\n\
    | - **Rules out:** Days of different lengths.\n\
    | - **Still allows:** Any one day length shared by all days.\n\
    | - **Freedom O5 leaves:** The length itself.\n\
    | \n\
    | ### every action costs more at any night moment than at any daytime moment, an entailmen\
    t: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (c :\
    \x20Unit), ∀ (a : Acorn.Host.Action), ∀ (t : Nat), ∀ (t' : Nat), @Eq.{1} Bool (@AcornVerif\
    .Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true → @Eq.{1} \
    Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t') Bo\
    ol.false → @LT.lt.{0} Nat instLTNat (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.\
    Host.Action UInt8 Nat w t' c a) (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.Host\
    .Action UInt8 Nat w t c a)\n\
    | ```\n\
    | \n\
    | - **Requires:** Even the cheapest action costs more at any night moment than at any dayt\
    ime moment, in the same situation.\n\
    | - **Rules out:** Any action that is no dearer at some night moment.\n\
    | - **Still allows:** Any extra amount.\n\
    | - **Freedom O5 leaves:** How much more.\n\
    | \n\
    | ### what the agent sees always tells day from night, an entailment: every subject that m\
    eets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (t :\
    \x20Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @Eq.{1} UInt8 (@AcornVerif.Intent.Day\
    Cycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t c) (@AcornVerif.Intent.DayCycle.D\
    ayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') → @Eq.{1} Bool (@AcornVerif.Intent.\
    DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) (@AcornVerif.Intent.DayCycle\
    .DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t')\n\
    | ```\n\
    | \n\
    | - **Requires:** From what it sees, the agent can always tell whether it is day or night.\
    \n\
    | - **Rules out:** An agent that cannot tell day from night at some moment.\n\
    | - **Still allows:** An agent that sees more than that.\n\
    | - **Freedom O5 leaves:** How much more it sees.\n\
    | \n\
    | ### what the agent sees always tells it which quarter of the day it is in, an entailment\
    : every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Exist\
    s.{1} Nat (fun (start : Nat) => ∀ (t : Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @E\
    q.{1} UInt8 (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w \
    t c) (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') \
    → @Eq.{1} Nat (AcornVerif.Intent.DayCycle.quarter (@AcornVerif.Intent.DayCycle.DayWorld.le\
    ngth Unit Acorn.Host.Action UInt8 Nat w) start t) (AcornVerif.Intent.DayCycle.quarter (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) start t'))\n\
    | ```\n\
    | \n\
    | - **Requires:** From what it sees, the agent can always tell which quarter of the day it\
    \x20is in.\n\
    | - **Rules out:** An agent that sees only day or night.\n\
    | - **Still allows:** Seeing a finer part of the day, or the exact tick.\n\
    | - **Freedom O5 leaves:** How much finer than a quarter.\n\
    | \n\
    | ### a day may last 1000 ticks, a possibility: some subject that meets the record satisfi\
    es it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Eq.{1\
    } Nat (@AcornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) (@O\
    fNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Nothing more: a world whose day lasts 1000 ticks can meet the record.\n\
    | - **Rules out:** Nothing.\n\
    | - **Still allows:** Short days and long days alike.\n\
    | - **Freedom O5 leaves:** The day's length.\n\
    | \n\
    | ### an action may cost more at one night moment than at another, a possibility: some sub\
    ject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Exist\
    s.{1} Unit (fun (c : Unit) => @Exists.{1} Acorn.Host.Action (fun (a : Acorn.Host.Action) =\
    > @Exists.{1} Nat (fun (t : Nat) => @Exists.{1} Nat (fun (t' : Nat) => And (@Eq.{1} Bool (\
    @AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true\
    ) (And (@Eq.{1} Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UI\
    nt8 Nat w t') Bool.true) (@Ne.{1} Nat (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acor\
    n.Host.Action UInt8 Nat w t c a) (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.Hos\
    t.Action UInt8 Nat w t' c a)))))))\n\
    | ```\n\
    | \n\
    | - **Requires:** Nothing more: an action may cost more at one night moment than at anothe\
    r, as long as every night cost is above every daytime cost.\n\
    | - **Rules out:** Nothing.\n\
    | - **Still allows:** A night that is dearer at midnight than at dusk.\n\
    | - **Freedom O5 leaves:** Whether the night's extra changes during the night.\n\
    | \n\
    | ## Definitions the record's meaning reaches\n\
    | \n\
    | These are not statements of the record: each is a declaration that a statement above dep\
    ends on, or that says what it is for a subject to meet the record and for a consequence to\
    \x20hold of it as shown, with everything those depend on in turn. Each is printed in full:\
    \x20its type, a definition's value, or for a definition by structural or well-founded recu\
    rsion the equation that determines it, and an inductive type's constructors, which for a s\
    tructure are its fields; a theorem's proof and an opaque constant's value are not, since n\
    o term that uses them depends on more than their types. Their plain words are those of the\
    \x20statements that use them.\n\
    | \n\
    | ### Acorn.Host.Action\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### Acorn.Host.Action.north\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.south\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.east\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.west\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.wait\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.harvest\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftAxe\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftBoat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.eat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Shape\n\
    | \n\
    | An inductive type. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type u → Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Shape.value\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.function\n\
    | \n\
    | ```lean\n\
    | ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.step\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.stepOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.action\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.actionOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u\
    } O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.bundle\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀\
    \x20(rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Member\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Member.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → \
    Out), LeanIntent.Member.{u} W\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (Ctx : Type), ∀ (Act : Type), ∀ (Obs : Type), ∀ (E : Type), Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 4 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.DayCycle.DayWorld.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (length : Nat), ∀ (night\
    \x20: Nat → Bool), ∀ (cost : Nat → Ctx → Act → E), ∀ (sees : Nat → Ctx → Obs), AcornVerif.\
    Intent.DayCycle.DayWorld Ctx Act Obs E\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.length\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 1, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.night\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 2, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Bool\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.NightHalf\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (length : Nat), ∀ (start : Nat), ∀ (t : Nat), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (length : Nat) => fun (start : Nat) => fun (t : Nat) => @LT.lt.{0} Nat instLTNat (@H\
    Mod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@HAdd.hAdd.{0, 0, 0} Nat N\
    at Nat (@instHAdd.{0} Nat instAddNat) t start) length) (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (\
    @instHDiv.{0} Nat Nat.instDiv) length (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat\
    _lit 2))))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.cost\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 3, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Ctx → Act → E\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.sees\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 4, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Ctx → Obs\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.quarter\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (length : Nat), ∀ (start : Nat), ∀ (t : Nat), Nat\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (length : Nat) => fun (start : Nat) => fun (t : Nat) => @HDiv.hDiv.{0, 0, 0} Nat Nat\
    \x20Nat (@instHDiv.{0} Nat Nat.instDiv) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} N\
    at instMulNat) (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@HAdd.hA\
    dd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t start) length) (@OfNat.ofNat.{0}\
    \x20Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) length\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Meets\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@Lean\
    Intent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.IntentRecord.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause\
    .{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanInte\
    nt.Pred.{u}), LeanIntent.IntentRecord.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Clause.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Pred\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Pred.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Dom\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.dom\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Cla\
    use's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Props\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.props\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.HoldsOf\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (c : LeanIntent.Consequence.{u} W), ∀ (r : LeanIntent.IntentRecord.{u}\
    \x20W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (c : LeanIntent.Consequence.{u} W) => fun (r : LeanIntent.Intent\
    Record.{u} W) => LeanIntent.Consequence.HoldsOf.match_1.{1} (fun (x : LeanIntent.Consequen\
    ce.Kind) => Prop) (@LeanIntent.Consequence.kind.{u} W c) (fun («_» : Unit) => ∀ (w : W), @\
    LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W c w) (fun («\
    _» : Unit) => @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRec\
    ord.Meets.{u} W r w) (@LeanIntent.Consequence.holds.{u} W c w)))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W \
    → Prop), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.entailment\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.possibility\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.HoldsOf.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : LeanIntent.Consequence.Kind → Sort u_1), ∀ (x : LeanIntent.Consequence.Kind)\
    , ∀ (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment), ∀ (h_2 : ∀ («_»\
    \x20: Unit), motive LeanIntent.Consequence.Kind.possibility), motive x\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : LeanIntent.Consequence.Kind → Sort u_1) => fun (x : LeanIntent.Consequence\
    .Kind) => fun (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment) => fun\
    \x20(h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.\
    Consequence.Kind.casesOn.{u_1} (fun (x_1 : LeanIntent.Consequence.Kind) => motive x_1) x (\
    h_1 Unit.unit) (h_2 Unit.unit)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.\
    Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : mo\
    tive LeanIntent.Consequence.Kind.possibility), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Conseq\
    uence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (po\
    ssibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kin\
    d.rec.{u} motive entailment possibility t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.kind\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.HasInstance\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)\n\
    | ```\n\
    | \n\
    | ## Lean's own libraries\n\
    | \n\
    | The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: the\
    y are those of Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, which made th\
    is text. A declaration is counted as Lean's own when Lean found the module that declares i\
    t in that release's library directory.\n\
    | \n\
    consequence the agent may see only whether it is day or night\n\
    shown as possibility\n\
    predicate 558\n\
    | # A consequence's predicate\n\
    | \n\
    | Printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks,\
    \x20binder names and metadata aside, from the root namespace with nothing opened.\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Eq.{1\
    } (AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) w (@AcornVerif.In\
    tent.DayCycle.dayOrNightOnly Unit Acorn.Host.Action UInt8 Nat (@OfNat.ofNat.{0} Nat (nat_l\
    it 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit\
    \x201))) (@OfNat.ofNat.{0} UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))) (@OfNat.ofNat\
    .{0} UInt8 (nat_lit 4) (@UInt8.instOfNat (nat_lit 4))))\n\
    | ```\n\
    | \n\
    | ## Definitions the predicate reaches\n\
    | \n\
    | Each is printed in full, as in the rendering of a record, with what an answer to it asks\
    \x20of every later revision (`LeanIntent.Answer.KeptBy`).\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (Ctx : Type), ∀ (Act : Type), ∀ (Obs : Type), ∀ (E : Type), Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 4 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.DayCycle.DayWorld.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (length : Nat), ∀ (night\
    \x20: Nat → Bool), ∀ (cost : Nat → Ctx → Act → E), ∀ (sees : Nat → Ctx → Obs), AcornVerif.\
    Intent.DayCycle.DayWorld Ctx Act Obs E\n\
    | ```\n\
    | \n\
    | ### Acorn.Host.Action\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### Acorn.Host.Action.north\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.south\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.east\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.west\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.wait\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.harvest\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftAxe\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftBoat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.eat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.dayOrNightOnly\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (lo : E), ∀ (hi : E), ∀ \
    (o₁ : Obs), ∀ (o₂ : Obs), AcornVerif.Intent.DayCycle.DayWorld Ctx Act Obs E\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {Ctx : Type} => fun {Act : Type} => fun {Obs : Type} => fun {E : Type} => fun (lo : \
    E) => fun (hi : E) => fun (o₁ : Obs) => fun (o₂ : Obs) => have __src : AcornVerif.Intent.D\
    ayCycle.DayWorld Ctx Act Obs E := @AcornVerif.Intent.DayCycle.clockWorld Ctx Act Obs E (@O\
    fNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (@OfNat.ofNat.{0} Nat (nat_lit \
    0) (instOfNatNat (nat_lit 0))) lo hi (fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (inst\
    OfNatNat (nat_lit 4)))) => o₁); @AcornVerif.Intent.DayCycle.DayWorld.mk Ctx Act Obs E (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Ctx Act Obs E __src) (@AcornVerif.Intent.DayCycle\
    .DayWorld.night Ctx Act Obs E __src) (@AcornVerif.Intent.DayCycle.DayWorld.cost Ctx Act Ob\
    s E __src) (fun (t : Nat) => fun (x : Ctx) => @ite.{1} Obs (AcornVerif.Intent.DayCycle.Nig\
    htHalf (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (@OfNat.ofNat.{0} Nat\
    \x20(nat_lit 0) (instOfNatNat (nat_lit 0))) t) (Nat.decLt (@HMod.hMod.{0, 0, 0} Nat Nat Na\
    t (@instHMod.{0} Nat Nat.instMod) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat ins\
    tAddNat) t (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@OfNat.ofNat.{0\
    } Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDi\
    v.{0} Nat Nat.instDiv) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (@OfN\
    at.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) o₁ o₂)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.clockWorld\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (length : Nat), ∀ (start\
    \x20: Nat), ∀ (lo : E), ∀ (hi : E), ∀ (sight : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (inst\
    OfNatNat (nat_lit 4))) → Obs), AcornVerif.Intent.DayCycle.DayWorld Ctx Act Obs E\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {Ctx : Type} => fun {Act : Type} => fun {Obs : Type} => fun {E : Type} => fun (lengt\
    h : Nat) => fun (start : Nat) => fun (lo : E) => fun (hi : E) => fun (sight : Fin (@OfNat.\
    ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Obs) => @AcornVerif.Intent.DayCycl\
    e.DayWorld.mk Ctx Act Obs E length (fun (t : Nat) => @Decidable.decide (AcornVerif.Intent.\
    DayCycle.NightHalf length start t) (Nat.decLt (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod\
    .{0} Nat Nat.instMod) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t s\
    tart) length) (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) length (@O\
    fNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) (fun (t : Nat) => fun (x : C\
    tx) => fun (x_1 : Act) => @ite.{1} E (AcornVerif.Intent.DayCycle.NightHalf length start t)\
    \x20(Nat.decLt (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@HAdd.hA\
    dd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t start) length) (@HDiv.hDiv.{0, 0\
    , 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) length (@OfNat.ofNat.{0} Nat (nat_lit 2) \
    (instOfNatNat (nat_lit 2))))) hi lo) (fun (t : Nat) => fun (x : Ctx) => sight (AcornVerif.\
    Intent.DayCycle.quarterIndex length start t))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.NightHalf\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (length : Nat), ∀ (start : Nat), ∀ (t : Nat), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (length : Nat) => fun (start : Nat) => fun (t : Nat) => @LT.lt.{0} Nat instLTNat (@H\
    Mod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@HAdd.hAdd.{0, 0, 0} Nat N\
    at Nat (@instHAdd.{0} Nat instAddNat) t start) length) (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (\
    @instHDiv.{0} Nat Nat.instDiv) length (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat\
    _lit 2))))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.quarterIndex\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (length : Nat), ∀ (start : Nat), ∀ (t : Nat), Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (i\
    nstOfNatNat (nat_lit 4)))\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (length : Nat) => fun (start : Nat) => fun (t : Nat) => @Fin.mk (@OfNat.ofNat.{0} Na\
    t (nat_lit 4) (instOfNatNat (nat_lit 4))) (@Min.min.{0} Nat instMinNat (AcornVerif.Intent.\
    DayCycle.quarter length start t) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit \
    3)))) (AcornVerif.Intent.DayCycle.quarterIndex._proof_2 length start t)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.quarter\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (length : Nat), ∀ (start : Nat), ∀ (t : Nat), Nat\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (length : Nat) => fun (start : Nat) => fun (t : Nat) => @HDiv.hDiv.{0, 0, 0} Nat Nat\
    \x20Nat (@instHDiv.{0} Nat Nat.instDiv) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} N\
    at instMulNat) (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@HAdd.hA\
    dd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t start) length) (@OfNat.ofNat.{0}\
    \x20Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) length\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.quarterIndex._proof_2\n\
    | \n\
    | A theorem, whose proof is not printed: any two proofs of a proposition are equal by defi\
    nitional proof irrelevance, so a term that uses it depends on nothing but its statement. I\
    t has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (length : Nat), ∀ (start : Nat), ∀ (t : Nat), @LT.lt.{0} Nat instLTNat (@Min.min.{0} N\
    at instMinNat (AcornVerif.Intent.DayCycle.quarter length start t) (@OfNat.ofNat.{0} Nat (n\
    at_lit 3) (instOfNatNat (nat_lit 3)))) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (na\
    t_lit 4)))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.length\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 1, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.night\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 2, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Bool\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.cost\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 3, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Ctx → Act → E\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.KeptBy\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (a : LeanIntent.Answer.{u} W), ∀ (r : LeanIntent.IntentRecord.{u} W), \
    Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (a : LeanIntent.Answer.{u} W) => fun (r : LeanIntent.IntentRecor\
    d.{u} W) => LeanIntent.Answer.KeptBy.match_1.{1} (fun (x : LeanIntent.Consequence.Kind) =>\
    \x20fun (x_1 : LeanIntent.Verdict) => Prop) (@LeanIntent.Consequence.kind.{u} W (@LeanInte\
    nt.Answer.consequence.{u} W a)) (@LeanIntent.Answer.verdict.{u} W a) (fun («_» : Unit) => \
    ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W \
    (@LeanIntent.Answer.consequence.{u} W a) w) (fun («_» : Unit) => @LeanIntent.HasInstance.{\
    u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u} W r w) (Not (@LeanIntent.\
    Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w)))) (fun («_» : Unit) =\
    > @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u\
    } W r w) (@LeanIntent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w))\
    ) (fun («_» : Unit) => ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → Not (@LeanInt\
    ent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Answer.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (consequence : LeanIntent.Consequence.{u} W), ∀ (verdict : LeanIntent.\
    Verdict), LeanIntent.Answer.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W \
    → Prop), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.entailment\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.possibility\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Verdict\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Verdict.confirmed\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Verdict.declined\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.IntentRecord.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause\
    .{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanInte\
    nt.Pred.{u}), LeanIntent.IntentRecord.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Shape\n\
    | \n\
    | An inductive type. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type u → Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Shape.value\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.function\n\
    | \n\
    | ```lean\n\
    | ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.step\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.stepOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.action\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.actionOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u\
    } O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.bundle\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀\
    \x20(rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Member\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Member.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → \
    Out), LeanIntent.Member.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Clause.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Pred\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Pred.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.KeptBy.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : LeanIntent.Consequence.Kind → LeanIntent.Verdict → Sort u_1), ∀ (x : LeanInt\
    ent.Consequence.Kind), ∀ (x_1 : LeanIntent.Verdict), ∀ (h_1 : ∀ («_» : Unit), motive LeanI\
    ntent.Consequence.Kind.entailment LeanIntent.Verdict.confirmed), ∀ (h_2 : ∀ («_» : Unit), \
    motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.declined), ∀ (h_3 : ∀ («_\
    » : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdict.confirmed), ∀\
    \x20(h_4 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdi\
    ct.declined), motive x x_1\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : LeanIntent.Consequence.Kind → LeanIntent.Verdict → Sort u_1) => fun (x : L\
    eanIntent.Consequence.Kind) => fun (x_1 : LeanIntent.Verdict) => fun (h_1 : ∀ («_» : Unit)\
    , motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.confirmed) => fun (h_2 \
    : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.decline\
    d) => fun (h_3 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent\
    .Verdict.confirmed) => fun (h_4 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possi\
    bility LeanIntent.Verdict.declined) => @LeanIntent.Consequence.Kind.casesOn.{u_1} (fun (x_\
    2 : LeanIntent.Consequence.Kind) => motive x_2 x_1) x (@LeanIntent.Verdict.casesOn.{u_1} (\
    fun (x_2 : LeanIntent.Verdict) => motive LeanIntent.Consequence.Kind.entailment x_2) x_1 (\
    h_1 Unit.unit) (h_2 Unit.unit)) (@LeanIntent.Verdict.casesOn.{u_1} (fun (x_2 : LeanIntent.\
    Verdict) => motive LeanIntent.Consequence.Kind.possibility x_2) x_1 (h_3 Unit.unit) (h_4 U\
    nit.unit))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.\
    Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : mo\
    tive LeanIntent.Consequence.Kind.possibility), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Conseq\
    uence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (po\
    ssibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kin\
    d.rec.{u} motive entailment possibility t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Verdict.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Verdict), Sort u}, ∀ (t : LeanIntent.Verdict), ∀ (confirme\
    d : motive LeanIntent.Verdict.confirmed), ∀ (declined : motive LeanIntent.Verdict.declined\
    ), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Verdict), Sort u} => fun (t : LeanIntent.Verdict) => fun\
    \x20(confirmed : motive LeanIntent.Verdict.confirmed) => fun (declined : motive LeanIntent\
    .Verdict.declined) => @LeanIntent.Verdict.rec.{u} motive confirmed declined t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.kind\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.consequence\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 1, counted after the parameters in the type of LeanIntent.Ans\
    wer's constructor, of its argument number 2, a value of LeanIntent.Answer. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Answer.{u} W), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.verdict\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Ans\
    wer's constructor, of its argument number 2, a value of LeanIntent.Answer. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Answer.{u} W), LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Meets\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@Lean\
    Intent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Dom\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.dom\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Cla\
    use's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Props\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.props\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.HasInstance\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)\n\
    | ```\n\
    | \n\
    | ## Lean's own libraries\n\
    | \n\
    | The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: the\
    y are those of Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, which made th\
    is text. A declaration is counted as Lean's own when Lean found the module that declares i\
    t in that release's library directory.\n\
    | \n\
    verdict declined\n\
    ",
  "lean-intent statement 1\n\
    kind answer\n\
    project acorn\n\
    id day-6-r2\n\
    date 2026-11-03\n\
    reference docs/spec-first-pilot.md, The decisions made on the owner's behalf\n\
    by agents\n\
    under agents-below-intent\n\
    record AcornVerif.Intent.DayCycle.dayCycle\n\
    revision 610\n\
    | # The intent record @AcornVerif.Intent.DayCycle.dayCycleFor Unit Acorn.Host.Action UInt8\
    \x20Nat instLTNat\n\
    | \n\
    | Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term \
    its kernel checks, binder names and metadata aside, from the root namespace with nothing o\
    pened. The plain words after it are written by a model and are trusted, not proved.\n\
    | \n\
    | ## Shape\n\
    | \n\
    | ### The subject\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Shape.value.{0} (AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action U\
    Int8 Nat)\n\
    | ```\n\
    | \n\
    | - **Requires:** The subject is a description of a world's day: how many ticks a day last\
    s, which ticks are night, what each action costs at each tick in each situation, and what \
    the agent sees at each tick in each situation. Time is counted in whole ticks from the sta\
    rt of a run, and one clock serves the whole world.\n\
    | - **Rules out:** Nothing by itself; it fixes only what the statements below talk about.\
    \n\
    | - **Still allows:** Any world's situations, actions, sights and energy amounts.\n\
    | - **Freedom O5 leaves:** None of its own. It carries no state from one tick to the next,\
    \x20so it is declared a plain value, of which obligation O4 asks nothing.\n\
    | \n\
    | ## Domain hypotheses\n\
    | \n\
    | None.\n\
    | \n\
    | ## Properties\n\
    | \n\
    | ### each day has a daytime half and a night half of equal length\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => And (@\
    LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w)) (And (@Eq.{1\
    } Nat (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@AcornVerif.Inten\
    t.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) (@OfNat.ofNat.{0} Nat (nat_\
    lit 2) (instOfNatNat (nat_lit 2)))) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_l\
    it 0)))) (@Exists.{1} Nat (fun (start : Nat) => ∀ (t : Nat), Iff (@Eq.{1} Bool (@AcornVeri\
    f.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true) (AcornVe\
    rif.Intent.DayCycle.NightHalf (@AcornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host\
    .Action UInt8 Nat w) start t))))\n\
    | ```\n\
    | \n\
    | - **Requires:** A day lasts a fixed, even number of ticks, at least two. The night is on\
    e unbroken stretch of exactly half of them and the daytime the other half, and every day i\
    s the same.\n\
    | - **Rules out:** A world with no night or no daytime; a day of an odd number of ticks; a\
    \x20night broken into several stretches; days of different lengths.\n\
    | - **Still allows:** Any even day length, and a night that starts at any tick of the day.\
    \n\
    | - **Freedom O5 leaves:** How long a day is and where in it the night starts.\n\
    | \n\
    | ### at night every action costs more energy\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (c :\
    \x20Unit), ∀ (a : Acorn.Host.Action), ∀ (t : Nat), ∀ (t' : Nat), @Eq.{1} Bool (@AcornVerif\
    .Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true → @Eq.{1} \
    Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t') Bo\
    ol.false → @LT.lt.{0} Nat instLTNat (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.\
    Host.Action UInt8 Nat w t' c a) (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.Host\
    .Action UInt8 Nat w t c a)\n\
    | ```\n\
    | \n\
    | - **Requires:** For every action and every situation, the action costs strictly more ene\
    rgy at every night tick than at every daytime tick, waiting included.\n\
    | - **Rules out:** Any action that, in some situation, costs as much or less at some night\
    \x20tick than at some daytime tick.\n\
    | - **Still allows:** Any amount more at night, and a night cost that changes during the n\
    ight, as long as it stays above every daytime cost.\n\
    | - **Freedom O5 leaves:** How much more the night costs, and whether that extra changes d\
    uring the night.\n\
    | \n\
    | ### the agent can always tell day from night\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (t :\
    \x20Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @Eq.{1} UInt8 (@AcornVerif.Intent.Day\
    Cycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t c) (@AcornVerif.Intent.DayCycle.D\
    ayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') → @Eq.{1} Bool (@AcornVerif.Intent.\
    DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) (@AcornVerif.Intent.DayCycle\
    .DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t')\n\
    | ```\n\
    | \n\
    | - **Requires:** Whatever the agent sees always tells it whether it is day or night.\n\
    | - **Rules out:** An agent that sees a day moment and a night moment alike.\n\
    | - **Still allows:** An agent that sees more than that.\n\
    | - **Freedom O5 leaves:** How much more it sees.\n\
    | \n\
    | ### the agent can always see where in the day it is, at least to a quarter of the day\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Exist\
    s.{1} Nat (fun (start : Nat) => ∀ (t : Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @E\
    q.{1} UInt8 (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w \
    t c) (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') \
    → @Eq.{1} Nat (AcornVerif.Intent.DayCycle.quarter (@AcornVerif.Intent.DayCycle.DayWorld.le\
    ngth Unit Acorn.Host.Action UInt8 Nat w) start t) (AcornVerif.Intent.DayCycle.quarter (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) start t'))\n\
    | ```\n\
    | \n\
    | - **Requires:** Whatever the agent sees always tells it which quarter of the day it is i\
    n.\n\
    | - **Rules out:** An agent that sees only whether it is day or night, in a day longer tha\
    n two ticks.\n\
    | - **Still allows:** An agent that sees the quarter, a finer part of the day, or the exac\
    t tick.\n\
    | - **Freedom O5 leaves:** How much more finely than a quarter the agent sees the time of \
    day.\n\
    | \n\
    | ## Vocabulary\n\
    | \n\
    | ### night half, a predicate over `Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) => AcornVerif.Intent.DayCycle.NightHalf \
    (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat Nat) p) (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0}\
    \x20Nat (Prod.{0, 0} Nat Nat) p)) (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0\
    , 0} Nat Nat) p))\n\
    | ```\n\
    | \n\
    | - **Requires:** Tick t is in the night when, counted around a day of the given length fr\
    om where the night starts, it falls in the first half.\n\
    | - **Rules out:** Tick 1 in a day of two ticks whose night starts at tick 0.\n\
    | - **Still allows:** Tick 0 in that day.\n\
    | - **Freedom O5 leaves:** None: it is a definition.\n\
    | \n\
    | ### costs less, a predicate over `Prod.{0, 0} Nat Nat`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} Nat Nat) => @LT.lt.{0} Nat instLTNat (@Prod.fst.{0, 0} Nat Nat p) (\
    @Prod.snd.{0, 0} Nat Nat p)\n\
    | ```\n\
    | \n\
    | - **Requires:** The world's own order on energy amounts.\n\
    | - **Rules out:** Whatever that order rules out.\n\
    | - **Still allows:** Whatever that order allows.\n\
    | - **Freedom O5 leaves:** None of its own.\n\
    | \n\
    | ### in quarter, a predicate over `Prod.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)\
    )`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))) => @Eq.{1} Nat (AcornV\
    erif.Intent.DayCycle.quarter (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))\
    \x20p) (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat Nat) (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat \
    (Prod.{0, 0} Nat Nat)) p)) (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Na\
    t Nat) (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) p)))) (@Prod.snd.{0, \
    0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat Nat) (@Prod.snd.{0, 0} Nat (Prod.{0, 0} \
    Nat (Prod.{0, 0} Nat Nat)) p)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Tick t lies in the given quarter of a day of the given length, counted f\
    rom the given start.\n\
    | - **Rules out:** Tick 0 in quarter 1 of a day of four ticks counted from tick 0.\n\
    | - **Still allows:** Tick 0 in quarter 0 of that day.\n\
    | - **Freedom O5 leaves:** None: it is a definition.\n\
    | \n\
    | ## Consequences\n\
    | \n\
    | ### every day lasts the same even number of ticks, at least two, placed alike, an entail\
    ment: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => And (@\
    LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w)) (And (@Eq.{1\
    } Nat (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@AcornVerif.Inten\
    t.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) (@OfNat.ofNat.{0} Nat (nat_\
    lit 2) (instOfNatNat (nat_lit 2)))) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_l\
    it 0)))) (∀ (t : Nat), @Eq.{1} Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn\
    .Host.Action UInt8 Nat w (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) \
    t (@AcornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w))) (@Aco\
    rnVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Every day lasts the same even number of ticks, at least two, and each da\
    y's night falls at the same ticks of the day.\n\
    | - **Rules out:** Days of different lengths.\n\
    | - **Still allows:** Any one day length shared by all days.\n\
    | - **Freedom O5 leaves:** The length itself.\n\
    | \n\
    | ### every action costs more at any night moment than at any daytime moment, an entailmen\
    t: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (c :\
    \x20Unit), ∀ (a : Acorn.Host.Action), ∀ (t : Nat), ∀ (t' : Nat), @Eq.{1} Bool (@AcornVerif\
    .Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true → @Eq.{1} \
    Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t') Bo\
    ol.false → @LT.lt.{0} Nat instLTNat (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.\
    Host.Action UInt8 Nat w t' c a) (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.Host\
    .Action UInt8 Nat w t c a)\n\
    | ```\n\
    | \n\
    | - **Requires:** Even the cheapest action costs more at any night moment than at any dayt\
    ime moment, in the same situation.\n\
    | - **Rules out:** Any action that is no dearer at some night moment.\n\
    | - **Still allows:** Any extra amount.\n\
    | - **Freedom O5 leaves:** How much more.\n\
    | \n\
    | ### what the agent sees always tells day from night, an entailment: every subject that m\
    eets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => ∀ (t :\
    \x20Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @Eq.{1} UInt8 (@AcornVerif.Intent.Day\
    Cycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t c) (@AcornVerif.Intent.DayCycle.D\
    ayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') → @Eq.{1} Bool (@AcornVerif.Intent.\
    DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) (@AcornVerif.Intent.DayCycle\
    .DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t')\n\
    | ```\n\
    | \n\
    | - **Requires:** From what it sees, the agent can always tell whether it is day or night.\
    \n\
    | - **Rules out:** An agent that cannot tell day from night at some moment.\n\
    | - **Still allows:** An agent that sees more than that.\n\
    | - **Freedom O5 leaves:** How much more it sees.\n\
    | \n\
    | ### what the agent sees always tells it which quarter of the day it is in, an entailment\
    : every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Exist\
    s.{1} Nat (fun (start : Nat) => ∀ (t : Nat), ∀ (t' : Nat), ∀ (c : Unit), ∀ (c' : Unit), @E\
    q.{1} UInt8 (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w \
    t c) (@AcornVerif.Intent.DayCycle.DayWorld.sees Unit Acorn.Host.Action UInt8 Nat w t' c') \
    → @Eq.{1} Nat (AcornVerif.Intent.DayCycle.quarter (@AcornVerif.Intent.DayCycle.DayWorld.le\
    ngth Unit Acorn.Host.Action UInt8 Nat w) start t) (AcornVerif.Intent.DayCycle.quarter (@Ac\
    ornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) start t'))\n\
    | ```\n\
    | \n\
    | - **Requires:** From what it sees, the agent can always tell which quarter of the day it\
    \x20is in.\n\
    | - **Rules out:** An agent that sees only day or night.\n\
    | - **Still allows:** Seeing a finer part of the day, or the exact tick.\n\
    | - **Freedom O5 leaves:** How much finer than a quarter.\n\
    | \n\
    | ### a day may last 1000 ticks, a possibility: some subject that meets the record satisfi\
    es it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Eq.{1\
    } Nat (@AcornVerif.Intent.DayCycle.DayWorld.length Unit Acorn.Host.Action UInt8 Nat w) (@O\
    fNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Nothing more: a world whose day lasts 1000 ticks can meet the record.\n\
    | - **Rules out:** Nothing.\n\
    | - **Still allows:** Short days and long days alike.\n\
    | - **Freedom O5 leaves:** The day's length.\n\
    | \n\
    | ### an action may cost more at one night moment than at another, a possibility: some sub\
    ject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Exist\
    s.{1} Unit (fun (c : Unit) => @Exists.{1} Acorn.Host.Action (fun (a : Acorn.Host.Action) =\
    > @Exists.{1} Nat (fun (t : Nat) => @Exists.{1} Nat (fun (t' : Nat) => And (@Eq.{1} Bool (\
    @AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true\
    ) (And (@Eq.{1} Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UI\
    nt8 Nat w t') Bool.true) (@Ne.{1} Nat (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acor\
    n.Host.Action UInt8 Nat w t c a) (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.Hos\
    t.Action UInt8 Nat w t' c a)))))))\n\
    | ```\n\
    | \n\
    | - **Requires:** Nothing more: an action may cost more at one night moment than at anothe\
    r, as long as every night cost is above every daytime cost.\n\
    | - **Rules out:** Nothing.\n\
    | - **Still allows:** A night that is dearer at midnight than at dusk.\n\
    | - **Freedom O5 leaves:** Whether the night's extra changes during the night.\n\
    | \n\
    | ## Definitions the record's meaning reaches\n\
    | \n\
    | These are not statements of the record: each is a declaration that a statement above dep\
    ends on, or that says what it is for a subject to meet the record and for a consequence to\
    \x20hold of it as shown, with everything those depend on in turn. Each is printed in full:\
    \x20its type, a definition's value, or for a definition by structural or well-founded recu\
    rsion the equation that determines it, and an inductive type's constructors, which for a s\
    tructure are its fields; a theorem's proof and an opaque constant's value are not, since n\
    o term that uses them depends on more than their types. Their plain words are those of the\
    \x20statements that use them.\n\
    | \n\
    | ### Acorn.Host.Action\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### Acorn.Host.Action.north\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.south\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.east\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.west\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.wait\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.harvest\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftAxe\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftBoat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.eat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Shape\n\
    | \n\
    | An inductive type. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type u → Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Shape.value\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.function\n\
    | \n\
    | ```lean\n\
    | ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.step\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.stepOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.action\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.actionOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u\
    } O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.bundle\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀\
    \x20(rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Member\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Member.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → \
    Out), LeanIntent.Member.{u} W\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (Ctx : Type), ∀ (Act : Type), ∀ (Obs : Type), ∀ (E : Type), Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 4 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.DayCycle.DayWorld.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (length : Nat), ∀ (night\
    \x20: Nat → Bool), ∀ (cost : Nat → Ctx → Act → E), ∀ (sees : Nat → Ctx → Obs), AcornVerif.\
    Intent.DayCycle.DayWorld Ctx Act Obs E\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.length\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 1, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.night\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 2, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Bool\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.NightHalf\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (length : Nat), ∀ (start : Nat), ∀ (t : Nat), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (length : Nat) => fun (start : Nat) => fun (t : Nat) => @LT.lt.{0} Nat instLTNat (@H\
    Mod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@HAdd.hAdd.{0, 0, 0} Nat N\
    at Nat (@instHAdd.{0} Nat instAddNat) t start) length) (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (\
    @instHDiv.{0} Nat Nat.instDiv) length (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat\
    _lit 2))))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.cost\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 3, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Ctx → Act → E\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.sees\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 4, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Ctx → Obs\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.quarter\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (length : Nat), ∀ (start : Nat), ∀ (t : Nat), Nat\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (length : Nat) => fun (start : Nat) => fun (t : Nat) => @HDiv.hDiv.{0, 0, 0} Nat Nat\
    \x20Nat (@instHDiv.{0} Nat Nat.instDiv) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} N\
    at instMulNat) (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) (@HAdd.hA\
    dd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t start) length) (@OfNat.ofNat.{0}\
    \x20Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) length\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Meets\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@Lean\
    Intent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.IntentRecord.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause\
    .{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanInte\
    nt.Pred.{u}), LeanIntent.IntentRecord.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Clause.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Pred\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Pred.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Dom\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.dom\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Cla\
    use's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Props\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.props\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.HoldsOf\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (c : LeanIntent.Consequence.{u} W), ∀ (r : LeanIntent.IntentRecord.{u}\
    \x20W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (c : LeanIntent.Consequence.{u} W) => fun (r : LeanIntent.Intent\
    Record.{u} W) => LeanIntent.Consequence.HoldsOf.match_1.{1} (fun (x : LeanIntent.Consequen\
    ce.Kind) => Prop) (@LeanIntent.Consequence.kind.{u} W c) (fun («_» : Unit) => ∀ (w : W), @\
    LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W c w) (fun («\
    _» : Unit) => @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRec\
    ord.Meets.{u} W r w) (@LeanIntent.Consequence.holds.{u} W c w)))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W \
    → Prop), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.entailment\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.possibility\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.HoldsOf.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : LeanIntent.Consequence.Kind → Sort u_1), ∀ (x : LeanIntent.Consequence.Kind)\
    , ∀ (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment), ∀ (h_2 : ∀ («_»\
    \x20: Unit), motive LeanIntent.Consequence.Kind.possibility), motive x\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : LeanIntent.Consequence.Kind → Sort u_1) => fun (x : LeanIntent.Consequence\
    .Kind) => fun (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment) => fun\
    \x20(h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.\
    Consequence.Kind.casesOn.{u_1} (fun (x_1 : LeanIntent.Consequence.Kind) => motive x_1) x (\
    h_1 Unit.unit) (h_2 Unit.unit)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.\
    Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : mo\
    tive LeanIntent.Consequence.Kind.possibility), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Conseq\
    uence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (po\
    ssibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kin\
    d.rec.{u} motive entailment possibility t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.kind\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.HasInstance\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)\n\
    | ```\n\
    | \n\
    | ## Lean's own libraries\n\
    | \n\
    | The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: the\
    y are those of Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, which made th\
    is text. A declaration is counted as Lean's own when Lean found the module that declares i\
    t in that release's library directory.\n\
    | \n\
    consequence an action may cost more at one night moment than at another\n\
    shown as possibility\n\
    predicate 472\n\
    | # A consequence's predicate\n\
    | \n\
    | Printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks,\
    \x20binder names and metadata aside, from the root namespace with nothing opened.\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.DayCycle.DayWorld Unit Acorn.Host.Action UInt8 Nat) => @Exist\
    s.{1} Unit (fun (c : Unit) => @Exists.{1} Acorn.Host.Action (fun (a : Acorn.Host.Action) =\
    > @Exists.{1} Nat (fun (t : Nat) => @Exists.{1} Nat (fun (t' : Nat) => And (@Eq.{1} Bool (\
    @AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UInt8 Nat w t) Bool.true\
    ) (And (@Eq.{1} Bool (@AcornVerif.Intent.DayCycle.DayWorld.night Unit Acorn.Host.Action UI\
    nt8 Nat w t') Bool.true) (@Ne.{1} Nat (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acor\
    n.Host.Action UInt8 Nat w t c a) (@AcornVerif.Intent.DayCycle.DayWorld.cost Unit Acorn.Hos\
    t.Action UInt8 Nat w t' c a)))))))\n\
    | ```\n\
    | \n\
    | ## Definitions the predicate reaches\n\
    | \n\
    | Each is printed in full, as in the rendering of a record, with what an answer to it asks\
    \x20of every later revision (`LeanIntent.Answer.KeptBy`).\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (Ctx : Type), ∀ (Act : Type), ∀ (Obs : Type), ∀ (E : Type), Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 4 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.DayCycle.DayWorld.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (length : Nat), ∀ (night\
    \x20: Nat → Bool), ∀ (cost : Nat → Ctx → Act → E), ∀ (sees : Nat → Ctx → Obs), AcornVerif.\
    Intent.DayCycle.DayWorld Ctx Act Obs E\n\
    | ```\n\
    | \n\
    | ### Acorn.Host.Action\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### Acorn.Host.Action.north\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.south\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.east\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.west\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.wait\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.harvest\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftAxe\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.craftBoat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | #### Acorn.Host.Action.eat\n\
    | \n\
    | ```lean\n\
    | Acorn.Host.Action\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.night\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 2, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Bool\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.DayCycle.DayWorld.cost\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 5 argume\
    nts and returns field number 3, counted after the parameters in the type of AcornVerif.Int\
    ent.DayCycle.DayWorld's constructor, of its argument number 5, a value of AcornVerif.Inten\
    t.DayCycle.DayWorld. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Ctx : Type}, ∀ {Act : Type}, ∀ {Obs : Type}, ∀ {E : Type}, ∀ (self : AcornVerif.Inten\
    t.DayCycle.DayWorld Ctx Act Obs E), Nat → Ctx → Act → E\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.KeptBy\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (a : LeanIntent.Answer.{u} W), ∀ (r : LeanIntent.IntentRecord.{u} W), \
    Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (a : LeanIntent.Answer.{u} W) => fun (r : LeanIntent.IntentRecor\
    d.{u} W) => LeanIntent.Answer.KeptBy.match_1.{1} (fun (x : LeanIntent.Consequence.Kind) =>\
    \x20fun (x_1 : LeanIntent.Verdict) => Prop) (@LeanIntent.Consequence.kind.{u} W (@LeanInte\
    nt.Answer.consequence.{u} W a)) (@LeanIntent.Answer.verdict.{u} W a) (fun («_» : Unit) => \
    ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W \
    (@LeanIntent.Answer.consequence.{u} W a) w) (fun («_» : Unit) => @LeanIntent.HasInstance.{\
    u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u} W r w) (Not (@LeanIntent.\
    Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w)))) (fun («_» : Unit) =\
    > @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u\
    } W r w) (@LeanIntent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w))\
    ) (fun («_» : Unit) => ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → Not (@LeanInt\
    ent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Answer.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (consequence : LeanIntent.Consequence.{u} W), ∀ (verdict : LeanIntent.\
    Verdict), LeanIntent.Answer.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W \
    → Prop), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.entailment\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.possibility\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Verdict\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Verdict.confirmed\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Verdict.declined\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.IntentRecord.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause\
    .{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanInte\
    nt.Pred.{u}), LeanIntent.IntentRecord.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Shape\n\
    | \n\
    | An inductive type. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type u → Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Shape.value\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.function\n\
    | \n\
    | ```lean\n\
    | ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.step\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.stepOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.action\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.actionOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u\
    } O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.bundle\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀\
    \x20(rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Member\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Member.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → \
    Out), LeanIntent.Member.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Clause.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Pred\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Pred.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.KeptBy.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : LeanIntent.Consequence.Kind → LeanIntent.Verdict → Sort u_1), ∀ (x : LeanInt\
    ent.Consequence.Kind), ∀ (x_1 : LeanIntent.Verdict), ∀ (h_1 : ∀ («_» : Unit), motive LeanI\
    ntent.Consequence.Kind.entailment LeanIntent.Verdict.confirmed), ∀ (h_2 : ∀ («_» : Unit), \
    motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.declined), ∀ (h_3 : ∀ («_\
    » : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdict.confirmed), ∀\
    \x20(h_4 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdi\
    ct.declined), motive x x_1\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : LeanIntent.Consequence.Kind → LeanIntent.Verdict → Sort u_1) => fun (x : L\
    eanIntent.Consequence.Kind) => fun (x_1 : LeanIntent.Verdict) => fun (h_1 : ∀ («_» : Unit)\
    , motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.confirmed) => fun (h_2 \
    : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.decline\
    d) => fun (h_3 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent\
    .Verdict.confirmed) => fun (h_4 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possi\
    bility LeanIntent.Verdict.declined) => @LeanIntent.Consequence.Kind.casesOn.{u_1} (fun (x_\
    2 : LeanIntent.Consequence.Kind) => motive x_2 x_1) x (@LeanIntent.Verdict.casesOn.{u_1} (\
    fun (x_2 : LeanIntent.Verdict) => motive LeanIntent.Consequence.Kind.entailment x_2) x_1 (\
    h_1 Unit.unit) (h_2 Unit.unit)) (@LeanIntent.Verdict.casesOn.{u_1} (fun (x_2 : LeanIntent.\
    Verdict) => motive LeanIntent.Consequence.Kind.possibility x_2) x_1 (h_3 Unit.unit) (h_4 U\
    nit.unit))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.\
    Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : mo\
    tive LeanIntent.Consequence.Kind.possibility), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Conseq\
    uence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (po\
    ssibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kin\
    d.rec.{u} motive entailment possibility t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Verdict.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Verdict), Sort u}, ∀ (t : LeanIntent.Verdict), ∀ (confirme\
    d : motive LeanIntent.Verdict.confirmed), ∀ (declined : motive LeanIntent.Verdict.declined\
    ), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Verdict), Sort u} => fun (t : LeanIntent.Verdict) => fun\
    \x20(confirmed : motive LeanIntent.Verdict.confirmed) => fun (declined : motive LeanIntent\
    .Verdict.declined) => @LeanIntent.Verdict.rec.{u} motive confirmed declined t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.kind\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.consequence\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 1, counted after the parameters in the type of LeanIntent.Ans\
    wer's constructor, of its argument number 2, a value of LeanIntent.Answer. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Answer.{u} W), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.verdict\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Ans\
    wer's constructor, of its argument number 2, a value of LeanIntent.Answer. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Answer.{u} W), LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Meets\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@Lean\
    Intent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Dom\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.dom\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Cla\
    use's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Props\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.props\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.HasInstance\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)\n\
    | ```\n\
    | \n\
    | ## Lean's own libraries\n\
    | \n\
    | The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: the\
    y are those of Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, which made th\
    is text. A declaration is counted as Lean's own when Lean found the module that declares i\
    t in that release's library directory.\n\
    | \n\
    verdict confirmed\n\
    ",
  "lean-intent statement 1\n\
    kind answer\n\
    project acorn\n\
    id hash-1-r2\n\
    date 2026-11-03\n\
    reference docs/spec-first-pilot.md, The decisions made on the owner's behalf\n\
    by agents\n\
    under agents-below-intent\n\
    record AcornVerif.Intent.Hash.hashes\n\
    revision 740\n\
    | # The intent record AcornVerif.Intent.Hash.hashes\n\
    | \n\
    | Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term \
    its kernel checks, binder names and metadata aside, from the root namespace with nothing o\
    pened. The plain words after it are written by a model and are trusted, not proved.\n\
    | \n\
    | ## Shape\n\
    | \n\
    | ### The subject\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Shape.value.{0} AcornVerif.Intent.Hash.Hashes\n\
    | ```\n\
    | \n\
    | - **Requires:** The subject is the pair of hash functions, each taking three 64-bit inpu\
    ts to one 64-bit spot.\n\
    | - **Rules out:** Nothing by itself.\n\
    | - **Still allows:** Any pair of such functions, until the properties narrow it.\n\
    | - **Freedom O5 leaves:** None of its own. The pair carries no state from one call to the\
    \x20next, so it is declared a plain value, of which obligation O4 asks nothing.\n\
    | \n\
    | ## Domain hypotheses\n\
    | \n\
    | None.\n\
    | \n\
    | ## Properties\n\
    | \n\
    | ### changing any one input always moves the spot\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => And (AcornVerif.Intent.Hash.OneInputMoves (Ac\
    ornVerif.Intent.Hash.Hashes.hash2 w)) (AcornVerif.Intent.Hash.OneInputMoves (AcornVerif.In\
    tent.Hash.Hashes.hash3 w))\n\
    | ```\n\
    | \n\
    | - **Requires:** In each function, changing exactly one input, the others kept, always ch\
    anges the spot: never the same spot, not merely rarely.\n\
    | - **Rules out:** A function that ignores an input, and one where two values of one input\
    \x20share a spot for some values of the others.\n\
    | - **Still allows:** Any amount of sharing between inputs that differ in two or three pla\
    ces.\n\
    | - **Freedom O5 leaves:** Everything about inputs that differ in more than one place.\n\
    | \n\
    | ### no fixed rule of reordering and shifting the inputs keeps every spot\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => And (AcornVerif.Intent.Hash.NoRuleKeepsSpots \
    (AcornVerif.Intent.Hash.Hashes.hash2 w)) (AcornVerif.Intent.Hash.NoRuleKeepsSpots (AcornVe\
    rif.Intent.Hash.Hashes.hash3 w))\n\
    | ```\n\
    | \n\
    | - **Requires:** No fixed rule moves every input to a different input in the same spot. A\
    \x20rule here puts the three inputs in some order, then adds a fixed amount to each, or fl\
    ips fixed bits of each.\n\
    | - **Rules out:** Combining the inputs by plain exclusive or or plain addition, where swa\
    pping two inputs keeps the spot; and any function where adding the same amounts, or flippi\
    ng the same bits, keeps every spot.\n\
    | - **Still allows:** Rules of other kinds, such as multiplying the inputs by fixed number\
    s; and any number of inputs sharing spots without a fixed rule behind it.\n\
    | - **Freedom O5 leaves:** How often inputs share spots overall: the record bounds no rate\
    .\n\
    | \n\
    | ## Vocabulary\n\
    | \n\
    | ### same spot, a predicate over `Prod.{0, 0} UInt64 UInt64`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} UInt64 UInt64) => @Eq.{1} UInt64 (@Prod.fst.{0, 0} UInt64 UInt64 p)\
    \x20(@Prod.snd.{0, 0} UInt64 UInt64 p)\n\
    | ```\n\
    | \n\
    | - **Requires:** Two spots are the same 64-bit value.\n\
    | - **Rules out:** Spots 0 and 1.\n\
    | - **Still allows:** Spots 0 and 0.\n\
    | - **Freedom O5 leaves:** None: it is equality.\n\
    | \n\
    | ## Consequences\n\
    | \n\
    | ### changing any one input always moves the spot, an entailment: every subject that meet\
    s the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => And (AcornVerif.Intent.Hash.OneInputMoves (Ac\
    ornVerif.Intent.Hash.Hashes.hash2 w)) (AcornVerif.Intent.Hash.OneInputMoves (AcornVerif.In\
    tent.Hash.Hashes.hash3 w))\n\
    | ```\n\
    | \n\
    | - **Requires:** Changing any one input always moves the spot, in both functions.\n\
    | - **Rules out:** Any single changed input landing in the same spot.\n\
    | - **Still allows:** Inputs that differ in two or three places sharing a spot.\n\
    | - **Freedom O5 leaves:** None beyond the property's.\n\
    | \n\
    | ### no fixed rule of reordering and shifting the inputs keeps every spot, an entailment:\
    \x20every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => And (AcornVerif.Intent.Hash.NoRuleKeepsSpots \
    (AcornVerif.Intent.Hash.Hashes.hash2 w)) (AcornVerif.Intent.Hash.NoRuleKeepsSpots (AcornVe\
    rif.Intent.Hash.Hashes.hash3 w))\n\
    | ```\n\
    | \n\
    | - **Requires:** No fixed reordering and shifting of the inputs keeps every spot.\n\
    | - **Rules out:** Systematic sharing by any such rule.\n\
    | - **Still allows:** Sharing by rules of other kinds, and sharing with no fixed rule.\n\
    | - **Freedom O5 leaves:** Which rules count as systematic beyond these.\n\
    | \n\
    | ### neither function combines its inputs by plain exclusive or or plain addition, an ent\
    ailment: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => And (@Ne.{1} (AcornVerif.Intent.Hash.Inputs →\
    \x20UInt64) (AcornVerif.Intent.Hash.Hashes.hash2 w) AcornVerif.Intent.Hash.xorAll) (And (@\
    Ne.{1} (AcornVerif.Intent.Hash.Inputs → UInt64) (AcornVerif.Intent.Hash.Hashes.hash2 w) Ac\
    ornVerif.Intent.Hash.addAll) (And (@Ne.{1} (AcornVerif.Intent.Hash.Inputs → UInt64) (Acorn\
    Verif.Intent.Hash.Hashes.hash3 w) AcornVerif.Intent.Hash.xorAll) (@Ne.{1} (AcornVerif.Inte\
    nt.Hash.Inputs → UInt64) (AcornVerif.Intent.Hash.Hashes.hash3 w) AcornVerif.Intent.Hash.ad\
    dAll)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Neither function combines its three inputs by plain exclusive or or by p\
    lain addition.\n\
    | - **Rules out:** Those two combinations, since swapping two inputs keeps their spot.\n\
    | - **Still allows:** Combinations that mix the inputs before combining them.\n\
    | - **Freedom O5 leaves:** None that this consequence adds.\n\
    | \n\
    | ### the same inputs always give the same spot, an entailment: every subject that meets t\
    he record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => ∀ (x : AcornVerif.Intent.Hash.Inputs), ∀ (y :\
    \x20AcornVerif.Intent.Hash.Inputs), @Eq.{1} AcornVerif.Intent.Hash.Inputs x y → And (@Eq.{\
    1} UInt64 (AcornVerif.Intent.Hash.Hashes.hash2 w x) (AcornVerif.Intent.Hash.Hashes.hash2 w\
    \x20y)) (@Eq.{1} UInt64 (AcornVerif.Intent.Hash.Hashes.hash3 w x) (AcornVerif.Intent.Hash.\
    Hashes.hash3 w y))\n\
    | ```\n\
    | \n\
    | - **Requires:** The same inputs always give the same spot, so a run can be replayed.\n\
    | - **Rules out:** Nothing: every function of this type meets it.\n\
    | - **Still allows:** Every pair of functions.\n\
    | - **Freedom O5 leaves:** None. It holds by construction; replay further trusts the compi\
    ler and the machine to compute 64-bit words alike everywhere.\n\
    | \n\
    | ## Definitions the record's meaning reaches\n\
    | \n\
    | These are not statements of the record: each is a declaration that a statement above dep\
    ends on, or that says what it is for a subject to meet the record and for a consequence to\
    \x20hold of it as shown, with everything those depend on in turn. Each is printed in full:\
    \x20its type, a definition's value, or for a definition by structural or well-founded recu\
    rsion the equation that determines it, and an inductive type's constructors, which for a s\
    tructure are its fields; a theorem's proof and an opaque constant's value are not, since n\
    o term that uses them depends on more than their types. Their plain words are those of the\
    \x20statements that use them.\n\
    | \n\
    | ### LeanIntent.Shape\n\
    | \n\
    | An inductive type. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type u → Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Shape.value\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.function\n\
    | \n\
    | ```lean\n\
    | ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.step\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.stepOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.action\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.actionOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u\
    } O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.bundle\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀\
    \x20(rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Member\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Member.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → \
    Out), LeanIntent.Member.{u} W\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Hashes\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Hashes.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (hash2 : AcornVerif.Intent.Hash.Inputs → UInt64), ∀ (hash3 : AcornVerif.Intent.Hash.In\
    puts → UInt64), AcornVerif.Intent.Hash.Hashes\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Inputs\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | Prod.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.OneInputMoves\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (f : AcornVerif.Intent.Hash.Inputs → UInt64), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (f : AcornVerif.Intent.Hash.Inputs → UInt64) => And (∀ (a : UInt64), ∀ (a' : UInt64)\
    , ∀ (b : UInt64), ∀ (c : UInt64), @Eq.{1} UInt64 (f (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} U\
    Int64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) (f (@Prod.mk.{0, 0} UInt64 (Prod.{0,\
    \x200} UInt64 UInt64) a' (@Prod.mk.{0, 0} UInt64 UInt64 b c))) → @Eq.{1} UInt64 a a') (And\
    \x20(∀ (a : UInt64), ∀ (b : UInt64), ∀ (b' : UInt64), ∀ (c : UInt64), @Eq.{1} UInt64 (f (@\
    Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) \
    (f (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b'\
    \x20c))) → @Eq.{1} UInt64 b b') (∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), ∀ (c' : U\
    Int64), @Eq.{1} UInt64 (f (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.\
    {0, 0} UInt64 UInt64 b c))) (f (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Pro\
    d.mk.{0, 0} UInt64 UInt64 b c'))) → @Eq.{1} UInt64 c c'))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Hashes.hash2\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 1, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Hashes's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash\
    .Hashes. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Hashes), AcornVerif.Intent.Hash.Inputs → UInt64\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Hashes.hash3\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 2, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Hashes's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash\
    .Hashes. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Hashes), AcornVerif.Intent.Hash.Inputs → UInt64\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.NoRuleKeepsSpots\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (f : AcornVerif.Intent.Hash.Inputs → UInt64), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (f : AcornVerif.Intent.Hash.Inputs → UInt64) => ∀ (r : AcornVerif.Intent.Hash.Rule),\
    \x20AcornVerif.Intent.Hash.Rule.Moves r → @Exists.{1} AcornVerif.Intent.Hash.Inputs (fun (\
    x : AcornVerif.Intent.Hash.Inputs) => @Ne.{1} UInt64 (f (AcornVerif.Intent.Hash.Rule.apply\
    \x20r x)) (f x))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Rule.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (order : AcornVerif.Intent.Hash.Order), ∀ (shift : AcornVerif.Intent.Hash.Shift), ∀ (a\
    mount : AcornVerif.Intent.Hash.Inputs), AcornVerif.Intent.Hash.Rule\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Order\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.abc\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.bac\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.acb\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.cba\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.bca\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.cab\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Shift\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Shift.flip\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Shift\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Shift.add\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Shift\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.Moves\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (r : AcornVerif.Intent.Hash.Rule), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (r : AcornVerif.Intent.Hash.Rule) => Not (And (@Eq.{1} AcornVerif.Intent.Hash.Order \
    (AcornVerif.Intent.Hash.Rule.order r) AcornVerif.Intent.Hash.Order.abc) (@Eq.{1} AcornVeri\
    f.Intent.Hash.Inputs (AcornVerif.Intent.Hash.Rule.amount r) (@Prod.mk.{0, 0} UInt64 (Prod.\
    {0, 0} UInt64 UInt64) (@OfNat.ofNat.{0} UInt64 (nat_lit 0) (@UInt64.instOfNat (nat_lit 0))\
    ) (@Prod.mk.{0, 0} UInt64 UInt64 (@OfNat.ofNat.{0} UInt64 (nat_lit 0) (@UInt64.instOfNat (\
    nat_lit 0))) (@OfNat.ofNat.{0} UInt64 (nat_lit 0) (@UInt64.instOfNat (nat_lit 0)))))))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.order\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 1, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Rule's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash.R\
    ule. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Rule), AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.amount\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 3, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Rule's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash.R\
    ule. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Rule), AcornVerif.Intent.Hash.Inputs\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.apply\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (r : AcornVerif.Intent.Hash.Rule), ∀ (x : AcornVerif.Intent.Hash.Inputs), AcornVerif.I\
    ntent.Hash.Inputs\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (r : AcornVerif.Intent.Hash.Rule) => fun (x : AcornVerif.Intent.Hash.Inputs) => Acor\
    nVerif.Intent.Hash.Rule.apply.match_1.{1} (fun (x_1 : AcornVerif.Intent.Hash.Inputs) => Ac\
    ornVerif.Intent.Hash.Inputs) (AcornVerif.Intent.Hash.Order.apply (AcornVerif.Intent.Hash.R\
    ule.order r) x) (fun (a : UInt64) => fun (b : UInt64) => fun (c : UInt64) => @Prod.mk.{0, \
    0} UInt64 (Prod.{0, 0} UInt64 UInt64) (AcornVerif.Intent.Hash.Shift.apply (AcornVerif.Inte\
    nt.Hash.Rule.shift r) a (@Prod.fst.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (AcornVerif.I\
    ntent.Hash.Rule.amount r))) (@Prod.mk.{0, 0} UInt64 UInt64 (AcornVerif.Intent.Hash.Shift.a\
    pply (AcornVerif.Intent.Hash.Rule.shift r) b (@Prod.fst.{0, 0} UInt64 UInt64 (@Prod.snd.{0\
    , 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (AcornVerif.Intent.Hash.Rule.amount r)))) (AcornVe\
    rif.Intent.Hash.Shift.apply (AcornVerif.Intent.Hash.Rule.shift r) c (@Prod.snd.{0, 0} UInt\
    64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (AcornVerif.Intent.Hash.Rul\
    e.amount r))))))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.apply.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : AcornVerif.Intent.Hash.Inputs → Sort u_1), ∀ (x : AcornVerif.Intent.Hash.Inp\
    uts), ∀ (h_1 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive (@Prod.mk.{0, 0} UIn\
    t64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))), motive x\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : AcornVerif.Intent.Hash.Inputs → Sort u_1) => fun (x : AcornVerif.Intent.Ha\
    sh.Inputs) => fun (h_1 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive (@Prod.mk.\
    {0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) => @Prod\
    .casesOn.{u_1, 0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (fun (x_1 : AcornVerif.Intent.Hash\
    .Inputs) => motive x_1) x (fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => \
    @Prod.casesOn.{u_1, 0, 0} UInt64 UInt64 (fun (x_1 : Prod.{0, 0} UInt64 UInt64) => motive (\
    @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_1)) snd (fun (x_1 : UInt64) => fu\
    n (x_2 : UInt64) => h_1 fst x_1 x_2))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Order.apply\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order → AcornVerif.Intent.Hash.Inputs → AcornVerif.Intent.Hash.In\
    puts\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (x : AcornVerif.Intent.Hash.Order) => fun (x_1 : AcornVerif.Intent.Hash.Inputs) => A\
    cornVerif.Intent.Hash.Order.apply.match_1.{1} (fun (x_2 : AcornVerif.Intent.Hash.Order) =>\
    \x20fun (x_3 : AcornVerif.Intent.Hash.Inputs) => AcornVerif.Intent.Hash.Inputs) x x_1 (fun\
    \x20(a : UInt64) => fun (b : UInt64) => fun (c : UInt64) => @Prod.mk.{0, 0} UInt64 (Prod.{\
    0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c)) (fun (a : UInt64) => fun (b : \
    UInt64) => fun (c : UInt64) => @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) b (@Prod\
    .mk.{0, 0} UInt64 UInt64 a c)) (fun (a : UInt64) => fun (b : UInt64) => fun (c : UInt64) =\
    > @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 c b)\
    ) (fun (a : UInt64) => fun (b : UInt64) => fun (c : UInt64) => @Prod.mk.{0, 0} UInt64 (Pro\
    d.{0, 0} UInt64 UInt64) c (@Prod.mk.{0, 0} UInt64 UInt64 b a)) (fun (a : UInt64) => fun (b\
    \x20: UInt64) => fun (c : UInt64) => @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) b \
    (@Prod.mk.{0, 0} UInt64 UInt64 c a)) (fun (a : UInt64) => fun (b : UInt64) => fun (c : UIn\
    t64) => @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) c (@Prod.mk.{0, 0} UInt64 UInt6\
    4 a b))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Order.apply.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : AcornVerif.Intent.Hash.Order → AcornVerif.Intent.Hash.Inputs → Sort u_1), ∀ \
    (x : AcornVerif.Intent.Hash.Order), ∀ (x_1 : AcornVerif.Intent.Hash.Inputs), ∀ (h_1 : ∀ (a\
    \x20: UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Order.abc (@P\
    rod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))), \
    ∀ (h_2 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Ord\
    er.bac (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt6\
    4 b c))), ∀ (h_3 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Inten\
    t.Hash.Order.acb (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UI\
    nt64 UInt64 b c))), ∀ (h_4 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornV\
    erif.Intent.Hash.Order.cba (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk\
    .{0, 0} UInt64 UInt64 b c))), ∀ (h_5 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), mot\
    ive AcornVerif.Intent.Hash.Order.bca (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a\
    \x20(@Prod.mk.{0, 0} UInt64 UInt64 b c))), ∀ (h_6 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c :\
    \x20UInt64), motive AcornVerif.Intent.Hash.Order.cab (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} \
    UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))), motive x x_1\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : AcornVerif.Intent.Hash.Order → AcornVerif.Intent.Hash.Inputs → Sort u_1) =\
    > fun (x : AcornVerif.Intent.Hash.Order) => fun (x_1 : AcornVerif.Intent.Hash.Inputs) => f\
    un (h_1 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Or\
    der.abc (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt\
    64 b c))) => fun (h_2 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.\
    Intent.Hash.Order.bac (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, \
    0} UInt64 UInt64 b c))) => fun (h_3 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), moti\
    ve AcornVerif.Intent.Hash.Order.acb (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a \
    (@Prod.mk.{0, 0} UInt64 UInt64 b c))) => fun (h_4 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c :\
    \x20UInt64), motive AcornVerif.Intent.Hash.Order.cba (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} \
    UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) => fun (h_5 : ∀ (a : UInt64), ∀ (b \
    : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Order.bca (@Prod.mk.{0, 0} UInt64\
    \x20(Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) => fun (h_6 : ∀ (a\
    \x20: UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Order.cab (@P\
    rod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) =\
    > @AcornVerif.Intent.Hash.Order.casesOn.{u_1} (fun (x_2 : AcornVerif.Intent.Hash.Order) =>\
    \x20motive x_2 x_1) x (@Prod.casesOn.{u_1, 0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (fun (\
    x_2 : AcornVerif.Intent.Hash.Inputs) => motive AcornVerif.Intent.Hash.Order.abc x_2) x_1 (\
    fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => @Prod.casesOn.{u_1, 0, 0} U\
    Int64 UInt64 (fun (x_2 : Prod.{0, 0} UInt64 UInt64) => motive AcornVerif.Intent.Hash.Order\
    .abc (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_2)) snd (fun (x_2 : UInt64)\
    \x20=> fun (x_3 : UInt64) => h_1 fst x_2 x_3))) (@Prod.casesOn.{u_1, 0, 0} UInt64 (Prod.{0\
    , 0} UInt64 UInt64) (fun (x_2 : AcornVerif.Intent.Hash.Inputs) => motive AcornVerif.Intent\
    .Hash.Order.bac x_2) x_1 (fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => @\
    Prod.casesOn.{u_1, 0, 0} UInt64 UInt64 (fun (x_2 : Prod.{0, 0} UInt64 UInt64) => motive Ac\
    ornVerif.Intent.Hash.Order.bac (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_2\
    )) snd (fun (x_2 : UInt64) => fun (x_3 : UInt64) => h_2 fst x_2 x_3))) (@Prod.casesOn.{u_1\
    , 0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (fun (x_2 : AcornVerif.Intent.Hash.Inputs) => m\
    otive AcornVerif.Intent.Hash.Order.acb x_2) x_1 (fun (fst : UInt64) => fun (snd : Prod.{0,\
    \x200} UInt64 UInt64) => @Prod.casesOn.{u_1, 0, 0} UInt64 UInt64 (fun (x_2 : Prod.{0, 0} U\
    Int64 UInt64) => motive AcornVerif.Intent.Hash.Order.acb (@Prod.mk.{0, 0} UInt64 (Prod.{0,\
    \x200} UInt64 UInt64) fst x_2)) snd (fun (x_2 : UInt64) => fun (x_3 : UInt64) => h_3 fst x\
    _2 x_3))) (@Prod.casesOn.{u_1, 0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (fun (x_2 : AcornV\
    erif.Intent.Hash.Inputs) => motive AcornVerif.Intent.Hash.Order.cba x_2) x_1 (fun (fst : U\
    Int64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => @Prod.casesOn.{u_1, 0, 0} UInt64 UInt64\
    \x20(fun (x_2 : Prod.{0, 0} UInt64 UInt64) => motive AcornVerif.Intent.Hash.Order.cba (@Pr\
    od.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_2)) snd (fun (x_2 : UInt64) => fun (\
    x_3 : UInt64) => h_4 fst x_2 x_3))) (@Prod.casesOn.{u_1, 0, 0} UInt64 (Prod.{0, 0} UInt64 \
    UInt64) (fun (x_2 : AcornVerif.Intent.Hash.Inputs) => motive AcornVerif.Intent.Hash.Order.\
    bca x_2) x_1 (fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => @Prod.casesOn\
    .{u_1, 0, 0} UInt64 UInt64 (fun (x_2 : Prod.{0, 0} UInt64 UInt64) => motive AcornVerif.Int\
    ent.Hash.Order.bca (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_2)) snd (fun \
    (x_2 : UInt64) => fun (x_3 : UInt64) => h_5 fst x_2 x_3))) (@Prod.casesOn.{u_1, 0, 0} UInt\
    64 (Prod.{0, 0} UInt64 UInt64) (fun (x_2 : AcornVerif.Intent.Hash.Inputs) => motive AcornV\
    erif.Intent.Hash.Order.cab x_2) x_1 (fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 U\
    Int64) => @Prod.casesOn.{u_1, 0, 0} UInt64 UInt64 (fun (x_2 : Prod.{0, 0} UInt64 UInt64) =\
    > motive AcornVerif.Intent.Hash.Order.cab (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt\
    64) fst x_2)) snd (fun (x_2 : UInt64) => fun (x_3 : UInt64) => h_6 fst x_2 x_3)))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Order.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : AcornVerif.Intent.Hash.Order), Sort u}, ∀ (t : AcornVerif.Intent.Hash\
    .Order), ∀ (abc : motive AcornVerif.Intent.Hash.Order.abc), ∀ (bac : motive AcornVerif.Int\
    ent.Hash.Order.bac), ∀ (acb : motive AcornVerif.Intent.Hash.Order.acb), ∀ (cba : motive Ac\
    ornVerif.Intent.Hash.Order.cba), ∀ (bca : motive AcornVerif.Intent.Hash.Order.bca), ∀ (cab\
    \x20: motive AcornVerif.Intent.Hash.Order.cab), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : AcornVerif.Intent.Hash.Order), Sort u} => fun (t : AcornVerif.Inten\
    t.Hash.Order) => fun (abc : motive AcornVerif.Intent.Hash.Order.abc) => fun (bac : motive \
    AcornVerif.Intent.Hash.Order.bac) => fun (acb : motive AcornVerif.Intent.Hash.Order.acb) =\
    > fun (cba : motive AcornVerif.Intent.Hash.Order.cba) => fun (bca : motive AcornVerif.Inte\
    nt.Hash.Order.bca) => fun (cab : motive AcornVerif.Intent.Hash.Order.cab) => @AcornVerif.I\
    ntent.Hash.Order.rec.{u} motive abc bac acb cba bca cab t\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Shift.apply\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Shift → UInt64 → UInt64 → UInt64\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (x : AcornVerif.Intent.Hash.Shift) => fun (x_1 : UInt64) => fun (x_2 : UInt64) => Ac\
    ornVerif.Intent.Hash.Shift.apply.match_1.{1} (fun (x_3 : AcornVerif.Intent.Hash.Shift) => \
    fun (x_4 : UInt64) => fun (x_5 : UInt64) => UInt64) x x_1 x_2 (fun (x_3 : UInt64) => fun (\
    d : UInt64) => @HXor.hXor.{0, 0, 0} UInt64 UInt64 UInt64 (@instHXorOfXorOp.{0} UInt64 inst\
    XorOpUInt64) x_3 d) (fun (x_3 : UInt64) => fun (d : UInt64) => @HAdd.hAdd.{0, 0, 0} UInt64\
    \x20UInt64 UInt64 (@instHAdd.{0} UInt64 instAddUInt64) x_3 d)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Shift.apply.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : AcornVerif.Intent.Hash.Shift → UInt64 → UInt64 → Sort u_1), ∀ (x : AcornVeri\
    f.Intent.Hash.Shift), ∀ (x_1 : UInt64), ∀ (x_2 : UInt64), ∀ (h_1 : ∀ (x_3 : UInt64), ∀ (d \
    : UInt64), motive AcornVerif.Intent.Hash.Shift.flip x_3 d), ∀ (h_2 : ∀ (x_3 : UInt64), ∀ (\
    d : UInt64), motive AcornVerif.Intent.Hash.Shift.add x_3 d), motive x x_1 x_2\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : AcornVerif.Intent.Hash.Shift → UInt64 → UInt64 → Sort u_1) => fun (x : Aco\
    rnVerif.Intent.Hash.Shift) => fun (x_1 : UInt64) => fun (x_2 : UInt64) => fun (h_1 : ∀ (x_\
    3 : UInt64), ∀ (d : UInt64), motive AcornVerif.Intent.Hash.Shift.flip x_3 d) => fun (h_2 :\
    \x20∀ (x_3 : UInt64), ∀ (d : UInt64), motive AcornVerif.Intent.Hash.Shift.add x_3 d) => @A\
    cornVerif.Intent.Hash.Shift.casesOn.{u_1} (fun (x_3 : AcornVerif.Intent.Hash.Shift) => mot\
    ive x_3 x_1 x_2) x (h_1 x_1 x_2) (h_2 x_1 x_2)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Shift.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : AcornVerif.Intent.Hash.Shift), Sort u}, ∀ (t : AcornVerif.Intent.Hash\
    .Shift), ∀ (flip : motive AcornVerif.Intent.Hash.Shift.flip), ∀ (add : motive AcornVerif.I\
    ntent.Hash.Shift.add), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : AcornVerif.Intent.Hash.Shift), Sort u} => fun (t : AcornVerif.Inten\
    t.Hash.Shift) => fun (flip : motive AcornVerif.Intent.Hash.Shift.flip) => fun (add : motiv\
    e AcornVerif.Intent.Hash.Shift.add) => @AcornVerif.Intent.Hash.Shift.rec.{u} motive flip a\
    dd t\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.shift\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 2, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Rule's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash.R\
    ule. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Rule), AcornVerif.Intent.Hash.Shift\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.xorAll\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (x : AcornVerif.Intent.Hash.Inputs), UInt64\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (x : AcornVerif.Intent.Hash.Inputs) => @HXor.hXor.{0, 0, 0} UInt64 UInt64 UInt64 (@i\
    nstHXorOfXorOp.{0} UInt64 instXorOpUInt64) (@HXor.hXor.{0, 0, 0} UInt64 UInt64 UInt64 (@in\
    stHXorOfXorOp.{0} UInt64 instXorOpUInt64) (@Prod.fst.{0, 0} UInt64 (Prod.{0, 0} UInt64 UIn\
    t64) x) (@Prod.fst.{0, 0} UInt64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt6\
    4) x))) (@Prod.snd.{0, 0} UInt64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt6\
    4) x))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.addAll\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (x : AcornVerif.Intent.Hash.Inputs), UInt64\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (x : AcornVerif.Intent.Hash.Inputs) => @HAdd.hAdd.{0, 0, 0} UInt64 UInt64 UInt64 (@i\
    nstHAdd.{0} UInt64 instAddUInt64) (@HAdd.hAdd.{0, 0, 0} UInt64 UInt64 UInt64 (@instHAdd.{0\
    } UInt64 instAddUInt64) (@Prod.fst.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) x) (@Prod.fst\
    .{0, 0} UInt64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) x))) (@Prod.snd\
    .{0, 0} UInt64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) x))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Meets\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@Lean\
    Intent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.IntentRecord.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause\
    .{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanInte\
    nt.Pred.{u}), LeanIntent.IntentRecord.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Clause.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Pred\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Pred.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Dom\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.dom\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Cla\
    use's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Props\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.props\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.HoldsOf\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (c : LeanIntent.Consequence.{u} W), ∀ (r : LeanIntent.IntentRecord.{u}\
    \x20W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (c : LeanIntent.Consequence.{u} W) => fun (r : LeanIntent.Intent\
    Record.{u} W) => LeanIntent.Consequence.HoldsOf.match_1.{1} (fun (x : LeanIntent.Consequen\
    ce.Kind) => Prop) (@LeanIntent.Consequence.kind.{u} W c) (fun («_» : Unit) => ∀ (w : W), @\
    LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W c w) (fun («\
    _» : Unit) => @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRec\
    ord.Meets.{u} W r w) (@LeanIntent.Consequence.holds.{u} W c w)))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W \
    → Prop), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.entailment\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.possibility\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.HoldsOf.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : LeanIntent.Consequence.Kind → Sort u_1), ∀ (x : LeanIntent.Consequence.Kind)\
    , ∀ (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment), ∀ (h_2 : ∀ («_»\
    \x20: Unit), motive LeanIntent.Consequence.Kind.possibility), motive x\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : LeanIntent.Consequence.Kind → Sort u_1) => fun (x : LeanIntent.Consequence\
    .Kind) => fun (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment) => fun\
    \x20(h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.\
    Consequence.Kind.casesOn.{u_1} (fun (x_1 : LeanIntent.Consequence.Kind) => motive x_1) x (\
    h_1 Unit.unit) (h_2 Unit.unit)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.\
    Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : mo\
    tive LeanIntent.Consequence.Kind.possibility), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Conseq\
    uence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (po\
    ssibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kin\
    d.rec.{u} motive entailment possibility t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.kind\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.HasInstance\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)\n\
    | ```\n\
    | \n\
    | ## Lean's own libraries\n\
    | \n\
    | The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: the\
    y are those of Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, which made th\
    is text. A declaration is counted as Lean's own when Lean found the module that declares i\
    t in that release's library directory.\n\
    | \n\
    consequence changing any one input always moves the spot\n\
    shown as entailment\n\
    predicate 436\n\
    | # A consequence's predicate\n\
    | \n\
    | Printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks,\
    \x20binder names and metadata aside, from the root namespace with nothing opened.\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => And (AcornVerif.Intent.Hash.OneInputMoves (Ac\
    ornVerif.Intent.Hash.Hashes.hash2 w)) (AcornVerif.Intent.Hash.OneInputMoves (AcornVerif.In\
    tent.Hash.Hashes.hash3 w))\n\
    | ```\n\
    | \n\
    | ## Definitions the predicate reaches\n\
    | \n\
    | Each is printed in full, as in the rendering of a record, with what an answer to it asks\
    \x20of every later revision (`LeanIntent.Answer.KeptBy`).\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Hashes\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Hashes.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (hash2 : AcornVerif.Intent.Hash.Inputs → UInt64), ∀ (hash3 : AcornVerif.Intent.Hash.In\
    puts → UInt64), AcornVerif.Intent.Hash.Hashes\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Inputs\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | Prod.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.OneInputMoves\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (f : AcornVerif.Intent.Hash.Inputs → UInt64), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (f : AcornVerif.Intent.Hash.Inputs → UInt64) => And (∀ (a : UInt64), ∀ (a' : UInt64)\
    , ∀ (b : UInt64), ∀ (c : UInt64), @Eq.{1} UInt64 (f (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} U\
    Int64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) (f (@Prod.mk.{0, 0} UInt64 (Prod.{0,\
    \x200} UInt64 UInt64) a' (@Prod.mk.{0, 0} UInt64 UInt64 b c))) → @Eq.{1} UInt64 a a') (And\
    \x20(∀ (a : UInt64), ∀ (b : UInt64), ∀ (b' : UInt64), ∀ (c : UInt64), @Eq.{1} UInt64 (f (@\
    Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) \
    (f (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b'\
    \x20c))) → @Eq.{1} UInt64 b b') (∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), ∀ (c' : U\
    Int64), @Eq.{1} UInt64 (f (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.\
    {0, 0} UInt64 UInt64 b c))) (f (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Pro\
    d.mk.{0, 0} UInt64 UInt64 b c'))) → @Eq.{1} UInt64 c c'))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Hashes.hash2\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 1, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Hashes's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash\
    .Hashes. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Hashes), AcornVerif.Intent.Hash.Inputs → UInt64\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Hashes.hash3\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 2, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Hashes's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash\
    .Hashes. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Hashes), AcornVerif.Intent.Hash.Inputs → UInt64\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.KeptBy\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (a : LeanIntent.Answer.{u} W), ∀ (r : LeanIntent.IntentRecord.{u} W), \
    Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (a : LeanIntent.Answer.{u} W) => fun (r : LeanIntent.IntentRecor\
    d.{u} W) => LeanIntent.Answer.KeptBy.match_1.{1} (fun (x : LeanIntent.Consequence.Kind) =>\
    \x20fun (x_1 : LeanIntent.Verdict) => Prop) (@LeanIntent.Consequence.kind.{u} W (@LeanInte\
    nt.Answer.consequence.{u} W a)) (@LeanIntent.Answer.verdict.{u} W a) (fun («_» : Unit) => \
    ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W \
    (@LeanIntent.Answer.consequence.{u} W a) w) (fun («_» : Unit) => @LeanIntent.HasInstance.{\
    u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u} W r w) (Not (@LeanIntent.\
    Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w)))) (fun («_» : Unit) =\
    > @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u\
    } W r w) (@LeanIntent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w))\
    ) (fun («_» : Unit) => ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → Not (@LeanInt\
    ent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Answer.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (consequence : LeanIntent.Consequence.{u} W), ∀ (verdict : LeanIntent.\
    Verdict), LeanIntent.Answer.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W \
    → Prop), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.entailment\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.possibility\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Verdict\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Verdict.confirmed\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Verdict.declined\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.IntentRecord.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause\
    .{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanInte\
    nt.Pred.{u}), LeanIntent.IntentRecord.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Shape\n\
    | \n\
    | An inductive type. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type u → Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Shape.value\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.function\n\
    | \n\
    | ```lean\n\
    | ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.step\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.stepOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.action\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.actionOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u\
    } O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.bundle\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀\
    \x20(rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Member\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Member.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → \
    Out), LeanIntent.Member.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Clause.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Pred\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Pred.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.KeptBy.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : LeanIntent.Consequence.Kind → LeanIntent.Verdict → Sort u_1), ∀ (x : LeanInt\
    ent.Consequence.Kind), ∀ (x_1 : LeanIntent.Verdict), ∀ (h_1 : ∀ («_» : Unit), motive LeanI\
    ntent.Consequence.Kind.entailment LeanIntent.Verdict.confirmed), ∀ (h_2 : ∀ («_» : Unit), \
    motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.declined), ∀ (h_3 : ∀ («_\
    » : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdict.confirmed), ∀\
    \x20(h_4 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdi\
    ct.declined), motive x x_1\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : LeanIntent.Consequence.Kind → LeanIntent.Verdict → Sort u_1) => fun (x : L\
    eanIntent.Consequence.Kind) => fun (x_1 : LeanIntent.Verdict) => fun (h_1 : ∀ («_» : Unit)\
    , motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.confirmed) => fun (h_2 \
    : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.decline\
    d) => fun (h_3 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent\
    .Verdict.confirmed) => fun (h_4 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possi\
    bility LeanIntent.Verdict.declined) => @LeanIntent.Consequence.Kind.casesOn.{u_1} (fun (x_\
    2 : LeanIntent.Consequence.Kind) => motive x_2 x_1) x (@LeanIntent.Verdict.casesOn.{u_1} (\
    fun (x_2 : LeanIntent.Verdict) => motive LeanIntent.Consequence.Kind.entailment x_2) x_1 (\
    h_1 Unit.unit) (h_2 Unit.unit)) (@LeanIntent.Verdict.casesOn.{u_1} (fun (x_2 : LeanIntent.\
    Verdict) => motive LeanIntent.Consequence.Kind.possibility x_2) x_1 (h_3 Unit.unit) (h_4 U\
    nit.unit))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.\
    Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : mo\
    tive LeanIntent.Consequence.Kind.possibility), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Conseq\
    uence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (po\
    ssibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kin\
    d.rec.{u} motive entailment possibility t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Verdict.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Verdict), Sort u}, ∀ (t : LeanIntent.Verdict), ∀ (confirme\
    d : motive LeanIntent.Verdict.confirmed), ∀ (declined : motive LeanIntent.Verdict.declined\
    ), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Verdict), Sort u} => fun (t : LeanIntent.Verdict) => fun\
    \x20(confirmed : motive LeanIntent.Verdict.confirmed) => fun (declined : motive LeanIntent\
    .Verdict.declined) => @LeanIntent.Verdict.rec.{u} motive confirmed declined t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.kind\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.consequence\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 1, counted after the parameters in the type of LeanIntent.Ans\
    wer's constructor, of its argument number 2, a value of LeanIntent.Answer. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Answer.{u} W), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.verdict\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Ans\
    wer's constructor, of its argument number 2, a value of LeanIntent.Answer. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Answer.{u} W), LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Meets\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@Lean\
    Intent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Dom\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.dom\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Cla\
    use's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Props\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.props\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.HasInstance\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)\n\
    | ```\n\
    | \n\
    | ## Lean's own libraries\n\
    | \n\
    | The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: the\
    y are those of Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, which made th\
    is text. A declaration is counted as Lean's own when Lean found the module that declares i\
    t in that release's library directory.\n\
    | \n\
    verdict confirmed\n\
    ",
  "lean-intent statement 1\n\
    kind answer\n\
    project acorn\n\
    id hash-2-r2\n\
    date 2026-11-03\n\
    reference docs/spec-first-pilot.md, The decisions made on the owner's behalf\n\
    by agents\n\
    under agents-below-intent\n\
    record AcornVerif.Intent.Hash.hashes\n\
    revision 740\n\
    | # The intent record AcornVerif.Intent.Hash.hashes\n\
    | \n\
    | Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term \
    its kernel checks, binder names and metadata aside, from the root namespace with nothing o\
    pened. The plain words after it are written by a model and are trusted, not proved.\n\
    | \n\
    | ## Shape\n\
    | \n\
    | ### The subject\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Shape.value.{0} AcornVerif.Intent.Hash.Hashes\n\
    | ```\n\
    | \n\
    | - **Requires:** The subject is the pair of hash functions, each taking three 64-bit inpu\
    ts to one 64-bit spot.\n\
    | - **Rules out:** Nothing by itself.\n\
    | - **Still allows:** Any pair of such functions, until the properties narrow it.\n\
    | - **Freedom O5 leaves:** None of its own. The pair carries no state from one call to the\
    \x20next, so it is declared a plain value, of which obligation O4 asks nothing.\n\
    | \n\
    | ## Domain hypotheses\n\
    | \n\
    | None.\n\
    | \n\
    | ## Properties\n\
    | \n\
    | ### changing any one input always moves the spot\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => And (AcornVerif.Intent.Hash.OneInputMoves (Ac\
    ornVerif.Intent.Hash.Hashes.hash2 w)) (AcornVerif.Intent.Hash.OneInputMoves (AcornVerif.In\
    tent.Hash.Hashes.hash3 w))\n\
    | ```\n\
    | \n\
    | - **Requires:** In each function, changing exactly one input, the others kept, always ch\
    anges the spot: never the same spot, not merely rarely.\n\
    | - **Rules out:** A function that ignores an input, and one where two values of one input\
    \x20share a spot for some values of the others.\n\
    | - **Still allows:** Any amount of sharing between inputs that differ in two or three pla\
    ces.\n\
    | - **Freedom O5 leaves:** Everything about inputs that differ in more than one place.\n\
    | \n\
    | ### no fixed rule of reordering and shifting the inputs keeps every spot\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => And (AcornVerif.Intent.Hash.NoRuleKeepsSpots \
    (AcornVerif.Intent.Hash.Hashes.hash2 w)) (AcornVerif.Intent.Hash.NoRuleKeepsSpots (AcornVe\
    rif.Intent.Hash.Hashes.hash3 w))\n\
    | ```\n\
    | \n\
    | - **Requires:** No fixed rule moves every input to a different input in the same spot. A\
    \x20rule here puts the three inputs in some order, then adds a fixed amount to each, or fl\
    ips fixed bits of each.\n\
    | - **Rules out:** Combining the inputs by plain exclusive or or plain addition, where swa\
    pping two inputs keeps the spot; and any function where adding the same amounts, or flippi\
    ng the same bits, keeps every spot.\n\
    | - **Still allows:** Rules of other kinds, such as multiplying the inputs by fixed number\
    s; and any number of inputs sharing spots without a fixed rule behind it.\n\
    | - **Freedom O5 leaves:** How often inputs share spots overall: the record bounds no rate\
    .\n\
    | \n\
    | ## Vocabulary\n\
    | \n\
    | ### same spot, a predicate over `Prod.{0, 0} UInt64 UInt64`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} UInt64 UInt64) => @Eq.{1} UInt64 (@Prod.fst.{0, 0} UInt64 UInt64 p)\
    \x20(@Prod.snd.{0, 0} UInt64 UInt64 p)\n\
    | ```\n\
    | \n\
    | - **Requires:** Two spots are the same 64-bit value.\n\
    | - **Rules out:** Spots 0 and 1.\n\
    | - **Still allows:** Spots 0 and 0.\n\
    | - **Freedom O5 leaves:** None: it is equality.\n\
    | \n\
    | ## Consequences\n\
    | \n\
    | ### changing any one input always moves the spot, an entailment: every subject that meet\
    s the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => And (AcornVerif.Intent.Hash.OneInputMoves (Ac\
    ornVerif.Intent.Hash.Hashes.hash2 w)) (AcornVerif.Intent.Hash.OneInputMoves (AcornVerif.In\
    tent.Hash.Hashes.hash3 w))\n\
    | ```\n\
    | \n\
    | - **Requires:** Changing any one input always moves the spot, in both functions.\n\
    | - **Rules out:** Any single changed input landing in the same spot.\n\
    | - **Still allows:** Inputs that differ in two or three places sharing a spot.\n\
    | - **Freedom O5 leaves:** None beyond the property's.\n\
    | \n\
    | ### no fixed rule of reordering and shifting the inputs keeps every spot, an entailment:\
    \x20every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => And (AcornVerif.Intent.Hash.NoRuleKeepsSpots \
    (AcornVerif.Intent.Hash.Hashes.hash2 w)) (AcornVerif.Intent.Hash.NoRuleKeepsSpots (AcornVe\
    rif.Intent.Hash.Hashes.hash3 w))\n\
    | ```\n\
    | \n\
    | - **Requires:** No fixed reordering and shifting of the inputs keeps every spot.\n\
    | - **Rules out:** Systematic sharing by any such rule.\n\
    | - **Still allows:** Sharing by rules of other kinds, and sharing with no fixed rule.\n\
    | - **Freedom O5 leaves:** Which rules count as systematic beyond these.\n\
    | \n\
    | ### neither function combines its inputs by plain exclusive or or plain addition, an ent\
    ailment: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => And (@Ne.{1} (AcornVerif.Intent.Hash.Inputs →\
    \x20UInt64) (AcornVerif.Intent.Hash.Hashes.hash2 w) AcornVerif.Intent.Hash.xorAll) (And (@\
    Ne.{1} (AcornVerif.Intent.Hash.Inputs → UInt64) (AcornVerif.Intent.Hash.Hashes.hash2 w) Ac\
    ornVerif.Intent.Hash.addAll) (And (@Ne.{1} (AcornVerif.Intent.Hash.Inputs → UInt64) (Acorn\
    Verif.Intent.Hash.Hashes.hash3 w) AcornVerif.Intent.Hash.xorAll) (@Ne.{1} (AcornVerif.Inte\
    nt.Hash.Inputs → UInt64) (AcornVerif.Intent.Hash.Hashes.hash3 w) AcornVerif.Intent.Hash.ad\
    dAll)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Neither function combines its three inputs by plain exclusive or or by p\
    lain addition.\n\
    | - **Rules out:** Those two combinations, since swapping two inputs keeps their spot.\n\
    | - **Still allows:** Combinations that mix the inputs before combining them.\n\
    | - **Freedom O5 leaves:** None that this consequence adds.\n\
    | \n\
    | ### the same inputs always give the same spot, an entailment: every subject that meets t\
    he record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => ∀ (x : AcornVerif.Intent.Hash.Inputs), ∀ (y :\
    \x20AcornVerif.Intent.Hash.Inputs), @Eq.{1} AcornVerif.Intent.Hash.Inputs x y → And (@Eq.{\
    1} UInt64 (AcornVerif.Intent.Hash.Hashes.hash2 w x) (AcornVerif.Intent.Hash.Hashes.hash2 w\
    \x20y)) (@Eq.{1} UInt64 (AcornVerif.Intent.Hash.Hashes.hash3 w x) (AcornVerif.Intent.Hash.\
    Hashes.hash3 w y))\n\
    | ```\n\
    | \n\
    | - **Requires:** The same inputs always give the same spot, so a run can be replayed.\n\
    | - **Rules out:** Nothing: every function of this type meets it.\n\
    | - **Still allows:** Every pair of functions.\n\
    | - **Freedom O5 leaves:** None. It holds by construction; replay further trusts the compi\
    ler and the machine to compute 64-bit words alike everywhere.\n\
    | \n\
    | ## Definitions the record's meaning reaches\n\
    | \n\
    | These are not statements of the record: each is a declaration that a statement above dep\
    ends on, or that says what it is for a subject to meet the record and for a consequence to\
    \x20hold of it as shown, with everything those depend on in turn. Each is printed in full:\
    \x20its type, a definition's value, or for a definition by structural or well-founded recu\
    rsion the equation that determines it, and an inductive type's constructors, which for a s\
    tructure are its fields; a theorem's proof and an opaque constant's value are not, since n\
    o term that uses them depends on more than their types. Their plain words are those of the\
    \x20statements that use them.\n\
    | \n\
    | ### LeanIntent.Shape\n\
    | \n\
    | An inductive type. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type u → Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Shape.value\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.function\n\
    | \n\
    | ```lean\n\
    | ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.step\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.stepOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.action\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.actionOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u\
    } O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.bundle\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀\
    \x20(rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Member\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Member.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → \
    Out), LeanIntent.Member.{u} W\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Hashes\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Hashes.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (hash2 : AcornVerif.Intent.Hash.Inputs → UInt64), ∀ (hash3 : AcornVerif.Intent.Hash.In\
    puts → UInt64), AcornVerif.Intent.Hash.Hashes\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Inputs\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | Prod.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.OneInputMoves\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (f : AcornVerif.Intent.Hash.Inputs → UInt64), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (f : AcornVerif.Intent.Hash.Inputs → UInt64) => And (∀ (a : UInt64), ∀ (a' : UInt64)\
    , ∀ (b : UInt64), ∀ (c : UInt64), @Eq.{1} UInt64 (f (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} U\
    Int64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) (f (@Prod.mk.{0, 0} UInt64 (Prod.{0,\
    \x200} UInt64 UInt64) a' (@Prod.mk.{0, 0} UInt64 UInt64 b c))) → @Eq.{1} UInt64 a a') (And\
    \x20(∀ (a : UInt64), ∀ (b : UInt64), ∀ (b' : UInt64), ∀ (c : UInt64), @Eq.{1} UInt64 (f (@\
    Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) \
    (f (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b'\
    \x20c))) → @Eq.{1} UInt64 b b') (∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), ∀ (c' : U\
    Int64), @Eq.{1} UInt64 (f (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.\
    {0, 0} UInt64 UInt64 b c))) (f (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Pro\
    d.mk.{0, 0} UInt64 UInt64 b c'))) → @Eq.{1} UInt64 c c'))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Hashes.hash2\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 1, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Hashes's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash\
    .Hashes. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Hashes), AcornVerif.Intent.Hash.Inputs → UInt64\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Hashes.hash3\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 2, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Hashes's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash\
    .Hashes. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Hashes), AcornVerif.Intent.Hash.Inputs → UInt64\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.NoRuleKeepsSpots\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (f : AcornVerif.Intent.Hash.Inputs → UInt64), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (f : AcornVerif.Intent.Hash.Inputs → UInt64) => ∀ (r : AcornVerif.Intent.Hash.Rule),\
    \x20AcornVerif.Intent.Hash.Rule.Moves r → @Exists.{1} AcornVerif.Intent.Hash.Inputs (fun (\
    x : AcornVerif.Intent.Hash.Inputs) => @Ne.{1} UInt64 (f (AcornVerif.Intent.Hash.Rule.apply\
    \x20r x)) (f x))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Rule.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (order : AcornVerif.Intent.Hash.Order), ∀ (shift : AcornVerif.Intent.Hash.Shift), ∀ (a\
    mount : AcornVerif.Intent.Hash.Inputs), AcornVerif.Intent.Hash.Rule\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Order\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.abc\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.bac\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.acb\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.cba\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.bca\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.cab\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Shift\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Shift.flip\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Shift\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Shift.add\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Shift\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.Moves\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (r : AcornVerif.Intent.Hash.Rule), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (r : AcornVerif.Intent.Hash.Rule) => Not (And (@Eq.{1} AcornVerif.Intent.Hash.Order \
    (AcornVerif.Intent.Hash.Rule.order r) AcornVerif.Intent.Hash.Order.abc) (@Eq.{1} AcornVeri\
    f.Intent.Hash.Inputs (AcornVerif.Intent.Hash.Rule.amount r) (@Prod.mk.{0, 0} UInt64 (Prod.\
    {0, 0} UInt64 UInt64) (@OfNat.ofNat.{0} UInt64 (nat_lit 0) (@UInt64.instOfNat (nat_lit 0))\
    ) (@Prod.mk.{0, 0} UInt64 UInt64 (@OfNat.ofNat.{0} UInt64 (nat_lit 0) (@UInt64.instOfNat (\
    nat_lit 0))) (@OfNat.ofNat.{0} UInt64 (nat_lit 0) (@UInt64.instOfNat (nat_lit 0)))))))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.order\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 1, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Rule's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash.R\
    ule. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Rule), AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.amount\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 3, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Rule's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash.R\
    ule. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Rule), AcornVerif.Intent.Hash.Inputs\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.apply\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (r : AcornVerif.Intent.Hash.Rule), ∀ (x : AcornVerif.Intent.Hash.Inputs), AcornVerif.I\
    ntent.Hash.Inputs\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (r : AcornVerif.Intent.Hash.Rule) => fun (x : AcornVerif.Intent.Hash.Inputs) => Acor\
    nVerif.Intent.Hash.Rule.apply.match_1.{1} (fun (x_1 : AcornVerif.Intent.Hash.Inputs) => Ac\
    ornVerif.Intent.Hash.Inputs) (AcornVerif.Intent.Hash.Order.apply (AcornVerif.Intent.Hash.R\
    ule.order r) x) (fun (a : UInt64) => fun (b : UInt64) => fun (c : UInt64) => @Prod.mk.{0, \
    0} UInt64 (Prod.{0, 0} UInt64 UInt64) (AcornVerif.Intent.Hash.Shift.apply (AcornVerif.Inte\
    nt.Hash.Rule.shift r) a (@Prod.fst.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (AcornVerif.I\
    ntent.Hash.Rule.amount r))) (@Prod.mk.{0, 0} UInt64 UInt64 (AcornVerif.Intent.Hash.Shift.a\
    pply (AcornVerif.Intent.Hash.Rule.shift r) b (@Prod.fst.{0, 0} UInt64 UInt64 (@Prod.snd.{0\
    , 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (AcornVerif.Intent.Hash.Rule.amount r)))) (AcornVe\
    rif.Intent.Hash.Shift.apply (AcornVerif.Intent.Hash.Rule.shift r) c (@Prod.snd.{0, 0} UInt\
    64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (AcornVerif.Intent.Hash.Rul\
    e.amount r))))))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.apply.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : AcornVerif.Intent.Hash.Inputs → Sort u_1), ∀ (x : AcornVerif.Intent.Hash.Inp\
    uts), ∀ (h_1 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive (@Prod.mk.{0, 0} UIn\
    t64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))), motive x\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : AcornVerif.Intent.Hash.Inputs → Sort u_1) => fun (x : AcornVerif.Intent.Ha\
    sh.Inputs) => fun (h_1 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive (@Prod.mk.\
    {0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) => @Prod\
    .casesOn.{u_1, 0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (fun (x_1 : AcornVerif.Intent.Hash\
    .Inputs) => motive x_1) x (fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => \
    @Prod.casesOn.{u_1, 0, 0} UInt64 UInt64 (fun (x_1 : Prod.{0, 0} UInt64 UInt64) => motive (\
    @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_1)) snd (fun (x_1 : UInt64) => fu\
    n (x_2 : UInt64) => h_1 fst x_1 x_2))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Order.apply\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order → AcornVerif.Intent.Hash.Inputs → AcornVerif.Intent.Hash.In\
    puts\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (x : AcornVerif.Intent.Hash.Order) => fun (x_1 : AcornVerif.Intent.Hash.Inputs) => A\
    cornVerif.Intent.Hash.Order.apply.match_1.{1} (fun (x_2 : AcornVerif.Intent.Hash.Order) =>\
    \x20fun (x_3 : AcornVerif.Intent.Hash.Inputs) => AcornVerif.Intent.Hash.Inputs) x x_1 (fun\
    \x20(a : UInt64) => fun (b : UInt64) => fun (c : UInt64) => @Prod.mk.{0, 0} UInt64 (Prod.{\
    0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c)) (fun (a : UInt64) => fun (b : \
    UInt64) => fun (c : UInt64) => @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) b (@Prod\
    .mk.{0, 0} UInt64 UInt64 a c)) (fun (a : UInt64) => fun (b : UInt64) => fun (c : UInt64) =\
    > @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 c b)\
    ) (fun (a : UInt64) => fun (b : UInt64) => fun (c : UInt64) => @Prod.mk.{0, 0} UInt64 (Pro\
    d.{0, 0} UInt64 UInt64) c (@Prod.mk.{0, 0} UInt64 UInt64 b a)) (fun (a : UInt64) => fun (b\
    \x20: UInt64) => fun (c : UInt64) => @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) b \
    (@Prod.mk.{0, 0} UInt64 UInt64 c a)) (fun (a : UInt64) => fun (b : UInt64) => fun (c : UIn\
    t64) => @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) c (@Prod.mk.{0, 0} UInt64 UInt6\
    4 a b))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Order.apply.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : AcornVerif.Intent.Hash.Order → AcornVerif.Intent.Hash.Inputs → Sort u_1), ∀ \
    (x : AcornVerif.Intent.Hash.Order), ∀ (x_1 : AcornVerif.Intent.Hash.Inputs), ∀ (h_1 : ∀ (a\
    \x20: UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Order.abc (@P\
    rod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))), \
    ∀ (h_2 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Ord\
    er.bac (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt6\
    4 b c))), ∀ (h_3 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Inten\
    t.Hash.Order.acb (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UI\
    nt64 UInt64 b c))), ∀ (h_4 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornV\
    erif.Intent.Hash.Order.cba (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk\
    .{0, 0} UInt64 UInt64 b c))), ∀ (h_5 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), mot\
    ive AcornVerif.Intent.Hash.Order.bca (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a\
    \x20(@Prod.mk.{0, 0} UInt64 UInt64 b c))), ∀ (h_6 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c :\
    \x20UInt64), motive AcornVerif.Intent.Hash.Order.cab (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} \
    UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))), motive x x_1\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : AcornVerif.Intent.Hash.Order → AcornVerif.Intent.Hash.Inputs → Sort u_1) =\
    > fun (x : AcornVerif.Intent.Hash.Order) => fun (x_1 : AcornVerif.Intent.Hash.Inputs) => f\
    un (h_1 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Or\
    der.abc (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt\
    64 b c))) => fun (h_2 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.\
    Intent.Hash.Order.bac (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, \
    0} UInt64 UInt64 b c))) => fun (h_3 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), moti\
    ve AcornVerif.Intent.Hash.Order.acb (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a \
    (@Prod.mk.{0, 0} UInt64 UInt64 b c))) => fun (h_4 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c :\
    \x20UInt64), motive AcornVerif.Intent.Hash.Order.cba (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} \
    UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) => fun (h_5 : ∀ (a : UInt64), ∀ (b \
    : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Order.bca (@Prod.mk.{0, 0} UInt64\
    \x20(Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) => fun (h_6 : ∀ (a\
    \x20: UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Order.cab (@P\
    rod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) =\
    > @AcornVerif.Intent.Hash.Order.casesOn.{u_1} (fun (x_2 : AcornVerif.Intent.Hash.Order) =>\
    \x20motive x_2 x_1) x (@Prod.casesOn.{u_1, 0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (fun (\
    x_2 : AcornVerif.Intent.Hash.Inputs) => motive AcornVerif.Intent.Hash.Order.abc x_2) x_1 (\
    fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => @Prod.casesOn.{u_1, 0, 0} U\
    Int64 UInt64 (fun (x_2 : Prod.{0, 0} UInt64 UInt64) => motive AcornVerif.Intent.Hash.Order\
    .abc (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_2)) snd (fun (x_2 : UInt64)\
    \x20=> fun (x_3 : UInt64) => h_1 fst x_2 x_3))) (@Prod.casesOn.{u_1, 0, 0} UInt64 (Prod.{0\
    , 0} UInt64 UInt64) (fun (x_2 : AcornVerif.Intent.Hash.Inputs) => motive AcornVerif.Intent\
    .Hash.Order.bac x_2) x_1 (fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => @\
    Prod.casesOn.{u_1, 0, 0} UInt64 UInt64 (fun (x_2 : Prod.{0, 0} UInt64 UInt64) => motive Ac\
    ornVerif.Intent.Hash.Order.bac (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_2\
    )) snd (fun (x_2 : UInt64) => fun (x_3 : UInt64) => h_2 fst x_2 x_3))) (@Prod.casesOn.{u_1\
    , 0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (fun (x_2 : AcornVerif.Intent.Hash.Inputs) => m\
    otive AcornVerif.Intent.Hash.Order.acb x_2) x_1 (fun (fst : UInt64) => fun (snd : Prod.{0,\
    \x200} UInt64 UInt64) => @Prod.casesOn.{u_1, 0, 0} UInt64 UInt64 (fun (x_2 : Prod.{0, 0} U\
    Int64 UInt64) => motive AcornVerif.Intent.Hash.Order.acb (@Prod.mk.{0, 0} UInt64 (Prod.{0,\
    \x200} UInt64 UInt64) fst x_2)) snd (fun (x_2 : UInt64) => fun (x_3 : UInt64) => h_3 fst x\
    _2 x_3))) (@Prod.casesOn.{u_1, 0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (fun (x_2 : AcornV\
    erif.Intent.Hash.Inputs) => motive AcornVerif.Intent.Hash.Order.cba x_2) x_1 (fun (fst : U\
    Int64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => @Prod.casesOn.{u_1, 0, 0} UInt64 UInt64\
    \x20(fun (x_2 : Prod.{0, 0} UInt64 UInt64) => motive AcornVerif.Intent.Hash.Order.cba (@Pr\
    od.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_2)) snd (fun (x_2 : UInt64) => fun (\
    x_3 : UInt64) => h_4 fst x_2 x_3))) (@Prod.casesOn.{u_1, 0, 0} UInt64 (Prod.{0, 0} UInt64 \
    UInt64) (fun (x_2 : AcornVerif.Intent.Hash.Inputs) => motive AcornVerif.Intent.Hash.Order.\
    bca x_2) x_1 (fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => @Prod.casesOn\
    .{u_1, 0, 0} UInt64 UInt64 (fun (x_2 : Prod.{0, 0} UInt64 UInt64) => motive AcornVerif.Int\
    ent.Hash.Order.bca (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_2)) snd (fun \
    (x_2 : UInt64) => fun (x_3 : UInt64) => h_5 fst x_2 x_3))) (@Prod.casesOn.{u_1, 0, 0} UInt\
    64 (Prod.{0, 0} UInt64 UInt64) (fun (x_2 : AcornVerif.Intent.Hash.Inputs) => motive AcornV\
    erif.Intent.Hash.Order.cab x_2) x_1 (fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 U\
    Int64) => @Prod.casesOn.{u_1, 0, 0} UInt64 UInt64 (fun (x_2 : Prod.{0, 0} UInt64 UInt64) =\
    > motive AcornVerif.Intent.Hash.Order.cab (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt\
    64) fst x_2)) snd (fun (x_2 : UInt64) => fun (x_3 : UInt64) => h_6 fst x_2 x_3)))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Order.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : AcornVerif.Intent.Hash.Order), Sort u}, ∀ (t : AcornVerif.Intent.Hash\
    .Order), ∀ (abc : motive AcornVerif.Intent.Hash.Order.abc), ∀ (bac : motive AcornVerif.Int\
    ent.Hash.Order.bac), ∀ (acb : motive AcornVerif.Intent.Hash.Order.acb), ∀ (cba : motive Ac\
    ornVerif.Intent.Hash.Order.cba), ∀ (bca : motive AcornVerif.Intent.Hash.Order.bca), ∀ (cab\
    \x20: motive AcornVerif.Intent.Hash.Order.cab), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : AcornVerif.Intent.Hash.Order), Sort u} => fun (t : AcornVerif.Inten\
    t.Hash.Order) => fun (abc : motive AcornVerif.Intent.Hash.Order.abc) => fun (bac : motive \
    AcornVerif.Intent.Hash.Order.bac) => fun (acb : motive AcornVerif.Intent.Hash.Order.acb) =\
    > fun (cba : motive AcornVerif.Intent.Hash.Order.cba) => fun (bca : motive AcornVerif.Inte\
    nt.Hash.Order.bca) => fun (cab : motive AcornVerif.Intent.Hash.Order.cab) => @AcornVerif.I\
    ntent.Hash.Order.rec.{u} motive abc bac acb cba bca cab t\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Shift.apply\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Shift → UInt64 → UInt64 → UInt64\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (x : AcornVerif.Intent.Hash.Shift) => fun (x_1 : UInt64) => fun (x_2 : UInt64) => Ac\
    ornVerif.Intent.Hash.Shift.apply.match_1.{1} (fun (x_3 : AcornVerif.Intent.Hash.Shift) => \
    fun (x_4 : UInt64) => fun (x_5 : UInt64) => UInt64) x x_1 x_2 (fun (x_3 : UInt64) => fun (\
    d : UInt64) => @HXor.hXor.{0, 0, 0} UInt64 UInt64 UInt64 (@instHXorOfXorOp.{0} UInt64 inst\
    XorOpUInt64) x_3 d) (fun (x_3 : UInt64) => fun (d : UInt64) => @HAdd.hAdd.{0, 0, 0} UInt64\
    \x20UInt64 UInt64 (@instHAdd.{0} UInt64 instAddUInt64) x_3 d)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Shift.apply.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : AcornVerif.Intent.Hash.Shift → UInt64 → UInt64 → Sort u_1), ∀ (x : AcornVeri\
    f.Intent.Hash.Shift), ∀ (x_1 : UInt64), ∀ (x_2 : UInt64), ∀ (h_1 : ∀ (x_3 : UInt64), ∀ (d \
    : UInt64), motive AcornVerif.Intent.Hash.Shift.flip x_3 d), ∀ (h_2 : ∀ (x_3 : UInt64), ∀ (\
    d : UInt64), motive AcornVerif.Intent.Hash.Shift.add x_3 d), motive x x_1 x_2\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : AcornVerif.Intent.Hash.Shift → UInt64 → UInt64 → Sort u_1) => fun (x : Aco\
    rnVerif.Intent.Hash.Shift) => fun (x_1 : UInt64) => fun (x_2 : UInt64) => fun (h_1 : ∀ (x_\
    3 : UInt64), ∀ (d : UInt64), motive AcornVerif.Intent.Hash.Shift.flip x_3 d) => fun (h_2 :\
    \x20∀ (x_3 : UInt64), ∀ (d : UInt64), motive AcornVerif.Intent.Hash.Shift.add x_3 d) => @A\
    cornVerif.Intent.Hash.Shift.casesOn.{u_1} (fun (x_3 : AcornVerif.Intent.Hash.Shift) => mot\
    ive x_3 x_1 x_2) x (h_1 x_1 x_2) (h_2 x_1 x_2)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Shift.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : AcornVerif.Intent.Hash.Shift), Sort u}, ∀ (t : AcornVerif.Intent.Hash\
    .Shift), ∀ (flip : motive AcornVerif.Intent.Hash.Shift.flip), ∀ (add : motive AcornVerif.I\
    ntent.Hash.Shift.add), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : AcornVerif.Intent.Hash.Shift), Sort u} => fun (t : AcornVerif.Inten\
    t.Hash.Shift) => fun (flip : motive AcornVerif.Intent.Hash.Shift.flip) => fun (add : motiv\
    e AcornVerif.Intent.Hash.Shift.add) => @AcornVerif.Intent.Hash.Shift.rec.{u} motive flip a\
    dd t\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.shift\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 2, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Rule's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash.R\
    ule. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Rule), AcornVerif.Intent.Hash.Shift\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.xorAll\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (x : AcornVerif.Intent.Hash.Inputs), UInt64\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (x : AcornVerif.Intent.Hash.Inputs) => @HXor.hXor.{0, 0, 0} UInt64 UInt64 UInt64 (@i\
    nstHXorOfXorOp.{0} UInt64 instXorOpUInt64) (@HXor.hXor.{0, 0, 0} UInt64 UInt64 UInt64 (@in\
    stHXorOfXorOp.{0} UInt64 instXorOpUInt64) (@Prod.fst.{0, 0} UInt64 (Prod.{0, 0} UInt64 UIn\
    t64) x) (@Prod.fst.{0, 0} UInt64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt6\
    4) x))) (@Prod.snd.{0, 0} UInt64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt6\
    4) x))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.addAll\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (x : AcornVerif.Intent.Hash.Inputs), UInt64\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (x : AcornVerif.Intent.Hash.Inputs) => @HAdd.hAdd.{0, 0, 0} UInt64 UInt64 UInt64 (@i\
    nstHAdd.{0} UInt64 instAddUInt64) (@HAdd.hAdd.{0, 0, 0} UInt64 UInt64 UInt64 (@instHAdd.{0\
    } UInt64 instAddUInt64) (@Prod.fst.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) x) (@Prod.fst\
    .{0, 0} UInt64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) x))) (@Prod.snd\
    .{0, 0} UInt64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) x))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Meets\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@Lean\
    Intent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.IntentRecord.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause\
    .{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanInte\
    nt.Pred.{u}), LeanIntent.IntentRecord.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Clause.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Pred\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Pred.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Dom\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.dom\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Cla\
    use's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Props\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.props\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.HoldsOf\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (c : LeanIntent.Consequence.{u} W), ∀ (r : LeanIntent.IntentRecord.{u}\
    \x20W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (c : LeanIntent.Consequence.{u} W) => fun (r : LeanIntent.Intent\
    Record.{u} W) => LeanIntent.Consequence.HoldsOf.match_1.{1} (fun (x : LeanIntent.Consequen\
    ce.Kind) => Prop) (@LeanIntent.Consequence.kind.{u} W c) (fun («_» : Unit) => ∀ (w : W), @\
    LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W c w) (fun («\
    _» : Unit) => @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRec\
    ord.Meets.{u} W r w) (@LeanIntent.Consequence.holds.{u} W c w)))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W \
    → Prop), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.entailment\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.possibility\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.HoldsOf.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : LeanIntent.Consequence.Kind → Sort u_1), ∀ (x : LeanIntent.Consequence.Kind)\
    , ∀ (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment), ∀ (h_2 : ∀ («_»\
    \x20: Unit), motive LeanIntent.Consequence.Kind.possibility), motive x\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : LeanIntent.Consequence.Kind → Sort u_1) => fun (x : LeanIntent.Consequence\
    .Kind) => fun (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment) => fun\
    \x20(h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.\
    Consequence.Kind.casesOn.{u_1} (fun (x_1 : LeanIntent.Consequence.Kind) => motive x_1) x (\
    h_1 Unit.unit) (h_2 Unit.unit)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.\
    Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : mo\
    tive LeanIntent.Consequence.Kind.possibility), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Conseq\
    uence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (po\
    ssibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kin\
    d.rec.{u} motive entailment possibility t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.kind\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.HasInstance\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)\n\
    | ```\n\
    | \n\
    | ## Lean's own libraries\n\
    | \n\
    | The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: the\
    y are those of Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, which made th\
    is text. A declaration is counted as Lean's own when Lean found the module that declares i\
    t in that release's library directory.\n\
    | \n\
    consequence no fixed rule of reordering and shifting the inputs keeps every spot\n\
    shown as entailment\n\
    predicate 670\n\
    | # A consequence's predicate\n\
    | \n\
    | Printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks,\
    \x20binder names and metadata aside, from the root namespace with nothing opened.\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => And (AcornVerif.Intent.Hash.NoRuleKeepsSpots \
    (AcornVerif.Intent.Hash.Hashes.hash2 w)) (AcornVerif.Intent.Hash.NoRuleKeepsSpots (AcornVe\
    rif.Intent.Hash.Hashes.hash3 w))\n\
    | ```\n\
    | \n\
    | ## Definitions the predicate reaches\n\
    | \n\
    | Each is printed in full, as in the rendering of a record, with what an answer to it asks\
    \x20of every later revision (`LeanIntent.Answer.KeptBy`).\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Hashes\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Hashes.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (hash2 : AcornVerif.Intent.Hash.Inputs → UInt64), ∀ (hash3 : AcornVerif.Intent.Hash.In\
    puts → UInt64), AcornVerif.Intent.Hash.Hashes\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Inputs\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | Prod.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.NoRuleKeepsSpots\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (f : AcornVerif.Intent.Hash.Inputs → UInt64), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (f : AcornVerif.Intent.Hash.Inputs → UInt64) => ∀ (r : AcornVerif.Intent.Hash.Rule),\
    \x20AcornVerif.Intent.Hash.Rule.Moves r → @Exists.{1} AcornVerif.Intent.Hash.Inputs (fun (\
    x : AcornVerif.Intent.Hash.Inputs) => @Ne.{1} UInt64 (f (AcornVerif.Intent.Hash.Rule.apply\
    \x20r x)) (f x))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Rule.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (order : AcornVerif.Intent.Hash.Order), ∀ (shift : AcornVerif.Intent.Hash.Shift), ∀ (a\
    mount : AcornVerif.Intent.Hash.Inputs), AcornVerif.Intent.Hash.Rule\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Order\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.abc\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.bac\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.acb\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.cba\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.bca\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.cab\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Shift\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Shift.flip\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Shift\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Shift.add\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Shift\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.Moves\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (r : AcornVerif.Intent.Hash.Rule), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (r : AcornVerif.Intent.Hash.Rule) => Not (And (@Eq.{1} AcornVerif.Intent.Hash.Order \
    (AcornVerif.Intent.Hash.Rule.order r) AcornVerif.Intent.Hash.Order.abc) (@Eq.{1} AcornVeri\
    f.Intent.Hash.Inputs (AcornVerif.Intent.Hash.Rule.amount r) (@Prod.mk.{0, 0} UInt64 (Prod.\
    {0, 0} UInt64 UInt64) (@OfNat.ofNat.{0} UInt64 (nat_lit 0) (@UInt64.instOfNat (nat_lit 0))\
    ) (@Prod.mk.{0, 0} UInt64 UInt64 (@OfNat.ofNat.{0} UInt64 (nat_lit 0) (@UInt64.instOfNat (\
    nat_lit 0))) (@OfNat.ofNat.{0} UInt64 (nat_lit 0) (@UInt64.instOfNat (nat_lit 0)))))))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.order\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 1, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Rule's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash.R\
    ule. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Rule), AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.amount\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 3, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Rule's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash.R\
    ule. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Rule), AcornVerif.Intent.Hash.Inputs\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.apply\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (r : AcornVerif.Intent.Hash.Rule), ∀ (x : AcornVerif.Intent.Hash.Inputs), AcornVerif.I\
    ntent.Hash.Inputs\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (r : AcornVerif.Intent.Hash.Rule) => fun (x : AcornVerif.Intent.Hash.Inputs) => Acor\
    nVerif.Intent.Hash.Rule.apply.match_1.{1} (fun (x_1 : AcornVerif.Intent.Hash.Inputs) => Ac\
    ornVerif.Intent.Hash.Inputs) (AcornVerif.Intent.Hash.Order.apply (AcornVerif.Intent.Hash.R\
    ule.order r) x) (fun (a : UInt64) => fun (b : UInt64) => fun (c : UInt64) => @Prod.mk.{0, \
    0} UInt64 (Prod.{0, 0} UInt64 UInt64) (AcornVerif.Intent.Hash.Shift.apply (AcornVerif.Inte\
    nt.Hash.Rule.shift r) a (@Prod.fst.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (AcornVerif.I\
    ntent.Hash.Rule.amount r))) (@Prod.mk.{0, 0} UInt64 UInt64 (AcornVerif.Intent.Hash.Shift.a\
    pply (AcornVerif.Intent.Hash.Rule.shift r) b (@Prod.fst.{0, 0} UInt64 UInt64 (@Prod.snd.{0\
    , 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (AcornVerif.Intent.Hash.Rule.amount r)))) (AcornVe\
    rif.Intent.Hash.Shift.apply (AcornVerif.Intent.Hash.Rule.shift r) c (@Prod.snd.{0, 0} UInt\
    64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (AcornVerif.Intent.Hash.Rul\
    e.amount r))))))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.apply.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : AcornVerif.Intent.Hash.Inputs → Sort u_1), ∀ (x : AcornVerif.Intent.Hash.Inp\
    uts), ∀ (h_1 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive (@Prod.mk.{0, 0} UIn\
    t64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))), motive x\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : AcornVerif.Intent.Hash.Inputs → Sort u_1) => fun (x : AcornVerif.Intent.Ha\
    sh.Inputs) => fun (h_1 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive (@Prod.mk.\
    {0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) => @Prod\
    .casesOn.{u_1, 0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (fun (x_1 : AcornVerif.Intent.Hash\
    .Inputs) => motive x_1) x (fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => \
    @Prod.casesOn.{u_1, 0, 0} UInt64 UInt64 (fun (x_1 : Prod.{0, 0} UInt64 UInt64) => motive (\
    @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_1)) snd (fun (x_1 : UInt64) => fu\
    n (x_2 : UInt64) => h_1 fst x_1 x_2))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Order.apply\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order → AcornVerif.Intent.Hash.Inputs → AcornVerif.Intent.Hash.In\
    puts\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (x : AcornVerif.Intent.Hash.Order) => fun (x_1 : AcornVerif.Intent.Hash.Inputs) => A\
    cornVerif.Intent.Hash.Order.apply.match_1.{1} (fun (x_2 : AcornVerif.Intent.Hash.Order) =>\
    \x20fun (x_3 : AcornVerif.Intent.Hash.Inputs) => AcornVerif.Intent.Hash.Inputs) x x_1 (fun\
    \x20(a : UInt64) => fun (b : UInt64) => fun (c : UInt64) => @Prod.mk.{0, 0} UInt64 (Prod.{\
    0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c)) (fun (a : UInt64) => fun (b : \
    UInt64) => fun (c : UInt64) => @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) b (@Prod\
    .mk.{0, 0} UInt64 UInt64 a c)) (fun (a : UInt64) => fun (b : UInt64) => fun (c : UInt64) =\
    > @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 c b)\
    ) (fun (a : UInt64) => fun (b : UInt64) => fun (c : UInt64) => @Prod.mk.{0, 0} UInt64 (Pro\
    d.{0, 0} UInt64 UInt64) c (@Prod.mk.{0, 0} UInt64 UInt64 b a)) (fun (a : UInt64) => fun (b\
    \x20: UInt64) => fun (c : UInt64) => @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) b \
    (@Prod.mk.{0, 0} UInt64 UInt64 c a)) (fun (a : UInt64) => fun (b : UInt64) => fun (c : UIn\
    t64) => @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) c (@Prod.mk.{0, 0} UInt64 UInt6\
    4 a b))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Order.apply.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : AcornVerif.Intent.Hash.Order → AcornVerif.Intent.Hash.Inputs → Sort u_1), ∀ \
    (x : AcornVerif.Intent.Hash.Order), ∀ (x_1 : AcornVerif.Intent.Hash.Inputs), ∀ (h_1 : ∀ (a\
    \x20: UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Order.abc (@P\
    rod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))), \
    ∀ (h_2 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Ord\
    er.bac (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt6\
    4 b c))), ∀ (h_3 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Inten\
    t.Hash.Order.acb (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UI\
    nt64 UInt64 b c))), ∀ (h_4 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornV\
    erif.Intent.Hash.Order.cba (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk\
    .{0, 0} UInt64 UInt64 b c))), ∀ (h_5 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), mot\
    ive AcornVerif.Intent.Hash.Order.bca (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a\
    \x20(@Prod.mk.{0, 0} UInt64 UInt64 b c))), ∀ (h_6 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c :\
    \x20UInt64), motive AcornVerif.Intent.Hash.Order.cab (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} \
    UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))), motive x x_1\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : AcornVerif.Intent.Hash.Order → AcornVerif.Intent.Hash.Inputs → Sort u_1) =\
    > fun (x : AcornVerif.Intent.Hash.Order) => fun (x_1 : AcornVerif.Intent.Hash.Inputs) => f\
    un (h_1 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Or\
    der.abc (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt\
    64 b c))) => fun (h_2 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.\
    Intent.Hash.Order.bac (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, \
    0} UInt64 UInt64 b c))) => fun (h_3 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), moti\
    ve AcornVerif.Intent.Hash.Order.acb (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a \
    (@Prod.mk.{0, 0} UInt64 UInt64 b c))) => fun (h_4 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c :\
    \x20UInt64), motive AcornVerif.Intent.Hash.Order.cba (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} \
    UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) => fun (h_5 : ∀ (a : UInt64), ∀ (b \
    : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Order.bca (@Prod.mk.{0, 0} UInt64\
    \x20(Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) => fun (h_6 : ∀ (a\
    \x20: UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Order.cab (@P\
    rod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) =\
    > @AcornVerif.Intent.Hash.Order.casesOn.{u_1} (fun (x_2 : AcornVerif.Intent.Hash.Order) =>\
    \x20motive x_2 x_1) x (@Prod.casesOn.{u_1, 0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (fun (\
    x_2 : AcornVerif.Intent.Hash.Inputs) => motive AcornVerif.Intent.Hash.Order.abc x_2) x_1 (\
    fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => @Prod.casesOn.{u_1, 0, 0} U\
    Int64 UInt64 (fun (x_2 : Prod.{0, 0} UInt64 UInt64) => motive AcornVerif.Intent.Hash.Order\
    .abc (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_2)) snd (fun (x_2 : UInt64)\
    \x20=> fun (x_3 : UInt64) => h_1 fst x_2 x_3))) (@Prod.casesOn.{u_1, 0, 0} UInt64 (Prod.{0\
    , 0} UInt64 UInt64) (fun (x_2 : AcornVerif.Intent.Hash.Inputs) => motive AcornVerif.Intent\
    .Hash.Order.bac x_2) x_1 (fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => @\
    Prod.casesOn.{u_1, 0, 0} UInt64 UInt64 (fun (x_2 : Prod.{0, 0} UInt64 UInt64) => motive Ac\
    ornVerif.Intent.Hash.Order.bac (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_2\
    )) snd (fun (x_2 : UInt64) => fun (x_3 : UInt64) => h_2 fst x_2 x_3))) (@Prod.casesOn.{u_1\
    , 0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (fun (x_2 : AcornVerif.Intent.Hash.Inputs) => m\
    otive AcornVerif.Intent.Hash.Order.acb x_2) x_1 (fun (fst : UInt64) => fun (snd : Prod.{0,\
    \x200} UInt64 UInt64) => @Prod.casesOn.{u_1, 0, 0} UInt64 UInt64 (fun (x_2 : Prod.{0, 0} U\
    Int64 UInt64) => motive AcornVerif.Intent.Hash.Order.acb (@Prod.mk.{0, 0} UInt64 (Prod.{0,\
    \x200} UInt64 UInt64) fst x_2)) snd (fun (x_2 : UInt64) => fun (x_3 : UInt64) => h_3 fst x\
    _2 x_3))) (@Prod.casesOn.{u_1, 0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (fun (x_2 : AcornV\
    erif.Intent.Hash.Inputs) => motive AcornVerif.Intent.Hash.Order.cba x_2) x_1 (fun (fst : U\
    Int64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => @Prod.casesOn.{u_1, 0, 0} UInt64 UInt64\
    \x20(fun (x_2 : Prod.{0, 0} UInt64 UInt64) => motive AcornVerif.Intent.Hash.Order.cba (@Pr\
    od.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_2)) snd (fun (x_2 : UInt64) => fun (\
    x_3 : UInt64) => h_4 fst x_2 x_3))) (@Prod.casesOn.{u_1, 0, 0} UInt64 (Prod.{0, 0} UInt64 \
    UInt64) (fun (x_2 : AcornVerif.Intent.Hash.Inputs) => motive AcornVerif.Intent.Hash.Order.\
    bca x_2) x_1 (fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => @Prod.casesOn\
    .{u_1, 0, 0} UInt64 UInt64 (fun (x_2 : Prod.{0, 0} UInt64 UInt64) => motive AcornVerif.Int\
    ent.Hash.Order.bca (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_2)) snd (fun \
    (x_2 : UInt64) => fun (x_3 : UInt64) => h_5 fst x_2 x_3))) (@Prod.casesOn.{u_1, 0, 0} UInt\
    64 (Prod.{0, 0} UInt64 UInt64) (fun (x_2 : AcornVerif.Intent.Hash.Inputs) => motive AcornV\
    erif.Intent.Hash.Order.cab x_2) x_1 (fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 U\
    Int64) => @Prod.casesOn.{u_1, 0, 0} UInt64 UInt64 (fun (x_2 : Prod.{0, 0} UInt64 UInt64) =\
    > motive AcornVerif.Intent.Hash.Order.cab (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt\
    64) fst x_2)) snd (fun (x_2 : UInt64) => fun (x_3 : UInt64) => h_6 fst x_2 x_3)))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Order.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : AcornVerif.Intent.Hash.Order), Sort u}, ∀ (t : AcornVerif.Intent.Hash\
    .Order), ∀ (abc : motive AcornVerif.Intent.Hash.Order.abc), ∀ (bac : motive AcornVerif.Int\
    ent.Hash.Order.bac), ∀ (acb : motive AcornVerif.Intent.Hash.Order.acb), ∀ (cba : motive Ac\
    ornVerif.Intent.Hash.Order.cba), ∀ (bca : motive AcornVerif.Intent.Hash.Order.bca), ∀ (cab\
    \x20: motive AcornVerif.Intent.Hash.Order.cab), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : AcornVerif.Intent.Hash.Order), Sort u} => fun (t : AcornVerif.Inten\
    t.Hash.Order) => fun (abc : motive AcornVerif.Intent.Hash.Order.abc) => fun (bac : motive \
    AcornVerif.Intent.Hash.Order.bac) => fun (acb : motive AcornVerif.Intent.Hash.Order.acb) =\
    > fun (cba : motive AcornVerif.Intent.Hash.Order.cba) => fun (bca : motive AcornVerif.Inte\
    nt.Hash.Order.bca) => fun (cab : motive AcornVerif.Intent.Hash.Order.cab) => @AcornVerif.I\
    ntent.Hash.Order.rec.{u} motive abc bac acb cba bca cab t\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Shift.apply\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Shift → UInt64 → UInt64 → UInt64\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (x : AcornVerif.Intent.Hash.Shift) => fun (x_1 : UInt64) => fun (x_2 : UInt64) => Ac\
    ornVerif.Intent.Hash.Shift.apply.match_1.{1} (fun (x_3 : AcornVerif.Intent.Hash.Shift) => \
    fun (x_4 : UInt64) => fun (x_5 : UInt64) => UInt64) x x_1 x_2 (fun (x_3 : UInt64) => fun (\
    d : UInt64) => @HXor.hXor.{0, 0, 0} UInt64 UInt64 UInt64 (@instHXorOfXorOp.{0} UInt64 inst\
    XorOpUInt64) x_3 d) (fun (x_3 : UInt64) => fun (d : UInt64) => @HAdd.hAdd.{0, 0, 0} UInt64\
    \x20UInt64 UInt64 (@instHAdd.{0} UInt64 instAddUInt64) x_3 d)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Shift.apply.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : AcornVerif.Intent.Hash.Shift → UInt64 → UInt64 → Sort u_1), ∀ (x : AcornVeri\
    f.Intent.Hash.Shift), ∀ (x_1 : UInt64), ∀ (x_2 : UInt64), ∀ (h_1 : ∀ (x_3 : UInt64), ∀ (d \
    : UInt64), motive AcornVerif.Intent.Hash.Shift.flip x_3 d), ∀ (h_2 : ∀ (x_3 : UInt64), ∀ (\
    d : UInt64), motive AcornVerif.Intent.Hash.Shift.add x_3 d), motive x x_1 x_2\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : AcornVerif.Intent.Hash.Shift → UInt64 → UInt64 → Sort u_1) => fun (x : Aco\
    rnVerif.Intent.Hash.Shift) => fun (x_1 : UInt64) => fun (x_2 : UInt64) => fun (h_1 : ∀ (x_\
    3 : UInt64), ∀ (d : UInt64), motive AcornVerif.Intent.Hash.Shift.flip x_3 d) => fun (h_2 :\
    \x20∀ (x_3 : UInt64), ∀ (d : UInt64), motive AcornVerif.Intent.Hash.Shift.add x_3 d) => @A\
    cornVerif.Intent.Hash.Shift.casesOn.{u_1} (fun (x_3 : AcornVerif.Intent.Hash.Shift) => mot\
    ive x_3 x_1 x_2) x (h_1 x_1 x_2) (h_2 x_1 x_2)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Shift.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : AcornVerif.Intent.Hash.Shift), Sort u}, ∀ (t : AcornVerif.Intent.Hash\
    .Shift), ∀ (flip : motive AcornVerif.Intent.Hash.Shift.flip), ∀ (add : motive AcornVerif.I\
    ntent.Hash.Shift.add), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : AcornVerif.Intent.Hash.Shift), Sort u} => fun (t : AcornVerif.Inten\
    t.Hash.Shift) => fun (flip : motive AcornVerif.Intent.Hash.Shift.flip) => fun (add : motiv\
    e AcornVerif.Intent.Hash.Shift.add) => @AcornVerif.Intent.Hash.Shift.rec.{u} motive flip a\
    dd t\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.shift\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 2, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Rule's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash.R\
    ule. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Rule), AcornVerif.Intent.Hash.Shift\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Hashes.hash2\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 1, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Hashes's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash\
    .Hashes. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Hashes), AcornVerif.Intent.Hash.Inputs → UInt64\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Hashes.hash3\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 2, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Hashes's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash\
    .Hashes. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Hashes), AcornVerif.Intent.Hash.Inputs → UInt64\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.KeptBy\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (a : LeanIntent.Answer.{u} W), ∀ (r : LeanIntent.IntentRecord.{u} W), \
    Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (a : LeanIntent.Answer.{u} W) => fun (r : LeanIntent.IntentRecor\
    d.{u} W) => LeanIntent.Answer.KeptBy.match_1.{1} (fun (x : LeanIntent.Consequence.Kind) =>\
    \x20fun (x_1 : LeanIntent.Verdict) => Prop) (@LeanIntent.Consequence.kind.{u} W (@LeanInte\
    nt.Answer.consequence.{u} W a)) (@LeanIntent.Answer.verdict.{u} W a) (fun («_» : Unit) => \
    ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W \
    (@LeanIntent.Answer.consequence.{u} W a) w) (fun («_» : Unit) => @LeanIntent.HasInstance.{\
    u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u} W r w) (Not (@LeanIntent.\
    Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w)))) (fun («_» : Unit) =\
    > @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u\
    } W r w) (@LeanIntent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w))\
    ) (fun («_» : Unit) => ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → Not (@LeanInt\
    ent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Answer.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (consequence : LeanIntent.Consequence.{u} W), ∀ (verdict : LeanIntent.\
    Verdict), LeanIntent.Answer.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W \
    → Prop), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.entailment\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.possibility\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Verdict\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Verdict.confirmed\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Verdict.declined\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.IntentRecord.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause\
    .{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanInte\
    nt.Pred.{u}), LeanIntent.IntentRecord.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Shape\n\
    | \n\
    | An inductive type. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type u → Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Shape.value\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.function\n\
    | \n\
    | ```lean\n\
    | ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.step\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.stepOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.action\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.actionOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u\
    } O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.bundle\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀\
    \x20(rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Member\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Member.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → \
    Out), LeanIntent.Member.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Clause.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Pred\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Pred.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.KeptBy.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : LeanIntent.Consequence.Kind → LeanIntent.Verdict → Sort u_1), ∀ (x : LeanInt\
    ent.Consequence.Kind), ∀ (x_1 : LeanIntent.Verdict), ∀ (h_1 : ∀ («_» : Unit), motive LeanI\
    ntent.Consequence.Kind.entailment LeanIntent.Verdict.confirmed), ∀ (h_2 : ∀ («_» : Unit), \
    motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.declined), ∀ (h_3 : ∀ («_\
    » : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdict.confirmed), ∀\
    \x20(h_4 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdi\
    ct.declined), motive x x_1\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : LeanIntent.Consequence.Kind → LeanIntent.Verdict → Sort u_1) => fun (x : L\
    eanIntent.Consequence.Kind) => fun (x_1 : LeanIntent.Verdict) => fun (h_1 : ∀ («_» : Unit)\
    , motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.confirmed) => fun (h_2 \
    : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.decline\
    d) => fun (h_3 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent\
    .Verdict.confirmed) => fun (h_4 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possi\
    bility LeanIntent.Verdict.declined) => @LeanIntent.Consequence.Kind.casesOn.{u_1} (fun (x_\
    2 : LeanIntent.Consequence.Kind) => motive x_2 x_1) x (@LeanIntent.Verdict.casesOn.{u_1} (\
    fun (x_2 : LeanIntent.Verdict) => motive LeanIntent.Consequence.Kind.entailment x_2) x_1 (\
    h_1 Unit.unit) (h_2 Unit.unit)) (@LeanIntent.Verdict.casesOn.{u_1} (fun (x_2 : LeanIntent.\
    Verdict) => motive LeanIntent.Consequence.Kind.possibility x_2) x_1 (h_3 Unit.unit) (h_4 U\
    nit.unit))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.\
    Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : mo\
    tive LeanIntent.Consequence.Kind.possibility), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Conseq\
    uence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (po\
    ssibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kin\
    d.rec.{u} motive entailment possibility t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Verdict.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Verdict), Sort u}, ∀ (t : LeanIntent.Verdict), ∀ (confirme\
    d : motive LeanIntent.Verdict.confirmed), ∀ (declined : motive LeanIntent.Verdict.declined\
    ), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Verdict), Sort u} => fun (t : LeanIntent.Verdict) => fun\
    \x20(confirmed : motive LeanIntent.Verdict.confirmed) => fun (declined : motive LeanIntent\
    .Verdict.declined) => @LeanIntent.Verdict.rec.{u} motive confirmed declined t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.kind\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.consequence\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 1, counted after the parameters in the type of LeanIntent.Ans\
    wer's constructor, of its argument number 2, a value of LeanIntent.Answer. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Answer.{u} W), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.verdict\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Ans\
    wer's constructor, of its argument number 2, a value of LeanIntent.Answer. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Answer.{u} W), LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Meets\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@Lean\
    Intent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Dom\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.dom\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Cla\
    use's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Props\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.props\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.HasInstance\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)\n\
    | ```\n\
    | \n\
    | ## Lean's own libraries\n\
    | \n\
    | The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: the\
    y are those of Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, which made th\
    is text. A declaration is counted as Lean's own when Lean found the module that declares i\
    t in that release's library directory.\n\
    | \n\
    verdict confirmed\n\
    ",
  "lean-intent statement 1\n\
    kind answer\n\
    project acorn\n\
    id hash-3-r2\n\
    date 2026-11-03\n\
    reference docs/spec-first-pilot.md, The decisions made on the owner's behalf\n\
    by agents\n\
    under agents-below-intent\n\
    record AcornVerif.Intent.Hash.hashes\n\
    revision 740\n\
    | # The intent record AcornVerif.Intent.Hash.hashes\n\
    | \n\
    | Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term \
    its kernel checks, binder names and metadata aside, from the root namespace with nothing o\
    pened. The plain words after it are written by a model and are trusted, not proved.\n\
    | \n\
    | ## Shape\n\
    | \n\
    | ### The subject\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Shape.value.{0} AcornVerif.Intent.Hash.Hashes\n\
    | ```\n\
    | \n\
    | - **Requires:** The subject is the pair of hash functions, each taking three 64-bit inpu\
    ts to one 64-bit spot.\n\
    | - **Rules out:** Nothing by itself.\n\
    | - **Still allows:** Any pair of such functions, until the properties narrow it.\n\
    | - **Freedom O5 leaves:** None of its own. The pair carries no state from one call to the\
    \x20next, so it is declared a plain value, of which obligation O4 asks nothing.\n\
    | \n\
    | ## Domain hypotheses\n\
    | \n\
    | None.\n\
    | \n\
    | ## Properties\n\
    | \n\
    | ### changing any one input always moves the spot\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => And (AcornVerif.Intent.Hash.OneInputMoves (Ac\
    ornVerif.Intent.Hash.Hashes.hash2 w)) (AcornVerif.Intent.Hash.OneInputMoves (AcornVerif.In\
    tent.Hash.Hashes.hash3 w))\n\
    | ```\n\
    | \n\
    | - **Requires:** In each function, changing exactly one input, the others kept, always ch\
    anges the spot: never the same spot, not merely rarely.\n\
    | - **Rules out:** A function that ignores an input, and one where two values of one input\
    \x20share a spot for some values of the others.\n\
    | - **Still allows:** Any amount of sharing between inputs that differ in two or three pla\
    ces.\n\
    | - **Freedom O5 leaves:** Everything about inputs that differ in more than one place.\n\
    | \n\
    | ### no fixed rule of reordering and shifting the inputs keeps every spot\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => And (AcornVerif.Intent.Hash.NoRuleKeepsSpots \
    (AcornVerif.Intent.Hash.Hashes.hash2 w)) (AcornVerif.Intent.Hash.NoRuleKeepsSpots (AcornVe\
    rif.Intent.Hash.Hashes.hash3 w))\n\
    | ```\n\
    | \n\
    | - **Requires:** No fixed rule moves every input to a different input in the same spot. A\
    \x20rule here puts the three inputs in some order, then adds a fixed amount to each, or fl\
    ips fixed bits of each.\n\
    | - **Rules out:** Combining the inputs by plain exclusive or or plain addition, where swa\
    pping two inputs keeps the spot; and any function where adding the same amounts, or flippi\
    ng the same bits, keeps every spot.\n\
    | - **Still allows:** Rules of other kinds, such as multiplying the inputs by fixed number\
    s; and any number of inputs sharing spots without a fixed rule behind it.\n\
    | - **Freedom O5 leaves:** How often inputs share spots overall: the record bounds no rate\
    .\n\
    | \n\
    | ## Vocabulary\n\
    | \n\
    | ### same spot, a predicate over `Prod.{0, 0} UInt64 UInt64`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} UInt64 UInt64) => @Eq.{1} UInt64 (@Prod.fst.{0, 0} UInt64 UInt64 p)\
    \x20(@Prod.snd.{0, 0} UInt64 UInt64 p)\n\
    | ```\n\
    | \n\
    | - **Requires:** Two spots are the same 64-bit value.\n\
    | - **Rules out:** Spots 0 and 1.\n\
    | - **Still allows:** Spots 0 and 0.\n\
    | - **Freedom O5 leaves:** None: it is equality.\n\
    | \n\
    | ## Consequences\n\
    | \n\
    | ### changing any one input always moves the spot, an entailment: every subject that meet\
    s the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => And (AcornVerif.Intent.Hash.OneInputMoves (Ac\
    ornVerif.Intent.Hash.Hashes.hash2 w)) (AcornVerif.Intent.Hash.OneInputMoves (AcornVerif.In\
    tent.Hash.Hashes.hash3 w))\n\
    | ```\n\
    | \n\
    | - **Requires:** Changing any one input always moves the spot, in both functions.\n\
    | - **Rules out:** Any single changed input landing in the same spot.\n\
    | - **Still allows:** Inputs that differ in two or three places sharing a spot.\n\
    | - **Freedom O5 leaves:** None beyond the property's.\n\
    | \n\
    | ### no fixed rule of reordering and shifting the inputs keeps every spot, an entailment:\
    \x20every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => And (AcornVerif.Intent.Hash.NoRuleKeepsSpots \
    (AcornVerif.Intent.Hash.Hashes.hash2 w)) (AcornVerif.Intent.Hash.NoRuleKeepsSpots (AcornVe\
    rif.Intent.Hash.Hashes.hash3 w))\n\
    | ```\n\
    | \n\
    | - **Requires:** No fixed reordering and shifting of the inputs keeps every spot.\n\
    | - **Rules out:** Systematic sharing by any such rule.\n\
    | - **Still allows:** Sharing by rules of other kinds, and sharing with no fixed rule.\n\
    | - **Freedom O5 leaves:** Which rules count as systematic beyond these.\n\
    | \n\
    | ### neither function combines its inputs by plain exclusive or or plain addition, an ent\
    ailment: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => And (@Ne.{1} (AcornVerif.Intent.Hash.Inputs →\
    \x20UInt64) (AcornVerif.Intent.Hash.Hashes.hash2 w) AcornVerif.Intent.Hash.xorAll) (And (@\
    Ne.{1} (AcornVerif.Intent.Hash.Inputs → UInt64) (AcornVerif.Intent.Hash.Hashes.hash2 w) Ac\
    ornVerif.Intent.Hash.addAll) (And (@Ne.{1} (AcornVerif.Intent.Hash.Inputs → UInt64) (Acorn\
    Verif.Intent.Hash.Hashes.hash3 w) AcornVerif.Intent.Hash.xorAll) (@Ne.{1} (AcornVerif.Inte\
    nt.Hash.Inputs → UInt64) (AcornVerif.Intent.Hash.Hashes.hash3 w) AcornVerif.Intent.Hash.ad\
    dAll)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Neither function combines its three inputs by plain exclusive or or by p\
    lain addition.\n\
    | - **Rules out:** Those two combinations, since swapping two inputs keeps their spot.\n\
    | - **Still allows:** Combinations that mix the inputs before combining them.\n\
    | - **Freedom O5 leaves:** None that this consequence adds.\n\
    | \n\
    | ### the same inputs always give the same spot, an entailment: every subject that meets t\
    he record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => ∀ (x : AcornVerif.Intent.Hash.Inputs), ∀ (y :\
    \x20AcornVerif.Intent.Hash.Inputs), @Eq.{1} AcornVerif.Intent.Hash.Inputs x y → And (@Eq.{\
    1} UInt64 (AcornVerif.Intent.Hash.Hashes.hash2 w x) (AcornVerif.Intent.Hash.Hashes.hash2 w\
    \x20y)) (@Eq.{1} UInt64 (AcornVerif.Intent.Hash.Hashes.hash3 w x) (AcornVerif.Intent.Hash.\
    Hashes.hash3 w y))\n\
    | ```\n\
    | \n\
    | - **Requires:** The same inputs always give the same spot, so a run can be replayed.\n\
    | - **Rules out:** Nothing: every function of this type meets it.\n\
    | - **Still allows:** Every pair of functions.\n\
    | - **Freedom O5 leaves:** None. It holds by construction; replay further trusts the compi\
    ler and the machine to compute 64-bit words alike everywhere.\n\
    | \n\
    | ## Definitions the record's meaning reaches\n\
    | \n\
    | These are not statements of the record: each is a declaration that a statement above dep\
    ends on, or that says what it is for a subject to meet the record and for a consequence to\
    \x20hold of it as shown, with everything those depend on in turn. Each is printed in full:\
    \x20its type, a definition's value, or for a definition by structural or well-founded recu\
    rsion the equation that determines it, and an inductive type's constructors, which for a s\
    tructure are its fields; a theorem's proof and an opaque constant's value are not, since n\
    o term that uses them depends on more than their types. Their plain words are those of the\
    \x20statements that use them.\n\
    | \n\
    | ### LeanIntent.Shape\n\
    | \n\
    | An inductive type. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type u → Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Shape.value\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.function\n\
    | \n\
    | ```lean\n\
    | ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.step\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.stepOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.action\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.actionOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u\
    } O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.bundle\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀\
    \x20(rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Member\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Member.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → \
    Out), LeanIntent.Member.{u} W\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Hashes\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Hashes.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (hash2 : AcornVerif.Intent.Hash.Inputs → UInt64), ∀ (hash3 : AcornVerif.Intent.Hash.In\
    puts → UInt64), AcornVerif.Intent.Hash.Hashes\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Inputs\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | Prod.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.OneInputMoves\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (f : AcornVerif.Intent.Hash.Inputs → UInt64), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (f : AcornVerif.Intent.Hash.Inputs → UInt64) => And (∀ (a : UInt64), ∀ (a' : UInt64)\
    , ∀ (b : UInt64), ∀ (c : UInt64), @Eq.{1} UInt64 (f (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} U\
    Int64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) (f (@Prod.mk.{0, 0} UInt64 (Prod.{0,\
    \x200} UInt64 UInt64) a' (@Prod.mk.{0, 0} UInt64 UInt64 b c))) → @Eq.{1} UInt64 a a') (And\
    \x20(∀ (a : UInt64), ∀ (b : UInt64), ∀ (b' : UInt64), ∀ (c : UInt64), @Eq.{1} UInt64 (f (@\
    Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) \
    (f (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b'\
    \x20c))) → @Eq.{1} UInt64 b b') (∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), ∀ (c' : U\
    Int64), @Eq.{1} UInt64 (f (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.\
    {0, 0} UInt64 UInt64 b c))) (f (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Pro\
    d.mk.{0, 0} UInt64 UInt64 b c'))) → @Eq.{1} UInt64 c c'))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Hashes.hash2\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 1, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Hashes's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash\
    .Hashes. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Hashes), AcornVerif.Intent.Hash.Inputs → UInt64\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Hashes.hash3\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 2, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Hashes's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash\
    .Hashes. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Hashes), AcornVerif.Intent.Hash.Inputs → UInt64\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.NoRuleKeepsSpots\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (f : AcornVerif.Intent.Hash.Inputs → UInt64), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (f : AcornVerif.Intent.Hash.Inputs → UInt64) => ∀ (r : AcornVerif.Intent.Hash.Rule),\
    \x20AcornVerif.Intent.Hash.Rule.Moves r → @Exists.{1} AcornVerif.Intent.Hash.Inputs (fun (\
    x : AcornVerif.Intent.Hash.Inputs) => @Ne.{1} UInt64 (f (AcornVerif.Intent.Hash.Rule.apply\
    \x20r x)) (f x))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Rule.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (order : AcornVerif.Intent.Hash.Order), ∀ (shift : AcornVerif.Intent.Hash.Shift), ∀ (a\
    mount : AcornVerif.Intent.Hash.Inputs), AcornVerif.Intent.Hash.Rule\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Order\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.abc\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.bac\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.acb\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.cba\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.bca\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.cab\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Shift\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Shift.flip\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Shift\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Shift.add\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Shift\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.Moves\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (r : AcornVerif.Intent.Hash.Rule), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (r : AcornVerif.Intent.Hash.Rule) => Not (And (@Eq.{1} AcornVerif.Intent.Hash.Order \
    (AcornVerif.Intent.Hash.Rule.order r) AcornVerif.Intent.Hash.Order.abc) (@Eq.{1} AcornVeri\
    f.Intent.Hash.Inputs (AcornVerif.Intent.Hash.Rule.amount r) (@Prod.mk.{0, 0} UInt64 (Prod.\
    {0, 0} UInt64 UInt64) (@OfNat.ofNat.{0} UInt64 (nat_lit 0) (@UInt64.instOfNat (nat_lit 0))\
    ) (@Prod.mk.{0, 0} UInt64 UInt64 (@OfNat.ofNat.{0} UInt64 (nat_lit 0) (@UInt64.instOfNat (\
    nat_lit 0))) (@OfNat.ofNat.{0} UInt64 (nat_lit 0) (@UInt64.instOfNat (nat_lit 0)))))))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.order\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 1, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Rule's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash.R\
    ule. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Rule), AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.amount\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 3, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Rule's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash.R\
    ule. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Rule), AcornVerif.Intent.Hash.Inputs\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.apply\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (r : AcornVerif.Intent.Hash.Rule), ∀ (x : AcornVerif.Intent.Hash.Inputs), AcornVerif.I\
    ntent.Hash.Inputs\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (r : AcornVerif.Intent.Hash.Rule) => fun (x : AcornVerif.Intent.Hash.Inputs) => Acor\
    nVerif.Intent.Hash.Rule.apply.match_1.{1} (fun (x_1 : AcornVerif.Intent.Hash.Inputs) => Ac\
    ornVerif.Intent.Hash.Inputs) (AcornVerif.Intent.Hash.Order.apply (AcornVerif.Intent.Hash.R\
    ule.order r) x) (fun (a : UInt64) => fun (b : UInt64) => fun (c : UInt64) => @Prod.mk.{0, \
    0} UInt64 (Prod.{0, 0} UInt64 UInt64) (AcornVerif.Intent.Hash.Shift.apply (AcornVerif.Inte\
    nt.Hash.Rule.shift r) a (@Prod.fst.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (AcornVerif.I\
    ntent.Hash.Rule.amount r))) (@Prod.mk.{0, 0} UInt64 UInt64 (AcornVerif.Intent.Hash.Shift.a\
    pply (AcornVerif.Intent.Hash.Rule.shift r) b (@Prod.fst.{0, 0} UInt64 UInt64 (@Prod.snd.{0\
    , 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (AcornVerif.Intent.Hash.Rule.amount r)))) (AcornVe\
    rif.Intent.Hash.Shift.apply (AcornVerif.Intent.Hash.Rule.shift r) c (@Prod.snd.{0, 0} UInt\
    64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (AcornVerif.Intent.Hash.Rul\
    e.amount r))))))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.apply.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : AcornVerif.Intent.Hash.Inputs → Sort u_1), ∀ (x : AcornVerif.Intent.Hash.Inp\
    uts), ∀ (h_1 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive (@Prod.mk.{0, 0} UIn\
    t64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))), motive x\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : AcornVerif.Intent.Hash.Inputs → Sort u_1) => fun (x : AcornVerif.Intent.Ha\
    sh.Inputs) => fun (h_1 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive (@Prod.mk.\
    {0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) => @Prod\
    .casesOn.{u_1, 0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (fun (x_1 : AcornVerif.Intent.Hash\
    .Inputs) => motive x_1) x (fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => \
    @Prod.casesOn.{u_1, 0, 0} UInt64 UInt64 (fun (x_1 : Prod.{0, 0} UInt64 UInt64) => motive (\
    @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_1)) snd (fun (x_1 : UInt64) => fu\
    n (x_2 : UInt64) => h_1 fst x_1 x_2))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Order.apply\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order → AcornVerif.Intent.Hash.Inputs → AcornVerif.Intent.Hash.In\
    puts\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (x : AcornVerif.Intent.Hash.Order) => fun (x_1 : AcornVerif.Intent.Hash.Inputs) => A\
    cornVerif.Intent.Hash.Order.apply.match_1.{1} (fun (x_2 : AcornVerif.Intent.Hash.Order) =>\
    \x20fun (x_3 : AcornVerif.Intent.Hash.Inputs) => AcornVerif.Intent.Hash.Inputs) x x_1 (fun\
    \x20(a : UInt64) => fun (b : UInt64) => fun (c : UInt64) => @Prod.mk.{0, 0} UInt64 (Prod.{\
    0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c)) (fun (a : UInt64) => fun (b : \
    UInt64) => fun (c : UInt64) => @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) b (@Prod\
    .mk.{0, 0} UInt64 UInt64 a c)) (fun (a : UInt64) => fun (b : UInt64) => fun (c : UInt64) =\
    > @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 c b)\
    ) (fun (a : UInt64) => fun (b : UInt64) => fun (c : UInt64) => @Prod.mk.{0, 0} UInt64 (Pro\
    d.{0, 0} UInt64 UInt64) c (@Prod.mk.{0, 0} UInt64 UInt64 b a)) (fun (a : UInt64) => fun (b\
    \x20: UInt64) => fun (c : UInt64) => @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) b \
    (@Prod.mk.{0, 0} UInt64 UInt64 c a)) (fun (a : UInt64) => fun (b : UInt64) => fun (c : UIn\
    t64) => @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) c (@Prod.mk.{0, 0} UInt64 UInt6\
    4 a b))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Order.apply.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : AcornVerif.Intent.Hash.Order → AcornVerif.Intent.Hash.Inputs → Sort u_1), ∀ \
    (x : AcornVerif.Intent.Hash.Order), ∀ (x_1 : AcornVerif.Intent.Hash.Inputs), ∀ (h_1 : ∀ (a\
    \x20: UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Order.abc (@P\
    rod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))), \
    ∀ (h_2 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Ord\
    er.bac (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt6\
    4 b c))), ∀ (h_3 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Inten\
    t.Hash.Order.acb (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UI\
    nt64 UInt64 b c))), ∀ (h_4 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornV\
    erif.Intent.Hash.Order.cba (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk\
    .{0, 0} UInt64 UInt64 b c))), ∀ (h_5 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), mot\
    ive AcornVerif.Intent.Hash.Order.bca (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a\
    \x20(@Prod.mk.{0, 0} UInt64 UInt64 b c))), ∀ (h_6 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c :\
    \x20UInt64), motive AcornVerif.Intent.Hash.Order.cab (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} \
    UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))), motive x x_1\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : AcornVerif.Intent.Hash.Order → AcornVerif.Intent.Hash.Inputs → Sort u_1) =\
    > fun (x : AcornVerif.Intent.Hash.Order) => fun (x_1 : AcornVerif.Intent.Hash.Inputs) => f\
    un (h_1 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Or\
    der.abc (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt\
    64 b c))) => fun (h_2 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.\
    Intent.Hash.Order.bac (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, \
    0} UInt64 UInt64 b c))) => fun (h_3 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), moti\
    ve AcornVerif.Intent.Hash.Order.acb (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a \
    (@Prod.mk.{0, 0} UInt64 UInt64 b c))) => fun (h_4 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c :\
    \x20UInt64), motive AcornVerif.Intent.Hash.Order.cba (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} \
    UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) => fun (h_5 : ∀ (a : UInt64), ∀ (b \
    : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Order.bca (@Prod.mk.{0, 0} UInt64\
    \x20(Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) => fun (h_6 : ∀ (a\
    \x20: UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Order.cab (@P\
    rod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) =\
    > @AcornVerif.Intent.Hash.Order.casesOn.{u_1} (fun (x_2 : AcornVerif.Intent.Hash.Order) =>\
    \x20motive x_2 x_1) x (@Prod.casesOn.{u_1, 0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (fun (\
    x_2 : AcornVerif.Intent.Hash.Inputs) => motive AcornVerif.Intent.Hash.Order.abc x_2) x_1 (\
    fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => @Prod.casesOn.{u_1, 0, 0} U\
    Int64 UInt64 (fun (x_2 : Prod.{0, 0} UInt64 UInt64) => motive AcornVerif.Intent.Hash.Order\
    .abc (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_2)) snd (fun (x_2 : UInt64)\
    \x20=> fun (x_3 : UInt64) => h_1 fst x_2 x_3))) (@Prod.casesOn.{u_1, 0, 0} UInt64 (Prod.{0\
    , 0} UInt64 UInt64) (fun (x_2 : AcornVerif.Intent.Hash.Inputs) => motive AcornVerif.Intent\
    .Hash.Order.bac x_2) x_1 (fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => @\
    Prod.casesOn.{u_1, 0, 0} UInt64 UInt64 (fun (x_2 : Prod.{0, 0} UInt64 UInt64) => motive Ac\
    ornVerif.Intent.Hash.Order.bac (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_2\
    )) snd (fun (x_2 : UInt64) => fun (x_3 : UInt64) => h_2 fst x_2 x_3))) (@Prod.casesOn.{u_1\
    , 0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (fun (x_2 : AcornVerif.Intent.Hash.Inputs) => m\
    otive AcornVerif.Intent.Hash.Order.acb x_2) x_1 (fun (fst : UInt64) => fun (snd : Prod.{0,\
    \x200} UInt64 UInt64) => @Prod.casesOn.{u_1, 0, 0} UInt64 UInt64 (fun (x_2 : Prod.{0, 0} U\
    Int64 UInt64) => motive AcornVerif.Intent.Hash.Order.acb (@Prod.mk.{0, 0} UInt64 (Prod.{0,\
    \x200} UInt64 UInt64) fst x_2)) snd (fun (x_2 : UInt64) => fun (x_3 : UInt64) => h_3 fst x\
    _2 x_3))) (@Prod.casesOn.{u_1, 0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (fun (x_2 : AcornV\
    erif.Intent.Hash.Inputs) => motive AcornVerif.Intent.Hash.Order.cba x_2) x_1 (fun (fst : U\
    Int64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => @Prod.casesOn.{u_1, 0, 0} UInt64 UInt64\
    \x20(fun (x_2 : Prod.{0, 0} UInt64 UInt64) => motive AcornVerif.Intent.Hash.Order.cba (@Pr\
    od.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_2)) snd (fun (x_2 : UInt64) => fun (\
    x_3 : UInt64) => h_4 fst x_2 x_3))) (@Prod.casesOn.{u_1, 0, 0} UInt64 (Prod.{0, 0} UInt64 \
    UInt64) (fun (x_2 : AcornVerif.Intent.Hash.Inputs) => motive AcornVerif.Intent.Hash.Order.\
    bca x_2) x_1 (fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => @Prod.casesOn\
    .{u_1, 0, 0} UInt64 UInt64 (fun (x_2 : Prod.{0, 0} UInt64 UInt64) => motive AcornVerif.Int\
    ent.Hash.Order.bca (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_2)) snd (fun \
    (x_2 : UInt64) => fun (x_3 : UInt64) => h_5 fst x_2 x_3))) (@Prod.casesOn.{u_1, 0, 0} UInt\
    64 (Prod.{0, 0} UInt64 UInt64) (fun (x_2 : AcornVerif.Intent.Hash.Inputs) => motive AcornV\
    erif.Intent.Hash.Order.cab x_2) x_1 (fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 U\
    Int64) => @Prod.casesOn.{u_1, 0, 0} UInt64 UInt64 (fun (x_2 : Prod.{0, 0} UInt64 UInt64) =\
    > motive AcornVerif.Intent.Hash.Order.cab (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt\
    64) fst x_2)) snd (fun (x_2 : UInt64) => fun (x_3 : UInt64) => h_6 fst x_2 x_3)))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Order.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : AcornVerif.Intent.Hash.Order), Sort u}, ∀ (t : AcornVerif.Intent.Hash\
    .Order), ∀ (abc : motive AcornVerif.Intent.Hash.Order.abc), ∀ (bac : motive AcornVerif.Int\
    ent.Hash.Order.bac), ∀ (acb : motive AcornVerif.Intent.Hash.Order.acb), ∀ (cba : motive Ac\
    ornVerif.Intent.Hash.Order.cba), ∀ (bca : motive AcornVerif.Intent.Hash.Order.bca), ∀ (cab\
    \x20: motive AcornVerif.Intent.Hash.Order.cab), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : AcornVerif.Intent.Hash.Order), Sort u} => fun (t : AcornVerif.Inten\
    t.Hash.Order) => fun (abc : motive AcornVerif.Intent.Hash.Order.abc) => fun (bac : motive \
    AcornVerif.Intent.Hash.Order.bac) => fun (acb : motive AcornVerif.Intent.Hash.Order.acb) =\
    > fun (cba : motive AcornVerif.Intent.Hash.Order.cba) => fun (bca : motive AcornVerif.Inte\
    nt.Hash.Order.bca) => fun (cab : motive AcornVerif.Intent.Hash.Order.cab) => @AcornVerif.I\
    ntent.Hash.Order.rec.{u} motive abc bac acb cba bca cab t\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Shift.apply\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Shift → UInt64 → UInt64 → UInt64\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (x : AcornVerif.Intent.Hash.Shift) => fun (x_1 : UInt64) => fun (x_2 : UInt64) => Ac\
    ornVerif.Intent.Hash.Shift.apply.match_1.{1} (fun (x_3 : AcornVerif.Intent.Hash.Shift) => \
    fun (x_4 : UInt64) => fun (x_5 : UInt64) => UInt64) x x_1 x_2 (fun (x_3 : UInt64) => fun (\
    d : UInt64) => @HXor.hXor.{0, 0, 0} UInt64 UInt64 UInt64 (@instHXorOfXorOp.{0} UInt64 inst\
    XorOpUInt64) x_3 d) (fun (x_3 : UInt64) => fun (d : UInt64) => @HAdd.hAdd.{0, 0, 0} UInt64\
    \x20UInt64 UInt64 (@instHAdd.{0} UInt64 instAddUInt64) x_3 d)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Shift.apply.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : AcornVerif.Intent.Hash.Shift → UInt64 → UInt64 → Sort u_1), ∀ (x : AcornVeri\
    f.Intent.Hash.Shift), ∀ (x_1 : UInt64), ∀ (x_2 : UInt64), ∀ (h_1 : ∀ (x_3 : UInt64), ∀ (d \
    : UInt64), motive AcornVerif.Intent.Hash.Shift.flip x_3 d), ∀ (h_2 : ∀ (x_3 : UInt64), ∀ (\
    d : UInt64), motive AcornVerif.Intent.Hash.Shift.add x_3 d), motive x x_1 x_2\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : AcornVerif.Intent.Hash.Shift → UInt64 → UInt64 → Sort u_1) => fun (x : Aco\
    rnVerif.Intent.Hash.Shift) => fun (x_1 : UInt64) => fun (x_2 : UInt64) => fun (h_1 : ∀ (x_\
    3 : UInt64), ∀ (d : UInt64), motive AcornVerif.Intent.Hash.Shift.flip x_3 d) => fun (h_2 :\
    \x20∀ (x_3 : UInt64), ∀ (d : UInt64), motive AcornVerif.Intent.Hash.Shift.add x_3 d) => @A\
    cornVerif.Intent.Hash.Shift.casesOn.{u_1} (fun (x_3 : AcornVerif.Intent.Hash.Shift) => mot\
    ive x_3 x_1 x_2) x (h_1 x_1 x_2) (h_2 x_1 x_2)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Shift.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : AcornVerif.Intent.Hash.Shift), Sort u}, ∀ (t : AcornVerif.Intent.Hash\
    .Shift), ∀ (flip : motive AcornVerif.Intent.Hash.Shift.flip), ∀ (add : motive AcornVerif.I\
    ntent.Hash.Shift.add), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : AcornVerif.Intent.Hash.Shift), Sort u} => fun (t : AcornVerif.Inten\
    t.Hash.Shift) => fun (flip : motive AcornVerif.Intent.Hash.Shift.flip) => fun (add : motiv\
    e AcornVerif.Intent.Hash.Shift.add) => @AcornVerif.Intent.Hash.Shift.rec.{u} motive flip a\
    dd t\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.shift\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 2, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Rule's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash.R\
    ule. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Rule), AcornVerif.Intent.Hash.Shift\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.xorAll\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (x : AcornVerif.Intent.Hash.Inputs), UInt64\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (x : AcornVerif.Intent.Hash.Inputs) => @HXor.hXor.{0, 0, 0} UInt64 UInt64 UInt64 (@i\
    nstHXorOfXorOp.{0} UInt64 instXorOpUInt64) (@HXor.hXor.{0, 0, 0} UInt64 UInt64 UInt64 (@in\
    stHXorOfXorOp.{0} UInt64 instXorOpUInt64) (@Prod.fst.{0, 0} UInt64 (Prod.{0, 0} UInt64 UIn\
    t64) x) (@Prod.fst.{0, 0} UInt64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt6\
    4) x))) (@Prod.snd.{0, 0} UInt64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt6\
    4) x))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.addAll\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (x : AcornVerif.Intent.Hash.Inputs), UInt64\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (x : AcornVerif.Intent.Hash.Inputs) => @HAdd.hAdd.{0, 0, 0} UInt64 UInt64 UInt64 (@i\
    nstHAdd.{0} UInt64 instAddUInt64) (@HAdd.hAdd.{0, 0, 0} UInt64 UInt64 UInt64 (@instHAdd.{0\
    } UInt64 instAddUInt64) (@Prod.fst.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) x) (@Prod.fst\
    .{0, 0} UInt64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) x))) (@Prod.snd\
    .{0, 0} UInt64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) x))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Meets\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@Lean\
    Intent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.IntentRecord.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause\
    .{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanInte\
    nt.Pred.{u}), LeanIntent.IntentRecord.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Clause.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Pred\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Pred.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Dom\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.dom\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Cla\
    use's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Props\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.props\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.HoldsOf\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (c : LeanIntent.Consequence.{u} W), ∀ (r : LeanIntent.IntentRecord.{u}\
    \x20W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (c : LeanIntent.Consequence.{u} W) => fun (r : LeanIntent.Intent\
    Record.{u} W) => LeanIntent.Consequence.HoldsOf.match_1.{1} (fun (x : LeanIntent.Consequen\
    ce.Kind) => Prop) (@LeanIntent.Consequence.kind.{u} W c) (fun («_» : Unit) => ∀ (w : W), @\
    LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W c w) (fun («\
    _» : Unit) => @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRec\
    ord.Meets.{u} W r w) (@LeanIntent.Consequence.holds.{u} W c w)))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W \
    → Prop), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.entailment\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.possibility\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.HoldsOf.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : LeanIntent.Consequence.Kind → Sort u_1), ∀ (x : LeanIntent.Consequence.Kind)\
    , ∀ (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment), ∀ (h_2 : ∀ («_»\
    \x20: Unit), motive LeanIntent.Consequence.Kind.possibility), motive x\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : LeanIntent.Consequence.Kind → Sort u_1) => fun (x : LeanIntent.Consequence\
    .Kind) => fun (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment) => fun\
    \x20(h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.\
    Consequence.Kind.casesOn.{u_1} (fun (x_1 : LeanIntent.Consequence.Kind) => motive x_1) x (\
    h_1 Unit.unit) (h_2 Unit.unit)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.\
    Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : mo\
    tive LeanIntent.Consequence.Kind.possibility), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Conseq\
    uence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (po\
    ssibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kin\
    d.rec.{u} motive entailment possibility t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.kind\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.HasInstance\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)\n\
    | ```\n\
    | \n\
    | ## Lean's own libraries\n\
    | \n\
    | The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: the\
    y are those of Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, which made th\
    is text. A declaration is counted as Lean's own when Lean found the module that declares i\
    t in that release's library directory.\n\
    | \n\
    consequence neither function combines its inputs by plain exclusive or or plain addition\n\
    shown as entailment\n\
    predicate 450\n\
    | # A consequence's predicate\n\
    | \n\
    | Printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks,\
    \x20binder names and metadata aside, from the root namespace with nothing opened.\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => And (@Ne.{1} (AcornVerif.Intent.Hash.Inputs →\
    \x20UInt64) (AcornVerif.Intent.Hash.Hashes.hash2 w) AcornVerif.Intent.Hash.xorAll) (And (@\
    Ne.{1} (AcornVerif.Intent.Hash.Inputs → UInt64) (AcornVerif.Intent.Hash.Hashes.hash2 w) Ac\
    ornVerif.Intent.Hash.addAll) (And (@Ne.{1} (AcornVerif.Intent.Hash.Inputs → UInt64) (Acorn\
    Verif.Intent.Hash.Hashes.hash3 w) AcornVerif.Intent.Hash.xorAll) (@Ne.{1} (AcornVerif.Inte\
    nt.Hash.Inputs → UInt64) (AcornVerif.Intent.Hash.Hashes.hash3 w) AcornVerif.Intent.Hash.ad\
    dAll)))\n\
    | ```\n\
    | \n\
    | ## Definitions the predicate reaches\n\
    | \n\
    | Each is printed in full, as in the rendering of a record, with what an answer to it asks\
    \x20of every later revision (`LeanIntent.Answer.KeptBy`).\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Hashes\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Hashes.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (hash2 : AcornVerif.Intent.Hash.Inputs → UInt64), ∀ (hash3 : AcornVerif.Intent.Hash.In\
    puts → UInt64), AcornVerif.Intent.Hash.Hashes\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Inputs\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | Prod.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Hashes.hash2\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 1, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Hashes's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash\
    .Hashes. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Hashes), AcornVerif.Intent.Hash.Inputs → UInt64\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.xorAll\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (x : AcornVerif.Intent.Hash.Inputs), UInt64\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (x : AcornVerif.Intent.Hash.Inputs) => @HXor.hXor.{0, 0, 0} UInt64 UInt64 UInt64 (@i\
    nstHXorOfXorOp.{0} UInt64 instXorOpUInt64) (@HXor.hXor.{0, 0, 0} UInt64 UInt64 UInt64 (@in\
    stHXorOfXorOp.{0} UInt64 instXorOpUInt64) (@Prod.fst.{0, 0} UInt64 (Prod.{0, 0} UInt64 UIn\
    t64) x) (@Prod.fst.{0, 0} UInt64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt6\
    4) x))) (@Prod.snd.{0, 0} UInt64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt6\
    4) x))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.addAll\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (x : AcornVerif.Intent.Hash.Inputs), UInt64\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (x : AcornVerif.Intent.Hash.Inputs) => @HAdd.hAdd.{0, 0, 0} UInt64 UInt64 UInt64 (@i\
    nstHAdd.{0} UInt64 instAddUInt64) (@HAdd.hAdd.{0, 0, 0} UInt64 UInt64 UInt64 (@instHAdd.{0\
    } UInt64 instAddUInt64) (@Prod.fst.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) x) (@Prod.fst\
    .{0, 0} UInt64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) x))) (@Prod.snd\
    .{0, 0} UInt64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) x))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Hashes.hash3\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 2, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Hashes's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash\
    .Hashes. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Hashes), AcornVerif.Intent.Hash.Inputs → UInt64\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.KeptBy\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (a : LeanIntent.Answer.{u} W), ∀ (r : LeanIntent.IntentRecord.{u} W), \
    Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (a : LeanIntent.Answer.{u} W) => fun (r : LeanIntent.IntentRecor\
    d.{u} W) => LeanIntent.Answer.KeptBy.match_1.{1} (fun (x : LeanIntent.Consequence.Kind) =>\
    \x20fun (x_1 : LeanIntent.Verdict) => Prop) (@LeanIntent.Consequence.kind.{u} W (@LeanInte\
    nt.Answer.consequence.{u} W a)) (@LeanIntent.Answer.verdict.{u} W a) (fun («_» : Unit) => \
    ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W \
    (@LeanIntent.Answer.consequence.{u} W a) w) (fun («_» : Unit) => @LeanIntent.HasInstance.{\
    u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u} W r w) (Not (@LeanIntent.\
    Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w)))) (fun («_» : Unit) =\
    > @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u\
    } W r w) (@LeanIntent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w))\
    ) (fun («_» : Unit) => ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → Not (@LeanInt\
    ent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Answer.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (consequence : LeanIntent.Consequence.{u} W), ∀ (verdict : LeanIntent.\
    Verdict), LeanIntent.Answer.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W \
    → Prop), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.entailment\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.possibility\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Verdict\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Verdict.confirmed\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Verdict.declined\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.IntentRecord.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause\
    .{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanInte\
    nt.Pred.{u}), LeanIntent.IntentRecord.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Shape\n\
    | \n\
    | An inductive type. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type u → Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Shape.value\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.function\n\
    | \n\
    | ```lean\n\
    | ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.step\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.stepOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.action\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.actionOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u\
    } O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.bundle\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀\
    \x20(rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Member\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Member.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → \
    Out), LeanIntent.Member.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Clause.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Pred\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Pred.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.KeptBy.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : LeanIntent.Consequence.Kind → LeanIntent.Verdict → Sort u_1), ∀ (x : LeanInt\
    ent.Consequence.Kind), ∀ (x_1 : LeanIntent.Verdict), ∀ (h_1 : ∀ («_» : Unit), motive LeanI\
    ntent.Consequence.Kind.entailment LeanIntent.Verdict.confirmed), ∀ (h_2 : ∀ («_» : Unit), \
    motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.declined), ∀ (h_3 : ∀ («_\
    » : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdict.confirmed), ∀\
    \x20(h_4 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdi\
    ct.declined), motive x x_1\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : LeanIntent.Consequence.Kind → LeanIntent.Verdict → Sort u_1) => fun (x : L\
    eanIntent.Consequence.Kind) => fun (x_1 : LeanIntent.Verdict) => fun (h_1 : ∀ («_» : Unit)\
    , motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.confirmed) => fun (h_2 \
    : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.decline\
    d) => fun (h_3 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent\
    .Verdict.confirmed) => fun (h_4 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possi\
    bility LeanIntent.Verdict.declined) => @LeanIntent.Consequence.Kind.casesOn.{u_1} (fun (x_\
    2 : LeanIntent.Consequence.Kind) => motive x_2 x_1) x (@LeanIntent.Verdict.casesOn.{u_1} (\
    fun (x_2 : LeanIntent.Verdict) => motive LeanIntent.Consequence.Kind.entailment x_2) x_1 (\
    h_1 Unit.unit) (h_2 Unit.unit)) (@LeanIntent.Verdict.casesOn.{u_1} (fun (x_2 : LeanIntent.\
    Verdict) => motive LeanIntent.Consequence.Kind.possibility x_2) x_1 (h_3 Unit.unit) (h_4 U\
    nit.unit))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.\
    Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : mo\
    tive LeanIntent.Consequence.Kind.possibility), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Conseq\
    uence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (po\
    ssibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kin\
    d.rec.{u} motive entailment possibility t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Verdict.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Verdict), Sort u}, ∀ (t : LeanIntent.Verdict), ∀ (confirme\
    d : motive LeanIntent.Verdict.confirmed), ∀ (declined : motive LeanIntent.Verdict.declined\
    ), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Verdict), Sort u} => fun (t : LeanIntent.Verdict) => fun\
    \x20(confirmed : motive LeanIntent.Verdict.confirmed) => fun (declined : motive LeanIntent\
    .Verdict.declined) => @LeanIntent.Verdict.rec.{u} motive confirmed declined t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.kind\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.consequence\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 1, counted after the parameters in the type of LeanIntent.Ans\
    wer's constructor, of its argument number 2, a value of LeanIntent.Answer. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Answer.{u} W), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.verdict\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Ans\
    wer's constructor, of its argument number 2, a value of LeanIntent.Answer. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Answer.{u} W), LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Meets\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@Lean\
    Intent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Dom\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.dom\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Cla\
    use's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Props\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.props\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.HasInstance\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)\n\
    | ```\n\
    | \n\
    | ## Lean's own libraries\n\
    | \n\
    | The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: the\
    y are those of Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, which made th\
    is text. A declaration is counted as Lean's own when Lean found the module that declares i\
    t in that release's library directory.\n\
    | \n\
    verdict confirmed\n\
    ",
  "lean-intent statement 1\n\
    kind answer\n\
    project acorn\n\
    id hash-6-r2\n\
    date 2026-11-03\n\
    reference docs/spec-first-pilot.md, The decisions made on the owner's behalf\n\
    by agents\n\
    under agents-below-intent\n\
    record AcornVerif.Intent.Hash.hashes\n\
    revision 740\n\
    | # The intent record AcornVerif.Intent.Hash.hashes\n\
    | \n\
    | Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term \
    its kernel checks, binder names and metadata aside, from the root namespace with nothing o\
    pened. The plain words after it are written by a model and are trusted, not proved.\n\
    | \n\
    | ## Shape\n\
    | \n\
    | ### The subject\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Shape.value.{0} AcornVerif.Intent.Hash.Hashes\n\
    | ```\n\
    | \n\
    | - **Requires:** The subject is the pair of hash functions, each taking three 64-bit inpu\
    ts to one 64-bit spot.\n\
    | - **Rules out:** Nothing by itself.\n\
    | - **Still allows:** Any pair of such functions, until the properties narrow it.\n\
    | - **Freedom O5 leaves:** None of its own. The pair carries no state from one call to the\
    \x20next, so it is declared a plain value, of which obligation O4 asks nothing.\n\
    | \n\
    | ## Domain hypotheses\n\
    | \n\
    | None.\n\
    | \n\
    | ## Properties\n\
    | \n\
    | ### changing any one input always moves the spot\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => And (AcornVerif.Intent.Hash.OneInputMoves (Ac\
    ornVerif.Intent.Hash.Hashes.hash2 w)) (AcornVerif.Intent.Hash.OneInputMoves (AcornVerif.In\
    tent.Hash.Hashes.hash3 w))\n\
    | ```\n\
    | \n\
    | - **Requires:** In each function, changing exactly one input, the others kept, always ch\
    anges the spot: never the same spot, not merely rarely.\n\
    | - **Rules out:** A function that ignores an input, and one where two values of one input\
    \x20share a spot for some values of the others.\n\
    | - **Still allows:** Any amount of sharing between inputs that differ in two or three pla\
    ces.\n\
    | - **Freedom O5 leaves:** Everything about inputs that differ in more than one place.\n\
    | \n\
    | ### no fixed rule of reordering and shifting the inputs keeps every spot\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => And (AcornVerif.Intent.Hash.NoRuleKeepsSpots \
    (AcornVerif.Intent.Hash.Hashes.hash2 w)) (AcornVerif.Intent.Hash.NoRuleKeepsSpots (AcornVe\
    rif.Intent.Hash.Hashes.hash3 w))\n\
    | ```\n\
    | \n\
    | - **Requires:** No fixed rule moves every input to a different input in the same spot. A\
    \x20rule here puts the three inputs in some order, then adds a fixed amount to each, or fl\
    ips fixed bits of each.\n\
    | - **Rules out:** Combining the inputs by plain exclusive or or plain addition, where swa\
    pping two inputs keeps the spot; and any function where adding the same amounts, or flippi\
    ng the same bits, keeps every spot.\n\
    | - **Still allows:** Rules of other kinds, such as multiplying the inputs by fixed number\
    s; and any number of inputs sharing spots without a fixed rule behind it.\n\
    | - **Freedom O5 leaves:** How often inputs share spots overall: the record bounds no rate\
    .\n\
    | \n\
    | ## Vocabulary\n\
    | \n\
    | ### same spot, a predicate over `Prod.{0, 0} UInt64 UInt64`\n\
    | \n\
    | ```lean\n\
    | fun (p : Prod.{0, 0} UInt64 UInt64) => @Eq.{1} UInt64 (@Prod.fst.{0, 0} UInt64 UInt64 p)\
    \x20(@Prod.snd.{0, 0} UInt64 UInt64 p)\n\
    | ```\n\
    | \n\
    | - **Requires:** Two spots are the same 64-bit value.\n\
    | - **Rules out:** Spots 0 and 1.\n\
    | - **Still allows:** Spots 0 and 0.\n\
    | - **Freedom O5 leaves:** None: it is equality.\n\
    | \n\
    | ## Consequences\n\
    | \n\
    | ### changing any one input always moves the spot, an entailment: every subject that meet\
    s the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => And (AcornVerif.Intent.Hash.OneInputMoves (Ac\
    ornVerif.Intent.Hash.Hashes.hash2 w)) (AcornVerif.Intent.Hash.OneInputMoves (AcornVerif.In\
    tent.Hash.Hashes.hash3 w))\n\
    | ```\n\
    | \n\
    | - **Requires:** Changing any one input always moves the spot, in both functions.\n\
    | - **Rules out:** Any single changed input landing in the same spot.\n\
    | - **Still allows:** Inputs that differ in two or three places sharing a spot.\n\
    | - **Freedom O5 leaves:** None beyond the property's.\n\
    | \n\
    | ### no fixed rule of reordering and shifting the inputs keeps every spot, an entailment:\
    \x20every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => And (AcornVerif.Intent.Hash.NoRuleKeepsSpots \
    (AcornVerif.Intent.Hash.Hashes.hash2 w)) (AcornVerif.Intent.Hash.NoRuleKeepsSpots (AcornVe\
    rif.Intent.Hash.Hashes.hash3 w))\n\
    | ```\n\
    | \n\
    | - **Requires:** No fixed reordering and shifting of the inputs keeps every spot.\n\
    | - **Rules out:** Systematic sharing by any such rule.\n\
    | - **Still allows:** Sharing by rules of other kinds, and sharing with no fixed rule.\n\
    | - **Freedom O5 leaves:** Which rules count as systematic beyond these.\n\
    | \n\
    | ### neither function combines its inputs by plain exclusive or or plain addition, an ent\
    ailment: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => And (@Ne.{1} (AcornVerif.Intent.Hash.Inputs →\
    \x20UInt64) (AcornVerif.Intent.Hash.Hashes.hash2 w) AcornVerif.Intent.Hash.xorAll) (And (@\
    Ne.{1} (AcornVerif.Intent.Hash.Inputs → UInt64) (AcornVerif.Intent.Hash.Hashes.hash2 w) Ac\
    ornVerif.Intent.Hash.addAll) (And (@Ne.{1} (AcornVerif.Intent.Hash.Inputs → UInt64) (Acorn\
    Verif.Intent.Hash.Hashes.hash3 w) AcornVerif.Intent.Hash.xorAll) (@Ne.{1} (AcornVerif.Inte\
    nt.Hash.Inputs → UInt64) (AcornVerif.Intent.Hash.Hashes.hash3 w) AcornVerif.Intent.Hash.ad\
    dAll)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Neither function combines its three inputs by plain exclusive or or by p\
    lain addition.\n\
    | - **Rules out:** Those two combinations, since swapping two inputs keeps their spot.\n\
    | - **Still allows:** Combinations that mix the inputs before combining them.\n\
    | - **Freedom O5 leaves:** None that this consequence adds.\n\
    | \n\
    | ### the same inputs always give the same spot, an entailment: every subject that meets t\
    he record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => ∀ (x : AcornVerif.Intent.Hash.Inputs), ∀ (y :\
    \x20AcornVerif.Intent.Hash.Inputs), @Eq.{1} AcornVerif.Intent.Hash.Inputs x y → And (@Eq.{\
    1} UInt64 (AcornVerif.Intent.Hash.Hashes.hash2 w x) (AcornVerif.Intent.Hash.Hashes.hash2 w\
    \x20y)) (@Eq.{1} UInt64 (AcornVerif.Intent.Hash.Hashes.hash3 w x) (AcornVerif.Intent.Hash.\
    Hashes.hash3 w y))\n\
    | ```\n\
    | \n\
    | - **Requires:** The same inputs always give the same spot, so a run can be replayed.\n\
    | - **Rules out:** Nothing: every function of this type meets it.\n\
    | - **Still allows:** Every pair of functions.\n\
    | - **Freedom O5 leaves:** None. It holds by construction; replay further trusts the compi\
    ler and the machine to compute 64-bit words alike everywhere.\n\
    | \n\
    | ## Definitions the record's meaning reaches\n\
    | \n\
    | These are not statements of the record: each is a declaration that a statement above dep\
    ends on, or that says what it is for a subject to meet the record and for a consequence to\
    \x20hold of it as shown, with everything those depend on in turn. Each is printed in full:\
    \x20its type, a definition's value, or for a definition by structural or well-founded recu\
    rsion the equation that determines it, and an inductive type's constructors, which for a s\
    tructure are its fields; a theorem's proof and an opaque constant's value are not, since n\
    o term that uses them depends on more than their types. Their plain words are those of the\
    \x20statements that use them.\n\
    | \n\
    | ### LeanIntent.Shape\n\
    | \n\
    | An inductive type. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type u → Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Shape.value\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.function\n\
    | \n\
    | ```lean\n\
    | ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.step\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.stepOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.action\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.actionOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u\
    } O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.bundle\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀\
    \x20(rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Member\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Member.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → \
    Out), LeanIntent.Member.{u} W\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Hashes\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Hashes.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (hash2 : AcornVerif.Intent.Hash.Inputs → UInt64), ∀ (hash3 : AcornVerif.Intent.Hash.In\
    puts → UInt64), AcornVerif.Intent.Hash.Hashes\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Inputs\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | Prod.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.OneInputMoves\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (f : AcornVerif.Intent.Hash.Inputs → UInt64), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (f : AcornVerif.Intent.Hash.Inputs → UInt64) => And (∀ (a : UInt64), ∀ (a' : UInt64)\
    , ∀ (b : UInt64), ∀ (c : UInt64), @Eq.{1} UInt64 (f (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} U\
    Int64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) (f (@Prod.mk.{0, 0} UInt64 (Prod.{0,\
    \x200} UInt64 UInt64) a' (@Prod.mk.{0, 0} UInt64 UInt64 b c))) → @Eq.{1} UInt64 a a') (And\
    \x20(∀ (a : UInt64), ∀ (b : UInt64), ∀ (b' : UInt64), ∀ (c : UInt64), @Eq.{1} UInt64 (f (@\
    Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) \
    (f (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b'\
    \x20c))) → @Eq.{1} UInt64 b b') (∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), ∀ (c' : U\
    Int64), @Eq.{1} UInt64 (f (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.\
    {0, 0} UInt64 UInt64 b c))) (f (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Pro\
    d.mk.{0, 0} UInt64 UInt64 b c'))) → @Eq.{1} UInt64 c c'))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Hashes.hash2\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 1, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Hashes's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash\
    .Hashes. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Hashes), AcornVerif.Intent.Hash.Inputs → UInt64\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Hashes.hash3\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 2, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Hashes's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash\
    .Hashes. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Hashes), AcornVerif.Intent.Hash.Inputs → UInt64\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.NoRuleKeepsSpots\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (f : AcornVerif.Intent.Hash.Inputs → UInt64), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (f : AcornVerif.Intent.Hash.Inputs → UInt64) => ∀ (r : AcornVerif.Intent.Hash.Rule),\
    \x20AcornVerif.Intent.Hash.Rule.Moves r → @Exists.{1} AcornVerif.Intent.Hash.Inputs (fun (\
    x : AcornVerif.Intent.Hash.Inputs) => @Ne.{1} UInt64 (f (AcornVerif.Intent.Hash.Rule.apply\
    \x20r x)) (f x))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Rule.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (order : AcornVerif.Intent.Hash.Order), ∀ (shift : AcornVerif.Intent.Hash.Shift), ∀ (a\
    mount : AcornVerif.Intent.Hash.Inputs), AcornVerif.Intent.Hash.Rule\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Order\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.abc\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.bac\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.acb\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.cba\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.bca\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Order.cab\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Shift\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Shift.flip\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Shift\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Shift.add\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Shift\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.Moves\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (r : AcornVerif.Intent.Hash.Rule), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (r : AcornVerif.Intent.Hash.Rule) => Not (And (@Eq.{1} AcornVerif.Intent.Hash.Order \
    (AcornVerif.Intent.Hash.Rule.order r) AcornVerif.Intent.Hash.Order.abc) (@Eq.{1} AcornVeri\
    f.Intent.Hash.Inputs (AcornVerif.Intent.Hash.Rule.amount r) (@Prod.mk.{0, 0} UInt64 (Prod.\
    {0, 0} UInt64 UInt64) (@OfNat.ofNat.{0} UInt64 (nat_lit 0) (@UInt64.instOfNat (nat_lit 0))\
    ) (@Prod.mk.{0, 0} UInt64 UInt64 (@OfNat.ofNat.{0} UInt64 (nat_lit 0) (@UInt64.instOfNat (\
    nat_lit 0))) (@OfNat.ofNat.{0} UInt64 (nat_lit 0) (@UInt64.instOfNat (nat_lit 0)))))))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.order\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 1, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Rule's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash.R\
    ule. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Rule), AcornVerif.Intent.Hash.Order\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.amount\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 3, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Rule's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash.R\
    ule. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Rule), AcornVerif.Intent.Hash.Inputs\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.apply\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (r : AcornVerif.Intent.Hash.Rule), ∀ (x : AcornVerif.Intent.Hash.Inputs), AcornVerif.I\
    ntent.Hash.Inputs\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (r : AcornVerif.Intent.Hash.Rule) => fun (x : AcornVerif.Intent.Hash.Inputs) => Acor\
    nVerif.Intent.Hash.Rule.apply.match_1.{1} (fun (x_1 : AcornVerif.Intent.Hash.Inputs) => Ac\
    ornVerif.Intent.Hash.Inputs) (AcornVerif.Intent.Hash.Order.apply (AcornVerif.Intent.Hash.R\
    ule.order r) x) (fun (a : UInt64) => fun (b : UInt64) => fun (c : UInt64) => @Prod.mk.{0, \
    0} UInt64 (Prod.{0, 0} UInt64 UInt64) (AcornVerif.Intent.Hash.Shift.apply (AcornVerif.Inte\
    nt.Hash.Rule.shift r) a (@Prod.fst.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (AcornVerif.I\
    ntent.Hash.Rule.amount r))) (@Prod.mk.{0, 0} UInt64 UInt64 (AcornVerif.Intent.Hash.Shift.a\
    pply (AcornVerif.Intent.Hash.Rule.shift r) b (@Prod.fst.{0, 0} UInt64 UInt64 (@Prod.snd.{0\
    , 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (AcornVerif.Intent.Hash.Rule.amount r)))) (AcornVe\
    rif.Intent.Hash.Shift.apply (AcornVerif.Intent.Hash.Rule.shift r) c (@Prod.snd.{0, 0} UInt\
    64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (AcornVerif.Intent.Hash.Rul\
    e.amount r))))))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.apply.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : AcornVerif.Intent.Hash.Inputs → Sort u_1), ∀ (x : AcornVerif.Intent.Hash.Inp\
    uts), ∀ (h_1 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive (@Prod.mk.{0, 0} UIn\
    t64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))), motive x\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : AcornVerif.Intent.Hash.Inputs → Sort u_1) => fun (x : AcornVerif.Intent.Ha\
    sh.Inputs) => fun (h_1 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive (@Prod.mk.\
    {0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) => @Prod\
    .casesOn.{u_1, 0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (fun (x_1 : AcornVerif.Intent.Hash\
    .Inputs) => motive x_1) x (fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => \
    @Prod.casesOn.{u_1, 0, 0} UInt64 UInt64 (fun (x_1 : Prod.{0, 0} UInt64 UInt64) => motive (\
    @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_1)) snd (fun (x_1 : UInt64) => fu\
    n (x_2 : UInt64) => h_1 fst x_1 x_2))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Order.apply\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Order → AcornVerif.Intent.Hash.Inputs → AcornVerif.Intent.Hash.In\
    puts\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (x : AcornVerif.Intent.Hash.Order) => fun (x_1 : AcornVerif.Intent.Hash.Inputs) => A\
    cornVerif.Intent.Hash.Order.apply.match_1.{1} (fun (x_2 : AcornVerif.Intent.Hash.Order) =>\
    \x20fun (x_3 : AcornVerif.Intent.Hash.Inputs) => AcornVerif.Intent.Hash.Inputs) x x_1 (fun\
    \x20(a : UInt64) => fun (b : UInt64) => fun (c : UInt64) => @Prod.mk.{0, 0} UInt64 (Prod.{\
    0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c)) (fun (a : UInt64) => fun (b : \
    UInt64) => fun (c : UInt64) => @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) b (@Prod\
    .mk.{0, 0} UInt64 UInt64 a c)) (fun (a : UInt64) => fun (b : UInt64) => fun (c : UInt64) =\
    > @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 c b)\
    ) (fun (a : UInt64) => fun (b : UInt64) => fun (c : UInt64) => @Prod.mk.{0, 0} UInt64 (Pro\
    d.{0, 0} UInt64 UInt64) c (@Prod.mk.{0, 0} UInt64 UInt64 b a)) (fun (a : UInt64) => fun (b\
    \x20: UInt64) => fun (c : UInt64) => @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) b \
    (@Prod.mk.{0, 0} UInt64 UInt64 c a)) (fun (a : UInt64) => fun (b : UInt64) => fun (c : UIn\
    t64) => @Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) c (@Prod.mk.{0, 0} UInt64 UInt6\
    4 a b))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Order.apply.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : AcornVerif.Intent.Hash.Order → AcornVerif.Intent.Hash.Inputs → Sort u_1), ∀ \
    (x : AcornVerif.Intent.Hash.Order), ∀ (x_1 : AcornVerif.Intent.Hash.Inputs), ∀ (h_1 : ∀ (a\
    \x20: UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Order.abc (@P\
    rod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))), \
    ∀ (h_2 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Ord\
    er.bac (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt6\
    4 b c))), ∀ (h_3 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Inten\
    t.Hash.Order.acb (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UI\
    nt64 UInt64 b c))), ∀ (h_4 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornV\
    erif.Intent.Hash.Order.cba (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk\
    .{0, 0} UInt64 UInt64 b c))), ∀ (h_5 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), mot\
    ive AcornVerif.Intent.Hash.Order.bca (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a\
    \x20(@Prod.mk.{0, 0} UInt64 UInt64 b c))), ∀ (h_6 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c :\
    \x20UInt64), motive AcornVerif.Intent.Hash.Order.cab (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} \
    UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))), motive x x_1\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : AcornVerif.Intent.Hash.Order → AcornVerif.Intent.Hash.Inputs → Sort u_1) =\
    > fun (x : AcornVerif.Intent.Hash.Order) => fun (x_1 : AcornVerif.Intent.Hash.Inputs) => f\
    un (h_1 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Or\
    der.abc (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt\
    64 b c))) => fun (h_2 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.\
    Intent.Hash.Order.bac (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, \
    0} UInt64 UInt64 b c))) => fun (h_3 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c : UInt64), moti\
    ve AcornVerif.Intent.Hash.Order.acb (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a \
    (@Prod.mk.{0, 0} UInt64 UInt64 b c))) => fun (h_4 : ∀ (a : UInt64), ∀ (b : UInt64), ∀ (c :\
    \x20UInt64), motive AcornVerif.Intent.Hash.Order.cba (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} \
    UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) => fun (h_5 : ∀ (a : UInt64), ∀ (b \
    : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Order.bca (@Prod.mk.{0, 0} UInt64\
    \x20(Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) => fun (h_6 : ∀ (a\
    \x20: UInt64), ∀ (b : UInt64), ∀ (c : UInt64), motive AcornVerif.Intent.Hash.Order.cab (@P\
    rod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) a (@Prod.mk.{0, 0} UInt64 UInt64 b c))) =\
    > @AcornVerif.Intent.Hash.Order.casesOn.{u_1} (fun (x_2 : AcornVerif.Intent.Hash.Order) =>\
    \x20motive x_2 x_1) x (@Prod.casesOn.{u_1, 0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (fun (\
    x_2 : AcornVerif.Intent.Hash.Inputs) => motive AcornVerif.Intent.Hash.Order.abc x_2) x_1 (\
    fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => @Prod.casesOn.{u_1, 0, 0} U\
    Int64 UInt64 (fun (x_2 : Prod.{0, 0} UInt64 UInt64) => motive AcornVerif.Intent.Hash.Order\
    .abc (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_2)) snd (fun (x_2 : UInt64)\
    \x20=> fun (x_3 : UInt64) => h_1 fst x_2 x_3))) (@Prod.casesOn.{u_1, 0, 0} UInt64 (Prod.{0\
    , 0} UInt64 UInt64) (fun (x_2 : AcornVerif.Intent.Hash.Inputs) => motive AcornVerif.Intent\
    .Hash.Order.bac x_2) x_1 (fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => @\
    Prod.casesOn.{u_1, 0, 0} UInt64 UInt64 (fun (x_2 : Prod.{0, 0} UInt64 UInt64) => motive Ac\
    ornVerif.Intent.Hash.Order.bac (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_2\
    )) snd (fun (x_2 : UInt64) => fun (x_3 : UInt64) => h_2 fst x_2 x_3))) (@Prod.casesOn.{u_1\
    , 0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (fun (x_2 : AcornVerif.Intent.Hash.Inputs) => m\
    otive AcornVerif.Intent.Hash.Order.acb x_2) x_1 (fun (fst : UInt64) => fun (snd : Prod.{0,\
    \x200} UInt64 UInt64) => @Prod.casesOn.{u_1, 0, 0} UInt64 UInt64 (fun (x_2 : Prod.{0, 0} U\
    Int64 UInt64) => motive AcornVerif.Intent.Hash.Order.acb (@Prod.mk.{0, 0} UInt64 (Prod.{0,\
    \x200} UInt64 UInt64) fst x_2)) snd (fun (x_2 : UInt64) => fun (x_3 : UInt64) => h_3 fst x\
    _2 x_3))) (@Prod.casesOn.{u_1, 0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) (fun (x_2 : AcornV\
    erif.Intent.Hash.Inputs) => motive AcornVerif.Intent.Hash.Order.cba x_2) x_1 (fun (fst : U\
    Int64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => @Prod.casesOn.{u_1, 0, 0} UInt64 UInt64\
    \x20(fun (x_2 : Prod.{0, 0} UInt64 UInt64) => motive AcornVerif.Intent.Hash.Order.cba (@Pr\
    od.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_2)) snd (fun (x_2 : UInt64) => fun (\
    x_3 : UInt64) => h_4 fst x_2 x_3))) (@Prod.casesOn.{u_1, 0, 0} UInt64 (Prod.{0, 0} UInt64 \
    UInt64) (fun (x_2 : AcornVerif.Intent.Hash.Inputs) => motive AcornVerif.Intent.Hash.Order.\
    bca x_2) x_1 (fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 UInt64) => @Prod.casesOn\
    .{u_1, 0, 0} UInt64 UInt64 (fun (x_2 : Prod.{0, 0} UInt64 UInt64) => motive AcornVerif.Int\
    ent.Hash.Order.bca (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) fst x_2)) snd (fun \
    (x_2 : UInt64) => fun (x_3 : UInt64) => h_5 fst x_2 x_3))) (@Prod.casesOn.{u_1, 0, 0} UInt\
    64 (Prod.{0, 0} UInt64 UInt64) (fun (x_2 : AcornVerif.Intent.Hash.Inputs) => motive AcornV\
    erif.Intent.Hash.Order.cab x_2) x_1 (fun (fst : UInt64) => fun (snd : Prod.{0, 0} UInt64 U\
    Int64) => @Prod.casesOn.{u_1, 0, 0} UInt64 UInt64 (fun (x_2 : Prod.{0, 0} UInt64 UInt64) =\
    > motive AcornVerif.Intent.Hash.Order.cab (@Prod.mk.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt\
    64) fst x_2)) snd (fun (x_2 : UInt64) => fun (x_3 : UInt64) => h_6 fst x_2 x_3)))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Order.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : AcornVerif.Intent.Hash.Order), Sort u}, ∀ (t : AcornVerif.Intent.Hash\
    .Order), ∀ (abc : motive AcornVerif.Intent.Hash.Order.abc), ∀ (bac : motive AcornVerif.Int\
    ent.Hash.Order.bac), ∀ (acb : motive AcornVerif.Intent.Hash.Order.acb), ∀ (cba : motive Ac\
    ornVerif.Intent.Hash.Order.cba), ∀ (bca : motive AcornVerif.Intent.Hash.Order.bca), ∀ (cab\
    \x20: motive AcornVerif.Intent.Hash.Order.cab), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : AcornVerif.Intent.Hash.Order), Sort u} => fun (t : AcornVerif.Inten\
    t.Hash.Order) => fun (abc : motive AcornVerif.Intent.Hash.Order.abc) => fun (bac : motive \
    AcornVerif.Intent.Hash.Order.bac) => fun (acb : motive AcornVerif.Intent.Hash.Order.acb) =\
    > fun (cba : motive AcornVerif.Intent.Hash.Order.cba) => fun (bca : motive AcornVerif.Inte\
    nt.Hash.Order.bca) => fun (cab : motive AcornVerif.Intent.Hash.Order.cab) => @AcornVerif.I\
    ntent.Hash.Order.rec.{u} motive abc bac acb cba bca cab t\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Shift.apply\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.Hash.Shift → UInt64 → UInt64 → UInt64\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (x : AcornVerif.Intent.Hash.Shift) => fun (x_1 : UInt64) => fun (x_2 : UInt64) => Ac\
    ornVerif.Intent.Hash.Shift.apply.match_1.{1} (fun (x_3 : AcornVerif.Intent.Hash.Shift) => \
    fun (x_4 : UInt64) => fun (x_5 : UInt64) => UInt64) x x_1 x_2 (fun (x_3 : UInt64) => fun (\
    d : UInt64) => @HXor.hXor.{0, 0, 0} UInt64 UInt64 UInt64 (@instHXorOfXorOp.{0} UInt64 inst\
    XorOpUInt64) x_3 d) (fun (x_3 : UInt64) => fun (d : UInt64) => @HAdd.hAdd.{0, 0, 0} UInt64\
    \x20UInt64 UInt64 (@instHAdd.{0} UInt64 instAddUInt64) x_3 d)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Shift.apply.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : AcornVerif.Intent.Hash.Shift → UInt64 → UInt64 → Sort u_1), ∀ (x : AcornVeri\
    f.Intent.Hash.Shift), ∀ (x_1 : UInt64), ∀ (x_2 : UInt64), ∀ (h_1 : ∀ (x_3 : UInt64), ∀ (d \
    : UInt64), motive AcornVerif.Intent.Hash.Shift.flip x_3 d), ∀ (h_2 : ∀ (x_3 : UInt64), ∀ (\
    d : UInt64), motive AcornVerif.Intent.Hash.Shift.add x_3 d), motive x x_1 x_2\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : AcornVerif.Intent.Hash.Shift → UInt64 → UInt64 → Sort u_1) => fun (x : Aco\
    rnVerif.Intent.Hash.Shift) => fun (x_1 : UInt64) => fun (x_2 : UInt64) => fun (h_1 : ∀ (x_\
    3 : UInt64), ∀ (d : UInt64), motive AcornVerif.Intent.Hash.Shift.flip x_3 d) => fun (h_2 :\
    \x20∀ (x_3 : UInt64), ∀ (d : UInt64), motive AcornVerif.Intent.Hash.Shift.add x_3 d) => @A\
    cornVerif.Intent.Hash.Shift.casesOn.{u_1} (fun (x_3 : AcornVerif.Intent.Hash.Shift) => mot\
    ive x_3 x_1 x_2) x (h_1 x_1 x_2) (h_2 x_1 x_2)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Shift.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : AcornVerif.Intent.Hash.Shift), Sort u}, ∀ (t : AcornVerif.Intent.Hash\
    .Shift), ∀ (flip : motive AcornVerif.Intent.Hash.Shift.flip), ∀ (add : motive AcornVerif.I\
    ntent.Hash.Shift.add), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : AcornVerif.Intent.Hash.Shift), Sort u} => fun (t : AcornVerif.Inten\
    t.Hash.Shift) => fun (flip : motive AcornVerif.Intent.Hash.Shift.flip) => fun (add : motiv\
    e AcornVerif.Intent.Hash.Shift.add) => @AcornVerif.Intent.Hash.Shift.rec.{u} motive flip a\
    dd t\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Rule.shift\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 2, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Rule's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash.R\
    ule. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Rule), AcornVerif.Intent.Hash.Shift\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.xorAll\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (x : AcornVerif.Intent.Hash.Inputs), UInt64\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (x : AcornVerif.Intent.Hash.Inputs) => @HXor.hXor.{0, 0, 0} UInt64 UInt64 UInt64 (@i\
    nstHXorOfXorOp.{0} UInt64 instXorOpUInt64) (@HXor.hXor.{0, 0, 0} UInt64 UInt64 UInt64 (@in\
    stHXorOfXorOp.{0} UInt64 instXorOpUInt64) (@Prod.fst.{0, 0} UInt64 (Prod.{0, 0} UInt64 UIn\
    t64) x) (@Prod.fst.{0, 0} UInt64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt6\
    4) x))) (@Prod.snd.{0, 0} UInt64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt6\
    4) x))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.addAll\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (x : AcornVerif.Intent.Hash.Inputs), UInt64\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (x : AcornVerif.Intent.Hash.Inputs) => @HAdd.hAdd.{0, 0, 0} UInt64 UInt64 UInt64 (@i\
    nstHAdd.{0} UInt64 instAddUInt64) (@HAdd.hAdd.{0, 0, 0} UInt64 UInt64 UInt64 (@instHAdd.{0\
    } UInt64 instAddUInt64) (@Prod.fst.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) x) (@Prod.fst\
    .{0, 0} UInt64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) x))) (@Prod.snd\
    .{0, 0} UInt64 UInt64 (@Prod.snd.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64) x))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Meets\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@Lean\
    Intent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.IntentRecord.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause\
    .{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanInte\
    nt.Pred.{u}), LeanIntent.IntentRecord.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Clause.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Pred\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Pred.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Dom\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.dom\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Cla\
    use's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Props\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.props\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.HoldsOf\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (c : LeanIntent.Consequence.{u} W), ∀ (r : LeanIntent.IntentRecord.{u}\
    \x20W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (c : LeanIntent.Consequence.{u} W) => fun (r : LeanIntent.Intent\
    Record.{u} W) => LeanIntent.Consequence.HoldsOf.match_1.{1} (fun (x : LeanIntent.Consequen\
    ce.Kind) => Prop) (@LeanIntent.Consequence.kind.{u} W c) (fun («_» : Unit) => ∀ (w : W), @\
    LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W c w) (fun («\
    _» : Unit) => @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRec\
    ord.Meets.{u} W r w) (@LeanIntent.Consequence.holds.{u} W c w)))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W \
    → Prop), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.entailment\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.possibility\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.HoldsOf.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : LeanIntent.Consequence.Kind → Sort u_1), ∀ (x : LeanIntent.Consequence.Kind)\
    , ∀ (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment), ∀ (h_2 : ∀ («_»\
    \x20: Unit), motive LeanIntent.Consequence.Kind.possibility), motive x\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : LeanIntent.Consequence.Kind → Sort u_1) => fun (x : LeanIntent.Consequence\
    .Kind) => fun (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment) => fun\
    \x20(h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.\
    Consequence.Kind.casesOn.{u_1} (fun (x_1 : LeanIntent.Consequence.Kind) => motive x_1) x (\
    h_1 Unit.unit) (h_2 Unit.unit)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.\
    Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : mo\
    tive LeanIntent.Consequence.Kind.possibility), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Conseq\
    uence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (po\
    ssibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kin\
    d.rec.{u} motive entailment possibility t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.kind\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.HasInstance\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)\n\
    | ```\n\
    | \n\
    | ## Lean's own libraries\n\
    | \n\
    | The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: the\
    y are those of Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, which made th\
    is text. A declaration is counted as Lean's own when Lean found the module that declares i\
    t in that release's library directory.\n\
    | \n\
    consequence the same inputs always give the same spot\n\
    shown as entailment\n\
    predicate 422\n\
    | # A consequence's predicate\n\
    | \n\
    | Printed exactly: as Lean syntax that Lean elaborates back to the term its kernel checks,\
    \x20binder names and metadata aside, from the root namespace with nothing opened.\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.Hash.Hashes) => ∀ (x : AcornVerif.Intent.Hash.Inputs), ∀ (y :\
    \x20AcornVerif.Intent.Hash.Inputs), @Eq.{1} AcornVerif.Intent.Hash.Inputs x y → And (@Eq.{\
    1} UInt64 (AcornVerif.Intent.Hash.Hashes.hash2 w x) (AcornVerif.Intent.Hash.Hashes.hash2 w\
    \x20y)) (@Eq.{1} UInt64 (AcornVerif.Intent.Hash.Hashes.hash3 w x) (AcornVerif.Intent.Hash.\
    Hashes.hash3 w y))\n\
    | ```\n\
    | \n\
    | ## Definitions the predicate reaches\n\
    | \n\
    | Each is printed in full, as in the rendering of a record, with what an answer to it asks\
    \x20of every later revision (`LeanIntent.Answer.KeptBy`).\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Hashes\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.Hash.Hashes.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (hash2 : AcornVerif.Intent.Hash.Inputs → UInt64), ∀ (hash3 : AcornVerif.Intent.Hash.In\
    puts → UInt64), AcornVerif.Intent.Hash.Hashes\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Inputs\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | Prod.{0, 0} UInt64 (Prod.{0, 0} UInt64 UInt64)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Hashes.hash2\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 1, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Hashes's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash\
    .Hashes. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Hashes), AcornVerif.Intent.Hash.Inputs → UInt64\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.Hash.Hashes.hash3\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argume\
    nts and returns field number 2, counted after the parameters in the type of AcornVerif.Int\
    ent.Hash.Hashes's constructor, of its argument number 1, a value of AcornVerif.Intent.Hash\
    .Hashes. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.Hash.Hashes), AcornVerif.Intent.Hash.Inputs → UInt64\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.KeptBy\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (a : LeanIntent.Answer.{u} W), ∀ (r : LeanIntent.IntentRecord.{u} W), \
    Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (a : LeanIntent.Answer.{u} W) => fun (r : LeanIntent.IntentRecor\
    d.{u} W) => LeanIntent.Answer.KeptBy.match_1.{1} (fun (x : LeanIntent.Consequence.Kind) =>\
    \x20fun (x_1 : LeanIntent.Verdict) => Prop) (@LeanIntent.Consequence.kind.{u} W (@LeanInte\
    nt.Answer.consequence.{u} W a)) (@LeanIntent.Answer.verdict.{u} W a) (fun («_» : Unit) => \
    ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W \
    (@LeanIntent.Answer.consequence.{u} W a) w) (fun («_» : Unit) => @LeanIntent.HasInstance.{\
    u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u} W r w) (Not (@LeanIntent.\
    Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w)))) (fun («_» : Unit) =\
    > @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.Meets.{u\
    } W r w) (@LeanIntent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w))\
    ) (fun («_» : Unit) => ∀ (w : W), @LeanIntent.IntentRecord.Meets.{u} W r w → Not (@LeanInt\
    ent.Consequence.holds.{u} W (@LeanIntent.Answer.consequence.{u} W a) w))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Answer.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (consequence : LeanIntent.Consequence.{u} W), ∀ (verdict : LeanIntent.\
    Verdict), LeanIntent.Answer.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W \
    → Prop), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.entailment\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.possibility\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Verdict\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Verdict.confirmed\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Verdict.declined\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.IntentRecord.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause\
    .{u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanInte\
    nt.Pred.{u}), LeanIntent.IntentRecord.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Shape\n\
    | \n\
    | An inductive type. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type u → Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Shape.value\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.function\n\
    | \n\
    | ```lean\n\
    | ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.step\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.stepOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.action\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.actionOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u\
    } O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.bundle\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀\
    \x20(rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Member\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Member.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → \
    Out), LeanIntent.Member.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Clause.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Pred\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameter\
    s are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its\
    \x20recursor is the one Lean's kernel derives from this declaration. Its constructors, in \
    order, each with its type:\n\
    | \n\
    | #### LeanIntent.Pred.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.KeptBy.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : LeanIntent.Consequence.Kind → LeanIntent.Verdict → Sort u_1), ∀ (x : LeanInt\
    ent.Consequence.Kind), ∀ (x_1 : LeanIntent.Verdict), ∀ (h_1 : ∀ («_» : Unit), motive LeanI\
    ntent.Consequence.Kind.entailment LeanIntent.Verdict.confirmed), ∀ (h_2 : ∀ («_» : Unit), \
    motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.declined), ∀ (h_3 : ∀ («_\
    » : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdict.confirmed), ∀\
    \x20(h_4 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent.Verdi\
    ct.declined), motive x x_1\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : LeanIntent.Consequence.Kind → LeanIntent.Verdict → Sort u_1) => fun (x : L\
    eanIntent.Consequence.Kind) => fun (x_1 : LeanIntent.Verdict) => fun (h_1 : ∀ («_» : Unit)\
    , motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.confirmed) => fun (h_2 \
    : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment LeanIntent.Verdict.decline\
    d) => fun (h_3 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility LeanIntent\
    .Verdict.confirmed) => fun (h_4 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possi\
    bility LeanIntent.Verdict.declined) => @LeanIntent.Consequence.Kind.casesOn.{u_1} (fun (x_\
    2 : LeanIntent.Consequence.Kind) => motive x_2 x_1) x (@LeanIntent.Verdict.casesOn.{u_1} (\
    fun (x_2 : LeanIntent.Verdict) => motive LeanIntent.Consequence.Kind.entailment x_2) x_1 (\
    h_1 Unit.unit) (h_2 Unit.unit)) (@LeanIntent.Verdict.casesOn.{u_1} (fun (x_2 : LeanIntent.\
    Verdict) => motive LeanIntent.Consequence.Kind.possibility x_2) x_1 (h_3 Unit.unit) (h_4 U\
    nit.unit))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.\
    Kind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : mo\
    tive LeanIntent.Consequence.Kind.possibility), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Conseq\
    uence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (po\
    ssibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kin\
    d.rec.{u} motive entailment possibility t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Verdict.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Verdict), Sort u}, ∀ (t : LeanIntent.Verdict), ∀ (confirme\
    d : motive LeanIntent.Verdict.confirmed), ∀ (declined : motive LeanIntent.Verdict.declined\
    ), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Verdict), Sort u} => fun (t : LeanIntent.Verdict) => fun\
    \x20(confirmed : motive LeanIntent.Verdict.confirmed) => fun (declined : motive LeanIntent\
    .Verdict.declined) => @LeanIntent.Verdict.rec.{u} motive confirmed declined t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.kind\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.consequence\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 1, counted after the parameters in the type of LeanIntent.Ans\
    wer's constructor, of its argument number 2, a value of LeanIntent.Answer. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Answer.{u} W), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Answer.verdict\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Ans\
    wer's constructor, of its argument number 2, a value of LeanIntent.Answer. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Answer.{u} W), LeanIntent.Verdict\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Meets\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@Lean\
    Intent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Dom\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.dom\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 2, counted after the parameters in the type of LeanIntent.Cla\
    use's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the univ\
    erse parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Props\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : Lea\
    nIntent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInt\
    ent.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.Inten\
    tRecord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.props\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Int\
    entRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It \
    has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u\
    } W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argume\
    nts and returns field number 3, counted after the parameters in the type of LeanIntent.Con\
    sequence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It ha\
    s the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.HasInstance\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)\n\
    | ```\n\
    | \n\
    | ## Lean's own libraries\n\
    | \n\
    | The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: the\
    y are those of Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, which made th\
    is text. A declaration is counted as Lean's own when Lean found the module that declares i\
    t in that release's library directory.\n\
    | \n\
    verdict confirmed\n\
    ",
  "lean-intent statement 1\n\
    kind origin\n\
    project acorn\n\
    id contract-1-origin\n\
    date 2026-11-03\n\
    words 1\n\
    | yes, and ensure that each contract has citations and links to their sources\n\
    by owner\n\
    as owner\n\
    record AcornVerif.Intent.WorldInterface.worldInterface\n\
    written by the agents that work on Acorn, from a research report on the research of Rich Su\
    tton, Khurram Javed and Oak Lab that a second model from another provider audited\n\
    had read 1\n\
    | the research report and Acorn's mission contract, whose design sections describe the exec\
    uting kernel, host and agent; which parts of the implementation, and of the work that chang\
    ed it, they read while writing is not recorded\n\
    adopted 8\n\
    | 1. Each step, the world sends the agent an observation and a scalar reward, and the agent\
    \x20answers with one of the actions the world makes available.\n\
    | 2. The set of actions is fixed in advance for each world.\n\
    | 3. Any further signal a world provides, such as a task signal, is part of the observation\
    .\n\
    | 4. The observation need not reveal the world's state, and the world generates the reward \
    outside the agent's direct control.\n\
    | 5. Everything the agent learns comes from these signals, never from the world's internal \
    variables.\n\
    | 6. No host, viewer or tool writes what the agent learns or decides; the viewer can only s\
    top it.\n\
    | 7. A world may restart, between attempts or by its own rules, as part of its own dynamics\
    , and a restart may be the agent's own action, as ARC-AGI-3's RESET is; the agent never res\
    tarts, and its memory is never reset.\n\
    | 8. Every world Acorn runs (the tile world, each ARC-AGI-3 game and the Microduck) meets t\
    his one interface.\n\
    ",
  "lean-intent statement 1\n\
    kind answer\n\
    project acorn\n\
    id contract-1-restatement\n\
    date 2026-11-03\n\
    words 1\n\
    | yes, and ensure that each contract has citations and links to their sources\n\
    by owner\n\
    as owner\n\
    record AcornVerif.Intent.WorldInterface.worldInterface\n\
    revision 1220\n\
    | # The intent record AcornVerif.Intent.WorldInterface.worldInterface\n\
    | \n\
    | Each statement is printed exactly: as Lean syntax that Lean elaborates back to the term i\
    ts kernel checks, binder names and metadata aside, from the root namespace with nothing ope\
    ned. The plain words after it are written by a model and are trusted, not proved.\n\
    | \n\
    | ## Shape\n\
    | \n\
    | ### The subject\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Shape.value.{1} AcornVerif.Intent.WorldInterface.System\n\
    | ```\n\
    | \n\
    | - **Requires:** Nothing of its own: the subject is a description of one world, one agent \
    and the run that couples them, over types each world chooses, declared a plain value.\n\
    | - **Rules out:** Nothing of its own.\n\
    | - **Still allows:** A world whose observation or reward is constant and an agent whose an\
    swer is constant, none of which a shape that asks every function to vary with its input wou\
    ld admit; and a world that never changes state.\n\
    | - **Freedom O5 leaves:** Two systems that meet the record may differ in everything the pr\
    operties leave open: the world's types, start, observation, reward, dynamics and set of act\
    ions, the agent, the input type and the stop request, when a host stops the run, how long a\
    fter the viewer's request it stops, and what the run's parts give at any state, memory and \
    input from which no run takes a step.\n\
    | \n\
    | ## Domain hypotheses\n\
    | \n\
    | None.\n\
    | \n\
    | ## Properties\n\
    | \n\
    | ### each step, the agent is given the world's observation of its current state\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => ∀ (ins : Nat → AcornVerif.Intent.Wor\
    ldInterface.System.Input w), ∀ (t : Nat), ∀ (s : AcornVerif.Intent.WorldInterface.System.St\
    ate w), ∀ (m : AcornVerif.Intent.WorldInterface.System.Memory w), AcornVerif.Intent.WorldIn\
    terface.System.Takes w ins t s m → @Eq.{1} (AcornVerif.Intent.WorldInterface.System.Obs w) \
    (@Prod.fst.{0, 0} (AcornVerif.Intent.WorldInterface.System.Obs w) Rat (AcornVerif.Intent.Wo\
    rldInterface.System.given w s m (ins t))) (AcornVerif.Intent.WorldInterface.System.observe \
    w s)\n\
    | ```\n\
    | \n\
    | - **Requires:** For every sequence of outside inputs, every time, and every state and mem\
    ory at which the run takes a step, the observation the run gives the agent is the world's o\
    bservation of that state.\n\
    | - **Rules out:** A run that, at a step it takes, gives the agent any other observation: t\
    he world's state where its observation hides it, or a task signal its observation does not \
    carry.\n\
    | - **Still allows:** Any observation a world makes of its state, from one that shows nothi\
    ng of it to one that shows all of it.\n\
    | - **Freedom O5 leaves:** What the world shows, and what the run would give at steps no ru\
    n takes.\n\
    | \n\
    | ### each step, the agent is given the reward the world generates at its current state\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => ∀ (ins : Nat → AcornVerif.Intent.Wor\
    ldInterface.System.Input w), ∀ (t : Nat), ∀ (s : AcornVerif.Intent.WorldInterface.System.St\
    ate w), ∀ (m : AcornVerif.Intent.WorldInterface.System.Memory w), AcornVerif.Intent.WorldIn\
    terface.System.Takes w ins t s m → @Eq.{1} Rat (@Prod.snd.{0, 0} (AcornVerif.Intent.WorldIn\
    terface.System.Obs w) Rat (AcornVerif.Intent.WorldInterface.System.given w s m (ins t))) (A\
    cornVerif.Intent.WorldInterface.System.reward w s)\n\
    | ```\n\
    | \n\
    | - **Requires:** For every sequence of outside inputs, every time, and every state and mem\
    ory at which the run takes a step, the reward the run gives the agent is the reward the wor\
    ld generates at that state.\n\
    | - **Rules out:** A run that, at a step it takes, gives the agent another reward, such as \
    one taken from the agent's own memory.\n\
    | - **Still allows:** Any rational reward the world generates from its state, which the age\
    nt's actions reach only by changing that state.\n\
    | - **Freedom O5 leaves:** The world's reward, and what the run would give at steps no run \
    takes.\n\
    | \n\
    | ### each step, the agent answers with an action the world makes available\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => ∀ (ins : Nat → AcornVerif.Intent.Wor\
    ldInterface.System.Input w), ∀ (t : Nat), ∀ (s : AcornVerif.Intent.WorldInterface.System.St\
    ate w), ∀ (m : AcornVerif.Intent.WorldInterface.System.Memory w), AcornVerif.Intent.WorldIn\
    terface.System.Takes w ins t s m → AcornVerif.Intent.WorldInterface.System.available w s (@\
    Prod.fst.{0, 0} (AcornVerif.Intent.WorldInterface.System.Act w) (AcornVerif.Intent.WorldInt\
    erface.System.Memory w) (AcornVerif.Intent.WorldInterface.System.answer w s m (ins t)))\n\
    | ```\n\
    | \n\
    | - **Requires:** For every sequence of outside inputs, every time, and every state and mem\
    ory at which the run takes a step, the action the agent answers is one the world makes avai\
    lable at that state.\n\
    | - **Rules out:** An agent that, at a step a run takes, answers with an action the world d\
    oes not make available.\n\
    | - **Still allows:** An agent that would answer otherwise to observations and rewards no r\
    un gives it.\n\
    | - **Freedom O5 leaves:** Which available action the agent chooses.\n\
    | \n\
    | ### the world makes the same actions available at every one of its states\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => ∀ (s : AcornVerif.Intent.WorldInterf\
    ace.System.State w), ∀ (s' : AcornVerif.Intent.WorldInterface.System.State w), ∀ (a : Acorn\
    Verif.Intent.WorldInterface.System.Act w), Iff (AcornVerif.Intent.WorldInterface.System.ava\
    ilable w s a) (AcornVerif.Intent.WorldInterface.System.available w s' a)\n\
    | ```\n\
    | \n\
    | - **Requires:** For every two states of the world and every action, the world makes the a\
    ction available at the one exactly when it makes it available at the other.\n\
    | - **Rules out:** A world whose available actions differ between two of its states, reache\
    d by a run or not, such as a game that makes RESET its only action at game over.\n\
    | - **Still allows:** Any one set of actions for each world, finite or not, which need not \
    hold every value of the action type.\n\
    | - **Freedom O5 leaves:** Which set of actions each world makes available.\n\
    | \n\
    | ### each step, the world is handed the action the agent answered\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => ∀ (ins : Nat → AcornVerif.Intent.Wor\
    ldInterface.System.Input w), ∀ (t : Nat), ∀ (s : AcornVerif.Intent.WorldInterface.System.St\
    ate w), ∀ (m : AcornVerif.Intent.WorldInterface.System.Memory w), AcornVerif.Intent.WorldIn\
    terface.System.Takes w ins t s m → @Eq.{1} (AcornVerif.Intent.WorldInterface.System.Act w) \
    (AcornVerif.Intent.WorldInterface.System.applied w s m (ins t) (@Prod.fst.{0, 0} (AcornVeri\
    f.Intent.WorldInterface.System.Act w) (AcornVerif.Intent.WorldInterface.System.Memory w) (A\
    cornVerif.Intent.WorldInterface.System.answer w s m (ins t)))) (@Prod.fst.{0, 0} (AcornVeri\
    f.Intent.WorldInterface.System.Act w) (AcornVerif.Intent.WorldInterface.System.Memory w) (A\
    cornVerif.Intent.WorldInterface.System.answer w s m (ins t)))\n\
    | ```\n\
    | \n\
    | - **Requires:** For every sequence of outside inputs, every time, and every state and mem\
    ory at which the run takes a step, the action the run hands the world is the action the age\
    nt answered.\n\
    | - **Rules out:** A run in which a host, a tool or the viewer hands the world another acti\
    on.\n\
    | - **Still allows:** Nothing more.\n\
    | - **Freedom O5 leaves:** What the run would hand the world at steps no run takes.\n\
    | \n\
    | ### each step, the world moves by its own dynamics\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => ∀ (ins : Nat → AcornVerif.Intent.Wor\
    ldInterface.System.Input w), ∀ (t : Nat), ∀ (s : AcornVerif.Intent.WorldInterface.System.St\
    ate w), ∀ (m : AcornVerif.Intent.WorldInterface.System.Memory w), AcornVerif.Intent.WorldIn\
    terface.System.Takes w ins t s m → @Eq.{1} (AcornVerif.Intent.WorldInterface.System.State w\
    ) (AcornVerif.Intent.WorldInterface.System.moved w s m (ins t) (AcornVerif.Intent.WorldInte\
    rface.System.applied w s m (ins t) (@Prod.fst.{0, 0} (AcornVerif.Intent.WorldInterface.Syst\
    em.Act w) (AcornVerif.Intent.WorldInterface.System.Memory w) (AcornVerif.Intent.WorldInterf\
    ace.System.answer w s m (ins t))))) (AcornVerif.Intent.WorldInterface.System.step w s (Acor\
    nVerif.Intent.WorldInterface.System.applied w s m (ins t) (@Prod.fst.{0, 0} (AcornVerif.Int\
    ent.WorldInterface.System.Act w) (AcornVerif.Intent.WorldInterface.System.Memory w) (AcornV\
    erif.Intent.WorldInterface.System.answer w s m (ins t)))))\n\
    | ```\n\
    | \n\
    | - **Requires:** For every sequence of outside inputs, every time, and every state and mem\
    ory at which the run takes a step, the world's next state is what its own dynamics give, fr\
    om that state, for the action the run hands it.\n\
    | - **Rules out:** A run that moves the world otherwise, such as a host putting it back at \
    its start outside its dynamics.\n\
    | - **Still allows:** Any dynamics, with restarts by the world's own rules, between attempt\
    s, or on an action of the agent's, as ARC-AGI-3's RESET is.\n\
    | - **Freedom O5 leaves:** The world's dynamics.\n\
    | \n\
    | ### each step, the agent keeps the memory its own answer produced\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => ∀ (ins : Nat → AcornVerif.Intent.Wor\
    ldInterface.System.Input w), ∀ (t : Nat), ∀ (s : AcornVerif.Intent.WorldInterface.System.St\
    ate w), ∀ (m : AcornVerif.Intent.WorldInterface.System.Memory w), AcornVerif.Intent.WorldIn\
    terface.System.Takes w ins t s m → @Eq.{1} (AcornVerif.Intent.WorldInterface.System.Memory \
    w) (AcornVerif.Intent.WorldInterface.System.kept w s m (ins t) (@Prod.snd.{0, 0} (AcornVeri\
    f.Intent.WorldInterface.System.Act w) (AcornVerif.Intent.WorldInterface.System.Memory w) (A\
    cornVerif.Intent.WorldInterface.System.answer w s m (ins t)))) (@Prod.snd.{0, 0} (AcornVeri\
    f.Intent.WorldInterface.System.Act w) (AcornVerif.Intent.WorldInterface.System.Memory w) (A\
    cornVerif.Intent.WorldInterface.System.answer w s m (ins t)))\n\
    | ```\n\
    | \n\
    | - **Requires:** For every sequence of outside inputs, every time, and every state and mem\
    ory at which the run takes a step, the memory the agent begins its next step with is the me\
    mory its own answer produced.\n\
    | - **Rules out:** A run in which, at a step it takes, a host, a tool, the viewer or a rest\
    art of the world, the agent's own RESET action included, leaves the agent a memory other th\
    an the one its own answer produced: a write, a reset or a restart of the agent.\n\
    | - **Still allows:** An agent whose own answer produces any memory, its initial one includ\
    ed: this property says nothing of how the agent itself keeps what it learned.\n\
    | - **Freedom O5 leaves:** How the agent's own answer changes its memory.\n\
    | \n\
    | ### a run the viewer keeps asking to stop stops\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => ∀ (ins : Nat → AcornVerif.Intent.Wor\
    ldInterface.System.Input w), ∀ (t₀ : Nat), (∀ (t : Nat), @LE.le.{0} Nat instLENat t₀ t → @E\
    q.{1} (AcornVerif.Intent.WorldInterface.System.Input w) (ins t) (AcornVerif.Intent.WorldInt\
    erface.System.stopRequest w)) → @Exists.{1} Nat (fun (t : Nat) => And (@LE.le.{0} Nat instL\
    ENat t₀ t) (∀ (s : AcornVerif.Intent.WorldInterface.System.State w), ∀ (m : AcornVerif.Inte\
    nt.WorldInterface.System.Memory w), Not (AcornVerif.Intent.WorldInterface.System.Takes w in\
    s t s m)))\n\
    | ```\n\
    | \n\
    | - **Requires:** For every sequence of outside inputs and every time from which the input \
    at every step is the viewer's stop request, there is a time at or after it at which the run\
    \x20takes no step.\n\
    | - **Rules out:** A run that, under inputs that are the stop request at every step from so\
    me time on, takes a step at every time from then on.\n\
    | - **Still allows:** A run that takes further steps after the request arrives before it st\
    ops; a run that ignores a stop request the viewer does not keep sending; and a run that als\
    o stops for other reasons, such as its host's own decision.\n\
    | - **Freedom O5 leaves:** How long after the request the run stops.\n\
    | \n\
    | ### the run can take its first step\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => @Exists.{1} (AcornVerif.Intent.World\
    Interface.System.Input w) (fun (e : AcornVerif.Intent.WorldInterface.System.Input w) => @Eq\
    .{1} Bool (AcornVerif.Intent.WorldInterface.System.goesOn w (AcornVerif.Intent.WorldInterfa\
    ce.System.start w) (AcornVerif.Intent.WorldInterface.System.initial w) e) Bool.true)\n\
    | ```\n\
    | \n\
    | - **Requires:** Some outside input lets the run take a step from the world's start and th\
    e agent's initial memory.\n\
    | - **Rules out:** A system whose run can take no step, whatever it is sent.\n\
    | - **Still allows:** A run that the viewer stops before its first step.\n\
    | - **Freedom O5 leaves:** Which inputs let the run begin.\n\
    | \n\
    | ## Vocabulary\n\
    | \n\
    | ### the run takes a step, a predicate over `AcornVerif.Intent.WorldInterface.Configuratio\
    n`\n\
    | \n\
    | ```lean\n\
    | fun (c : AcornVerif.Intent.WorldInterface.Configuration) => AcornVerif.Intent.WorldInterf\
    ace.System.Takes (@Sigma.fst.{1, 0} AcornVerif.Intent.WorldInterface.System (fun (w : Acorn\
    Verif.Intent.WorldInterface.System) => Prod.{0, 0} (Nat → AcornVerif.Intent.WorldInterface.\
    System.Input w) (Prod.{0, 0} Nat (Prod.{0, 0} (AcornVerif.Intent.WorldInterface.System.Stat\
    e w) (AcornVerif.Intent.WorldInterface.System.Memory w)))) c) (@Prod.fst.{0, 0} (Nat → Acor\
    nVerif.Intent.WorldInterface.System.Input (@Sigma.fst.{1, 0} AcornVerif.Intent.WorldInterfa\
    ce.System (fun (w : AcornVerif.Intent.WorldInterface.System) => Prod.{0, 0} (Nat → AcornVer\
    if.Intent.WorldInterface.System.Input w) (Prod.{0, 0} Nat (Prod.{0, 0} (AcornVerif.Intent.W\
    orldInterface.System.State w) (AcornVerif.Intent.WorldInterface.System.Memory w)))) c)) (Pr\
    od.{0, 0} Nat (Prod.{0, 0} (AcornVerif.Intent.WorldInterface.System.State (@Sigma.fst.{1, 0\
    } AcornVerif.Intent.WorldInterface.System (fun (w : AcornVerif.Intent.WorldInterface.System\
    ) => Prod.{0, 0} (Nat → AcornVerif.Intent.WorldInterface.System.Input w) (Prod.{0, 0} Nat (\
    Prod.{0, 0} (AcornVerif.Intent.WorldInterface.System.State w) (AcornVerif.Intent.WorldInter\
    face.System.Memory w)))) c)) (AcornVerif.Intent.WorldInterface.System.Memory (@Sigma.fst.{1\
    , 0} AcornVerif.Intent.WorldInterface.System (fun (w : AcornVerif.Intent.WorldInterface.Sys\
    tem) => Prod.{0, 0} (Nat → AcornVerif.Intent.WorldInterface.System.Input w) (Prod.{0, 0} Na\
    t (Prod.{0, 0} (AcornVerif.Intent.WorldInterface.System.State w) (AcornVerif.Intent.WorldIn\
    terface.System.Memory w)))) c)))) (@Sigma.snd.{1, 0} AcornVerif.Intent.WorldInterface.Syste\
    m (fun (w : AcornVerif.Intent.WorldInterface.System) => Prod.{0, 0} (Nat → AcornVerif.Inten\
    t.WorldInterface.System.Input w) (Prod.{0, 0} Nat (Prod.{0, 0} (AcornVerif.Intent.WorldInte\
    rface.System.State w) (AcornVerif.Intent.WorldInterface.System.Memory w)))) c)) (@Prod.fst.\
    {0, 0} Nat (Prod.{0, 0} (AcornVerif.Intent.WorldInterface.System.State (@Sigma.fst.{1, 0} A\
    cornVerif.Intent.WorldInterface.System (fun (w : AcornVerif.Intent.WorldInterface.System) =\
    > Prod.{0, 0} (Nat → AcornVerif.Intent.WorldInterface.System.Input w) (Prod.{0, 0} Nat (Pro\
    d.{0, 0} (AcornVerif.Intent.WorldInterface.System.State w) (AcornVerif.Intent.WorldInterfac\
    e.System.Memory w)))) c)) (AcornVerif.Intent.WorldInterface.System.Memory (@Sigma.fst.{1, 0\
    } AcornVerif.Intent.WorldInterface.System (fun (w : AcornVerif.Intent.WorldInterface.System\
    ) => Prod.{0, 0} (Nat → AcornVerif.Intent.WorldInterface.System.Input w) (Prod.{0, 0} Nat (\
    Prod.{0, 0} (AcornVerif.Intent.WorldInterface.System.State w) (AcornVerif.Intent.WorldInter\
    face.System.Memory w)))) c))) (@Prod.snd.{0, 0} (Nat → AcornVerif.Intent.WorldInterface.Sys\
    tem.Input (@Sigma.fst.{1, 0} AcornVerif.Intent.WorldInterface.System (fun (w : AcornVerif.I\
    ntent.WorldInterface.System) => Prod.{0, 0} (Nat → AcornVerif.Intent.WorldInterface.System.\
    Input w) (Prod.{0, 0} Nat (Prod.{0, 0} (AcornVerif.Intent.WorldInterface.System.State w) (A\
    cornVerif.Intent.WorldInterface.System.Memory w)))) c)) (Prod.{0, 0} Nat (Prod.{0, 0} (Acor\
    nVerif.Intent.WorldInterface.System.State (@Sigma.fst.{1, 0} AcornVerif.Intent.WorldInterfa\
    ce.System (fun (w : AcornVerif.Intent.WorldInterface.System) => Prod.{0, 0} (Nat → AcornVer\
    if.Intent.WorldInterface.System.Input w) (Prod.{0, 0} Nat (Prod.{0, 0} (AcornVerif.Intent.W\
    orldInterface.System.State w) (AcornVerif.Intent.WorldInterface.System.Memory w)))) c)) (Ac\
    ornVerif.Intent.WorldInterface.System.Memory (@Sigma.fst.{1, 0} AcornVerif.Intent.WorldInte\
    rface.System (fun (w : AcornVerif.Intent.WorldInterface.System) => Prod.{0, 0} (Nat → Acorn\
    Verif.Intent.WorldInterface.System.Input w) (Prod.{0, 0} Nat (Prod.{0, 0} (AcornVerif.Inten\
    t.WorldInterface.System.State w) (AcornVerif.Intent.WorldInterface.System.Memory w)))) c)))\
    ) (@Sigma.snd.{1, 0} AcornVerif.Intent.WorldInterface.System (fun (w : AcornVerif.Intent.Wo\
    rldInterface.System) => Prod.{0, 0} (Nat → AcornVerif.Intent.WorldInterface.System.Input w)\
    \x20(Prod.{0, 0} Nat (Prod.{0, 0} (AcornVerif.Intent.WorldInterface.System.State w) (AcornVeri\
    f.Intent.WorldInterface.System.Memory w)))) c))) (@Prod.fst.{0, 0} (AcornVerif.Intent.World\
    Interface.System.State (@Sigma.fst.{1, 0} AcornVerif.Intent.WorldInterface.System (fun (w :\
    \x20AcornVerif.Intent.WorldInterface.System) => Prod.{0, 0} (Nat → AcornVerif.Intent.WorldInte\
    rface.System.Input w) (Prod.{0, 0} Nat (Prod.{0, 0} (AcornVerif.Intent.WorldInterface.Syste\
    m.State w) (AcornVerif.Intent.WorldInterface.System.Memory w)))) c)) (AcornVerif.Intent.Wor\
    ldInterface.System.Memory (@Sigma.fst.{1, 0} AcornVerif.Intent.WorldInterface.System (fun (\
    w : AcornVerif.Intent.WorldInterface.System) => Prod.{0, 0} (Nat → AcornVerif.Intent.WorldI\
    nterface.System.Input w) (Prod.{0, 0} Nat (Prod.{0, 0} (AcornVerif.Intent.WorldInterface.Sy\
    stem.State w) (AcornVerif.Intent.WorldInterface.System.Memory w)))) c)) (@Prod.snd.{0, 0} N\
    at (Prod.{0, 0} (AcornVerif.Intent.WorldInterface.System.State (@Sigma.fst.{1, 0} AcornVeri\
    f.Intent.WorldInterface.System (fun (w : AcornVerif.Intent.WorldInterface.System) => Prod.{\
    0, 0} (Nat → AcornVerif.Intent.WorldInterface.System.Input w) (Prod.{0, 0} Nat (Prod.{0, 0}\
    \x20(AcornVerif.Intent.WorldInterface.System.State w) (AcornVerif.Intent.WorldInterface.System\
    .Memory w)))) c)) (AcornVerif.Intent.WorldInterface.System.Memory (@Sigma.fst.{1, 0} AcornV\
    erif.Intent.WorldInterface.System (fun (w : AcornVerif.Intent.WorldInterface.System) => Pro\
    d.{0, 0} (Nat → AcornVerif.Intent.WorldInterface.System.Input w) (Prod.{0, 0} Nat (Prod.{0,\
    \x200} (AcornVerif.Intent.WorldInterface.System.State w) (AcornVerif.Intent.WorldInterface.Sys\
    tem.Memory w)))) c))) (@Prod.snd.{0, 0} (Nat → AcornVerif.Intent.WorldInterface.System.Inpu\
    t (@Sigma.fst.{1, 0} AcornVerif.Intent.WorldInterface.System (fun (w : AcornVerif.Intent.Wo\
    rldInterface.System) => Prod.{0, 0} (Nat → AcornVerif.Intent.WorldInterface.System.Input w)\
    \x20(Prod.{0, 0} Nat (Prod.{0, 0} (AcornVerif.Intent.WorldInterface.System.State w) (AcornVeri\
    f.Intent.WorldInterface.System.Memory w)))) c)) (Prod.{0, 0} Nat (Prod.{0, 0} (AcornVerif.I\
    ntent.WorldInterface.System.State (@Sigma.fst.{1, 0} AcornVerif.Intent.WorldInterface.Syste\
    m (fun (w : AcornVerif.Intent.WorldInterface.System) => Prod.{0, 0} (Nat → AcornVerif.Inten\
    t.WorldInterface.System.Input w) (Prod.{0, 0} Nat (Prod.{0, 0} (AcornVerif.Intent.WorldInte\
    rface.System.State w) (AcornVerif.Intent.WorldInterface.System.Memory w)))) c)) (AcornVerif\
    .Intent.WorldInterface.System.Memory (@Sigma.fst.{1, 0} AcornVerif.Intent.WorldInterface.Sy\
    stem (fun (w : AcornVerif.Intent.WorldInterface.System) => Prod.{0, 0} (Nat → AcornVerif.In\
    tent.WorldInterface.System.Input w) (Prod.{0, 0} Nat (Prod.{0, 0} (AcornVerif.Intent.WorldI\
    nterface.System.State w) (AcornVerif.Intent.WorldInterface.System.Memory w)))) c)))) (@Sigm\
    a.snd.{1, 0} AcornVerif.Intent.WorldInterface.System (fun (w : AcornVerif.Intent.WorldInter\
    face.System) => Prod.{0, 0} (Nat → AcornVerif.Intent.WorldInterface.System.Input w) (Prod.{\
    0, 0} Nat (Prod.{0, 0} (AcornVerif.Intent.WorldInterface.System.State w) (AcornVerif.Intent\
    .WorldInterface.System.Memory w)))) c)))) (@Prod.snd.{0, 0} (AcornVerif.Intent.WorldInterfa\
    ce.System.State (@Sigma.fst.{1, 0} AcornVerif.Intent.WorldInterface.System (fun (w : AcornV\
    erif.Intent.WorldInterface.System) => Prod.{0, 0} (Nat → AcornVerif.Intent.WorldInterface.S\
    ystem.Input w) (Prod.{0, 0} Nat (Prod.{0, 0} (AcornVerif.Intent.WorldInterface.System.State\
    \x20w) (AcornVerif.Intent.WorldInterface.System.Memory w)))) c)) (AcornVerif.Intent.WorldInter\
    face.System.Memory (@Sigma.fst.{1, 0} AcornVerif.Intent.WorldInterface.System (fun (w : Aco\
    rnVerif.Intent.WorldInterface.System) => Prod.{0, 0} (Nat → AcornVerif.Intent.WorldInterfac\
    e.System.Input w) (Prod.{0, 0} Nat (Prod.{0, 0} (AcornVerif.Intent.WorldInterface.System.St\
    ate w) (AcornVerif.Intent.WorldInterface.System.Memory w)))) c)) (@Prod.snd.{0, 0} Nat (Pro\
    d.{0, 0} (AcornVerif.Intent.WorldInterface.System.State (@Sigma.fst.{1, 0} AcornVerif.Inten\
    t.WorldInterface.System (fun (w : AcornVerif.Intent.WorldInterface.System) => Prod.{0, 0} (\
    Nat → AcornVerif.Intent.WorldInterface.System.Input w) (Prod.{0, 0} Nat (Prod.{0, 0} (Acorn\
    Verif.Intent.WorldInterface.System.State w) (AcornVerif.Intent.WorldInterface.System.Memory\
    \x20w)))) c)) (AcornVerif.Intent.WorldInterface.System.Memory (@Sigma.fst.{1, 0} AcornVerif.In\
    tent.WorldInterface.System (fun (w : AcornVerif.Intent.WorldInterface.System) => Prod.{0, 0\
    } (Nat → AcornVerif.Intent.WorldInterface.System.Input w) (Prod.{0, 0} Nat (Prod.{0, 0} (Ac\
    ornVerif.Intent.WorldInterface.System.State w) (AcornVerif.Intent.WorldInterface.System.Mem\
    ory w)))) c))) (@Prod.snd.{0, 0} (Nat → AcornVerif.Intent.WorldInterface.System.Input (@Sig\
    ma.fst.{1, 0} AcornVerif.Intent.WorldInterface.System (fun (w : AcornVerif.Intent.WorldInte\
    rface.System) => Prod.{0, 0} (Nat → AcornVerif.Intent.WorldInterface.System.Input w) (Prod.\
    {0, 0} Nat (Prod.{0, 0} (AcornVerif.Intent.WorldInterface.System.State w) (AcornVerif.Inten\
    t.WorldInterface.System.Memory w)))) c)) (Prod.{0, 0} Nat (Prod.{0, 0} (AcornVerif.Intent.W\
    orldInterface.System.State (@Sigma.fst.{1, 0} AcornVerif.Intent.WorldInterface.System (fun \
    (w : AcornVerif.Intent.WorldInterface.System) => Prod.{0, 0} (Nat → AcornVerif.Intent.World\
    Interface.System.Input w) (Prod.{0, 0} Nat (Prod.{0, 0} (AcornVerif.Intent.WorldInterface.S\
    ystem.State w) (AcornVerif.Intent.WorldInterface.System.Memory w)))) c)) (AcornVerif.Intent\
    .WorldInterface.System.Memory (@Sigma.fst.{1, 0} AcornVerif.Intent.WorldInterface.System (f\
    un (w : AcornVerif.Intent.WorldInterface.System) => Prod.{0, 0} (Nat → AcornVerif.Intent.Wo\
    rldInterface.System.Input w) (Prod.{0, 0} Nat (Prod.{0, 0} (AcornVerif.Intent.WorldInterfac\
    e.System.State w) (AcornVerif.Intent.WorldInterface.System.Memory w)))) c)))) (@Sigma.snd.{\
    1, 0} AcornVerif.Intent.WorldInterface.System (fun (w : AcornVerif.Intent.WorldInterface.Sy\
    stem) => Prod.{0, 0} (Nat → AcornVerif.Intent.WorldInterface.System.Input w) (Prod.{0, 0} N\
    at (Prod.{0, 0} (AcornVerif.Intent.WorldInterface.System.State w) (AcornVerif.Intent.WorldI\
    nterface.System.Memory w)))) c))))\n\
    | ```\n\
    | \n\
    | - **Requires:** Under the given outside inputs, the run took each step before the given t\
    ime, holds the given state and memory at that time, and takes the next step.\n\
    | - **Rules out:** A configuration the run does not reach, or one at which it does not go o\
    n.\n\
    | - **Still allows:** Every configuration the run reaches and goes on from.\n\
    | - **Freedom O5 leaves:** None of its own: it is a definition the properties are written i\
    n.\n\
    | \n\
    | ## Consequences\n\
    | \n\
    | ### every step a run takes is the closed loop of the world and the agent, an entailment: \
    every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => ∀ (ins : Nat → AcornVerif.Intent.Wor\
    ldInterface.System.Input w), ∀ (t : Nat), ∀ (s : AcornVerif.Intent.WorldInterface.System.St\
    ate w), ∀ (m : AcornVerif.Intent.WorldInterface.System.Memory w), AcornVerif.Intent.WorldIn\
    terface.System.Takes w ins t s m → AcornVerif.Intent.WorldInterface.System.Reaches w ins (@\
    HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t (@OfNat.ofNat.{0} Nat (nat\
    _lit 1) (instOfNatNat (nat_lit 1)))) (@Prod.fst.{0, 0} (AcornVerif.Intent.WorldInterface.Sy\
    stem.State w) (AcornVerif.Intent.WorldInterface.System.Memory w) (AcornVerif.Intent.WorldIn\
    terface.loopStep w s m)) (@Prod.snd.{0, 0} (AcornVerif.Intent.WorldInterface.System.State w\
    ) (AcornVerif.Intent.WorldInterface.System.Memory w) (AcornVerif.Intent.WorldInterface.loop\
    Step w s m))\n\
    | ```\n\
    | \n\
    | - **Requires:** At every step a run takes, the world moves by its own dynamics on the age\
    nt's answer to the world's observation and reward, and the agent keeps the memory that answ\
    er produced: each step is the closed loop of the world and the agent.\n\
    | - **Rules out:** Any step a run takes whose next state or memory differs from the closed \
    loop's.\n\
    | - **Still allows:** Nothing more.\n\
    | - **Freedom O5 leaves:** When the run stops, and what the run's parts give wherever no st\
    ep is taken, besides the world's and the agent's own.\n\
    | \n\
    | ### what hosts, viewers and tools send changes nothing but whether the run goes on, an en\
    tailment: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => ∀ (ins : Nat → AcornVerif.Intent.Wor\
    ldInterface.System.Input w), ∀ (ins' : Nat → AcornVerif.Intent.WorldInterface.System.Input \
    w), ∀ (t : Nat), ∀ (s : AcornVerif.Intent.WorldInterface.System.State w), ∀ (s' : AcornVeri\
    f.Intent.WorldInterface.System.State w), ∀ (m : AcornVerif.Intent.WorldInterface.System.Mem\
    ory w), ∀ (m' : AcornVerif.Intent.WorldInterface.System.Memory w), AcornVerif.Intent.WorldI\
    nterface.System.Reaches w ins t s m → AcornVerif.Intent.WorldInterface.System.Reaches w ins\
    ' t s' m' → And (@Eq.{1} (AcornVerif.Intent.WorldInterface.System.State w) s s') (@Eq.{1} (\
    AcornVerif.Intent.WorldInterface.System.Memory w) m m')\n\
    | ```\n\
    | \n\
    | - **Requires:** Under any two sequences of outside inputs, a run that has taken the same \
    number of steps holds the same state and memory: what hosts, viewers and tools send decides\
    \x20only whether the run goes on.\n\
    | - **Rules out:** Any outside input that changes what a step does.\n\
    | - **Still allows:** Outside inputs that stop the run at different times.\n\
    | - **Freedom O5 leaves:** When the run stops.\n\
    | \n\
    | ### the run handsState, which hands the agent the world's state its observation hides, is\
    \x20ruled out, an entailment: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => @Ne.{2} AcornVerif.Intent.WorldInter\
    face.System w AcornVerif.Intent.WorldInterface.handsState\n\
    | ```\n\
    | \n\
    | - **Requires:** The run handsState, of the world shrouded, which starts at true and shows\
    \x20false at both of its states, and the agent echo, in which the agent is given the state its\
    elf as its observation, does not meet the record.\n\
    | - **Rules out:** That run; the same world and agent run faithfully meet the record (shrou\
    ded_meets).\n\
    | - **Still allows:** Nothing more.\n\
    | - **Freedom O5 leaves:** Everything but being that one system.\n\
    | \n\
    | ### the run resetsAtRestart, which resets the agent's memory when the world restarts, is \
    ruled out, an entailment: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => @Ne.{2} AcornVerif.Intent.WorldInter\
    face.System w AcornVerif.Intent.WorldInterface.resetsAtRestart\n\
    | ```\n\
    | \n\
    | - **Requires:** The run resetsAtRestart, of the world attempts, which restarts after ever\
    y two steps, and the agent echo, which counts its steps, in which the agent's memory is res\
    et to 0 whenever the world restarts, does not meet the record.\n\
    | - **Rules out:** That run; the same world and agent with the memory kept meet the record \
    (attempts_meets).\n\
    | - **Still allows:** Nothing more.\n\
    | - **Freedom O5 leaves:** Everything but being that one system.\n\
    | \n\
    | ### the run hostWritesMemory, in which a host writes the agent's memory, is ruled out, an\
    \x20entailment: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => @Ne.{2} AcornVerif.Intent.WorldInter\
    face.System w AcornVerif.Intent.WorldInterface.hostWritesMemory\n\
    | ```\n\
    | \n\
    | - **Requires:** The run hostWritesMemory, of mirror and echo, in which a host adds one to\
    \x20the memory the agent's answer produced, does not meet the record.\n\
    | - **Rules out:** That run; the same world and agent run faithfully meet the record (base_\
    meets).\n\
    | - **Still allows:** Nothing more.\n\
    | - **Freedom O5 leaves:** Everything but being that one system.\n\
    | \n\
    | ### the run hostOverridesAction, in which a host hands the world another action, is ruled\
    \x20out, an entailment: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => @Ne.{2} AcornVerif.Intent.WorldInter\
    face.System w AcornVerif.Intent.WorldInterface.hostOverridesAction\n\
    | ```\n\
    | \n\
    | - **Requires:** The run hostOverridesAction, of mirror and echo, in which a host hands th\
    e world the other action than the agent answered, does not meet the record.\n\
    | - **Rules out:** That run; the same world and agent run faithfully meet the record (base_\
    meets).\n\
    | - **Still allows:** Nothing more.\n\
    | - **Freedom O5 leaves:** Everything but being that one system.\n\
    | \n\
    | ### the run rewardFromMemory, which gives the agent a reward taken from its own memory, i\
    s ruled out, an entailment: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => @Ne.{2} AcornVerif.Intent.WorldInter\
    face.System w AcornVerif.Intent.WorldInterface.rewardFromMemory\n\
    | ```\n\
    | \n\
    | - **Requires:** The run rewardFromMemory, of mirror and holdsOne, which gives the agent a\
    s its reward the 1 its memory holds while the world generates 0, does not meet the record.\
    \n\
    | - **Rules out:** That run; the same world and agent given the world's reward meet the rec\
    ord (holdsOne_meets).\n\
    | - **Still allows:** Nothing more.\n\
    | - **Freedom O5 leaves:** Everything but being that one system.\n\
    | \n\
    | ### the game resetOnlyAtGameOver, played by arcPlayer, which makes RESET its only availab\
    le action at game over, is ruled out, an entailment: every subject that meets the record sa\
    tisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => @Ne.{2} AcornVerif.Intent.WorldInter\
    face.System w (AcornVerif.Intent.WorldInterface.couple AcornVerif.Intent.WorldInterface.res\
    etOnlyAtGameOver AcornVerif.Intent.WorldInterface.arcPlayer)\n\
    | ```\n\
    | \n\
    | - **Requires:** The game resetOnlyAtGameOver, in the manner of ARC-AGI-3, played by arcPl\
    ayer, which makes RESET its only available action at game over, does not meet the record; i\
    ts player reaches game over after one step.\n\
    | - **Rules out:** That run; the same game with every action available everywhere meets the\
    \x20record (resettable_meets).\n\
    | - **Still allows:** Nothing more.\n\
    | - **Freedom O5 leaves:** Everything but being that one system.\n\
    | \n\
    | ### the run hostRestarts, in which a host restarts the world outside its dynamics, is rul\
    ed out, an entailment: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => @Ne.{2} AcornVerif.Intent.WorldInter\
    face.System w AcornVerif.Intent.WorldInterface.hostRestarts\n\
    | ```\n\
    | \n\
    | - **Requires:** The run hostRestarts, of attempts and echo, in which a host puts the worl\
    d back at its start at every step, outside its dynamics, does not meet the record.\n\
    | - **Rules out:** That run; the same world and agent run faithfully meet the record (attem\
    pts_meets).\n\
    | - **Still allows:** Nothing more.\n\
    | - **Freedom O5 leaves:** Everything but being that one system.\n\
    | \n\
    | ### the run neverStops, which goes on whatever the viewer sends, is ruled out, an entailm\
    ent: every subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => @Ne.{2} AcornVerif.Intent.WorldInter\
    face.System w AcornVerif.Intent.WorldInterface.neverStops\n\
    | ```\n\
    | \n\
    | - **Requires:** The run neverStops, of mirror and echo, which takes every step whatever t\
    he viewer sends, does not meet the record.\n\
    | - **Rules out:** That run; the same world and agent with a run that stops on the viewer's\
    \x20request meet the record (base_meets).\n\
    | - **Still allows:** Nothing more.\n\
    | - **Freedom O5 leaves:** Everything but being that one system.\n\
    | \n\
    | ### some system that meets the record has a world whose observation shows nothing of its \
    state, a possibility: some subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => ∀ (s : AcornVerif.Intent.WorldInterf\
    ace.System.State w), ∀ (s' : AcornVerif.Intent.WorldInterface.System.State w), @Eq.{1} (Aco\
    rnVerif.Intent.WorldInterface.System.Obs w) (AcornVerif.Intent.WorldInterface.System.observ\
    e w s) (AcornVerif.Intent.WorldInterface.System.observe w s')\n\
    | ```\n\
    | \n\
    | - **Requires:** Nothing more: some system that meets the record has a world whose observa\
    tion is the same at every state.\n\
    | - **Rules out:** Nothing.\n\
    | - **Still allows:** A world that shows the agent nothing of its state.\n\
    | - **Freedom O5 leaves:** Everything but that the world's observation is the same at every\
    \x20state; the record itself requires neither hiding nor showing the state.\n\
    | \n\
    | ### some system that meets the record has a world whose observation tells its states apar\
    t, a possibility: some subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => ∀ (s : AcornVerif.Intent.WorldInterf\
    ace.System.State w), ∀ (s' : AcornVerif.Intent.WorldInterface.System.State w), @Eq.{1} (Aco\
    rnVerif.Intent.WorldInterface.System.Obs w) (AcornVerif.Intent.WorldInterface.System.observ\
    e w s) (AcornVerif.Intent.WorldInterface.System.observe w s') → @Eq.{1} (AcornVerif.Intent.\
    WorldInterface.System.State w) s s'\n\
    | ```\n\
    | \n\
    | - **Requires:** Nothing more: some system that meets the record has a world whose observa\
    tion tells every two of its states apart.\n\
    | - **Rules out:** Nothing.\n\
    | - **Still allows:** A world that shows the agent its whole state.\n\
    | - **Freedom O5 leaves:** Everything but that the world's observation tells its states apa\
    rt; the record itself requires neither hiding nor showing the state.\n\
    | \n\
    | ### a world may restart by its own rules while the agent keeps its memory, a possibility:\
    \x20some subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => @Exists.{1} (Nat → AcornVerif.Intent\
    .WorldInterface.System.Input w) (fun (ins : Nat → AcornVerif.Intent.WorldInterface.System.I\
    nput w) => @Exists.{1} Nat (fun (t : Nat) => @Exists.{1} (AcornVerif.Intent.WorldInterface.\
    System.State w) (fun (s : AcornVerif.Intent.WorldInterface.System.State w) => @Exists.{1} (\
    AcornVerif.Intent.WorldInterface.System.Memory w) (fun (m : AcornVerif.Intent.WorldInterfac\
    e.System.Memory w) => And (AcornVerif.Intent.WorldInterface.System.Takes w ins t s m) (And \
    (@Ne.{1} (AcornVerif.Intent.WorldInterface.System.State w) s (AcornVerif.Intent.WorldInterf\
    ace.System.start w)) (And (@Eq.{1} (AcornVerif.Intent.WorldInterface.System.State w) (@Prod\
    .fst.{0, 0} (AcornVerif.Intent.WorldInterface.System.State w) (AcornVerif.Intent.WorldInter\
    face.System.Memory w) (AcornVerif.Intent.WorldInterface.loopStep w s m)) (AcornVerif.Intent\
    .WorldInterface.System.start w)) (@Ne.{1} (AcornVerif.Intent.WorldInterface.System.Memory w\
    ) (@Prod.snd.{0, 0} (AcornVerif.Intent.WorldInterface.System.State w) (AcornVerif.Intent.Wo\
    rldInterface.System.Memory w) (AcornVerif.Intent.WorldInterface.loopStep w s m)) (AcornVeri\
    f.Intent.WorldInterface.System.initial w))))))))\n\
    | ```\n\
    | \n\
    | - **Requires:** Nothing more: some run of a system that meets the record takes a step fro\
    m a state other than the world's start at which the world returns to its start by its own d\
    ynamics while the agent's answer produced a memory other than its initial one, which the ag\
    ent keeps.\n\
    | - **Rules out:** Nothing.\n\
    | - **Still allows:** A world that restarts between attempts or by its own rules, with the \
    agent's memory carried across.\n\
    | - **Freedom O5 leaves:** When and how a world restarts.\n\
    | \n\
    | ### a world may restart on an action of the agent's, as ARC-AGI-3's RESET does, a possibi\
    lity: some subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => @Exists.{1} (AcornVerif.Intent.World\
    Interface.System.Act w) (fun (a : AcornVerif.Intent.WorldInterface.System.Act w) => @Exists\
    .{1} (AcornVerif.Intent.WorldInterface.System.State w) (fun (g : AcornVerif.Intent.WorldInt\
    erface.System.State w) => And (@Ne.{1} (AcornVerif.Intent.WorldInterface.System.State w) g \
    (AcornVerif.Intent.WorldInterface.System.start w)) (And (∀ (s : AcornVerif.Intent.WorldInte\
    rface.System.State w), And (AcornVerif.Intent.WorldInterface.System.available w s a) (@Eq.{\
    1} (AcornVerif.Intent.WorldInterface.System.State w) (AcornVerif.Intent.WorldInterface.Syst\
    em.step w s a) (AcornVerif.Intent.WorldInterface.System.start w))) (∀ (b : AcornVerif.Inten\
    t.WorldInterface.System.Act w), @Ne.{1} (AcornVerif.Intent.WorldInterface.System.Act w) b a\
    \x20→ @Eq.{1} (AcornVerif.Intent.WorldInterface.System.State w) (AcornVerif.Intent.WorldInterf\
    ace.System.step w g b) g))))\n\
    | ```\n\
    | \n\
    | - **Requires:** Nothing more: some system that meets the record has an action, available \
    at every state, that takes the world back to its start from every state, and a state other \
    than the start that every other action leaves as it is.\n\
    | - **Rules out:** Nothing.\n\
    | - **Still allows:** A restart that is the agent's own action, as ARC-AGI-3's RESET is, an\
    d a game over that only that action leaves.\n\
    | - **Freedom O5 leaves:** Which actions restart a world.\n\
    | \n\
    | ### some system that meets the record has an agent that keeps nothing of what it is given\
    , a possibility: some subject that meets the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => ∀ (m : AcornVerif.Intent.WorldInterf\
    ace.System.Memory w), ∀ (o : Prod.{0, 0} (AcornVerif.Intent.WorldInterface.System.Obs w) Ra\
    t), ∀ (o' : Prod.{0, 0} (AcornVerif.Intent.WorldInterface.System.Obs w) Rat), @Eq.{1} (Acor\
    nVerif.Intent.WorldInterface.System.Memory w) (@Prod.snd.{0, 0} (AcornVerif.Intent.WorldInt\
    erface.System.Act w) (AcornVerif.Intent.WorldInterface.System.Memory w) (AcornVerif.Intent.\
    WorldInterface.System.act w m o)) (@Prod.snd.{0, 0} (AcornVerif.Intent.WorldInterface.Syste\
    m.Act w) (AcornVerif.Intent.WorldInterface.System.Memory w) (AcornVerif.Intent.WorldInterfa\
    ce.System.act w m o'))\n\
    | ```\n\
    | \n\
    | - **Requires:** Nothing more: some system that meets the record has an agent whose memory\
    \x20after an answer does not depend on what it was given.\n\
    | - **Rules out:** Nothing.\n\
    | - **Still allows:** An agent that keeps nothing of its experience.\n\
    | - **Freedom O5 leaves:** Everything but that the agent's memory after an answer ignores w\
    hat it was given.\n\
    | \n\
    | ### the viewer may stop a run before its first step, a possibility: some subject that mee\
    ts the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => @Exists.{1} (Nat → AcornVerif.Intent\
    .WorldInterface.System.Input w) (fun (ins : Nat → AcornVerif.Intent.WorldInterface.System.I\
    nput w) => And (@Eq.{1} (AcornVerif.Intent.WorldInterface.System.Input w) (ins (@OfNat.ofNa\
    t.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (AcornVerif.Intent.WorldInterface.System\
    .stopRequest w)) (∀ (s : AcornVerif.Intent.WorldInterface.System.State w), ∀ (m : AcornVeri\
    f.Intent.WorldInterface.System.Memory w), Not (AcornVerif.Intent.WorldInterface.System.Take\
    s w ins (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) s m)))\n\
    | ```\n\
    | \n\
    | - **Requires:** Nothing more: some system that meets the record takes no first step under\
    \x20some outside inputs whose first is the viewer's stop request.\n\
    | - **Rules out:** Nothing.\n\
    | - **Still allows:** The viewer stopping a run before its first step.\n\
    | - **Freedom O5 leaves:** When the viewer stops a run.\n\
    | \n\
    | ### a host may stop a run without the viewer asking, a possibility: some subject that mee\
    ts the record satisfies it\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => @Exists.{1} (Nat → AcornVerif.Intent\
    .WorldInterface.System.Input w) (fun (ins : Nat → AcornVerif.Intent.WorldInterface.System.I\
    nput w) => @Exists.{1} Nat (fun (t : Nat) => @Exists.{1} (AcornVerif.Intent.WorldInterface.\
    System.State w) (fun (s : AcornVerif.Intent.WorldInterface.System.State w) => @Exists.{1} (\
    AcornVerif.Intent.WorldInterface.System.Memory w) (fun (m : AcornVerif.Intent.WorldInterfac\
    e.System.Memory w) => And (AcornVerif.Intent.WorldInterface.System.Reaches w ins t s m) (An\
    d (@Ne.{1} (AcornVerif.Intent.WorldInterface.System.Input w) (ins t) (AcornVerif.Intent.Wor\
    ldInterface.System.stopRequest w)) (@Eq.{1} Bool (AcornVerif.Intent.WorldInterface.System.g\
    oesOn w s m (ins t)) Bool.false))))))\n\
    | ```\n\
    | \n\
    | - **Requires:** Nothing more: some run of some system that meets the record, having reach\
    ed a state and memory, does not take the next step, at an input that is not the viewer's st\
    op request.\n\
    | - **Rules out:** Nothing.\n\
    | - **Still allows:** A host that stops a run of its own accord.\n\
    | - **Freedom O5 leaves:** When a host stops a run.\n\
    | \n\
    | ## Definitions the record's meaning reaches\n\
    | \n\
    | These are not statements of the record: each is a declaration that a statement above depe\
    nds on, or that says what it is for a subject to meet the record and for a consequence to h\
    old of it as shown, with everything those depend on in turn. Each is printed in full: its t\
    ype, a definition's value, or for a definition by structural or well-founded recursion the \
    equation that determines it, and an inductive type's constructors, which for a structure ar\
    e its fields; a theorem's proof and an opaque constant's value are not, since no term that \
    uses them depends on more than their types. Their plain words are those of the statements t\
    hat use them.\n\
    | \n\
    | ### LeanIntent.Shape\n\
    | \n\
    | An inductive type. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type u → Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 1 indices. Its \
    recursor is the one Lean's kernel derives from this declaration. Its constructors, in order\
    , each with its type:\n\
    | \n\
    | #### LeanIntent.Shape.value\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.function\n\
    | \n\
    | ```lean\n\
    | ∀ (A : Type u), ∀ (B : A → Type u), LeanIntent.Shape.{u} (∀ (x : A), B x)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.step\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), LeanIntent.Shape.{u} (S → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.stepOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), LeanIntent.Shape.{u} (S → I → S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.action\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → Prod.{u, u} O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.actionOn\n\
    | \n\
    | ```lean\n\
    | ∀ (S : Type u), ∀ (I : Type u), ∀ (O : Type u), LeanIntent.Shape.{u} (S → I → Prod.{u, u}\
    \x20O S)\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Shape.bundle\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ {D : Type u}, ∀ (data : W → D), ∀ (first : LeanIntent.Member.{u} W), ∀ \
    (rest : List.{u + 1} (LeanIntent.Member.{u} W)), LeanIntent.Shape.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Member\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameters\
    \x20are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its \
    recursor is the one Lean's kernel derives from this declaration. Its constructors, in order\
    , each with its type:\n\
    | \n\
    | #### LeanIntent.Member.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (In : Type u), ∀ (Out : Type u), ∀ (get : W → In → O\
    ut), LeanIntent.Member.{u} W\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.System\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameters\
    \x20are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type 1\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its \
    recursor is the one Lean's kernel derives from this declaration. Its constructors, in order\
    , each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.WorldInterface.System.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (State : Type), ∀ (Obs : Type), ∀ (Act : Type), ∀ (Memory : Type), ∀ (Input : Type), ∀ \
    (start : State), ∀ (observe : State → Obs), ∀ (reward : State → Rat), ∀ (available : State \
    → Act → Prop), ∀ (step : State → Act → State), ∀ (initial : Memory), ∀ (act : Memory → Prod\
    .{0, 0} Obs Rat → Prod.{0, 0} Act Memory), ∀ (stopRequest : Input), ∀ (goesOn : State → Mem\
    ory → Input → Bool), ∀ (given : State → Memory → Input → Prod.{0, 0} Obs Rat), ∀ (applied :\
    \x20State → Memory → Input → Act → Act), ∀ (moved : State → Memory → Input → Act → State), ∀ (\
    kept : State → Memory → Input → Memory → Memory), AcornVerif.Intent.WorldInterface.System\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.System.Input\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argumen\
    ts and returns field number 5, counted after the parameters in the type of AcornVerif.Inten\
    t.WorldInterface.System's constructor, of its argument number 1, a value of AcornVerif.Inte\
    nt.WorldInterface.System. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.WorldInterface.System), Type\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.System.State\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argumen\
    ts and returns field number 1, counted after the parameters in the type of AcornVerif.Inten\
    t.WorldInterface.System's constructor, of its argument number 1, a value of AcornVerif.Inte\
    nt.WorldInterface.System. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.WorldInterface.System), Type\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.System.Memory\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argumen\
    ts and returns field number 4, counted after the parameters in the type of AcornVerif.Inten\
    t.WorldInterface.System's constructor, of its argument number 1, a value of AcornVerif.Inte\
    nt.WorldInterface.System. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.WorldInterface.System), Type\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.System.Takes\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (w : AcornVerif.Intent.WorldInterface.System), ∀ (ins : Nat → AcornVerif.Intent.WorldIn\
    terface.System.Input w), ∀ (t : Nat), ∀ (s : AcornVerif.Intent.WorldInterface.System.State \
    w), ∀ (m : AcornVerif.Intent.WorldInterface.System.Memory w), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => fun (ins : Nat → AcornVerif.Intent.W\
    orldInterface.System.Input w) => fun (t : Nat) => fun (s : AcornVerif.Intent.WorldInterface\
    .System.State w) => fun (m : AcornVerif.Intent.WorldInterface.System.Memory w) => And (Acor\
    nVerif.Intent.WorldInterface.System.Reaches w ins t s m) (@Eq.{1} Bool (AcornVerif.Intent.W\
    orldInterface.System.goesOn w s m (ins t)) Bool.true)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.System.Reaches\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (w : AcornVerif.Intent.WorldInterface.System), ∀ (ins : Nat → AcornVerif.Intent.WorldIn\
    terface.System.Input w), Nat → AcornVerif.Intent.WorldInterface.System.State w → AcornVerif\
    .Intent.WorldInterface.System.Memory w → Prop\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 2 are parameters and the other 3 indices. Its \
    recursor is the one Lean's kernel derives from this declaration. Its constructors, in order\
    , each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.WorldInterface.System.Reaches.start\n\
    | \n\
    | ```lean\n\
    | ∀ {w : AcornVerif.Intent.WorldInterface.System}, ∀ {ins : Nat → AcornVerif.Intent.WorldIn\
    terface.System.Input w}, AcornVerif.Intent.WorldInterface.System.Reaches w ins (@OfNat.ofNa\
    t.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (AcornVerif.Intent.WorldInterface.System.\
    start w) (AcornVerif.Intent.WorldInterface.System.initial w)\n\
    | ```\n\
    | \n\
    | #### AcornVerif.Intent.WorldInterface.System.Reaches.next\n\
    | \n\
    | ```lean\n\
    | ∀ {w : AcornVerif.Intent.WorldInterface.System}, ∀ {ins : Nat → AcornVerif.Intent.WorldIn\
    terface.System.Input w}, ∀ {t : Nat}, ∀ {s : AcornVerif.Intent.WorldInterface.System.State \
    w}, ∀ {m : AcornVerif.Intent.WorldInterface.System.Memory w}, AcornVerif.Intent.WorldInterf\
    ace.System.Reaches w ins t s m → @Eq.{1} Bool (AcornVerif.Intent.WorldInterface.System.goes\
    On w s m (ins t)) Bool.true → AcornVerif.Intent.WorldInterface.System.Reaches w ins (@HAdd.\
    hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t (@OfNat.ofNat.{0} Nat (nat_lit \
    1) (instOfNatNat (nat_lit 1)))) (AcornVerif.Intent.WorldInterface.System.moved w s m (ins t\
    ) (AcornVerif.Intent.WorldInterface.System.applied w s m (ins t) (@Prod.fst.{0, 0} (AcornVe\
    rif.Intent.WorldInterface.System.Act w) (AcornVerif.Intent.WorldInterface.System.Memory w) \
    (AcornVerif.Intent.WorldInterface.System.answer w s m (ins t))))) (AcornVerif.Intent.WorldI\
    nterface.System.kept w s m (ins t) (@Prod.snd.{0, 0} (AcornVerif.Intent.WorldInterface.Syst\
    em.Act w) (AcornVerif.Intent.WorldInterface.System.Memory w) (AcornVerif.Intent.WorldInterf\
    ace.System.answer w s m (ins t))))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.System.start\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argumen\
    ts and returns field number 6, counted after the parameters in the type of AcornVerif.Inten\
    t.WorldInterface.System's constructor, of its argument number 1, a value of AcornVerif.Inte\
    nt.WorldInterface.System. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.WorldInterface.System), AcornVerif.Intent.WorldInterface.Syst\
    em.State self\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.System.initial\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argumen\
    ts and returns field number 11, counted after the parameters in the type of AcornVerif.Inte\
    nt.WorldInterface.System's constructor, of its argument number 1, a value of AcornVerif.Int\
    ent.WorldInterface.System. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.WorldInterface.System), AcornVerif.Intent.WorldInterface.Syst\
    em.Memory self\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.System.goesOn\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argumen\
    ts and returns field number 14, counted after the parameters in the type of AcornVerif.Inte\
    nt.WorldInterface.System's constructor, of its argument number 1, a value of AcornVerif.Int\
    ent.WorldInterface.System. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.WorldInterface.System), AcornVerif.Intent.WorldInterface.Syst\
    em.State self → AcornVerif.Intent.WorldInterface.System.Memory self → AcornVerif.Intent.Wor\
    ldInterface.System.Input self → Bool\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.System.moved\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argumen\
    ts and returns field number 17, counted after the parameters in the type of AcornVerif.Inte\
    nt.WorldInterface.System's constructor, of its argument number 1, a value of AcornVerif.Int\
    ent.WorldInterface.System. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.WorldInterface.System), AcornVerif.Intent.WorldInterface.Syst\
    em.State self → AcornVerif.Intent.WorldInterface.System.Memory self → AcornVerif.Intent.Wor\
    ldInterface.System.Input self → AcornVerif.Intent.WorldInterface.System.Act self → AcornVer\
    if.Intent.WorldInterface.System.State self\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.System.Act\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argumen\
    ts and returns field number 3, counted after the parameters in the type of AcornVerif.Inten\
    t.WorldInterface.System's constructor, of its argument number 1, a value of AcornVerif.Inte\
    nt.WorldInterface.System. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.WorldInterface.System), Type\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.System.applied\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argumen\
    ts and returns field number 16, counted after the parameters in the type of AcornVerif.Inte\
    nt.WorldInterface.System's constructor, of its argument number 1, a value of AcornVerif.Int\
    ent.WorldInterface.System. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.WorldInterface.System), AcornVerif.Intent.WorldInterface.Syst\
    em.State self → AcornVerif.Intent.WorldInterface.System.Memory self → AcornVerif.Intent.Wor\
    ldInterface.System.Input self → AcornVerif.Intent.WorldInterface.System.Act self → AcornVer\
    if.Intent.WorldInterface.System.Act self\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.System.answer\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (w : AcornVerif.Intent.WorldInterface.System), ∀ (s : AcornVerif.Intent.WorldInterface.\
    System.State w), ∀ (m : AcornVerif.Intent.WorldInterface.System.Memory w), ∀ (e : AcornVeri\
    f.Intent.WorldInterface.System.Input w), Prod.{0, 0} (AcornVerif.Intent.WorldInterface.Syst\
    em.Act w) (AcornVerif.Intent.WorldInterface.System.Memory w)\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => fun (s : AcornVerif.Intent.WorldInte\
    rface.System.State w) => fun (m : AcornVerif.Intent.WorldInterface.System.Memory w) => fun \
    (e : AcornVerif.Intent.WorldInterface.System.Input w) => AcornVerif.Intent.WorldInterface.S\
    ystem.act w m (AcornVerif.Intent.WorldInterface.System.given w s m e)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.System.act\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argumen\
    ts and returns field number 12, counted after the parameters in the type of AcornVerif.Inte\
    nt.WorldInterface.System's constructor, of its argument number 1, a value of AcornVerif.Int\
    ent.WorldInterface.System. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.WorldInterface.System), AcornVerif.Intent.WorldInterface.Syst\
    em.Memory self → Prod.{0, 0} (AcornVerif.Intent.WorldInterface.System.Obs self) Rat → Prod.\
    {0, 0} (AcornVerif.Intent.WorldInterface.System.Act self) (AcornVerif.Intent.WorldInterface\
    .System.Memory self)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.System.Obs\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argumen\
    ts and returns field number 2, counted after the parameters in the type of AcornVerif.Inten\
    t.WorldInterface.System's constructor, of its argument number 1, a value of AcornVerif.Inte\
    nt.WorldInterface.System. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.WorldInterface.System), Type\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.System.given\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argumen\
    ts and returns field number 15, counted after the parameters in the type of AcornVerif.Inte\
    nt.WorldInterface.System's constructor, of its argument number 1, a value of AcornVerif.Int\
    ent.WorldInterface.System. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.WorldInterface.System), AcornVerif.Intent.WorldInterface.Syst\
    em.State self → AcornVerif.Intent.WorldInterface.System.Memory self → AcornVerif.Intent.Wor\
    ldInterface.System.Input self → Prod.{0, 0} (AcornVerif.Intent.WorldInterface.System.Obs se\
    lf) Rat\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.System.kept\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argumen\
    ts and returns field number 18, counted after the parameters in the type of AcornVerif.Inte\
    nt.WorldInterface.System's constructor, of its argument number 1, a value of AcornVerif.Int\
    ent.WorldInterface.System. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.WorldInterface.System), AcornVerif.Intent.WorldInterface.Syst\
    em.State self → AcornVerif.Intent.WorldInterface.System.Memory self → AcornVerif.Intent.Wor\
    ldInterface.System.Input self → AcornVerif.Intent.WorldInterface.System.Memory self → Acorn\
    Verif.Intent.WorldInterface.System.Memory self\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.System.observe\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argumen\
    ts and returns field number 7, counted after the parameters in the type of AcornVerif.Inten\
    t.WorldInterface.System's constructor, of its argument number 1, a value of AcornVerif.Inte\
    nt.WorldInterface.System. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.WorldInterface.System), AcornVerif.Intent.WorldInterface.Syst\
    em.State self → AcornVerif.Intent.WorldInterface.System.Obs self\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.System.reward\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argumen\
    ts and returns field number 8, counted after the parameters in the type of AcornVerif.Inten\
    t.WorldInterface.System's constructor, of its argument number 1, a value of AcornVerif.Inte\
    nt.WorldInterface.System. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.WorldInterface.System), AcornVerif.Intent.WorldInterface.Syst\
    em.State self → Rat\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.System.available\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argumen\
    ts and returns field number 9, counted after the parameters in the type of AcornVerif.Inten\
    t.WorldInterface.System's constructor, of its argument number 1, a value of AcornVerif.Inte\
    nt.WorldInterface.System. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.WorldInterface.System), AcornVerif.Intent.WorldInterface.Syst\
    em.State self → AcornVerif.Intent.WorldInterface.System.Act self → Prop\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.System.step\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argumen\
    ts and returns field number 10, counted after the parameters in the type of AcornVerif.Inte\
    nt.WorldInterface.System's constructor, of its argument number 1, a value of AcornVerif.Int\
    ent.WorldInterface.System. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.WorldInterface.System), AcornVerif.Intent.WorldInterface.Syst\
    em.State self → AcornVerif.Intent.WorldInterface.System.Act self → AcornVerif.Intent.WorldI\
    nterface.System.State self\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.System.stopRequest\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argumen\
    ts and returns field number 13, counted after the parameters in the type of AcornVerif.Inte\
    nt.WorldInterface.System's constructor, of its argument number 1, a value of AcornVerif.Int\
    ent.WorldInterface.System. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.WorldInterface.System), AcornVerif.Intent.WorldInterface.Syst\
    em.Input self\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.Configuration\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type 1\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | @Sigma.{1, 0} AcornVerif.Intent.WorldInterface.System (fun (w : AcornVerif.Intent.WorldIn\
    terface.System) => Prod.{0, 0} (Nat → AcornVerif.Intent.WorldInterface.System.Input w) (Pro\
    d.{0, 0} Nat (Prod.{0, 0} (AcornVerif.Intent.WorldInterface.System.State w) (AcornVerif.Int\
    ent.WorldInterface.System.Memory w))))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.loopStep\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (w : AcornVerif.Intent.WorldInterface.System), ∀ (s : AcornVerif.Intent.WorldInterface.\
    System.State w), ∀ (m : AcornVerif.Intent.WorldInterface.System.Memory w), Prod.{0, 0} (Aco\
    rnVerif.Intent.WorldInterface.System.State w) (AcornVerif.Intent.WorldInterface.System.Memo\
    ry w)\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (w : AcornVerif.Intent.WorldInterface.System) => fun (s : AcornVerif.Intent.WorldInte\
    rface.System.State w) => fun (m : AcornVerif.Intent.WorldInterface.System.Memory w) => @Pro\
    d.mk.{0, 0} (AcornVerif.Intent.WorldInterface.System.State w) (AcornVerif.Intent.WorldInter\
    face.System.Memory w) (AcornVerif.Intent.WorldInterface.System.step w s (@Prod.fst.{0, 0} (\
    AcornVerif.Intent.WorldInterface.System.Act w) (AcornVerif.Intent.WorldInterface.System.Mem\
    ory w) (AcornVerif.Intent.WorldInterface.System.act w m (@Prod.mk.{0, 0} (AcornVerif.Intent\
    .WorldInterface.System.Obs w) Rat (AcornVerif.Intent.WorldInterface.System.observe w s) (Ac\
    ornVerif.Intent.WorldInterface.System.reward w s))))) (@Prod.snd.{0, 0} (AcornVerif.Intent.\
    WorldInterface.System.Act w) (AcornVerif.Intent.WorldInterface.System.Memory w) (AcornVerif\
    .Intent.WorldInterface.System.act w m (@Prod.mk.{0, 0} (AcornVerif.Intent.WorldInterface.Sy\
    stem.Obs w) Rat (AcornVerif.Intent.WorldInterface.System.observe w s) (AcornVerif.Intent.Wo\
    rldInterface.System.reward w s))))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.handsState\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.WorldInterface.System\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.WorldInterface.runOf AcornVerif.Intent.WorldInterface.shrouded AcornVer\
    if.Intent.WorldInterface.echo (fun (x : AcornVerif.Intent.WorldInterface.World.State AcornV\
    erif.Intent.WorldInterface.shrouded) => fun (x_1 : @AcornVerif.Intent.WorldInterface.Agent.\
    Memory (AcornVerif.Intent.WorldInterface.World.Obs AcornVerif.Intent.WorldInterface.shroude\
    d) (AcornVerif.Intent.WorldInterface.World.Act AcornVerif.Intent.WorldInterface.shrouded) A\
    cornVerif.Intent.WorldInterface.echo) => fun (e : Bool) => Bool.not e) (fun (s : AcornVerif\
    .Intent.WorldInterface.World.State AcornVerif.Intent.WorldInterface.shrouded) => fun (x : @\
    AcornVerif.Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.WorldInterface.World.Obs A\
    cornVerif.Intent.WorldInterface.shrouded) (AcornVerif.Intent.WorldInterface.World.Act Acorn\
    Verif.Intent.WorldInterface.shrouded) AcornVerif.Intent.WorldInterface.echo) => fun (x_1 : \
    Bool) => @Prod.mk.{0, 0} (AcornVerif.Intent.WorldInterface.World.Obs AcornVerif.Intent.Worl\
    dInterface.shrouded) Rat s (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))\
    \x20(fun (x : AcornVerif.Intent.WorldInterface.World.State AcornVerif.Intent.WorldInterface.sh\
    rouded) => fun (x_1 : @AcornVerif.Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.Wor\
    ldInterface.World.Obs AcornVerif.Intent.WorldInterface.shrouded) (AcornVerif.Intent.WorldIn\
    terface.World.Act AcornVerif.Intent.WorldInterface.shrouded) AcornVerif.Intent.WorldInterfa\
    ce.echo) => fun (x_2 : Bool) => fun (a : AcornVerif.Intent.WorldInterface.World.Act AcornVe\
    rif.Intent.WorldInterface.shrouded) => a) (fun (x : AcornVerif.Intent.WorldInterface.World.\
    State AcornVerif.Intent.WorldInterface.shrouded) => fun (x_1 : @AcornVerif.Intent.WorldInte\
    rface.Agent.Memory (AcornVerif.Intent.WorldInterface.World.Obs AcornVerif.Intent.WorldInter\
    face.shrouded) (AcornVerif.Intent.WorldInterface.World.Act AcornVerif.Intent.WorldInterface\
    .shrouded) AcornVerif.Intent.WorldInterface.echo) => fun (x_2 : Bool) => fun (a : AcornVeri\
    f.Intent.WorldInterface.World.Act AcornVerif.Intent.WorldInterface.shrouded) => a) (fun (x \
    : AcornVerif.Intent.WorldInterface.World.State AcornVerif.Intent.WorldInterface.shrouded) =\
    > fun (x_1 : @AcornVerif.Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.WorldInterfa\
    ce.World.Obs AcornVerif.Intent.WorldInterface.shrouded) (AcornVerif.Intent.WorldInterface.W\
    orld.Act AcornVerif.Intent.WorldInterface.shrouded) AcornVerif.Intent.WorldInterface.echo) \
    => fun (x_2 : Bool) => fun (m : @AcornVerif.Intent.WorldInterface.Agent.Memory (AcornVerif.\
    Intent.WorldInterface.World.Obs AcornVerif.Intent.WorldInterface.shrouded) (AcornVerif.Inte\
    nt.WorldInterface.World.Act AcornVerif.Intent.WorldInterface.shrouded) AcornVerif.Intent.Wo\
    rldInterface.echo) => m)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.runOf\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : AcornVerif.Intent.WorldInterface.World), ∀ (A : AcornVerif.Intent.WorldInterface.A\
    gent (AcornVerif.Intent.WorldInterface.World.Obs W) (AcornVerif.Intent.WorldInterface.World\
    .Act W)), ∀ (going : AcornVerif.Intent.WorldInterface.World.State W → @AcornVerif.Intent.Wo\
    rldInterface.Agent.Memory (AcornVerif.Intent.WorldInterface.World.Obs W) (AcornVerif.Intent\
    .WorldInterface.World.Act W) A → Bool → Bool), ∀ (giving : AcornVerif.Intent.WorldInterface\
    .World.State W → @AcornVerif.Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.WorldInt\
    erface.World.Obs W) (AcornVerif.Intent.WorldInterface.World.Act W) A → Bool → Prod.{0, 0} (\
    AcornVerif.Intent.WorldInterface.World.Obs W) Rat), ∀ (handing : AcornVerif.Intent.WorldInt\
    erface.World.State W → @AcornVerif.Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.Wo\
    rldInterface.World.Obs W) (AcornVerif.Intent.WorldInterface.World.Act W) A → Bool → AcornVe\
    rif.Intent.WorldInterface.World.Act W → AcornVerif.Intent.WorldInterface.World.Act W), ∀ (m\
    oving : AcornVerif.Intent.WorldInterface.World.State W → @AcornVerif.Intent.WorldInterface.\
    Agent.Memory (AcornVerif.Intent.WorldInterface.World.Obs W) (AcornVerif.Intent.WorldInterfa\
    ce.World.Act W) A → Bool → AcornVerif.Intent.WorldInterface.World.Act W → AcornVerif.Intent\
    .WorldInterface.World.State W), ∀ (keeping : AcornVerif.Intent.WorldInterface.World.State W\
    \x20→ @AcornVerif.Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.WorldInterface.World.O\
    bs W) (AcornVerif.Intent.WorldInterface.World.Act W) A → Bool → @AcornVerif.Intent.WorldInt\
    erface.Agent.Memory (AcornVerif.Intent.WorldInterface.World.Obs W) (AcornVerif.Intent.World\
    Interface.World.Act W) A → @AcornVerif.Intent.WorldInterface.Agent.Memory (AcornVerif.Inten\
    t.WorldInterface.World.Obs W) (AcornVerif.Intent.WorldInterface.World.Act W) A), AcornVerif\
    .Intent.WorldInterface.System\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (W : AcornVerif.Intent.WorldInterface.World) => fun (A : AcornVerif.Intent.WorldInter\
    face.Agent (AcornVerif.Intent.WorldInterface.World.Obs W) (AcornVerif.Intent.WorldInterface\
    .World.Act W)) => fun (going : AcornVerif.Intent.WorldInterface.World.State W → @AcornVerif\
    .Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.WorldInterface.World.Obs W) (AcornVe\
    rif.Intent.WorldInterface.World.Act W) A → Bool → Bool) => fun (giving : AcornVerif.Intent.\
    WorldInterface.World.State W → @AcornVerif.Intent.WorldInterface.Agent.Memory (AcornVerif.I\
    ntent.WorldInterface.World.Obs W) (AcornVerif.Intent.WorldInterface.World.Act W) A → Bool →\
    \x20Prod.{0, 0} (AcornVerif.Intent.WorldInterface.World.Obs W) Rat) => fun (handing : AcornVer\
    if.Intent.WorldInterface.World.State W → @AcornVerif.Intent.WorldInterface.Agent.Memory (Ac\
    ornVerif.Intent.WorldInterface.World.Obs W) (AcornVerif.Intent.WorldInterface.World.Act W) \
    A → Bool → AcornVerif.Intent.WorldInterface.World.Act W → AcornVerif.Intent.WorldInterface.\
    World.Act W) => fun (moving : AcornVerif.Intent.WorldInterface.World.State W → @AcornVerif.\
    Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.WorldInterface.World.Obs W) (AcornVer\
    if.Intent.WorldInterface.World.Act W) A → Bool → AcornVerif.Intent.WorldInterface.World.Act\
    \x20W → AcornVerif.Intent.WorldInterface.World.State W) => fun (keeping : AcornVerif.Intent.Wo\
    rldInterface.World.State W → @AcornVerif.Intent.WorldInterface.Agent.Memory (AcornVerif.Int\
    ent.WorldInterface.World.Obs W) (AcornVerif.Intent.WorldInterface.World.Act W) A → Bool → @\
    AcornVerif.Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.WorldInterface.World.Obs W\
    ) (AcornVerif.Intent.WorldInterface.World.Act W) A → @AcornVerif.Intent.WorldInterface.Agen\
    t.Memory (AcornVerif.Intent.WorldInterface.World.Obs W) (AcornVerif.Intent.WorldInterface.W\
    orld.Act W) A) => AcornVerif.Intent.WorldInterface.System.mk (AcornVerif.Intent.WorldInterf\
    ace.World.State W) (AcornVerif.Intent.WorldInterface.World.Obs W) (AcornVerif.Intent.WorldI\
    nterface.World.Act W) (@AcornVerif.Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.Wo\
    rldInterface.World.Obs W) (AcornVerif.Intent.WorldInterface.World.Act W) A) Bool (AcornVeri\
    f.Intent.WorldInterface.World.start W) (AcornVerif.Intent.WorldInterface.World.observe W) (\
    AcornVerif.Intent.WorldInterface.World.reward W) (AcornVerif.Intent.WorldInterface.World.av\
    ailable W) (AcornVerif.Intent.WorldInterface.World.step W) (@AcornVerif.Intent.WorldInterfa\
    ce.Agent.initial (AcornVerif.Intent.WorldInterface.World.Obs W) (AcornVerif.Intent.WorldInt\
    erface.World.Act W) A) (@AcornVerif.Intent.WorldInterface.Agent.act (AcornVerif.Intent.Worl\
    dInterface.World.Obs W) (AcornVerif.Intent.WorldInterface.World.Act W) A) Bool.true going g\
    iving handing moving keeping\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.World\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameters\
    \x20are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type 1\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its \
    recursor is the one Lean's kernel derives from this declaration. Its constructors, in order\
    , each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.WorldInterface.World.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (State : Type), ∀ (Obs : Type), ∀ (Act : Type), ∀ (start : State), ∀ (observe : State →\
    \x20Obs), ∀ (reward : State → Rat), ∀ (available : State → Act → Prop), ∀ (step : State → Act \
    → State), AcornVerif.Intent.WorldInterface.World\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.Agent\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameters\
    \x20are the structure's fields, in order. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (Obs : Type), ∀ (Act : Type), Type 1\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 2 are parameters and the other 0 indices. Its \
    recursor is the one Lean's kernel derives from this declaration. Its constructors, in order\
    , each with its type:\n\
    | \n\
    | #### AcornVerif.Intent.WorldInterface.Agent.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {Obs : Type}, ∀ {Act : Type}, ∀ (Memory : Type), ∀ (initial : Memory), ∀ (act : Memory \
    → Prod.{0, 0} Obs Rat → Prod.{0, 0} Act Memory), AcornVerif.Intent.WorldInterface.Agent Obs\
    \x20Act\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.World.Obs\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argumen\
    ts and returns field number 2, counted after the parameters in the type of AcornVerif.Inten\
    t.WorldInterface.World's constructor, of its argument number 1, a value of AcornVerif.Inten\
    t.WorldInterface.World. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.WorldInterface.World), Type\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.World.Act\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argumen\
    ts and returns field number 3, counted after the parameters in the type of AcornVerif.Inten\
    t.WorldInterface.World's constructor, of its argument number 1, a value of AcornVerif.Inten\
    t.WorldInterface.World. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.WorldInterface.World), Type\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.World.State\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argumen\
    ts and returns field number 1, counted after the parameters in the type of AcornVerif.Inten\
    t.WorldInterface.World's constructor, of its argument number 1, a value of AcornVerif.Inten\
    t.WorldInterface.World. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.WorldInterface.World), Type\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.Agent.Memory\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 3 argumen\
    ts and returns field number 1, counted after the parameters in the type of AcornVerif.Inten\
    t.WorldInterface.Agent's constructor, of its argument number 3, a value of AcornVerif.Inten\
    t.WorldInterface.Agent. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Obs : Type}, ∀ {Act : Type}, ∀ (self : AcornVerif.Intent.WorldInterface.Agent Obs Act)\
    , Type\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.World.start\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argumen\
    ts and returns field number 4, counted after the parameters in the type of AcornVerif.Inten\
    t.WorldInterface.World's constructor, of its argument number 1, a value of AcornVerif.Inten\
    t.WorldInterface.World. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.WorldInterface.World), AcornVerif.Intent.WorldInterface.World\
    .State self\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.World.observe\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argumen\
    ts and returns field number 5, counted after the parameters in the type of AcornVerif.Inten\
    t.WorldInterface.World's constructor, of its argument number 1, a value of AcornVerif.Inten\
    t.WorldInterface.World. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.WorldInterface.World), AcornVerif.Intent.WorldInterface.World\
    .State self → AcornVerif.Intent.WorldInterface.World.Obs self\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.World.reward\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argumen\
    ts and returns field number 6, counted after the parameters in the type of AcornVerif.Inten\
    t.WorldInterface.World's constructor, of its argument number 1, a value of AcornVerif.Inten\
    t.WorldInterface.World. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.WorldInterface.World), AcornVerif.Intent.WorldInterface.World\
    .State self → Rat\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.World.available\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argumen\
    ts and returns field number 7, counted after the parameters in the type of AcornVerif.Inten\
    t.WorldInterface.World's constructor, of its argument number 1, a value of AcornVerif.Inten\
    t.WorldInterface.World. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.WorldInterface.World), AcornVerif.Intent.WorldInterface.World\
    .State self → AcornVerif.Intent.WorldInterface.World.Act self → Prop\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.World.step\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 1 argumen\
    ts and returns field number 8, counted after the parameters in the type of AcornVerif.Inten\
    t.WorldInterface.World's constructor, of its argument number 1, a value of AcornVerif.Inten\
    t.WorldInterface.World. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (self : AcornVerif.Intent.WorldInterface.World), AcornVerif.Intent.WorldInterface.World\
    .State self → AcornVerif.Intent.WorldInterface.World.Act self → AcornVerif.Intent.WorldInte\
    rface.World.State self\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.Agent.initial\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 3 argumen\
    ts and returns field number 2, counted after the parameters in the type of AcornVerif.Inten\
    t.WorldInterface.Agent's constructor, of its argument number 3, a value of AcornVerif.Inten\
    t.WorldInterface.Agent. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Obs : Type}, ∀ {Act : Type}, ∀ (self : AcornVerif.Intent.WorldInterface.Agent Obs Act)\
    , @AcornVerif.Intent.WorldInterface.Agent.Memory Obs Act self\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.Agent.act\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 3 argumen\
    ts and returns field number 3, counted after the parameters in the type of AcornVerif.Inten\
    t.WorldInterface.Agent's constructor, of its argument number 3, a value of AcornVerif.Inten\
    t.WorldInterface.Agent. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {Obs : Type}, ∀ {Act : Type}, ∀ (self : AcornVerif.Intent.WorldInterface.Agent Obs Act)\
    , @AcornVerif.Intent.WorldInterface.Agent.Memory Obs Act self → Prod.{0, 0} Obs Rat → Prod.\
    {0, 0} Act (@AcornVerif.Intent.WorldInterface.Agent.Memory Obs Act self)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.shrouded\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.WorldInterface.World\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.WorldInterface.World.mk Bool Bool Bool Bool.true (fun (x : Bool) => Boo\
    l.false) (fun (x : Bool) => @OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) \
    (fun (x : Bool) => fun (x_1 : Bool) => True) (fun (x : Bool) => fun (a : Bool) => a)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.echo\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.WorldInterface.Agent Bool Bool\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | @AcornVerif.Intent.WorldInterface.Agent.mk Bool Bool Nat (@OfNat.ofNat.{0} Nat (nat_lit 0\
    ) (instOfNatNat (nat_lit 0))) (fun (m : Nat) => fun (o : Prod.{0, 0} Bool Rat) => @Prod.mk.\
    {0, 0} Bool Nat (@Prod.fst.{0, 0} Bool Rat o) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.\
    {0} Nat instAddNat) m (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.resetsAtRestart\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.WorldInterface.System\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.WorldInterface.runOf AcornVerif.Intent.WorldInterface.attempts AcornVer\
    if.Intent.WorldInterface.echo (fun (x : AcornVerif.Intent.WorldInterface.World.State AcornV\
    erif.Intent.WorldInterface.attempts) => fun (x_1 : @AcornVerif.Intent.WorldInterface.Agent.\
    Memory (AcornVerif.Intent.WorldInterface.World.Obs AcornVerif.Intent.WorldInterface.attempt\
    s) (AcornVerif.Intent.WorldInterface.World.Act AcornVerif.Intent.WorldInterface.attempts) A\
    cornVerif.Intent.WorldInterface.echo) => fun (e : Bool) => Bool.not e) (fun (s : AcornVerif\
    .Intent.WorldInterface.World.State AcornVerif.Intent.WorldInterface.attempts) => fun (x : @\
    AcornVerif.Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.WorldInterface.World.Obs A\
    cornVerif.Intent.WorldInterface.attempts) (AcornVerif.Intent.WorldInterface.World.Act Acorn\
    Verif.Intent.WorldInterface.attempts) AcornVerif.Intent.WorldInterface.echo) => fun (x_1 : \
    Bool) => @Prod.mk.{0, 0} (AcornVerif.Intent.WorldInterface.World.Obs AcornVerif.Intent.Worl\
    dInterface.attempts) Rat s (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))\
    \x20(fun (x : AcornVerif.Intent.WorldInterface.World.State AcornVerif.Intent.WorldInterface.at\
    tempts) => fun (x_1 : @AcornVerif.Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.Wor\
    ldInterface.World.Obs AcornVerif.Intent.WorldInterface.attempts) (AcornVerif.Intent.WorldIn\
    terface.World.Act AcornVerif.Intent.WorldInterface.attempts) AcornVerif.Intent.WorldInterfa\
    ce.echo) => fun (x_2 : Bool) => fun (a : AcornVerif.Intent.WorldInterface.World.Act AcornVe\
    rif.Intent.WorldInterface.attempts) => a) (fun (s : AcornVerif.Intent.WorldInterface.World.\
    State AcornVerif.Intent.WorldInterface.attempts) => fun (x : @AcornVerif.Intent.WorldInterf\
    ace.Agent.Memory (AcornVerif.Intent.WorldInterface.World.Obs AcornVerif.Intent.WorldInterfa\
    ce.attempts) (AcornVerif.Intent.WorldInterface.World.Act AcornVerif.Intent.WorldInterface.a\
    ttempts) AcornVerif.Intent.WorldInterface.echo) => fun (x_1 : Bool) => fun (x_2 : AcornVeri\
    f.Intent.WorldInterface.World.Act AcornVerif.Intent.WorldInterface.attempts) => Bool.not s)\
    \x20(fun (s : AcornVerif.Intent.WorldInterface.World.State AcornVerif.Intent.WorldInterface.at\
    tempts) => fun (x : @AcornVerif.Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.World\
    Interface.World.Obs AcornVerif.Intent.WorldInterface.attempts) (AcornVerif.Intent.WorldInte\
    rface.World.Act AcornVerif.Intent.WorldInterface.attempts) AcornVerif.Intent.WorldInterface\
    .echo) => fun (x_1 : Bool) => fun (m : @AcornVerif.Intent.WorldInterface.Agent.Memory (Acor\
    nVerif.Intent.WorldInterface.World.Obs AcornVerif.Intent.WorldInterface.attempts) (AcornVer\
    if.Intent.WorldInterface.World.Act AcornVerif.Intent.WorldInterface.attempts) AcornVerif.In\
    tent.WorldInterface.echo) => @cond.{1} (@AcornVerif.Intent.WorldInterface.Agent.Memory (Aco\
    rnVerif.Intent.WorldInterface.World.Obs AcornVerif.Intent.WorldInterface.attempts) (AcornVe\
    rif.Intent.WorldInterface.World.Act AcornVerif.Intent.WorldInterface.attempts) AcornVerif.I\
    ntent.WorldInterface.echo) s Nat.zero m)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.attempts\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.WorldInterface.World\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.WorldInterface.World.mk Bool Bool Bool Bool.false (fun (s : Bool) => s)\
    \x20(fun (x : Bool) => @OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (fun (x \
    : Bool) => fun (x_1 : Bool) => True) (fun (s : Bool) => fun (x : Bool) => Bool.not s)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.hostWritesMemory\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.WorldInterface.System\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.WorldInterface.runOf AcornVerif.Intent.WorldInterface.mirror AcornVerif\
    .Intent.WorldInterface.echo (fun (x : AcornVerif.Intent.WorldInterface.World.State AcornVer\
    if.Intent.WorldInterface.mirror) => fun (x_1 : @AcornVerif.Intent.WorldInterface.Agent.Memo\
    ry (AcornVerif.Intent.WorldInterface.World.Obs AcornVerif.Intent.WorldInterface.mirror) (Ac\
    ornVerif.Intent.WorldInterface.World.Act AcornVerif.Intent.WorldInterface.mirror) AcornVeri\
    f.Intent.WorldInterface.echo) => fun (e : Bool) => Bool.not e) (fun (s : AcornVerif.Intent.\
    WorldInterface.World.State AcornVerif.Intent.WorldInterface.mirror) => fun (x : @AcornVerif\
    .Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.WorldInterface.World.Obs AcornVerif.\
    Intent.WorldInterface.mirror) (AcornVerif.Intent.WorldInterface.World.Act AcornVerif.Intent\
    .WorldInterface.mirror) AcornVerif.Intent.WorldInterface.echo) => fun (x_1 : Bool) => @Prod\
    .mk.{0, 0} (AcornVerif.Intent.WorldInterface.World.Obs AcornVerif.Intent.WorldInterface.mir\
    ror) Rat s (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) (fun (x : Acorn\
    Verif.Intent.WorldInterface.World.State AcornVerif.Intent.WorldInterface.mirror) => fun (x_\
    1 : @AcornVerif.Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.WorldInterface.World.\
    Obs AcornVerif.Intent.WorldInterface.mirror) (AcornVerif.Intent.WorldInterface.World.Act Ac\
    ornVerif.Intent.WorldInterface.mirror) AcornVerif.Intent.WorldInterface.echo) => fun (x_2 :\
    \x20Bool) => fun (a : AcornVerif.Intent.WorldInterface.World.Act AcornVerif.Intent.WorldInterf\
    ace.mirror) => a) (fun (x : AcornVerif.Intent.WorldInterface.World.State AcornVerif.Intent.\
    WorldInterface.mirror) => fun (x_1 : @AcornVerif.Intent.WorldInterface.Agent.Memory (AcornV\
    erif.Intent.WorldInterface.World.Obs AcornVerif.Intent.WorldInterface.mirror) (AcornVerif.I\
    ntent.WorldInterface.World.Act AcornVerif.Intent.WorldInterface.mirror) AcornVerif.Intent.W\
    orldInterface.echo) => fun (x_2 : Bool) => fun (a : AcornVerif.Intent.WorldInterface.World.\
    Act AcornVerif.Intent.WorldInterface.mirror) => a) (fun (x : AcornVerif.Intent.WorldInterfa\
    ce.World.State AcornVerif.Intent.WorldInterface.mirror) => fun (x_1 : @AcornVerif.Intent.Wo\
    rldInterface.Agent.Memory (AcornVerif.Intent.WorldInterface.World.Obs AcornVerif.Intent.Wor\
    ldInterface.mirror) (AcornVerif.Intent.WorldInterface.World.Act AcornVerif.Intent.WorldInte\
    rface.mirror) AcornVerif.Intent.WorldInterface.echo) => fun (x_2 : Bool) => fun (m : @Acorn\
    Verif.Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.WorldInterface.World.Obs AcornV\
    erif.Intent.WorldInterface.mirror) (AcornVerif.Intent.WorldInterface.World.Act AcornVerif.I\
    ntent.WorldInterface.mirror) AcornVerif.Intent.WorldInterface.echo) => Nat.succ m)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.mirror\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.WorldInterface.World\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.WorldInterface.World.mk Bool Bool Bool Bool.false (fun (s : Bool) => s)\
    \x20(fun (x : Bool) => @OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (fun (x \
    : Bool) => fun (x_1 : Bool) => True) (fun (x : Bool) => fun (a : Bool) => a)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.hostOverridesAction\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.WorldInterface.System\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.WorldInterface.runOf AcornVerif.Intent.WorldInterface.mirror AcornVerif\
    .Intent.WorldInterface.echo (fun (x : AcornVerif.Intent.WorldInterface.World.State AcornVer\
    if.Intent.WorldInterface.mirror) => fun (x_1 : @AcornVerif.Intent.WorldInterface.Agent.Memo\
    ry (AcornVerif.Intent.WorldInterface.World.Obs AcornVerif.Intent.WorldInterface.mirror) (Ac\
    ornVerif.Intent.WorldInterface.World.Act AcornVerif.Intent.WorldInterface.mirror) AcornVeri\
    f.Intent.WorldInterface.echo) => fun (e : Bool) => Bool.not e) (fun (s : AcornVerif.Intent.\
    WorldInterface.World.State AcornVerif.Intent.WorldInterface.mirror) => fun (x : @AcornVerif\
    .Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.WorldInterface.World.Obs AcornVerif.\
    Intent.WorldInterface.mirror) (AcornVerif.Intent.WorldInterface.World.Act AcornVerif.Intent\
    .WorldInterface.mirror) AcornVerif.Intent.WorldInterface.echo) => fun (x_1 : Bool) => @Prod\
    .mk.{0, 0} (AcornVerif.Intent.WorldInterface.World.Obs AcornVerif.Intent.WorldInterface.mir\
    ror) Rat s (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) (fun (x : Acorn\
    Verif.Intent.WorldInterface.World.State AcornVerif.Intent.WorldInterface.mirror) => fun (x_\
    1 : @AcornVerif.Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.WorldInterface.World.\
    Obs AcornVerif.Intent.WorldInterface.mirror) (AcornVerif.Intent.WorldInterface.World.Act Ac\
    ornVerif.Intent.WorldInterface.mirror) AcornVerif.Intent.WorldInterface.echo) => fun (x_2 :\
    \x20Bool) => fun (a : AcornVerif.Intent.WorldInterface.World.Act AcornVerif.Intent.WorldInterf\
    ace.mirror) => Bool.not a) (fun (x : AcornVerif.Intent.WorldInterface.World.State AcornVeri\
    f.Intent.WorldInterface.mirror) => fun (x_1 : @AcornVerif.Intent.WorldInterface.Agent.Memor\
    y (AcornVerif.Intent.WorldInterface.World.Obs AcornVerif.Intent.WorldInterface.mirror) (Aco\
    rnVerif.Intent.WorldInterface.World.Act AcornVerif.Intent.WorldInterface.mirror) AcornVerif\
    .Intent.WorldInterface.echo) => fun (x_2 : Bool) => fun (a : AcornVerif.Intent.WorldInterfa\
    ce.World.Act AcornVerif.Intent.WorldInterface.mirror) => a) (fun (x : AcornVerif.Intent.Wor\
    ldInterface.World.State AcornVerif.Intent.WorldInterface.mirror) => fun (x_1 : @AcornVerif.\
    Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.WorldInterface.World.Obs AcornVerif.I\
    ntent.WorldInterface.mirror) (AcornVerif.Intent.WorldInterface.World.Act AcornVerif.Intent.\
    WorldInterface.mirror) AcornVerif.Intent.WorldInterface.echo) => fun (x_2 : Bool) => fun (m\
    \x20: @AcornVerif.Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.WorldInterface.World.O\
    bs AcornVerif.Intent.WorldInterface.mirror) (AcornVerif.Intent.WorldInterface.World.Act Aco\
    rnVerif.Intent.WorldInterface.mirror) AcornVerif.Intent.WorldInterface.echo) => m)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.rewardFromMemory\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.WorldInterface.System\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.WorldInterface.runOf AcornVerif.Intent.WorldInterface.mirror AcornVerif\
    .Intent.WorldInterface.holdsOne (fun (x : AcornVerif.Intent.WorldInterface.World.State Acor\
    nVerif.Intent.WorldInterface.mirror) => fun (x_1 : @AcornVerif.Intent.WorldInterface.Agent.\
    Memory (AcornVerif.Intent.WorldInterface.World.Obs AcornVerif.Intent.WorldInterface.mirror)\
    \x20(AcornVerif.Intent.WorldInterface.World.Act AcornVerif.Intent.WorldInterface.mirror) Acorn\
    Verif.Intent.WorldInterface.holdsOne) => fun (e : Bool) => Bool.not e) (fun (s : AcornVerif\
    .Intent.WorldInterface.World.State AcornVerif.Intent.WorldInterface.mirror) => fun (m : @Ac\
    ornVerif.Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.WorldInterface.World.Obs Aco\
    rnVerif.Intent.WorldInterface.mirror) (AcornVerif.Intent.WorldInterface.World.Act AcornVeri\
    f.Intent.WorldInterface.mirror) AcornVerif.Intent.WorldInterface.holdsOne) => fun (x : Bool\
    ) => @Prod.mk.{0, 0} (AcornVerif.Intent.WorldInterface.World.Obs AcornVerif.Intent.WorldInt\
    erface.mirror) Rat s m) (fun (x : AcornVerif.Intent.WorldInterface.World.State AcornVerif.I\
    ntent.WorldInterface.mirror) => fun (x_1 : @AcornVerif.Intent.WorldInterface.Agent.Memory (\
    AcornVerif.Intent.WorldInterface.World.Obs AcornVerif.Intent.WorldInterface.mirror) (AcornV\
    erif.Intent.WorldInterface.World.Act AcornVerif.Intent.WorldInterface.mirror) AcornVerif.In\
    tent.WorldInterface.holdsOne) => fun (x_2 : Bool) => fun (a : AcornVerif.Intent.WorldInterf\
    ace.World.Act AcornVerif.Intent.WorldInterface.mirror) => a) (fun (x : AcornVerif.Intent.Wo\
    rldInterface.World.State AcornVerif.Intent.WorldInterface.mirror) => fun (x_1 : @AcornVerif\
    .Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.WorldInterface.World.Obs AcornVerif.\
    Intent.WorldInterface.mirror) (AcornVerif.Intent.WorldInterface.World.Act AcornVerif.Intent\
    .WorldInterface.mirror) AcornVerif.Intent.WorldInterface.holdsOne) => fun (x_2 : Bool) => f\
    un (a : AcornVerif.Intent.WorldInterface.World.Act AcornVerif.Intent.WorldInterface.mirror)\
    \x20=> a) (fun (x : AcornVerif.Intent.WorldInterface.World.State AcornVerif.Intent.WorldInterf\
    ace.mirror) => fun (x_1 : @AcornVerif.Intent.WorldInterface.Agent.Memory (AcornVerif.Intent\
    .WorldInterface.World.Obs AcornVerif.Intent.WorldInterface.mirror) (AcornVerif.Intent.World\
    Interface.World.Act AcornVerif.Intent.WorldInterface.mirror) AcornVerif.Intent.WorldInterfa\
    ce.holdsOne) => fun (x_2 : Bool) => fun (m : @AcornVerif.Intent.WorldInterface.Agent.Memory\
    \x20(AcornVerif.Intent.WorldInterface.World.Obs AcornVerif.Intent.WorldInterface.mirror) (Acor\
    nVerif.Intent.WorldInterface.World.Act AcornVerif.Intent.WorldInterface.mirror) AcornVerif.\
    Intent.WorldInterface.holdsOne) => m)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.holdsOne\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.WorldInterface.Agent Bool Bool\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | @AcornVerif.Intent.WorldInterface.Agent.mk Bool Bool Rat (@OfNat.ofNat.{0} Rat (nat_lit 1\
    ) (@Rat.instOfNat (nat_lit 1))) (fun (m : Rat) => fun (o : Prod.{0, 0} Bool Rat) => @Prod.m\
    k.{0, 0} Bool Rat (@Prod.fst.{0, 0} Bool Rat o) m)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.couple\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : AcornVerif.Intent.WorldInterface.World), ∀ (A : AcornVerif.Intent.WorldInterface.A\
    gent (AcornVerif.Intent.WorldInterface.World.Obs W) (AcornVerif.Intent.WorldInterface.World\
    .Act W)), AcornVerif.Intent.WorldInterface.System\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (W : AcornVerif.Intent.WorldInterface.World) => fun (A : AcornVerif.Intent.WorldInter\
    face.Agent (AcornVerif.Intent.WorldInterface.World.Obs W) (AcornVerif.Intent.WorldInterface\
    .World.Act W)) => AcornVerif.Intent.WorldInterface.System.mk (AcornVerif.Intent.WorldInterf\
    ace.World.State W) (AcornVerif.Intent.WorldInterface.World.Obs W) (AcornVerif.Intent.WorldI\
    nterface.World.Act W) (@AcornVerif.Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.Wo\
    rldInterface.World.Obs W) (AcornVerif.Intent.WorldInterface.World.Act W) A) Bool (AcornVeri\
    f.Intent.WorldInterface.World.start W) (AcornVerif.Intent.WorldInterface.World.observe W) (\
    AcornVerif.Intent.WorldInterface.World.reward W) (AcornVerif.Intent.WorldInterface.World.av\
    ailable W) (AcornVerif.Intent.WorldInterface.World.step W) (@AcornVerif.Intent.WorldInterfa\
    ce.Agent.initial (AcornVerif.Intent.WorldInterface.World.Obs W) (AcornVerif.Intent.WorldInt\
    erface.World.Act W) A) (@AcornVerif.Intent.WorldInterface.Agent.act (AcornVerif.Intent.Worl\
    dInterface.World.Obs W) (AcornVerif.Intent.WorldInterface.World.Act W) A) Bool.true (fun (x\
    \x20: AcornVerif.Intent.WorldInterface.World.State W) => fun (x_1 : @AcornVerif.Intent.WorldIn\
    terface.Agent.Memory (AcornVerif.Intent.WorldInterface.World.Obs W) (AcornVerif.Intent.Worl\
    dInterface.World.Act W) A) => fun (e : Bool) => Bool.not e) (fun (s : AcornVerif.Intent.Wor\
    ldInterface.World.State W) => fun (x : @AcornVerif.Intent.WorldInterface.Agent.Memory (Acor\
    nVerif.Intent.WorldInterface.World.Obs W) (AcornVerif.Intent.WorldInterface.World.Act W) A)\
    \x20=> fun (x_1 : Bool) => @Prod.mk.{0, 0} (AcornVerif.Intent.WorldInterface.World.Obs W) Rat \
    (AcornVerif.Intent.WorldInterface.World.observe W s) (AcornVerif.Intent.WorldInterface.Worl\
    d.reward W s)) (fun (x : AcornVerif.Intent.WorldInterface.World.State W) => fun (x_1 : @Aco\
    rnVerif.Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.WorldInterface.World.Obs W) (\
    AcornVerif.Intent.WorldInterface.World.Act W) A) => fun (x_2 : Bool) => fun (a : AcornVerif\
    .Intent.WorldInterface.World.Act W) => a) (fun (s : AcornVerif.Intent.WorldInterface.World.\
    State W) => fun (x : @AcornVerif.Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.Worl\
    dInterface.World.Obs W) (AcornVerif.Intent.WorldInterface.World.Act W) A) => fun (x_1 : Boo\
    l) => fun (a : AcornVerif.Intent.WorldInterface.World.Act W) => AcornVerif.Intent.WorldInte\
    rface.World.step W s a) (fun (x : AcornVerif.Intent.WorldInterface.World.State W) => fun (x\
    _1 : @AcornVerif.Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.WorldInterface.World\
    .Obs W) (AcornVerif.Intent.WorldInterface.World.Act W) A) => fun (x_2 : Bool) => fun (m : @\
    AcornVerif.Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.WorldInterface.World.Obs W\
    ) (AcornVerif.Intent.WorldInterface.World.Act W) A) => m)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.resetOnlyAtGameOver\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.WorldInterface.World\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.WorldInterface.World.mk Nat Nat Bool (@OfNat.ofNat.{0} Nat (nat_lit 0) \
    (instOfNatNat (nat_lit 0))) (fun (s : Nat) => s) (fun (x : Nat) => @OfNat.ofNat.{0} Rat (na\
    t_lit 0) (@Rat.instOfNat (nat_lit 0))) (fun (s : Nat) => fun (a : Bool) => Or (@Eq.{1} Nat \
    s (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Eq.{1} Bool a Bool.true)\
    ) (fun (s : Nat) => fun (a : Bool) => @ite.{1} Nat (@Eq.{1} Bool a Bool.true) (instDecidabl\
    eEqBool a Bool.true) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@ite.{1\
    } Nat (@Eq.{1} Nat s (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (instDe\
    cidableEqNat s (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@OfNat.ofNat\
    .{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) s))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.arcPlayer\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.WorldInterface.Agent Nat Bool\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | @AcornVerif.Intent.WorldInterface.Agent.mk Nat Bool Nat (@OfNat.ofNat.{0} Nat (nat_lit 0)\
    \x20(instOfNatNat (nat_lit 0))) (fun (m : Nat) => fun (o : Prod.{0, 0} Nat Rat) => @Prod.mk.{0\
    , 0} Bool Nat (@bne.{0} Nat (@instBEqOfDecidableEq.{0} Nat instDecidableEqNat) (@Prod.fst.{\
    0, 0} Nat Rat o) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@HAdd.hAdd\
    .{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m (@OfNat.ofNat.{0} Nat (nat_lit 1) (\
    instOfNatNat (nat_lit 1)))))\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.hostRestarts\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.WorldInterface.System\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.WorldInterface.runOf AcornVerif.Intent.WorldInterface.attempts AcornVer\
    if.Intent.WorldInterface.echo (fun (x : AcornVerif.Intent.WorldInterface.World.State AcornV\
    erif.Intent.WorldInterface.attempts) => fun (x_1 : @AcornVerif.Intent.WorldInterface.Agent.\
    Memory (AcornVerif.Intent.WorldInterface.World.Obs AcornVerif.Intent.WorldInterface.attempt\
    s) (AcornVerif.Intent.WorldInterface.World.Act AcornVerif.Intent.WorldInterface.attempts) A\
    cornVerif.Intent.WorldInterface.echo) => fun (e : Bool) => Bool.not e) (fun (s : AcornVerif\
    .Intent.WorldInterface.World.State AcornVerif.Intent.WorldInterface.attempts) => fun (x : @\
    AcornVerif.Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.WorldInterface.World.Obs A\
    cornVerif.Intent.WorldInterface.attempts) (AcornVerif.Intent.WorldInterface.World.Act Acorn\
    Verif.Intent.WorldInterface.attempts) AcornVerif.Intent.WorldInterface.echo) => fun (x_1 : \
    Bool) => @Prod.mk.{0, 0} (AcornVerif.Intent.WorldInterface.World.Obs AcornVerif.Intent.Worl\
    dInterface.attempts) Rat s (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))\
    \x20(fun (x : AcornVerif.Intent.WorldInterface.World.State AcornVerif.Intent.WorldInterface.at\
    tempts) => fun (x_1 : @AcornVerif.Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.Wor\
    ldInterface.World.Obs AcornVerif.Intent.WorldInterface.attempts) (AcornVerif.Intent.WorldIn\
    terface.World.Act AcornVerif.Intent.WorldInterface.attempts) AcornVerif.Intent.WorldInterfa\
    ce.echo) => fun (x_2 : Bool) => fun (a : AcornVerif.Intent.WorldInterface.World.Act AcornVe\
    rif.Intent.WorldInterface.attempts) => a) (fun (x : AcornVerif.Intent.WorldInterface.World.\
    State AcornVerif.Intent.WorldInterface.attempts) => fun (x_1 : @AcornVerif.Intent.WorldInte\
    rface.Agent.Memory (AcornVerif.Intent.WorldInterface.World.Obs AcornVerif.Intent.WorldInter\
    face.attempts) (AcornVerif.Intent.WorldInterface.World.Act AcornVerif.Intent.WorldInterface\
    .attempts) AcornVerif.Intent.WorldInterface.echo) => fun (x_2 : Bool) => fun (x_3 : AcornVe\
    rif.Intent.WorldInterface.World.Act AcornVerif.Intent.WorldInterface.attempts) => Bool.fals\
    e) (fun (x : AcornVerif.Intent.WorldInterface.World.State AcornVerif.Intent.WorldInterface.\
    attempts) => fun (x_1 : @AcornVerif.Intent.WorldInterface.Agent.Memory (AcornVerif.Intent.W\
    orldInterface.World.Obs AcornVerif.Intent.WorldInterface.attempts) (AcornVerif.Intent.World\
    Interface.World.Act AcornVerif.Intent.WorldInterface.attempts) AcornVerif.Intent.WorldInter\
    face.echo) => fun (x_2 : Bool) => fun (m : @AcornVerif.Intent.WorldInterface.Agent.Memory (\
    AcornVerif.Intent.WorldInterface.World.Obs AcornVerif.Intent.WorldInterface.attempts) (Acor\
    nVerif.Intent.WorldInterface.World.Act AcornVerif.Intent.WorldInterface.attempts) AcornVeri\
    f.Intent.WorldInterface.echo) => m)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.neverStops\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.WorldInterface.System\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | have __src : AcornVerif.Intent.WorldInterface.System := AcornVerif.Intent.WorldInterface.\
    base; AcornVerif.Intent.WorldInterface.System.mk (AcornVerif.Intent.WorldInterface.System.S\
    tate __src) (AcornVerif.Intent.WorldInterface.System.Obs __src) (AcornVerif.Intent.WorldInt\
    erface.System.Act __src) (AcornVerif.Intent.WorldInterface.System.Memory __src) (AcornVerif\
    .Intent.WorldInterface.System.Input __src) (AcornVerif.Intent.WorldInterface.System.start _\
    _src) (AcornVerif.Intent.WorldInterface.System.observe __src) (AcornVerif.Intent.WorldInter\
    face.System.reward __src) (AcornVerif.Intent.WorldInterface.System.available __src) (AcornV\
    erif.Intent.WorldInterface.System.step __src) (AcornVerif.Intent.WorldInterface.System.init\
    ial __src) (AcornVerif.Intent.WorldInterface.System.act __src) (AcornVerif.Intent.WorldInte\
    rface.System.stopRequest __src) (fun (x : AcornVerif.Intent.WorldInterface.System.State __s\
    rc) => fun (x_1 : AcornVerif.Intent.WorldInterface.System.Memory __src) => fun (x_2 : Acorn\
    Verif.Intent.WorldInterface.System.Input __src) => Bool.true) (AcornVerif.Intent.WorldInter\
    face.System.given __src) (AcornVerif.Intent.WorldInterface.System.applied __src) (AcornVeri\
    f.Intent.WorldInterface.System.moved __src) (AcornVerif.Intent.WorldInterface.System.kept _\
    _src)\n\
    | ```\n\
    | \n\
    | ### AcornVerif.Intent.WorldInterface.base\n\
    | \n\
    | A definition. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.WorldInterface.System\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | AcornVerif.Intent.WorldInterface.couple AcornVerif.Intent.WorldInterface.mirror AcornVeri\
    f.Intent.WorldInterface.echo\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Meets\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => And (@LeanI\
    ntent.IntentRecord.Dom.{u} W r w) (@LeanIntent.IntentRecord.Props.{u} W r w)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameters\
    \x20are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its \
    recursor is the one Lean's kernel derives from this declaration. Its constructors, in order\
    , each with its type:\n\
    | \n\
    | #### LeanIntent.IntentRecord.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (shape : LeanIntent.Shape.{u} W), ∀ (dom : List.{u} (LeanIntent.Clause.\
    {u} W)), ∀ (props : List.{u} (LeanIntent.Clause.{u} W)), ∀ (vocab : List.{u + 1} LeanIntent\
    .Pred.{u}), LeanIntent.IntentRecord.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameters\
    \x20are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its \
    recursor is the one Lean's kernel derives from this declaration. Its constructors, in order\
    , each with its type:\n\
    | \n\
    | #### LeanIntent.Clause.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (holds : W → Prop), LeanIntent.Clause.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Pred\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameters\
    \x20are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | Type (u + 1)\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its \
    recursor is the one Lean's kernel derives from this declaration. Its constructors, in order\
    , each with its type:\n\
    | \n\
    | #### LeanIntent.Pred.mk\n\
    | \n\
    | ```lean\n\
    | ∀ (name : String), ∀ (Arg : Type u), ∀ (holds : Arg → Prop), LeanIntent.Pred.{u}\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Dom\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (d : Lean\
    Intent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInten\
    t.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.IntentRe\
    cord.dom.{u} W r) d → @LeanIntent.Clause.holds.{u} W d w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.dom\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argumen\
    ts and returns field number 2, counted after the parameters in the type of LeanIntent.Inten\
    tRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It has\
    \x20the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u}\
    \x20W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Clause.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argumen\
    ts and returns field number 2, counted after the parameters in the type of LeanIntent.Claus\
    e's constructor, of its argument number 2, a value of LeanIntent.Clause. It has the univers\
    e parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Clause.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.Props\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (r : LeanIntent.IntentRecord.{u} W), ∀ (w : W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (r : LeanIntent.IntentRecord.{u} W) => fun (w : W) => ∀ (p : Lean\
    Intent.Clause.{u} W), @Membership.mem.{u, u} (LeanIntent.Clause.{u} W) (List.{u} (LeanInten\
    t.Clause.{u} W)) (@List.instMembership.{u} (LeanIntent.Clause.{u} W)) (@LeanIntent.IntentRe\
    cord.props.{u} W r) p → @LeanIntent.Clause.holds.{u} W p w\n\
    | ```\n\
    | \n\
    | ### LeanIntent.IntentRecord.props\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argumen\
    ts and returns field number 3, counted after the parameters in the type of LeanIntent.Inten\
    tRecord's constructor, of its argument number 2, a value of LeanIntent.IntentRecord. It has\
    \x20the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.IntentRecord.{u} W), List.{u} (LeanIntent.Clause.{u}\
    \x20W)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.HoldsOf\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (c : LeanIntent.Consequence.{u} W), ∀ (r : LeanIntent.IntentRecord.{u} \
    W), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {W : Type u} => fun (c : LeanIntent.Consequence.{u} W) => fun (r : LeanIntent.IntentR\
    ecord.{u} W) => LeanIntent.Consequence.HoldsOf.match_1.{1} (fun (x : LeanIntent.Consequence\
    .Kind) => Prop) (@LeanIntent.Consequence.kind.{u} W c) (fun («_» : Unit) => ∀ (w : W), @Lea\
    nIntent.IntentRecord.Meets.{u} W r w → @LeanIntent.Consequence.holds.{u} W c w) (fun («_» :\
    \x20Unit) => @LeanIntent.HasInstance.{u + 1} W (fun (w : W) => And (@LeanIntent.IntentRecord.M\
    eets.{u} W r w) (@LeanIntent.Consequence.holds.{u} W c w)))\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence\n\
    | \n\
    | A structure: an inductive type with one constructor, whose arguments after its parameters\
    \x20are the structure's fields, in order. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (W : Type u), Type u\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 1 are parameters and the other 0 indices. Its \
    recursor is the one Lean's kernel derives from this declaration. Its constructors, in order\
    , each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.mk\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (name : String), ∀ (kind : LeanIntent.Consequence.Kind), ∀ (holds : W →\
    \x20Prop), LeanIntent.Consequence.{u} W\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind\n\
    | \n\
    | An inductive type. It has no universe parameter. Its type:\n\
    | \n\
    | ```lean\n\
    | Type\n\
    | ```\n\
    | \n\
    | Of the arguments its type takes, the first 0 are parameters and the other 0 indices. Its \
    recursor is the one Lean's kernel derives from this declaration. Its constructors, in order\
    , each with its type:\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.entailment\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | #### LeanIntent.Consequence.Kind.possibility\n\
    | \n\
    | ```lean\n\
    | LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.HoldsOf.match_1\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ (motive : LeanIntent.Consequence.Kind → Sort u_1), ∀ (x : LeanIntent.Consequence.Kind),\
    \x20∀ (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment), ∀ (h_2 : ∀ («_» :\
    \x20Unit), motive LeanIntent.Consequence.Kind.possibility), motive x\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun (motive : LeanIntent.Consequence.Kind → Sort u_1) => fun (x : LeanIntent.Consequence.\
    Kind) => fun (h_1 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.entailment) => fun (\
    h_2 : ∀ («_» : Unit), motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Conseq\
    uence.Kind.casesOn.{u_1} (fun (x_1 : LeanIntent.Consequence.Kind) => motive x_1) x (h_1 Uni\
    t.unit) (h_2 Unit.unit)\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.Kind.casesOn\n\
    | \n\
    | A definition. It has the universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u}, ∀ (t : LeanIntent.Consequence.K\
    ind), ∀ (entailment : motive LeanIntent.Consequence.Kind.entailment), ∀ (possibility : moti\
    ve LeanIntent.Consequence.Kind.possibility), motive t\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {motive : ∀ (t : LeanIntent.Consequence.Kind), Sort u} => fun (t : LeanIntent.Consequ\
    ence.Kind) => fun (entailment : motive LeanIntent.Consequence.Kind.entailment) => fun (poss\
    ibility : motive LeanIntent.Consequence.Kind.possibility) => @LeanIntent.Consequence.Kind.r\
    ec.{u} motive entailment possibility t\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.kind\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argumen\
    ts and returns field number 2, counted after the parameters in the type of LeanIntent.Conse\
    quence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It has t\
    he universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), LeanIntent.Consequence.Kind\n\
    | ```\n\
    | \n\
    | ### LeanIntent.Consequence.holds\n\
    | \n\
    | A function that reads a field of a structure: its value is `fun` over its first 2 argumen\
    ts and returns field number 3, counted after the parameters in the type of LeanIntent.Conse\
    quence's constructor, of its argument number 2, a value of LeanIntent.Consequence. It has t\
    he universe parameter u. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {W : Type u}, ∀ (self : LeanIntent.Consequence.{u} W), W → Prop\n\
    | ```\n\
    | \n\
    | ### LeanIntent.HasInstance\n\
    | \n\
    | A definition. It has the universe parameter u_1. Its type:\n\
    | \n\
    | ```lean\n\
    | ∀ {α : Sort u_1}, ∀ (P : α → Prop), Prop\n\
    | ```\n\
    | \n\
    | Its value:\n\
    | \n\
    | ```lean\n\
    | fun {α : Sort u_1} => fun (P : α → Prop) => @Exists.{u_1} α (fun (a : α) => P a)\n\
    | ```\n\
    | \n\
    | ## Lean's own libraries\n\
    | \n\
    | The declarations of Lean's own libraries (Init, Std, Lean and Lake) are not printed: they\
    \x20are those of Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, which made this\
    \x20text. A declaration is counted as Lean's own when Lean found the module that declares it i\
    n that release's library directory.\n\
    | \n\
    consequence the record's plain restatement\n\
    shown as entailment\n\
    predicate 1\n\
    | the record, as its revision prints it\n\
    verdict confirmed\n\
    "]⟩

end AcornVerif.Intent.Decisions
