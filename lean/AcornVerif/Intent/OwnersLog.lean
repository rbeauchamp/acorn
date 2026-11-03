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
  process that imports the modules `intent-check` reads, so that its texts are the checker's.

No statement is the owner's but the declaration and the delegation; every answer names the agents,
acting under the delegation, as its author. The decisions and their reasons are described in
`AcornVerif.Intent.Decisions` and the pilot report, `docs/spec-first-pilot.md`.
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
    "]⟩

end AcornVerif.Intent.Decisions
