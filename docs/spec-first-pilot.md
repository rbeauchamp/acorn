# Spec-first pilot report

This report answers [#177](https://github.com/rbeauchamp/acorn/issues/177): a pilot of the spec-first method on three Acorn functions, `World.dayPhase` and the hash functions `Rng.hash2` and `Rng.hash3`, before the method is applied across Acorn ([#178](https://github.com/rbeauchamp/acorn/issues/178)).
Whether to apply it across Acorn is the owner's decision on this report.

The method, carried by the owner's spec-first skill and the [lean-intent](https://github.com/rbeauchamp/lean-intent) library (pinned at commit 30fe70d), turns an owner's words into an *intent record*, a Lean structure of named properties of a subject, before any code; proves the record adequate (lean-intent's obligations O1 to O5: well formed, satisfiable, each property refutable, a step that does nothing refused, and any freedom between models made explicit); compares it with a second model's blind formalization of the same words; settles its consequences; and then proves the code against it.

## What the pilot found first: where the owner's intent lives

Asked in plain words what `World.dayPhase` is for, the owner did not know: an agent had added it, and the owner could only guess that it was meant to give the world days and nights.
The owner held no intent of their own for any of the three functions.
For each, the assistant supervising the work read the code and the issue that fixed it, explained it, and proposed a statement of what the *world* should do, which the owner adopted:

- day and night: "each day has a daytime half and a night half of equal length; at night every action costs more energy; the agent can always see where in the day it is";
- the hashes: "Different things the agent senses, different places, and different goals should land in the same spot only about as rarely as pure chance, never systematically. The same inputs always give the same result, so a run can be replayed."

So each statement came from someone who had read the code, which weakens the method's premise that the record is written before the code is seen: the records themselves were written before their functions' source was read (only the functions' types, from Lean's environment), but their source statement was not.

Shown the first function's seven plain-word consequences as questions, the owner did not answer them: they were finer than the owner wants to specify.
The owner then decided how the method divides the work (2026-10-29): an owner works at the level of intent, and that level is not fixed; below it, each detail of a specification is a design decision the agents make and record, with its reason tied to the owner's intent, marked as decided on the owner's behalf and never presented as the owner's; the owner's attention goes only to confirming a plain restatement of their intent, to real forks the intent does not settle that change what they get, and to one-way doors and quality-for-cost trades.
The owner likened the division to an interface and its implementation: their intent is a system's contract (what its inputs must satisfy, what its outcomes and mission results must be, and what stays invariant), and specifications of internal functions are implementation details the agents own and may change.

The records for `World.dayPhase` and the hashes are therefore the agents' own design, decided on the owner's behalf, not owner intent.
What reached the owner, per function:

| Function | Owner's statement reached by | Consequences derived | Decided on the owner's behalf | Reached the owner, and why | Owner's time |
|---|---|---|---|---|---|
| `World.dayPhase` | adopting a proposed world-level statement | 7 | all 7 | none; the owner answered the method question instead | see below |
| `Rng.hash2`, `Rng.hash3` | adopting a proposed world-level statement | 6 | 5 | one: whether to require a collision-rate bound, a quality-for-cost trade; the owner accepted it as not covered | see below |

The owner's time is an estimate by the assistant supervising the work, from the conversation, which the owner confirmed as about right, not the owner's own measurement: about 10 minutes answering the three function-level questions (12:05 to 12:40 UTC on 2026-10-29, mostly waiting between messages), and about 15 minutes on the discussion of the method that replaced per-consequence confirmation, which settled both functions and the collision-rate question together.

## Recommendation: which Acorn contracts owner-level records should describe

Acorn's purpose, from its README, is agents that learn from experience to achieve goals in big worlds, learning one observation at a time from one continuous stream, with the algorithms developed and verified in Lean.
Owner-level intent records belong at the contracts that purpose names, where the owner holds intent and an implementation can change beneath them:

1. **The agent's interface with a world.** What the agent receives each step (an observation, and a reward or task signal) and what it returns (an action), with no other channel: the agent cannot read a world's internals, and a host or the viewer cannot alter its learning decisions. This is the contract every world, the tile world, ARC-AGI-3 games and Microduck alike, must meet, and the one the owner's chosen worlds exercise.
2. **What a big world must satisfy.** The class of worlds the agent must handle, stated by properties rather than by one world (the work of #69, with ARC-AGI-3 in #71 and Microduck in #173): for example that a world's state is larger than any bounded agent can represent, that it keeps changing, and that goals are reachable but not given.
3. **The invariants of learning from one stream of experience.** Each step does bounded work and holds bounded memory; nothing is replayed, reset or trained offline; every learned quantity changes only through the stream; and a stopped and resumed run continues exactly as the uninterrupted run would (the checkpoint contract).

These three are the system's preconditions, postconditions and invariants in the owner's sense.
Day and night, terrain noise and feature hashing sit below them: the agents choose them to meet these contracts, and their records, like the two here, are the agents' design.

## The records and their adequacy

| Record | Subject | Obligations proved | Degenerate check |
|---|---|---|---|
| `AcornVerif.Intent.DayCycle.dayCycle` | `DayWorld`: day length, night, energy cost and sight, generic in the world's types | O2 (`dayCycle_o2`), O2 before running (`dayCycle_o2Run`), O3 (`dayCycle_o3`), O4 (`dayCycle_o4`), O5 widest and not with equality (`dayCycle_o5_widest`, `dayCycle_not_o5_eq`) | not covered: the subject is a structure of functions, a higher-order subject lean-intent's check does not cover yet |
| `AcornVerif.Intent.Hash.hashes` | `Hashes`: the pair of functions on three 64-bit words | O2 (`hashes_o2`), O3 (`hashes_o3`), O4 (`hashes_o4`), O5 widest (`hashes_o5_widest`) | not covered: a structure of functions on 64-bit words, neither of which the check covers |

O1 holds of every record by construction.
The hash record's O2 before running, a pair of functions meeting the whole record, is not proved: see the hash results below.
lean-intent's cone check, run on each record against its implementation's declarations, accepted both: the day record's meaning reaches none of `World.dayPhase`, `Action.energyCost` and `World.observe`, and the hash record's none of `Rng.hash2`, `Rng.hash3` and `Rng.mix64` (observed, lean-intent at 30fe70d on Lean v4.35.0).

## The decisions made on the owner's behalf

Each decision is recorded twice in `AcornVerif.Intent.Decisions`: as an answer of lean-intent's owners' log given by the principal named agents under the owner's delegation, so the log itself says the owner did not give it, and as a typed answer that the record's current revision keeps (`dayCycle_keeps`, `hashes_keeps`).
lean-intent's authority trace, run on that log, accepts all eleven answers as given under a delegation that traces back to the owner (observed by evaluation, not proved here).
Where the blind second reading differed, the decision names the divergence and how the owner's statement settles it, and keeps Acorn's existing behaviour unless the statement requires otherwise.

### Day and night

1. Every day lasts the same even number of ticks, the night one unbroken half, every day alike (`everyDayAlike`). The blind reading let days differ in length; the statement speaks of "each day" without asking for varying days, and Acorn's day has one length per configuration, so the record keeps one length.
2. Every action, waiting included, costs more at any night moment than at any daytime moment, in the same situation (`nightAlwaysDearer`): "at night every action costs more energy", read literally.
3. What the agent sees always tells day from night (`tellsDayFromNightAlways`).
4. The day's length stays open (`longDay`): the statement sets none.
5. "Where in the day it is" is read as at least the quarter of the day (`seesQuarterOfDay`), and an agent that sees only day or night is ruled out (`dayOrNightOnlyWorld`, declined). The blind reading required the exact tick. The words ask for more than day or night but not for the exact tick, and Acorn's agent sees which eighth of the day it is in, which meets the quarter reading; requiring the exact tick would change what the agent observes without the statement asking for it.
6. The night's extra cost may change during the night (`nightCostVaries`). The blind reading priced every night moment alike; the statement compares night with day only.
7. Time is counted in whole ticks with one clock for the whole world (the record's shape): Acorn's world steps one tick at a time on one clock.

### The hashes

1. Changing any one input always moves the spot (`oneChangeMoves`), never merely rarely. The blind reading allowed a single changed input to collide at the chance rate; never is within "only about as rarely as pure chance", rules out a function that sends almost everything to one spot, and Acorn's functions already meet it.
2. "Never systematically" means no fixed rule of reordering the inputs and shifting them by fixed amounts, by exclusive or or by addition, keeps every spot (`noFixedRule`). The blind reading left the patterns that count open; these are the patterns a combination of words by exclusive or, addition and reordering can obey, and #155's collisions were of this kind.
3. Neither function combines its inputs by plain exclusive or or plain addition (`rulesOutPlainCombinations`), which follows from 2.
4. The record does not ask that the two functions never share spots. The blind reading left it open; in Acorn `Rng.hash2` feeds the terrain and the curriculum's draws and `Rng.hash3` feature slots, samples, context codes and goal cues, so no input of one competes for a spot with an input of the other.
5. The owner's own decision: no collision-rate bound is required. "Only about as rarely as pure chance" is a rate over 2^192 inputs that cannot be proved of real code at an affordable cost now, and decisions 1 to 3 close the systematic collisions #155 was; recorded as not covered, accepted risk.
6. The same inputs always give the same spot (`replay`): true of every Lean function by construction, with replay further trusting the compiler and machine to compute 64-bit words alike everywhere.

## The second, blind formalization

Each statement was formalized a second time by OpenAI's gpt-6-astra through the Codex command line (codex-cli 0.165.0), in a fresh, ephemeral, read-only session with memories and hooks off and stdin closed, given only the owner's words, the subject's types and lean-intent's record module.
Codex's own event log shows each session read only those three files and made no web request; both formalizations elaborated against lean-intent unchanged.
These options do not switch off Codex's global instruction file, the owner's general engineering guidance, which carries no part of either record.
The differences, and how each was settled, are in the decisions above.

## The code against the records

- **Day and night.** `AcornVerif.Intent.DayCycleWorld` reads Acorn's world as the record's subject and ties that reading to the executing code: `payAndAct_spends` (the step spends the subject's cost) and `observe_day` (a successful observation reports the subject's sight). `acornDay_fulfils` proves, through lean-intent's refinement link, that `World.dayPhase` fulfils the record for every day of `8 * m` ticks dividing 2^64, and `standard_fulfils` for the standard 2048-tick day. Outside it: an odd day length, which `WorldConfig.admit` accepts and the record rules out because its halves cannot be equal (`acornDay_odd_unfulfilled`); a length that does not divide 2^64, for which the 64-bit clock's wrap after 2^64 ticks breaks one day; and lengths of 2, 4 and 6 ticks, which the proof does not cover. No executing entry point builds a custom day length; these lengths are accepted risk, and #185 is to make admission refuse the lengths the record rules out.
- **The hashes.** `AcornVerif.Intent.HashImplementation` proves the first property of both functions (`acornHashes_oneInputMoves`) from `mix64` being a bijection, and that no reordering alone keeps every spot (`acornHashes_reorder`). The second property is not proved for rules that shift two or more inputs: for those it comes down to `mix64` having no fixed difference in any of 2^64 directions, a statement about SplitMix64's finalizer that no proof here establishes and for which no affordable route is known. It is expected to hold, since the finalizer is a nonlinear bijection. Leaving it open was decided on the owner's behalf for its cost, as the owner had accepted the collision-rate bound as not covered for the same reason; #184 is to prove it. Until then the hash record's O2 before running is unproved too.

## Would the records have refused the defects of #154 and #155?

Yes, as theorems in `AcornVerif.Intent.BeforeFixes`:

- `dayPhaseBefore_unfulfilled`: `World.dayPhase` as it was before #159 makes 12 of the 20 ticks of a 20-tick day night, and the day record refuses it for every world of that configuration, which `WorldConfig.admit` accepts (`twentyTickDay_admitted`).
- `hashes_refuses_before` and `hash2Before_keeps`: `Rng.hash3` and `Rng.hash2` as they were before #161 keep every spot when the same bits of two inputs are flipped, and the hash record refuses them.

## What to change before applying the method across Acorn

In the skill:

1. Ask for intent at the level the owner holds it: a system's contract, not an internal function. For an agent-invented function, start one level up, and say whose words the record's source is when the owner adopts a proposal written by someone who read the code.
2. Make "decided on the owner's behalf" a first-class outcome of step 4, with the reason tied to the owner's intent, and send the owner only a restatement of their intent, unsettled forks that change what they get, and one-way doors or quality-for-cost trades. A list of per-consequence questions cost the owner more attention than it was worth.
3. In the blind formalization, close the command's input (Codex otherwise waits on stdin), turn off memories and hooks, run read-only and ephemeral, and say that the interface's global instruction file still loads.

In lean-intent:

1. The renderer prints every statement fully elaborated (explicit universes, instances and `@` applications): the day record renders as 625 lines no owner would read. A printer that keeps the round-trip guarantee while printing with notation and without implicit arguments would make the rendering usable.
2. No shape fits a subject that is a description made of functions with no state (a world's day rules, a pair of hash functions): `.value` asks nothing of O4. Either a shape for such bundles or guidance that `.value` is right for them.
3. The degenerate check covers neither subject here (higher-order, 64-bit words); #11 tracks it.
4. Records generic in a world's types need witness hypotheses for O2, O3 and every possibility; a way to render a generic record at representative types without changing what it says would help.
5. The owners' log answers carry the record's revision and the predicate as text that nothing ties to the Lean terms; #5 tracks it.
6. Properties over all 64-bit inputs of a mixing function, such as "no fixed rule keeps every spot", have no affordable proof route in a project that forbids evaluation by native code, which leaves O2 before running unproved for such records. A recipe for constructing a model, or a documented acceptance of an argued model, would close the gap.
