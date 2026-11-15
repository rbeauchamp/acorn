# Roadmap

This page says what Acorn works on now, in what order, and why.
GitHub's issues are the record of each piece of work; this page is the order between them.
It was last set on 2026-11-14, and a change to the order changes this page in the same pull request.

## Terms

- The *mission theorem* is the theorem the [mission contract](mission-contract.md) asks for: that Acorn's agent, as running Lean code, achieves goals over a formally stated class of big worlds. It is one theorem for each class.
- A *rung* is one such class of worlds, with its theorem. The classes form a ladder, from the first and smallest toward "any big world". Each rung has one tracking issue, labelled rung.
- An *obligation* is a numbered item of the mission contract's [open obligations](mission-contract.md#open-obligations): a statement not yet precise, a theorem not yet proved or a choice not yet made.
- A *lane* is a kind of work. On a rung there are three: *state* (write a contract, a theorem or a premise exactly, in Lean), *discover* (find the algorithm for which the rung's theorem is true) and *prove* (prove a stated obligation of the executing code). Four more group the rest: *world*, *theory*, *community* and *upkeep*.
- A *parked* issue is not on the active rung. It stays open, and its last roadmap comment says when it re-enters.
- A *mission*, as a unit of work, is an issue with a frozen contract that outside contributors and their agents can land ([missions](missions.md)).

## Where the mission stands

No theorem in the tree yet says that Acorn's executed agent learns.
On the first rung, whose world, visit length and agent are fixed, `rung_mission` proves the mission theorem's statement from six premises about the executed agent. Two are proved: the one on memory, for the agent with its whole state as its memory (`rung_memory_bounded`), and the one on finding, that the agent solves each of more members than the covering bound on some visit (`rung_finds`). Finding is a result about how the agent explores before any reward, not about what it learns from one. No theorem proves the other four, retention among them, and which memory the statement reads is the owner's decision ([#249](https://github.com/rbeauchamp/acorn/issues/249)). What remains is those premises, a proof that the agent's reports to contract 3 describe its step, a statement for an agent that explores with random draws, and the link from the rung's run to the native entry.

- **Proved.** The kernel's model of worlds and agents. That no agent achieves goals in every world, and that on a class which conceals its goals every agent solves at most a covering bound of members on a first visit. One class of worlds that meets the mission contract's conditions (a) to (c) for a big class (`witness_big`). That every agent which keeps nothing of its experience solves at most a covering bound of members on every visit (`visits_need`). That a reference agent which replays a route it has found separates from those agents and retains what it solved, under its own hypotheses (`witness_separation`, `replay_keeps`). That the host's loop of visits is the kernel's (`executed_visits_closed_loop`). Exact resumption from a checkpoint, and that no host write reaches learning.
- **Proved of the mission theorem's statement.** The statement is one proposition over the four intent records (`Mission`), and on a class of worlds in visits it follows from named premises about the class and the agent (`visits_mission`). On the first rung's class every premise about the class holds, the reward lemma included (`find_mission`, `classReward_eq`). A reference agent of fixed memory meets the whole statement there, with every premise discharged (`witness_mission`).
- **Proved of the first rung's constants.** The rung's world is the standard configuration at seed 1 and side 64 with no deer and no food (`witness_standard`), started at the box's center (`witness_start`); a visit is seven steps; the agent is the cold agent the host constructs for the primitive research profile (`rungConstruction`). The class is big there (`witness_big`), with at least 147 members (`witness_mission`) and at most 392 (`rung_members`) against a covering bound of 98. Every frame of the rung's agent holds at most 1712 slots, so the credit horizon holds of it with no hypothesis on frames (`rung_frames`, `rung_weight_rests`), and on the controller's cold run a slot laid at most seven steps before a first reward has a weight the reward moves (`rung_reach`).
- **Proved of the executed agent's exploration.** Before a first reward, the agent of a profile with no hierarchy under the declared exploration rate, which the primitive research profile is, takes the actions of an *explorer*: a machine whose whole state is the exploratory run it has committed to and the action generator, and which reads no percept (`cold_actions`, `Explorer.step_eq`). On a class that conceals its goals, an agent solves a member on some visit exactly when its run in the reference, where no goal is met, meets that member's goal on some visit (`Conceals.found_iff`). So whether the rung's agent finds is a property of one action sequence (`rung_finds_iff`), and Lean's kernel evaluates enough of it: the agent solves each of 99 members on one of its first 72 visits, against the covering bound of 98 (`rung_finds`).
- **Proved of the executed agent's controller.** Its control weights stay zero until its first reward (`pre_reward_weights_zero`). What a bias on a few slots then does to the greedy choice (`candidates_of_gap`, `candidates_of_resting`), and how far back a first reward reaches (`creditReach`).
- **Observed.** Two registered studies on the standard curriculum, each refuted at its horizon ([baseline assessment](baseline-assessment.md#conformance-sequence), U6 and U7). They describe the code before a later change to the hashes, and neither ran on the first rung's class.
- **Open.** The mission theorem, on every rung.

## The owner's direction

On 2026-11-05 the owner directed that all effort goes to Acorn's mission, with supporting work only for bugs, problems of velocity and issues already planned.
Under the mission contract, Acorn's results are theorems about running code; a run of the agent is a smoke test and never evidence.
The order below follows both: one rung is active, and work that no active rung needs is parked.

## The active rung: concealed targets in visits

The first rung is the class of concealed targets of one grid world, run in visits ([#230](https://github.com/rbeauchamp/acorn/issues/230)).
A *concealed target* is a goal whose location the agent's observation does not show until the agent reaches it.
A *visit* is one attempt of a fixed length, after which the world returns to its start and the agent keeps its memory.
The rung's theorem says that the executed agent solves more members of the class on one common visit than any agent that keeps nothing of its experience can on any visit, that it keeps solving what it has solved, and that it does both within fixed work and memory while learning from each experience once.

The replaying reference agent already separates and retains on this class, under its own hypotheses (`witness_separation`, `replay_keeps`), and a reference agent of fixed memory that remembers which of its exploring walks met the goal meets the rung's whole statement (`witness_mission`).
So the statement alone does not tell a continual learner from an agent built to memorise a route in this world.
The rung's value is that Acorn's general agent, with nothing specific to this world, meets it within the contract's invariants.
The first rung on which no agent can keep every solution is capacity, condition (d) of the mission contract.

### The rung's constants

The owner decided on 2026-11-14 that the first rung's world is the host's standard configuration at seed 1 and side 64 with no deer and no food, started at the box's center, with visits of seven steps and the primitive research profile (`rung_mission`).
The same class in the host's own world, deer included, is a later rung ([#256](https://github.com/rbeauchamp/acorn/issues/256)).

- **Why this world and visit length.** They are the one world and visit length at which a class is proved big (`witness_big`), in the one kind of world whose frames are proved within the sizes the credit horizon assumes (`rung_frames`). No theorem says a shorter visit fails.
- **Why seed 1.** It is the least seed at which the host's own world started at the box's center: Lean's interpreter evaluated the host's generation at side 64 to a start at the tile (27, 27) for seed 0 and at the center, (32, 32), for seed 1 (observed on 2026-11-14; not proved). So the rung's world has the start and the terrain of the world that `acorn-core visits` builds at seed 1 and side 64, and differs from it by that world's eight deer.
- **What a run of the entry would show.** In the same evaluation at seed 1, over seven steps with the body waiting, no food appeared, one deer stayed nine tiles from the start and the other seven at least 18 tiles from it, and walks of seven steps were open in all four directions (observed on 2026-11-14). A frame's window reaches five tiles, so that deer is in view only from tiles within five of it, which a walk reaches after at least four steps toward it, and no deer reads the body's action (*argued*). A run of the entry at that seed and side with seven steps is then a smoke test of a member, and differs from the member's run only where that deer is in view. No theorem relates the two worlds, and such a run needs the owner's authorization as any other does ([#232](https://github.com/rbeauchamp/acorn/issues/232)).
- **What was weighed.** A visit at the proved reach of a first reward, 81 steps, has a covering bound of 616, so its class needs the terrain of at least 89 tiles proved (*argued*: a step brings at most seven more targets within reach), against the 21 the witness reads. The host's own world needs three things proved first: that its spawn search ends at the box's center, a bound on the frames of a visit in a world with deer, of which only the interface's bound of 3648 slots is proved, and the walks in that world. The spawn search evaluates the terrain 163 times for each candidate it considers (`considerSpawn`). Lean's kernel took 0.66 seconds to classify the terrain of the tile (33, 32) of the rung's world, and 5.3 seconds, 0.75 seconds a step, to check the witness's walk of seven steps east (observed on 2026-11-14 in the cloud container of the session that fixed the constants, with Lean 4.35.0, as the profiler's type-checking time of a proof that the kernel decides). A proof pays the kernel's time for each tile it reads, each time its module is rebuilt.
- **What the agent's profile leaves out.** The primitive profile is one the host neither saves nor loads, so exact resumption says nothing of the rung's agent.

### What the rung's agent finds

The owner decided on 2026-11-15 that the rung's premise on finding is certified by Lean's kernel, at the cost recorded here (`rung_finds`).

- **What is proved.** The rung's agent solves each of 99 listed members on one of its first 72 visits: each lies within three tiles of the body's walk on visit 23, 45, 47 or 71, counted from zero (`rungWalks`, `rungFound`). It is proved of the agent's one run, with no assumption on the generator's words. Before a first reward the agent's actions are the explorer's (`cold_actions`), no reward is paid in the reference (`reference_unpaid`), and a member is solved by a visit exactly when the run in the reference has met it by that visit (`cold_found_within`).
- **What was observed first.** Lean's interpreter evaluated the explorer of seed 1 over the grid's nine actions, and the executed world step from the rung's world along its walks. The walks of the first 54 visits met 99 members, the first count above 98, and those of the first 400 visits met 155 (observed on 2026-11-15 in the cloud container of the session that proved the reduction, with Lean 4.35.0; about four seconds; not proved). No agent ran and no learner was updated: the evaluation read the generator, the draw of a policy whose values are all zero, and the world.
- **Why these four visits.** They are not the first at which the count passes the bound. A search over that evaluation chose them because they need few evaluated steps: 19 moves, where the cheapest choice it found among the first 54 visits needed 38 (observed, by a script outside the tree).
- **What the proof costs.** Lean's kernel took 5.3 seconds to evaluate the explorer's first 576 decisions (`rung_actions`) and 18.8 seconds to evaluate the world step along the four walks (`walks_traced`); the module took 27 seconds to build (observed on 2026-11-15 in the same container, as the profiler's type-checking time and the build's report). The kernel pays that time each time the module is rebuilt.
- **What it leaves open.** What the agent does after a first reward, which questions 2 to 4 of [#232](https://github.com/rbeauchamp/acorn/issues/232) ask. Under another seed, in another world or under a profile with a hierarchy, the explorer or its walks differ, and nothing is proved of them.

### What the rung needs

| Obligation | Needed | Issue |
|---|---|---|
| 9, separation and retention for the executed agent | Yes: it is the theorem. Stated as the premises `ExecutedFinds` and `ExecutedRetains`. `ExecutedFinds` is proved (`rung_finds`). Retention on every later visit conflicts with the agent's constant exploration rate (argued) | [#230](https://github.com/rbeauchamp/acorn/issues/230); [#248](https://github.com/rbeauchamp/acorn/issues/248) decides how retention is asked |
| 4, goal-information and exploration premises | Yes. The goal information is proved (`reward_step`). Finding needed no premise about the class: the agent's actions before a first reward are a function of its seed (`cold_actions`), and the kernel evaluates their walks in the rung's world (`rung_finds`). No premise that suffices for retention is known | [#232](https://github.com/rbeauchamp/acorn/issues/232) decides them |
| 15, the failing fraction of runs | Yes, for retention. Its counting part is stated (`AllBut`, `visits_mission_allBut`). The rung's agent has one seed, so its finding is proved of its one run, by a stated visit and with no fraction (`rung_finds`). The agent's draws are modelled before a first reward only (`Explorer`); a model after it, a number of visits for retaining, and the fraction itself are open | [#231](https://github.com/rbeauchamp/acorn/issues/231) for the count, [#248](https://github.com/rbeauchamp/acorn/issues/248) and [#232](https://github.com/rbeauchamp/acorn/issues/232) for the rest |
| 16, the class's reward lemma | Discharged for this class (`classReward_eq`), with an attempt's rewards counted up to its first payment, which the owner can overrule | [#231](https://github.com/rbeauchamp/acorn/issues/231) |
| 6, a bound on reachable memory | Proved for the executed agent with its whole state as its memory: the states a host runs are finitely many under every profile (`running_memory_bits`), each step of a run keeps the agent among them (`step_running`), and the premise `MemoryBounded` holds on the rung (`rung_memory_bounded`). It holds as well of a memory that is one function of the state which the agent's step keeps (`projected_memory_bounded`) | [#249](https://github.com/rbeauchamp/acorn/issues/249) decides which memory the premise reads |
| 7, executed work, and learning from each experience once | Yes: the premises `WorkBounded` and `LearnsOnArrival` | [#90](https://github.com/rbeauchamp/acorn/issues/90) for work, [#233](https://github.com/rbeauchamp/acorn/issues/233) for once-only learning |
| 3, the viewer's rule as a theorem | Completes contract 1 beside the rung | [#213](https://github.com/rbeauchamp/acorn/issues/213), step 5 |
| 2, 5, 10, 11, 13, 14 | No: the rung runs in visits and does not use the campaign join | |
| 12, a guarantee counted over the generator's seeds | No: it stays a named assumption | [#184](https://github.com/rbeauchamp/acorn/issues/184), parked |

### Order of work

1. **State.**
   - The intent record of the postcondition, steps 1 to 4 ([#219](https://github.com/rbeauchamp/acorn/issues/219)).
   - The intent record of contract 2, steps 1 to 4 ([#214](https://github.com/rbeauchamp/acorn/issues/214)).
   - The rung's theorem in Lean ([#231](https://github.com/rbeauchamp/acorn/issues/231)). In the tree: its definitions, a proof that a reference agent meets it (`witness_mission`), a proof of it for the executed agent from named open premises (`executed_mission`), so the way the theorem depends on its obligations is checked by Lean's kernel, and the rung's constants (`rung_mission`), with the theorems its world and visit length rest on. Remaining: the decisions listed below, and the blind second reading of the statement.
2. **Discover.** Decide the rung for the primitive research profile, by theorem ([#232](https://github.com/rbeauchamp/acorn/issues/232)): does its exploration find enough members, does credit reach the start of the next visit, does the first reward collapse exploration, and does shared weight send the agent off its route. The first is decided: the rung's agent finds (`rung_finds`). The other three are open. Two algorithm changes are scoped and open on those answers: exploring without reward and after the first reward ([#170](https://github.com/rbeauchamp/acorn/issues/170)), and a one-step model that carries a success back ([#171](https://github.com/rbeauchamp/acorn/issues/171)).
3. **Prove.** The invariants, stated over constructions so that an algorithm change does not reopen them: reachable memory (proved for worlds of the grid, `visits_memory_bounded`), work ([#90](https://github.com/rbeauchamp/acorn/issues/90)), once-only learning ([#233](https://github.com/rbeauchamp/acorn/issues/233)), and the executing code against the records of contracts 1 and 3 ([#213](https://github.com/rbeauchamp/acorn/issues/213), [#215](https://github.com/rbeauchamp/acorn/issues/215)).
4. **Assemble.** The rung's theorem for the primitive profile, then for the ranked profile ([#230](https://github.com/rbeauchamp/acorn/issues/230)).

Stating comes first because it is the cheapest step and it decides which of the others are needed.
Discovery decides whether the theorem is true; the proofs of step 3 assume it.

## The rungs after the first

Their order is the owner's decision and is not yet made ([#234](https://github.com/rbeauchamp/acorn/issues/234)).
The nearest class to the first rung's is the same class in the host's own world at seed 1 and side 64, deer included, which the entry `acorn-core visits` builds ([#256](https://github.com/rbeauchamp/acorn/issues/256)); [the rung's constants](#the-rungs-constants) list what it needs proved first.
The recommendation recorded there is: capacity on an agent of restricted capacity, then a class of ARC-AGI-3 games ([#71](https://github.com/rbeauchamp/acorn/issues/71)), then a class of Microduck scenes ([#236](https://github.com/rbeauchamp/acorn/issues/236)), then a class of worlds with no restarts.

## Parked work, and when it re-enters

| Issues | Re-enters when |
|---|---|
| [#256](https://github.com/rbeauchamp/acorn/issues/256), the first rung's class in the host's own world | The first rung is decided for the primitive profile ([#232](https://github.com/rbeauchamp/acorn/issues/232)), or a diagnostic run for it needs a world the entry runs exactly |
| [#71](https://github.com/rbeauchamp/acorn/issues/71), ARC-AGI-3 games as a class | The order of the later rungs is decided and the first rung has landed |
| [#236](https://github.com/rbeauchamp/acorn/issues/236), Microduck scenes, with [#173](https://github.com/rbeauchamp/acorn/issues/173), [#136](https://github.com/rbeauchamp/acorn/issues/136), [#172](https://github.com/rbeauchamp/acorn/issues/172), [#121](https://github.com/rbeauchamp/acorn/issues/121) and [#175](https://github.com/rbeauchamp/acorn/issues/175) | The same |
| [#17](https://github.com/rbeauchamp/acorn/issues/17), learned agent state | Step 2 finds interference to be the obstruction, or a rung's class needs memory |
| [#13](https://github.com/rbeauchamp/acorn/issues/13) and [#14](https://github.com/rbeauchamp/acorn/issues/14), reward centering and the average-reward update | Step 2 finds that the first reward collapses exploration and centering bears on it, or at a rung with no restarts |
| [#15](https://github.com/rbeauchamp/acorn/issues/15), search control | The one-step model of [#171](https://github.com/rbeauchamp/acorn/issues/171) exists, or the option models' ranking after [#48](https://github.com/rbeauchamp/acorn/issues/48) |
| [#138](https://github.com/rbeauchamp/acorn/issues/138), the spectrum of a one-step model | The one-step model of [#171](https://github.com/rbeauchamp/acorn/issues/171) exists |
| [#48](https://github.com/rbeauchamp/acorn/issues/48) and [#47](https://github.com/rbeauchamp/acorn/issues/47), the option models' residual | The first rung is carried to the ranked profile |
| [#18](https://github.com/rbeauchamp/acorn/issues/18), utility feedback | The capacity rung is placed |
| [#19](https://github.com/rbeauchamp/acorn/issues/19), nonlinear learners | The owner places it, after learned agent state |
| [#137](https://github.com/rbeauchamp/acorn/issues/137), actor-critic control | A rung's class has a best memoryless policy that is strictly stochastic |
| [#184](https://github.com/rbeauchamp/acorn/issues/184), the hash property behind obligation 12 | A mission theorem needs that obligation discharged |

## Decisions that wait on the owner

Each is an issue labelled `needs-owner-decision`, with a recommendation in its text.

- The order of the rungs after the first, and the agent configuration condition (d) is first proved for ([#234](https://github.com/rbeauchamp/acorn/issues/234)).
- Whether open statements live in the governed tree or in a separate library ([#238](https://github.com/rbeauchamp/acorn/issues/238)).
- A standing, bounded budget for diagnostic runs of `acorn-core visits` in step 2, as smoke tests and never as evidence ([#232](https://github.com/rbeauchamp/acorn/issues/232)). Such a run is of the host's own world, with its deer and food, started at its spawn; [the rung's constants](#the-rungs-constants) say how that world relates to the first rung's at seed 1.
- What the feature generator reads in a world with no symbol array ([#175](https://github.com/rbeauchamp/acorn/issues/175)).
- Whether a mission may change a file of the trusted base ([#132](https://github.com/rbeauchamp/acorn/issues/132)).
- How retention is asked of an agent that keeps exploring: up to a number of visits, or exploration that ends once a member is solved ([#248](https://github.com/rbeauchamp/acorn/issues/248)).
- Which memory of the executed agent contract 3 reads: its whole state, or what its decisions read ([#249](https://github.com/rbeauchamp/acorn/issues/249)).
- Whether the clauses of contract 3's record that no obligation states get a number in the mission contract ([#250](https://github.com/rbeauchamp/acorn/issues/250)).
- The proposals for outside contributors, below.

Stating the first rung's theorem ([#231](https://github.com/rbeauchamp/acorn/issues/231)) also made four choices on the owner's behalf, which the owner can overrule:

- An attempt's reward is counted up to its first payment (`untilPaid`), because the plain sum of a visit's rewards counts every step at which the goal stays met (`rewards_sum`).
- The open premises of the rung's theorem are hypotheses of theorems in the governed tree.
- Contract 3's bounds on memory and work are asked once for the whole class, where the record asks them of each member's run.
- Separation and finding name the members the comparison counts.

## Opening the work to outside contributors

[#237](https://github.com/rbeauchamp/acorn/issues/237) tracks this, in three steps.

1. Before any outreach: this page ([#235](https://github.com/rbeauchamp/acorn/issues/235)), open statements held in Lean so that they stay checked against the current code ([#238](https://github.com/rbeauchamp/acorn/issues/238)), and one vocabulary ([#244](https://github.com/rbeauchamp/acorn/issues/244)).
2. Then more kinds of contribution ([#239](https://github.com/rbeauchamp/acorn/issues/239)), claims and credit that hold ([#240](https://github.com/rbeauchamp/acorn/issues/240)) and a lower cost of entry ([#241](https://github.com/rbeauchamp/acorn/issues/241)), with at least 20 open statements seeded.
3. Then a theory track that formalizes results of the papers Acorn cites ([#242](https://github.com/rbeauchamp/acorn/issues/242), with [#134](https://github.com/rbeauchamp/acorn/issues/134) and [#135](https://github.com/rbeauchamp/acorn/issues/135)), a venue and an announcement ([#243](https://github.com/rbeauchamp/acorn/issues/243)).

Five missions are open today.
[#200](https://github.com/rbeauchamp/acorn/issues/200) and [#201](https://github.com/rbeauchamp/acorn/issues/201) are lemmas for a design of learned agent state that is not admitted.
[#132](https://github.com/rbeauchamp/acorn/issues/132), [#163](https://github.com/rbeauchamp/acorn/issues/163) and [#174](https://github.com/rbeauchamp/acorn/issues/174) are off the path.
The [mission board](mission-board.md) is the dated list.

## Upkeep

Bugs and problems of velocity stay in scope under the owner's direction: [#185](https://github.com/rbeauchamp/acorn/issues/185), [#165](https://github.com/rbeauchamp/acorn/issues/165), [#103](https://github.com/rbeauchamp/acorn/issues/103) and [#133](https://github.com/rbeauchamp/acorn/issues/133).
[#36](https://github.com/rbeauchamp/acorn/issues/36) waits on the constants of its bounds before it can be posted as a mission.

## How the issues encode this

- **Milestones.** [Rung 1: concealed targets in visits](https://github.com/rbeauchamp/acorn/milestone/1) holds the active rung. [Later rungs](https://github.com/rbeauchamp/acorn/milestone/2) holds what waits for it. [Open the roadmap](https://github.com/rbeauchamp/acorn/milestone/3) holds the work for outside contributors.
- **Labels.** One lane on each issue: `lane:state`, `lane:discover`, `lane:prove`, `lane:world`, `lane:theory`, `lane:community` or `lane:upkeep`. A tracking issue of a rung carries the label rung. An issue off the active rung carries the label parked. `needs-owner-decision` and `needs-statement` say what an issue waits on: the second marks work that needs an exact statement before it can be posted as a mission.
- **Sub-issues** group the parts of one deliverable under its tracking issue.
- **Blocked-by links** give the order between issues.

The issues that can be worked on now are the open issues of the first milestone that no open issue blocks.
