# Roadmap

This page says what Acorn works on now, in what order, and why.
GitHub's issues are the record of each piece of work; this page is the order between them.
It was last set on 2026-11-13, and a change to the order changes this page in the same pull request.

## Terms

- The *mission theorem* is the theorem the [mission contract](mission-contract.md) asks for: that Acorn's agent, as running Lean code, achieves goals over a formally stated class of big worlds. It is one theorem for each class.
- A *rung* is one such class of worlds, with its theorem. The classes form a ladder, from the first and smallest toward "any big world". Each rung has one tracking issue, labelled rung.
- An *obligation* is a numbered item of the mission contract's [open obligations](mission-contract.md#open-obligations): a statement not yet precise, a theorem not yet proved or a choice not yet made.
- A *lane* is a kind of work. On a rung there are three: *state* (write a contract, a theorem or a premise exactly, in Lean), *discover* (find the algorithm for which the rung's theorem is true) and *prove* (prove a stated obligation of the executing code). Four more group the rest: *world*, *theory*, *community* and *upkeep*.
- A *parked* issue is not on the active rung. It stays open, and its last roadmap comment says when it re-enters.
- A *mission*, as a unit of work, is an issue with a frozen contract that outside contributors and their agents can land ([missions](missions.md)).

## Where the mission stands

No theorem in the tree yet says that Acorn's executed agent learns.
On the first rung, `executed_mission` proves the mission theorem's statement of the executed agent from premises that name the open obligations, so what remains is those premises.

- **Proved.** The kernel's model of worlds and agents. That no agent achieves goals in every world, and that on a class which conceals its goals every agent solves at most a covering bound of members on a first visit. One class of worlds that meets the mission contract's conditions (a) to (c) for a big class (`witness_big`). That every agent which keeps nothing of its experience solves at most a covering bound of members on every visit (`visits_need`). That a reference agent which replays a route it has found separates from those agents and retains what it solved, under its own hypotheses (`witness_separation`, `replay_keeps`). That the host's loop of visits is the kernel's (`executed_visits_closed_loop`). Exact resumption from a checkpoint, and that no host write reaches learning.
- **Proved of the mission theorem's statement.** The statement is one proposition over the four intent records (`Mission`), and on a class of worlds in visits it follows from named premises about the class and the agent (`visits_mission`). On the first rung's class every premise about the class holds, the reward lemma included (`find_mission`, `classReward_eq`). A reference agent of fixed memory meets the whole statement there, with every premise discharged (`witness_mission`).
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

### What the rung needs

| Obligation | Needed | Issue |
|---|---|---|
| 9, separation and retention for the executed agent | Yes: it is the theorem. Stated as the premises `ExecutedFinds` and `ExecutedRetains` | [#230](https://github.com/rbeauchamp/acorn/issues/230) |
| 4, goal-information and exploration premises | Yes. The goal information is proved (`reward_step`); no premise about exploration that suffices for the executed agent is known | [#232](https://github.com/rbeauchamp/acorn/issues/232) decides them |
| 15, the failing fraction of runs | Yes. Its form is stated (`AllBut`, `executed_mission_allBut`); the fraction as a function of the class and the visits is open | [#231](https://github.com/rbeauchamp/acorn/issues/231) for the form, [#232](https://github.com/rbeauchamp/acorn/issues/232) for the fraction |
| 16, the class's reward lemma | Discharged for this class (`classReward_eq`), with an attempt's rewards counted up to its first payment, which the owner can overrule | [#231](https://github.com/rbeauchamp/acorn/issues/231) |
| 6, a bound on reachable memory | Yes: the premise `MemoryBounded` | [#195](https://github.com/rbeauchamp/acorn/issues/195), a posted mission |
| 7, executed work, and learning from each experience once | Yes: the premises `WorkBounded` and `LearnsOnce` | [#90](https://github.com/rbeauchamp/acorn/issues/90) for work, [#233](https://github.com/rbeauchamp/acorn/issues/233) for once-only learning |
| 3, the viewer's rule as a theorem | Completes contract 1 beside the rung | [#213](https://github.com/rbeauchamp/acorn/issues/213), step 5 |
| 2, 5, 10, 11, 13, 14 | No: the rung runs in visits and does not use the campaign join | |
| 12, a guarantee counted over the generator's seeds | No: it stays a named assumption | [#184](https://github.com/rbeauchamp/acorn/issues/184), parked |

### Order of work

1. **State.**
   - The intent record of the postcondition, steps 1 to 4 ([#219](https://github.com/rbeauchamp/acorn/issues/219)).
   - The intent record of contract 2, steps 1 to 4 ([#214](https://github.com/rbeauchamp/acorn/issues/214)).
   - The rung's theorem in Lean ([#231](https://github.com/rbeauchamp/acorn/issues/231)). In the tree: its definitions, a proof that a reference agent meets it (`witness_mission`) and a proof of it for the executed agent from named open premises (`executed_mission`), so the way the theorem depends on its obligations is checked by Lean's kernel. Remaining: the class constants of the executed agent's rung, and the blind second reading of the statement.
2. **Discover.** Decide the rung for the primitive research profile, by theorem ([#232](https://github.com/rbeauchamp/acorn/issues/232)): does its exploration find enough members, does credit reach the start of the next visit, does the first reward collapse exploration, and does shared weight send the agent off its route. Two algorithm changes are scoped and open on those answers: exploring without reward and after the first reward ([#170](https://github.com/rbeauchamp/acorn/issues/170)), and a one-step model that carries a success back ([#171](https://github.com/rbeauchamp/acorn/issues/171)).
3. **Prove.** The invariants, stated over constructions so that an algorithm change does not reopen them: reachable memory ([#195](https://github.com/rbeauchamp/acorn/issues/195)), work ([#90](https://github.com/rbeauchamp/acorn/issues/90)), once-only learning ([#233](https://github.com/rbeauchamp/acorn/issues/233)), and the executing code against the records of contracts 1 and 3 ([#213](https://github.com/rbeauchamp/acorn/issues/213), [#215](https://github.com/rbeauchamp/acorn/issues/215)).
4. **Assemble.** The rung's theorem for the primitive profile, then for the ranked profile ([#230](https://github.com/rbeauchamp/acorn/issues/230)).

Stating comes first because it is the cheapest step and it decides which of the others are needed.
Discovery decides whether the theorem is true; the proofs of step 3 assume it.

## The rungs after the first

Their order is the owner's decision and is not yet made ([#234](https://github.com/rbeauchamp/acorn/issues/234)).
The recommendation recorded there is: capacity on an agent of restricted capacity, then a class of ARC-AGI-3 games ([#71](https://github.com/rbeauchamp/acorn/issues/71)), then a class of Microduck scenes ([#236](https://github.com/rbeauchamp/acorn/issues/236)), then a class of worlds with no restarts.

## Parked work, and when it re-enters

| Issues | Re-enters when |
|---|---|
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
- Whether open statements live in the governed tree or in a separate library ([#238](https://github.com/rbeauchamp/acorn/issues/238)). The open premises of the first rung's theorem are hypotheses of theorems in the governed tree, which the owner can overrule ([#231](https://github.com/rbeauchamp/acorn/issues/231)).
- Whether the first rung counts an attempt's reward up to its first payment, as `untilPaid` does, or the class changes so that the plain sum of a visit's rewards orders agents as the members they solve do ([#231](https://github.com/rbeauchamp/acorn/issues/231)).
- A standing, bounded budget for diagnostic runs of `acorn-core visits` in step 2, as smoke tests and never as evidence ([#232](https://github.com/rbeauchamp/acorn/issues/232)).
- What the feature generator reads in a world with no symbol array ([#175](https://github.com/rbeauchamp/acorn/issues/175)).
- Whether a mission may change a file of the trusted base ([#132](https://github.com/rbeauchamp/acorn/issues/132)).
- The proposals for outside contributors, below.

## Opening the work to outside contributors

[#237](https://github.com/rbeauchamp/acorn/issues/237) tracks this, in three steps.

1. Before any outreach: this page ([#235](https://github.com/rbeauchamp/acorn/issues/235)), open statements held in Lean so that they stay checked against the current code ([#238](https://github.com/rbeauchamp/acorn/issues/238)), and one vocabulary ([#244](https://github.com/rbeauchamp/acorn/issues/244)).
2. Then more kinds of contribution ([#239](https://github.com/rbeauchamp/acorn/issues/239)), claims and credit that hold ([#240](https://github.com/rbeauchamp/acorn/issues/240)) and a lower cost of entry ([#241](https://github.com/rbeauchamp/acorn/issues/241)), with at least 20 open statements seeded.
3. Then a theory track that formalizes results of the papers Acorn cites ([#242](https://github.com/rbeauchamp/acorn/issues/242), with [#134](https://github.com/rbeauchamp/acorn/issues/134) and [#135](https://github.com/rbeauchamp/acorn/issues/135)), a venue and an announcement ([#243](https://github.com/rbeauchamp/acorn/issues/243)).

Six missions are open today.
[#195](https://github.com/rbeauchamp/acorn/issues/195) is on the first rung's path.
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
