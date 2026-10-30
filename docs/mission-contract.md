# Acorn's mission contract

Acorn pursues Oak Lab's mission: "Our goal is to discover and implement algorithms that allow agents to achieve goals in big worlds" [[1]](#r1).
Acorn's owner states what pursuing it means for Acorn: to prove that Acorn's agent achieves goals over a formally modelled class of big worlds.
The proof takes the form of a contract: preconditions on the class of worlds, a postcondition on achieving goals, and invariants of learning from one continuous stream of experience.
Running the agent in ARC-AGI-3 games or on the Microduck shows it working and finds defects; it is never the evidence.

This document states that contract and the decisions behind it, for contributors and their agents.
It is the contract of Acorn's mission as a whole; each [mission issue](../CONTRIBUTING.md#missions-for-outside-contributors-and-agents) freezes a contract of its own, a theorem or check that serves a part of this one.
Each part is given first in plain words and then precisely enough that a Lean statement follows from it.
No theorem in the tree yet proves the contract for Acorn's agent; [the last section](#open-obligations) lists what remains.

## How to read this document

Each part separates three kinds of statement, and labels each:

- **Source.** What published work establishes, quoted or stated with the section, definition, theorem, figure or slide that says it. Questions about what the mission means are answered from Oak Lab's and Sutton's work; other work is cited for a mathematical result, or because Oak Lab's or Sutton's work itself cites it, and the ARC-AGI-3 documentation for a fact about that world. A source that supports a direction is never read as proving one of Acorn's conditions, and each part says what its sources leave unestablished.
- **Acorn's choice.** A design decision of Acorn's, with the argument or Acorn theorem that defends it. The owner's own decisions are marked as the owner's; every other choice was made on the owner's behalf by the AI agents that work on Acorn, from the evidence given, and can be revisited.
- **Open.** An obligation nobody has discharged: a statement not yet precise, a theorem not yet proved, or a choice not yet made.

A name in backticks is an Acorn declaration that exists in the tree under that name; a theorem so named is checked by Lean's kernel.
A statement marked *argued* is derived by hand and not machine-checked.
A Lean block marked *proposed* is not in the tree.
Every passage cited here was read in its source on 2026-10-29.
Every research work cited is one that an independent citation audit verified against its primary text, and works that audit could not verify are not cited; the ARC-AGI-3 documentation is cited only for how that interface restarts a game.

Terms used throughout:

- A *world* is a deterministic state machine that hands the agent one percept per step and moves on the agent's action (`Kernel.World`). A *percept* is what the agent receives in one step: an observation frame and the reward of the preceding transition (`Percept`).
- An *agent* turns its memory and one percept into an action and its next memory (`Kernel.Agent`). Its *stream* is the sequence of percepts it receives.
- A *class of worlds* is a family of worlds, its *members*, each with its own start state (`WorldClass`). An *attempt goal* is a condition on a world's states with a step cap (`AttemptGoal`); an agent *achieves* it when its own run reaches a satisfying state within the cap (`Achieves`), and the goal is *feasible* when some sequence of actions does (`Feasible`).
- A *frozen agent* keeps nothing of what it perceives: its memory advances without reading its percepts, though its action may read the current one (`ExperienceFree`). An agent whose actions read no percept is frozen (`OpenLoop.experienceFree`).
- A *visit* is one attempt of a fixed length from a member's start state. Between visits the member's world returns to its start state while the agent keeps its memory (`Kernel.visits`); an agent *solves a member on a visit* when it achieves the member's goal within that visit (`SolvesOnVisit`).
- A *covering bound* k says that one action sequence meets the goals of at most k members within the cap (`Covered`).
- The *grid world* is the tile world the viewer shows, under the name the code and proofs use.

## The mission contract

**In plain words.**
Acorn is an agent, written as running Lean code, about which one kind of theorem is to be proved.
For each stated class with its learning preconditions, consider a separate run of the same agent from the same initial memory in each member, keeping memory across that member's visits.
Learning only from its own single stream in each run, the agent eventually solves more than the class's covering bound k members on one common visit; every frozen agent solves at most k members on any visit.
Within each member's repeated visits, once it achieves the goal it keeps achieving it while the problem stays the same.
This promises class-level separation and retention; eventual success in every member is a stronger obligation that this contract does not yet impose.
The parts are the interface every world meets ([contract 1](#contract-1-the-interface-every-world-meets)), what makes a class of worlds big ([contract 2](#contract-2-what-makes-a-class-of-worlds-big)), the invariants of learning from one stream ([contract 3](#contract-3-invariants-of-learning-from-one-stream)) and what achieving goals promises ([the postcondition](#the-postcondition-what-achieves-goals-promises)).
The theorems concern the definitions that execute.

- **Source.** The mission sentence is the opening of Oak Lab's mission page [[1]](#r1). Its section "Our algorithms learn in real-time without storing or replaying data" says that Oak Lab's "batch-size-one learning algorithms can learn directly from experience without storing or replaying data". The Alberta Plan characterizes "the problem of AI as the online maximization of reward via continual sensing and acting, with limited computation", and grounds learning in experience alone: "Only experience is available to the agent, and the environment is known only as a source and sink for these signals" ([[3]](#r3), "Research Vision: Intelligence as signal processing over time", with Figure 1). Neither source states a formal criterion of success.
- **The owner's decision: a theorem, not a score.** The promise is a theorem about the executed definitions. A score measures finitely many cases, while a theorem covers every world of the class it states; [missions](../CONTRIBUTING.md#missions-for-outside-contributors-and-agents) gives the rule, with an audit that found ARC-AGI-3's public games reachable by strategies that do not learn.
- **Acorn's choice: the comparison is with frozen agents, not with an optimum.** In a big world the agent cannot "represent the value or optimal action for every state" ([[2]](#r2), "The Big World Hypothesis"), so the optimum is no yardstick. A frozen agent is one that keeps nothing of its stream, so what learning from experience must add is to solve more members of the class on one visit than every frozen agent can on any visit. Every individual feasible goal has a frozen scripted solver (`feasible_iff_script`, `script_experienceFree`); the separation concerns one agent across the class, not a goal that defeats every frozen agent. The sources motivate the comparison (tracking can do better than every converging algorithm, see [the postcondition](#the-postcondition-what-achieves-goals-promises)); the predicate is Acorn's.
- **Open.** The mission theorem itself, for Acorn's executed agent; [the open obligations](#open-obligations) list its parts.

Two mathematical facts shape how "any big world" is read.

### No agent achieves goals in every world

- **Source.** Lattimore and Hutter prove that no policy is strongly asymptotically optimal in the class of all deterministic computable environments: none converges to the optimal value in every environment of the class ([[11]](#r11), Theorem 8, part 1). The theorem's scope is its own: a policy is a deterministic map from histories to actions (Definition 3), action and observation sets are finite and rewards lie in [0, 1] (Assumption 2), and the discount function is computable with finite, positive tails (Definition 5). It concerns that class and that limit, not a finite horizon in a smaller class.
- **Acorn's theorems.** Over an interface with at least two actions, a kernel agent's first action is fixed by its initial memory and the first percept. So for every such interface, every percept and every kernel agent there is a world delivering that one percept at every state, with a start state and a goal of step cap one that some action sequence meets and the agent's closed loop does not (`no_agent_achieves_every_world`). The executed agent is such an agent over the grid interface, from every state of it (`executed_defeated`). This is a lemma for why the mission theorem has preconditions, not a result about learning.
- **Acorn's choice.** The contract quantifies over a stated class whose preconditions exclude such worlds, and the class grows step by step toward the mission. As the [README](../README.md#purpose-and-worlds) says, "each restriction is a step toward that end, not a narrowing of it".

### In a big world nobody does well on a first encounter

- **Source.** In the Alberta Plan, "The larger sensory signal, the observation, is explicitly not expected to provide complete information about the state of the environment" ([[3]](#r3), "Research Vision"), and in a big world the agent "can neither fully perceive the state of the world nor can it represent the value or optimal action for every state" ([[2]](#r2), "The Big World Hypothesis"). Partial observation alone does not make a first encounter fail: a fixed rule still solves a goal whose solution its observation shows.
- **Acorn's theorems.** A class *conceals* its goals when every member shows the agent the percepts of one reference world until that member's goal is first met (`Conceals`). In such a class every agent, learning or not, solves on a first encounter at most as many members as one action sequence meets (`Conceals.need`). In the grid world this covers the executed agent: from every state of it, it solves at most 49 + 7·cap of the concealed targets on a first visit of cap steps (`executed_find_first`).
- **Acorn's choice.** The promise is improvement from experience, never success on a first try, and concealment is a precondition of a big class ([contract 2](#contract-2-what-makes-a-class-of-worlds-big) (b)).

## Contract 1: the interface every world meets

**In plain words.**
Each step the world hands the agent one percept: what it observes, the reward of the last step, and the signals the world declares.
The agent answers with one action from the world's declared set.
Nothing else passes in either direction: the agent cannot read the world's internal state, and no host, viewer or tool changes what the agent learns or decides; the viewer can only stop it.
Every world meets this same contract: the tile world, each ARC-AGI-3 game and the Microduck.

- **Source.** "These three time series—observation, action, and reward—constitute the experience of the agent. We expect all learning to be grounded in these three signals and not in variables internal to the environment" ([[3]](#r3), "Research Vision", Figure 1). The reward "is scalar and defines the ultimate goal of the agent—to maximize the total reward summed over time" (same passage), and the reward hypothesis states "That all of what we mean by goals and purposes can be well thought of as maximization of the expected value of the cumulative sum of a received scalar signal (reward)" [[4]](#r4).
- **Acorn's choice and theorems.**
  - By construction: a world is a `Kernel.World` over the executed `Interface`, and an agent a `Kernel.Agent` whose only input is a `Percept` (a frame and the reward word) and whose only output is an action below the interface's declared count. That no agent reads a world's state is a fact of the types, for every kernel agent. The executed decision is such an agent (`executedAgent`).
  - What the executed decision reads of a percept: on two percepts that agree in the frame's active features and unit outputs, the reward word and three declared extra arrows, it returns the same decision and the same next state (`act_extras`).
  - No host write reaches learning: a host operation that keeps the learners changes neither the next decision nor the learners after it (`act_accounting`), and from two states with the same learners the executed agent takes the same action at every time, in every world (`executed_actions`). At each of the three step orders, the agent's step from two states with the same learners returns the same decision and states with the same learners (`actOrdered_learners`), so it reads its lifetime observations only to write them; every order's step reaches the completion boundary, which writes them (`TemporalControl.finish_eq`).
  - The viewer: only a stop request enters the core, at an attempt boundary, and source and compiled ownership keep learned code from reaching host control ([verification](verification.md#viewer-ownership-boundaries)). This is enforced by gates, not by a theorem.
  - Goals: Acorn states a goal as an attempt goal, a condition on states with a step cap, so that achieving it is an event a theorem can count over a class's members. The reward word remains the agent's signal. Stating goals this way is Acorn's choice, not a consequence of the reward hypothesis.
- **Open.**
  - That the host's run and the kernel's closed loop take the same actions: `act_accounting` is not composed along a run ([design](design.md#what-a-class-of-worlds-can-and-cannot-show)).
  - A theorem form of the viewer's rule: every message the core accepts from the viewer is a stop whose handling changes no learned field.
  - The classes of ARC-AGI-3 games ([#71](https://github.com/rbeauchamp/acorn/issues/71)) and Microduck scenes ([#173](https://github.com/rbeauchamp/acorn/issues/173)), each stated over this interface.

## Contract 2: what makes a class of worlds big

This is fork F2: what measures "big". It was decided on the owner's behalf.

**In plain words.**
A world is big relative to an agent: the agent is far smaller than the world, so it can neither perceive the world's whole state nor represent the right action for every state.
Acorn turns that relation into four conditions a class of worlds can be proved to meet:

- (a) *feasible:* every goal can be achieved from where its attempt starts, so the class holds no traps;
- (b) *concealed:* before a goal is first met, the member's percepts match those of one reference world; learning from success requires additional feedback;
- (c) *small frozen share:* a frozen agent solves only a small share of the class on any visit, so learning is necessary;
- (d) *beyond capacity,* the scaled target: the class poses more separate problems than the agent's memory can hold solutions to at once, so the agent must keep learning and forgetting on its one stream.

Today's bigness conditions are (a) to (c); (d) is the named target for larger classes.
Conditions (a) to (c) establish the comparison bound, not that experience supplies information from which the agent can learn a solution. Each class's mission theorem also needs its own learning preconditions, as below.

- **Source.**
  - The big world hypothesis is relational: "the agent is orders of magnitude smaller than the environment. It can neither fully perceive the state of the world nor can it represent the value or optimal action for every state." It "is more a statement about the class of problems we should care about than a fact about all decision-making problems. It can be made true or false by exercising control over the design of the environment and the agent" ([[2]](#r2), "The Big World Hypothesis"). For benchmarks, "The alternative is to restrict the computational capabilities of the agents instead of making the environments larger", for example "the number of operations, the amount of memory, the amount of memory bandwidth, or the amount of energy" ([[2]](#r2), "Benchmarking Algorithms in Big Worlds").
  - A world of 20 states can be big for a restricted agent. In the Black and White world, a prediction from one scalar parameter cannot represent a stationary environment of 20 states: "an extreme example with strong representational limitations, so strong that its 20 states is a big space" ([[5]](#r5), Section 1; the world is defined in Section 2).
  - Kumar and colleagues pose agent design under a fixed information capacity: maximize average reward subject to sup_t H(U_t) ≤ C, a bound on the entropy of the agent state, in nats ([[7]](#r7), Section 4.2.1, Equation 12). Javed and Sutton summarize that work as showing "that continual learning is a necessary element of reinforcement learning when the agent is computationally constrained" ([[2]](#r2), "The Big World Hypothesis").
  - What the sources do not establish: none defines bigness by conditions (a) to (d), none gives the counting condition of (d) below, and none shows that concealment exceeds a memory bound. These are Acorn's own conditions, derived here.
- **Acorn's choice: a relation, not raw size.** Bigness is not measured by the bits of the world's state. A world can be padded with state that no goal depends on, which makes it larger without making learning any more necessary, and Acorn's grid world fails a raw-size test anyway: about three million learned parameters hold 94.4 million bits, while the whole state of a 1024 × 1024 world fits in fewer than 67.7 million (argued in the [baseline assessment](baseline-assessment.md#measured-against-the-published-oak-and-alberta-plan-designs)). The relation that matters is between what the agent can perceive and hold, conditions (b) and (d), and what the goals need.
- **Acorn's theorems for (a) to (c).**
  - (b) is `Conceals`. With it every agent is blind on the class: until a member's goal is first met, it takes in that member the actions it takes in the reference world (`Conceals.blind`).
  - (c) follows from (b) and a covering bound k for one visit's length: on every visit, every frozen agent solves at most k members (`visits_need`). Condition (c) asks for more than k members; the margin of members over k measures how small the frozen share is.
  - (c) excludes a class one action sequence solves, which gives no evidence of learning. An agent that reads no percept and restarts its count on every visit, with a counter of ⌈log₂ (length + 1)⌉ bits (`visitScript`, `visitScript_openLoop`, `visitScript_memory`), solves every member of such a class on every visit (`blindSolvable_frozen`), so every covering bound of the class for that visit length is at least the size of every finite set of its members (`blindSolvable_covered`). This is a lemma the mission theorem uses for the margin of (c), not a result about learning.
  - (a) is `Feasible` for each member's goal within one visit.
  - Satisfiable in one world: in the grid world at seed 5 and side 64, with visits of seven steps, the class of concealed targets has a covering bound of 98, and an agent that replays a route it has found solves 147 of its members on visit 2 (counting from 0), while every frozen agent solves fewer than 147 on every visit (`witness_separation`). That theorem does not establish (a) for every member of the class, since the class holds targets no visit can meet.
  - One class meeting (a) to (c): in the same world, with the same visits and the same bound of 98, the concealed targets a visit can meet (`feasibleFind`) are feasible, concealed and more numerous than the bound (`witness_big`). Their feasibility holds by how the class is indexed, so the theorem's content is the concealment, the bound and the count. It says nothing about the goal-information and exploration premises below, and it is a lemma the mission theorem on this class uses, not a result about learning.

The Lean form of (a) to (c) is `BigClass`, over the kernel's definitions:

```lean
structure BigClass (family : WorldClass interface) (goals : family.Goals) (len k : ℕ) where
  reference : World interface
  origin : reference.State
  conceals : Conceals family goals reference origin                     -- (b)
  covered : Covered family (visitGoals goals len) k                      -- (c), with visits_need
  feasible : ∀ i, Feasible (visitGoals goals len i) (family.start i)     -- (a), every visit
  members : Finset family.Index
  large : k < members.card                                               -- (c), small share
```

**Acorn's choice: qualify learning separately from bigness.** The mission theorem is specialized to each chosen class, rather than claiming that this structure alone implies separation for Acorn's agent. A class must also expose enough goal information and support the agent's exploration; those premises must be stated independently of the promised success and justified for that class.

*Argued obstruction.* Two members can give the same constant percept forever while requiring different first actions for their one-step goals. With len = k = 1, both goals are feasible, concealment holds, and one action sequence covers at most one member. Every agent nevertheless has identical memories and actions in the two runs, by induction on the shared percept stream, including across visits. It solves at most one member on any common visit. Thus (a) to (c) alone cannot support the mission implication.

The replay comparison has a precise additional premise: one function signal from percepts to booleans must, for every member i, state s and action a, return true on that member's percept after stepping from s by a if and only if that successor state satisfies member i's goal (`replay_separates`). The same function serves all members; it cannot be given the hidden member index. The theorem also requires a fixed exploration schedule whose visits up to some finite last visit meet the goals of a set of more than k members. Feasibility alone does not establish that a particular schedule does so. These hypotheses suffice for the replay agent's separation, not for Acorn's executed agent; the latter's corresponding goal-information and exploration obligations remain open. The grid-world theorem `witness_separation` discharges the replay hypotheses for its stated set of targets.

**Condition (d): a counting bound** (`campaign_count`, `campaign_count_bits`).
A *campaign* presents N ≥ 1 slots of a concealed class in one stream (`campaign`): one visit of a fixed length to each slot in turn, cycle after cycle, never restarting the agent, and each slot's world starting each visit from its own start state.
An *assignment* picks, for each slot, a member from a set of T members, so there are T^N assignments.
Let k be the class's covering bound for one visit.
Then for every agent, every N and every cycle, the assignments on which the agent solves every slot on that cycle (`SolvesSlot`) number at most m · k^N, where m is the size of any set holding the memories the agent has at that cycle's start under those assignments (`campaign_count`).
For an agent whose memory takes at most 2^b values (`MemoryWithin`, b bits), that is at most 2^b · k^N assignments (`campaign_count_bits`).
The fraction of such assignments is then at most 2^b · (k/T)^N, which is below 1 exactly when N · log₂(T/k) > b (*argued*, from the count).

*Proof.*
Group the assignments by the agent's memory at the start of the cycle; there are at most m groups.
Within a group that memory is fixed.
On slot 1's visit, concealment makes the percepts those of the reference world until success, so the actions before success are fixed by the memory, and slot 1 succeeds for at most k members.
For each such member the run through slot 1's visit is determined, so the memory at slot 2's visit is fixed, and slot 2 succeeds for at most k members; and so on through slot N.
So at most k^N assignments fall in each group. ∎

The bound counts memory values, in bits; it needs no entropy, so the nats of the capacity C above play no part in it.
It is a lemma the mission theorem on campaigns uses, not a result about learning. It holds of the executed agent as of every agent, but no theorem yet bounds the size of a set holding the memories that agent reaches.
What it means for Acorn's agent today (*argued*): at a visit length of 96 steps, k = 49 + 7 · 96 = 721; a window of radius 99 holds 198² tiles, of which at most 49 lie within three tiles of the start and are not members, so it holds at least 39,155 members, and each slot carries log₂(39155/721) ≈ 5.76 bits.
If the agent's memory were the 94.4 million bits of its learned parameters, the bound would bite only beyond about 16.4 million slots, each visited twice at 97 decisions a visit: about 3.2 × 10⁹ steps.
That is why (d) is the scaled target and not today's precondition.

- **Open.**
  - Goal-information and exploration premises for each chosen class, and a proof that they support learning by Acorn's executed agent. The replay theorem's decoding and exploration hypotheses cannot be dropped when using it as a comparison.
  - A memory bound for the executed agent: its memory type holds exact naturals, so `MemoryWithin` holds of no fixed width for that type, and (d) needs a bound on the memories it can reach.
  - Whether (d) is first instantiated for an agent configuration of restricted capacity, as Javed and Sutton recommend for benchmarks ([[2]](#r2), "Benchmarking Algorithms in Big Worlds"), or only at the full configuration. This is a roadmap choice not yet made.

## Contract 3: invariants of learning from one stream

**In plain words.**
Every step does work and holds memory bounded by fixed functions of the world's interface and the agent's configuration.
Everything the agent knows at any moment is a function of its starting state and the percepts it has received, each learned once and in order: nothing is replayed, trained offline, written by a host or reset.
A stopped agent resumes exactly where it stopped.

- **Source.** Oak Lab's algorithms "learn directly from experience without storing or replaying data" ([[1]](#r1), "Our algorithms learn in real-time without storing or replaying data"). The Alberta Plan's temporal uniformity: "Temporal uniformity means that all times are the same with respect to the algorithms running on the agent. There are no special training periods when training information is available or when rewards are counted more or less than others. … If the agent learns or plans, then it learns or plans on every time step." The same passage acknowledges "that there may be situations in which it is preferable to depart from absolute temporal uniformity", and on computation, "Computer power, though exponentially more plentiful, is never infinite" ([[3]](#r3), "Research Vision"). For big worlds, "Accepting the big world hypothesis means we should actively look for more computationally efficient learning algorithms" ([[2]](#r2), "Need for Computationally Efficient Learning Algorithms"). The sources state a direction and allow considered departures; they do not state exact bounds, once-only learning, a ban on resets and host writes, or exact resumption.
- **Acorn's choice.** These invariants are strict and hold on every step of every run, because the contract is a theorem over every run, not a tendency. Each is Acorn's contract.
- **Acorn's theorems.**
  - Causal dependence: the memory at a time is the fold of the agent's decisions over the percepts before it, in order (`memory_causal`), and likewise for a step in two parts (`memory_parts`). These theorems hold for every kernel agent. They say nothing about how many learning updates a decision performs on a stored percept: the type of `Kernel.Agent.act` allows it to store a percept and reuse it on every later call, even with fixed memory and work bounds.
  - Exact resumption: loading the bytes a save writes returns the saved state, every field of it (`load_saved`), and resuming returns it with a new evaluator session (`resume_saved`).
  - No host write reaches learning: `act_accounting`, under contract 1.
  - Bounded memory, for some states: for every state whose evaluator naturals each encode within their allowance, a save writes at most a fixed number of bytes (`snapshot_size_bound`).
  - Bounded work, for an accounting: the accounting of a step's first part is bounded for every agent state and percept (`choose_work`). It bounds the accounting of a costed twin; the twin's correspondence with the compiled code was observed in one build and is not proved ([design](design.md#the-work-of-the-first-part)).

*Proposed* Lean form of the resource bounds only, for an agent with a work measure and a size measure:

```lean
structure StreamResourceBounds (A : Kernel.Agent I) (work : A.Memory → Percept I → ℕ)
    (size : A.Memory → ℕ) (W S : ℕ) : Prop where
  boundedWork : ∀ (world : World I) start t,
    work (memoryAt world A start t) (perceptAt world A start t) ≤ W
  boundedMemory : ∀ (world : World I) start t, size (memoryAt world A start t) ≤ S
```

Causality needs no field: `memory_causal` holds of every kernel agent. The proposed resource predicate does not express once-only learning, absence of replay, host isolation or exact resumption.

**Acorn's choice: a separate once-only, no-replay contract.** Direct learning from an experience must consume that experience once, in stream order; stored past observation/action/reward samples must not be submitted again as training data. Retained learned parameters and model-based planning are distinct from resubmitting experience. This property requires a semantics that identifies experience consumption and distinguishes those uses inside the executed learning operations; an arbitrary causal memory transition does not supply one. The property is an additional obligation of the mission, not a consequence of the resource bounds.

- **Open.**
  - A formal once-only, no-replay contract over the executed learning operations, identifying each experience and its consumption, allowing retained learned state and planning while excluding resubmitted samples. Prove it for every reachable update and link it through the host's dispatch, checkpoint load and resumption paths; the current kernel interface has no experience-consumption semantics with which to state that theorem.
  - That every state the executed agent can reach has evaluator naturals within their allowance, so that its memory is bounded on every run.
  - A Lean semantics of executed work, and a work bound over it; until then the work field can be stated only over the accounting.
  - That the host's run is the kernel's closed loop (contract 1), so that these theorems describe the run that executes.

## The postcondition: what "achieves goals" promises

This is fork F1: how strong "achieves goals" is. It was decided on the owner's behalf.

**In plain words.**
On each class of the ladder below:

- (i) *separation:* after experience, there is one visit number and a finite set of more than k members such that the agent solves each of those members on that visit in its separate run; every frozen agent solves at most k members on any visit;
- (ii) *retention:* while the problem stays the same, once the agent has achieved a member's goal it keeps achieving it on later visits;
- (iii) on classes beyond its capacity (contract 2 (d)), where it cannot keep every solution at once, it keeps the ability to learn, so that it can learn again a solution it had to give up. The precise form of (iii) is open.

Separation allows members outside that successful set to remain unsolved; retention applies to every member whenever it is solved. These quantify over separate runs from the same agent initial memory, with continuity within each member's visits. A campaign that interleaves different members in one run needs postcondition (iii).
The contract does not promise success on a first encounter, eventual success in every member, the optimal action in every state, or, until an attempt bound is proved, how many failed visits learning takes.

- **Source.**
  - *Tracking.* Tracking "can perform better than any converging algorithm on a stationary problem" ([[5]](#r5), Abstract, shown in Section 2), and "tracking methods may outperform converging methods, even in stationary domains" ([[6]](#r6), Section 2.4). "Learning things when they are needed and discarding them when they are not is sometimes called tracking", and "A key requirement for tracking to be effective is temporal coherence" ([[2]](#r2), "Online continual learning for achieving goals in big worlds").
  - *Forgetting that follows resources.* An agent without the resources to retain everything "can learn aspects that are important for decision-making at the current time and discard them when they are no longer" (same section). Like a CPU cache, "by retaining the right pieces of information and discarding the least useful ones, a small cache can have a high hit ratio" ([[2]](#r2), "Humans extensively rely on tracking in everyday life"). Kumar and colleagues' experiments indicate that "A performant agent can forget recurring information if it can relearn that information quickly relative to the duration of the information's utility" and that "When computation is constraining, forgetting can increase average reward" ([[7]](#r7), the permuted-MNIST experiments of Section 6.1, as summarized at the end of Section 6). These are experimental findings, not theorems.
  - *Keeping the ability to learn.* "Plasticity = the ability to learn" ([[9]](#r9), slide 4). Standard deep-learning methods "gradually lose plasticity in continual-learning settings until they learn no better than a shallow network", and "Plasticity is maintained indefinitely only by algorithms that continually inject diversity into the network" ([[8]](#r8), abstract). These are empirical findings, not a guarantee of relearning.
  - What the sources do not establish: a guarantee that the agent keeps a solution after its first success, a bound on relearning from every memory it can reach, or a bound on failed attempts. These are Acorn's design obligations.
- **Acorn's choice: separation and retention now, the attempt bound later.**
  - Separation alone is too weak (*argued*): an agent that succeeds once by luck in many members and never again meets it, and shows no learning. Retention rules that agent out.
  - Retention of every solution forever is too strong (*argued*, from `campaign_count_bits`): the counting bound holds for every cycle, so once N · log₂(T/k) > b, a b-bit agent that has solved every slot at least once and kept every solution would solve every slot in the next cycle, which happens for at most a fraction 2^b · (k/T)^N of the assignments. Keeping every solution would also contradict the tracking the sources describe, in which knowledge no longer used is given up.
  - Within one member's visits the problem is the same on every visit, because each visit starts the member's world from its start state; so there retention is required on every later visit, as the proposed form below states.
  - Separation and retention are jointly satisfiable and not trivially met: an agent that replays a route it has found re-solves on every later visit each member it solved once, wherever one common signal decodes goal satisfaction from the percept after every step (`replay_keeps`, `replay_solves`). With that same decoding hypothesis, concealment, a covering bound and an exploration schedule that meets the goals of more members than the bound by a finite visit, it separates (`replay_separates`); one grid world discharges these hypotheses (`witness_separation`). No frozen agent separates (`visits_need`). Retention alone is met by an agent that never succeeds; the conjunction is not. Replaying actions in the world is distinct from replaying stored experience for training, and these theorems prove neither the no-replay learning contract nor fixed resource bounds.
- **Open.**
  - Separation and retention for Acorn's executed agent. Today both are proved only for the replaying agent, a reference that shows these two postconditions can be met under its decoding and exploration hypotheses.
  - A precise form of (iii) for campaigns: from which memories the agent must be able to learn again, and within how many visits.
  - The attempt bound: how many failed visits learning may take, as a function of the class. It needs a theory of exploration for Acorn's setting.

*Proposed* Lean form of (i) and (ii):

```lean
def Separates (family : WorldClass I) (goals : family.Goals) (len k : ℕ) (A : Kernel.Agent I) : Prop :=
  ∃ (visit : ℕ) (solved : Finset family.Index),
    k < solved.card ∧ ∀ i ∈ solved, SolvesOnVisit family goals len A visit i

def Retains (family : WorldClass I) (goals : family.Goals) (len : ℕ) (A : Kernel.Agent I) : Prop :=
  ∀ i visit later, visit < later →
    SolvesOnVisit family goals len A visit i → SolvesOnVisit family goals len A later i
```

## Fork F3: the world may restart; the agent never does

This is the owner's decision.

**In plain words.**
The agent is never reset: its memory carries across every visit, every stop and every resumption.
The world may restart, between visits, on an ARC-AGI-3 reset or when the host stops, and each restart is part of the class's declared dynamics.

- **Source.** In Sutton and colleagues' reward-respecting subtasks, the agent interacts with its environment "in a sequence of episodes", each beginning in one fixed start state, and "termination resets the state", while the policy the agent follows "gradually approaches an optimal policy" ([[10]](#r10), Section 2). So this work on options and planning sets its subtasks in a world that restarts under a learner that continues across episodes. The Alberta Plan's agents are "long-lived" and, if they learn, learn "on every time step" ([[3]](#r3), introduction and "Research Vision"). No source states that the agent is never reset; that rule is Acorn's.
- **Acorn's argument and theorems.**
  - A world that persists between attempts can hold what the agent's memory does not. An agent that follows a step counter until its percept shows the goal met, and then takes an action that keeps it met, keeps every goal it has met although its memory reads no percept (`park_keeps`). In such a world no frozen-agent bound on later visits follows, and a learner that beats the first-visit bound shows nothing a frozen agent could not.
  - Visits restart the world and not the agent: each member returns to its own start state between visits, so on every visit every frozen agent solves at most the covering bound (`visits_need`), while the learning agent's memory carries over.
  - ARC-AGI-3 games restart: RESET "Initializes or restarts the game or level state", and in a game-over state it is the only valid action ([[14]](#r14), "Actions"). A contract that forbade the world to restart would exclude these worlds.
  - A stop does not reset the agent: resumption restores the saved state exactly (`load_saved`).
- **Open.**
  - No host loop of Acorn yet returns a world to its start state between attempts, and no theorem relates a host loop to `Kernel.visits` ([design](design.md#goals-the-observation-conceals-and-visits)).
  - A crash in the middle of an attempt is a restart the visits model does not cover.

## Fork F4: how guarantees for exploring agents are stated

This was decided on the owner's behalf.

**In plain words.**
A guarantee about an agent that explores with its random generator may be stated as holding on all but a stated fraction of runs, under the explicit assumption that the generator's draws are ideal: independent and uniform.
That assumption is a hypothesis of each such theorem, never an axiom, and it is listed in the mission theorem's trusted base, together with the acknowledged gap between ideal draws and Acorn's actual generator.
Where a guarantee needs no randomness, it holds on every run.

- **Source.** Reinforcement-learning theory states guarantees for learning agents in probabilistic forms. Differential Q-learning converges "almost surely" if the MDP is communicating, the solution of its Bellman equation (Equation 5) is unique up to a constant, step sizes decrease appropriately, every state–action pair is updated infinitely often and the ratio of update frequencies stays finite ([[12]](#r12), Theorem 1, Section 2). UCRL2's regret bound holds "With probability of at least 1 − δ" in every finite MDP of finite diameter with random rewards in [0, 1] ([[13]](#r13), Theorem 2, Section 2). The probability is that of the random process the environment and the algorithm generate together ([[13]](#r13), Section 1); UCRL2 itself chooses each action deterministically from its optimistic policy ([[13]](#r13), Section 3), so there the probability comes from the MDP's random transitions and rewards. The sources do not say that an exploring agent must draw random numbers, nor how an ideal random draw relates to a concrete generator.
- **Acorn's choice: probability is a modelling option, not a requirement.**
  - Concealment does not force random exploration (*argued*): where a goal's solution is one of finitely many candidates and each visit can try one, an agent that tries a new candidate on each visit succeeds within as many visits as there are candidates, on every run. Acorn's separation theorem takes a deterministic schedule of exploration (`replay_separates`), and one grid world discharges it with fixed walks (`witness_separation`).
  - Where a guarantee does rest on the agent's draws, it is stated over the ideal model, with the fraction δ of failing runs given. The fraction of failing runs is chosen over an expected count because separation and retention are properties of one run: a bound on that fraction says how often a run fails, which an expectation does not.
  - The gap is explicit. Acorn's generator is deterministic: seeded word streams after SplitMix64 and xoshiro256** (`Acorn.Rng`). Acorn proves exact counting facts about it, such as how many 64-bit words its range selection maps to each value (`current_range_card`), and these give a distribution only under the hypothesis that the source word is uniform. That the generator's outputs may stand in for ideal draws is an acknowledged assumption of the trusted base, not a theorem.
  - This trades strength for a proof route: a guarantee under the ideal model is weaker than one counted exactly over the generator's 2^64 seeds. Every theorem that uses the model names its assumption, so the trade stays visible.
- **Open.** A guarantee counted exactly over the generator's seeds, with no assumption. Acorn has no proof route for it today; a related property of Acorn's hash functions over all 2^64 inputs is open as [#184](https://github.com/rbeauchamp/acorn/issues/184).

## The mission theorem and its ladder

Put together, under F1 to F4, the mission is one theorem for each chosen class of a ladder of classes. The class, goals, visit length, covering bound and learning preconditions are fixed for that theorem; the conditions of `BigClass` alone are not sufficient premises.
For the executed agent from its initial state s₀, with work and size measures and bounds fixed by the interface and configuration, the proposed conclusion is the conjunction of:

- the resource bounds stated by the proposed StreamResourceBounds predicate;
- the separate once-only, no-replay contract, causal dependence, host isolation and exact resumption of contract 3, linked to the executed learning and lifecycle operations;
- separation as stated by the proposed Separates predicate for that class;
- retention as stated by the proposed Retains predicate for that class.

Each class theorem must establish its bigness conditions and state and justify its goal-information and exploration premises independently of these conclusions. The replay comparison uses exactly the decoding and exploration hypotheses described in contract 2; the mission theorem must establish how Acorn's executed agent uses the available information and explores. Neither the existence of feasible action sequences nor the comparison theorem supplies that linkage.
Where the agent's exploration draws on its generator, F4 turns separation and retention into statements about all but a fraction δ of runs, under the hypothesis that the draws are ideal.
The replaying agent establishes joint satisfiability only of separation and retention under its hypotheses, and no frozen agent meets separation (see [the postcondition](#the-postcondition-what-achieves-goals-promises)). Satisfiability of the complete conjunction with fixed resources and the learning and lifecycle invariants remains open.
The once-only, no-replay semantics and executed work measure (contract 3), each class's learning premises and, under F4, how the fraction δ depends on the class and the number of visits must be made precise before the full Lean theorem can be stated.

**Proof boundary.** Refining this contract into Lean requires preserving each cited theorem's quantified domain, hypotheses and exact conclusion: a frozen-agent upper bound supplies no learner's lower bound, a causal fold supplies no learning-update count, and a class-level existential set supplies no guarantee for every member. This correspondence with the prose is argued, not machine-checked; the missing semantics and execution linkage remain proof obligations, not established guarantees.

The ladder starts with the concealed targets of one grid world. Its later rungs include campaigns beyond the agent's capacity (contract 2 (d)), classes of Microduck scenes and classes of ARC-AGI-3 games; their order, like which world comes next, is not yet decided ([README](../README.md#purpose-and-worlds)).
"Any big world" is the limit of the ladder, never one theorem: each class is a step toward the mission, not a narrowing of it.

## Open obligations

Collected from the sections above. An obligation keeps its number when it is discharged: number 1 was the finite form of "no agent achieves goals in every world", now `no_agent_achieves_every_world` and `executed_defeated`; number 4's class is `witness_big`, and number 5's counting bound is `campaign_count`. Each of these is a lemma the mission theorem uses, not a mission result about learning.

2. That the host's run and the kernel's closed loop take the same actions, with the host's accounting composed along a run.
3. A theorem form of the viewer's rule: every message the core accepts from the viewer is a stop whose handling changes no learned field.
4. Goal-information and exploration premises sufficient for Acorn's executed agent, for a class of the grid world that meets contract 2 (a) to (c). Bigness alone does not supply them.
5. The choice of the agent configuration the counting bound of contract 2 (d) is first instantiated for.
6. A bound on the memories the executed agent can reach, which contract 3 and contract 2 (d) both need.
7. A Lean semantics of executed work and a work bound over it, and a separate once-only, no-replay contract with experience-consumption semantics and a proof over the executed updates and their host, checkpoint and resumption paths. The resource predicate and causal fold establish no such consumption rule.
8. A host loop that runs visits, related by a theorem to `Kernel.visits`, and an account of a crash in the middle of an attempt.
9. Separation and retention for the executed agent under each class's declared learning preconditions, jointly with the resource, learning and lifecycle invariants. The replay comparison establishes only the two postconditions under its own hypotheses.
10. A precise postcondition (iii) for campaigns: learning again what had to be given up.
11. An attempt bound, which needs a theory of exploration for Acorn's setting.
12. A guarantee for exploring agents counted exactly over the generator's seeds; until then, the ideal-draw assumption stays in the trusted base.
13. The classes of ARC-AGI-3 games ([#71](https://github.com/rbeauchamp/acorn/issues/71)) and Microduck scenes ([#173](https://github.com/rbeauchamp/acorn/issues/173)) stated over the interface, with proved preconditions or, where a world's rules are external code, preconditions stated as named hypotheses.

## References

1. <a id="r1"></a>Oak Lab, "Mission" ([page](https://oaklab.ai/mission)), read 2026-10-29.
2. <a id="r2"></a>Khurram Javed and Richard S. Sutton, "The Big World Hypothesis and its Ramifications for Artificial Intelligence", Oak Lab, 2024 ([page](https://oaklab.ai/posts/the-big-world-hypothesis)).
3. <a id="r3"></a>Richard S. Sutton, Michael Bowling and Patrick M. Pilarski, "The Alberta Plan for AI Research", [arXiv:2208.11173v3](https://arxiv.org/abs/2208.11173v3), 2023 (first version 2022).
4. <a id="r4"></a>Richard S. Sutton, "The reward hypothesis", RLAI open web page, September 10, 2004 ([page](http://incompleteideas.net/rlai.cs.ualberta.ca/RLAI/rewardhypothesis.html)).
5. <a id="r5"></a>Richard S. Sutton, Anna Koop and David Silver, "On the Role of Tracking in Stationary Environments", Proceedings of the 24th International Conference on Machine Learning (ICML), 2007 ([pdf](http://incompleteideas.net/papers/SKS-07.pdf)).
6. <a id="r6"></a>David Silver, Richard S. Sutton and Martin Müller, "Sample-Based Learning and Search with Permanent and Transient Memories", Proceedings of the 25th International Conference on Machine Learning (ICML), 2008 ([pdf](http://incompleteideas.net/papers/SSM-08.pdf)).
7. <a id="r7"></a>Saurabh Kumar, Henrik Marklund, Ashish Rao, Yifan Zhu, Hong Jun Jeon, Yueyang Liu and Benjamin Van Roy, "Continual Learning as Computationally Constrained Reinforcement Learning", [arXiv:2307.04345v2](https://arxiv.org/abs/2307.04345v2), 2023.
8. <a id="r8"></a>Shibhansh Dohare, J. Fernando Hernandez-Garcia, Qingfeng Lan, Parash Rahman, A. Rupam Mahmood and Richard S. Sutton, "Loss of plasticity in deep continual learning", Nature 632, 768–774, 2024 ([doi:10.1038/s41586-024-07711-7](https://doi.org/10.1038/s41586-024-07711-7)).
9. <a id="r9"></a>Richard S. Sutton and Shibhansh Dohare, "Maintaining Plasticity in Deep Continual Learning", keynote at the Conference on Lifelong Learning Agents (CoLLAs), August 24, 2022 ([slides](http://incompleteideas.net/Talks/plasticity.pdf)).
10. <a id="r10"></a>Richard S. Sutton, Marlos C. Machado, G. Zacharias Holland, David Szepesvari, Finbarr Timbers, Brian Tanner and Adam White, "Reward-Respecting Subtasks for Model-Based Reinforcement Learning", Artificial Intelligence, 2023 ([doi:10.1016/j.artint.2023.104001](https://doi.org/10.1016/j.artint.2023.104001); [arXiv:2202.03466v4](https://arxiv.org/abs/2202.03466v4)).
11. <a id="r11"></a>Tor Lattimore and Marcus Hutter, "Asymptotically Optimal Agents", Proceedings of the 22nd International Conference on Algorithmic Learning Theory (ALT), 2011, pages 368–382 ([arXiv:1107.5537](https://arxiv.org/abs/1107.5537)).
12. <a id="r12"></a>Yi Wan, Abhishek Naik and Richard S. Sutton, "Learning and Planning in Average-Reward Markov Decision Processes", Proceedings of the 38th International Conference on Machine Learning (ICML), PMLR 139, 2021 ([arXiv:2006.16318v3](https://arxiv.org/abs/2006.16318v3)).
13. <a id="r13"></a>Thomas Jaksch, Ronald Ortner and Peter Auer, "Near-optimal Regret Bounds for Reinforcement Learning", Journal of Machine Learning Research 11, 1563–1600, 2010 ([pdf](https://jmlr.org/papers/volume11/jaksch10a/jaksch10a.pdf)).
14. <a id="r14"></a>ARC Prize, ARC-AGI-3 documentation, "Actions" ([page](https://docs.arcprize.org/actions)), read 2026-10-29.
