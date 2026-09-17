# Prior-art admission and research qualification

This is a reference for researchers reviewing the implemented algorithms.
For an introduction, read [the design](design.md#the-learning-loop) first.
**PAR** means prior-art review; each numbered entry connects a mechanism to its
source, Acorn's adaptation, implementation/proof owners and remaining limits.
Some entries describe local constructions inspired by prior art, rather than
an unchanged published algorithm. Equation-level citations live with the code
and proofs.

## Admission standard

The objective is a complete, practical integration of general learning
mechanisms for this repository's continuing setting. A paper's use of a narrow
benchmark does not make its algorithm environment-specific. Reject on an actual
incompatible dependency or assumption, with evidence of where it enters the
mechanism. Reproducing published benchmark scores is an optional diagnostic,
not an admission requirement; reproducing the mechanism and accounting for its
assumptions are required.

**The admission bar.** Five criteria must all pass: **sound** (the derivation
reproduces), **in-setting** (one unbroken stream, batch size one, no replay, no
target network, no resets, bounded work per step), **semantically compatible
and non-degenerate in composition**, **affordable** (`O(active)` work, `O(d)`
memory), and **buildable** (specified precisely enough to implement without
inventing the missing mechanism). A nonzero update is insufficient if it learns
the wrong quantity. A known incompatibility or degeneracy needs a correction
with a formal characterization and closure at the strongest applicable layer
in `AGENTS.md`; disclosure or hoped-for tuning does not clear it.

**Material adaptation contract.** Each entry identifies the source mechanism,
its state, update equations, interfaces and load-bearing assumptions. For each
material change, record:

- **Kind:** equivalent specialization, published variant, proved source
  correction, or local approximation. Name any missing mechanism explicitly;
  a new algorithm is separate scope, not an undocumented integration detail.
- **Reason:** the integration need, why this choice meets it, and why a closer
  published construction is unsuitable or more costly. A change being bounded,
  published somewhere, or already implemented is not a sufficient rationale.
- **Consequences:** the meaning of the implemented quantities and which source
  identities, assumptions and guarantees survive, change or are lost. Identify
  the current indexed type, derivation, Lean theorem or admission gate that owns each
  claimed property; distinguish real-arithmetic identities from float behavior.
- **Composition:** reconcile units, time basis, state ownership, information
  available at the update, learned targets, normalization/reference levels and
  changing policies or models across interfaces. Numerical projections need an
  algorithmic interpretation as well as a state-safety argument. A clipped
  estimate does not inherit the unconstrained algorithm's guarantees.
- **Residual uncertainty:** name what is unknown and why it is empirical or
  outside the supported theorem assumptions. Uncertain usefulness may remain;
  a known contradiction in the claimed mechanism may not. Any measurement
  follows the proof-first and prospective study-plan rules in `AGENTS.md` and the
  [scientific evidence guidance](../CONTRIBUTING.md#scientific-evidence).

Apply this contract proportionately to material choices, in the existing entry;
do not require a new dossier for ordinary integration work. An exact published
variant need not acquire a new whole-system convergence proof to be usable.
An approximation is admissible only when the five criteria still pass, its
target and rationale are coherent, and claims are limited to what its owners
establish. A label alone is not a justification.

**Every verdict carries a recorded refutation attempt** by a fresh-context
reviewer whose only instruction was to break it — what was attacked, what it
found, what survived, and what was changed as a result. An unattacked verdict is
unfinished work.

Each entry has the shape the protocol prescribes: **Claim** · **Derivation**
· **Setting** · **Cost** · **Adaptations** · **Composition** · **Verdict** · **Proof of any
correction** · **Refutation attempt**.

## Default promotion and demotion

Admission permits an explicitly selectable research integration. It does not
promote that integration into an implicit ordinary-runtime selection. An
admission verdict of **adopt** below means the mechanism satisfies its stated
technical contract; current default qualification is recorded separately.
Default selection requires the qualification decisions below.

Before promotion, record all five decisions in the relevant PAR entry:

| Requirement | Evidence required before default use |
|---|---|
| Correct and compatible | Pass admission, close known semantic defects, and name the compiler-backed owner and scope of every claimed invariant. |
| Stated benefit | Define the improvement in goal achievement, adaptation, a necessary capability, or resource efficiency, with stream conditions and horizon. |
| Convincing evidence | Prove derivable claims. Name each irreducibly empirical UNKNOWN and register its estimand, comparator, meaningful margin, uncertainty method and assumptions, population, selection history, and stopping rule before outcomes. |
| Acceptable tradeoffs | Meet declared lifetime memory, latency, stability and performance-loss limits. A benefit on one measure does not excuse a failed constraint on another. |
| Actual composition | Bind the complete source/configuration, initialization, learned state, interfaces and comparison arms. Confirm empirical promotion claims on fresh data after development and selection; identify a reproducible fallback. |

For empirical performance promotion, the appropriate uncertainty bound must
clear a predefined practically meaningful improvement, on the stated estimand.
A positive mean or a small p-value alone is insufficient. Cost or capability
promotion must establish that benefit while satisfying a predefined acceptable
performance-loss margin. Fix the numerical margins for the objective before
observing outcomes; do not invent universal percentages or retrofit margins to
an existing result. Report negative and inconclusive results and account for
multiple comparisons, selection, dependence, missing/failed runs and exclusions.
The [scientific evidence guidance](../CONTRIBUTING.md#scientific-evidence) owns full protocol, registration,
retention and reproduction requirements. Creating a protocol does not authorize
execution; the smallest informative empirical setting remains the last resort.

Uncertainty-aware evaluation is motivated by Agarwal, Schwarzer, Castro,
Courville & Bellemare, *Deep Reinforcement Learning at the Edge of the Statistical
Precipice*, NeurIPS 2021, §4.1, PDF p. 5: “reporting interval estimates”
([paper](https://proceedings.neurips.cc/paper_files/paper/2021/file/f514cec81cb148559cf475e7426eed5e-Paper.pdf),
opened 2026-09-05). That paper studies multi-task deep-RL evaluation; it does not
validate a particular uncertainty method or sampling model for Acorn. The
promotion margins, fresh confirmation and demotion rules here are repository
policy, not attributed paper results.

| Finding | Default decision |
|---|---|
| Correctness or composition defect | Repair or disable the affected integration regardless of its measured score. |
| Credible underperformance without a previously accepted compensating benefit | Demote it and use the qualified fallback for the affected composition. |
| Missing or inconclusive promotion evidence | Keep it experimental; absence of a demonstrated loss is not promotion evidence. |
| Declared benefit and all tradeoff requirements met | Promote with an explicit decision and evidence record. |

A foundational mechanism needed for the learning discipline may carry an
explicitly accepted cost. The owner must accept the necessity, bounded cost,
evidence obligations and reconsideration condition before outcome access.
“It might help eventually” is not an exception, and an after-the-fact mission
rationale cannot convert a negative result into promotion evidence.

Qualification attaches to an integration in a composition, not to an algorithm
for all settings. Material changes to learning equations, interfaces, features,
reward/control criteria or selection rules require reconsideration. Prove
equivalence when available; otherwise disclose what evidence no longer
transfers and keep the changed mechanism experimental pending qualification.
Review the decision with a fresh-context refutation attempt. A deterministic
audit pins the chosen behavior.


### Current default qualification

No agent configuration is approved as an implicit runtime default. The status
labels below distinguish technical integration from evidence of useful learning:

- **provisional-reference:** an implemented reference mechanism with stated
  adaptations and contracts, without qualified benefit in the current agent.
- **research-only:** an explicitly selectable research integration, without
  default qualification.
- **demoted:** explicitly ineligible for default use; retained for research.

PAR-9, PAR-10 and PAR-12 are research-only; PAR-15 remains demoted.

| PAR | Decision | Intended mechanism | Limit | Next step |
|---|---|---|---|---|
| PAR-1 | provisional-reference | SwiftTD | Qualification pending | Preserve contracts; qualify prospectively. |
| PAR-2 | provisional-reference | Swift-Sarsa | Qualification pending | Preserve contracts; qualify prospectively. |
| PAR-3 | provisional-reference | Horde | Qualification pending | Preserve contracts; qualify prospectively. |
| PAR-4 | provisional-reference | Generate and test | Qualification pending | Preserve contracts; qualify prospectively. |
| PAR-5 | provisional-reference | Reward-respecting subtasks | Qualification pending | Preserve contracts; qualify prospectively. |
| PAR-6 | provisional-reference | Potential-based shaping | Qualification pending | Preserve contracts; qualify prospectively. |
| PAR-7 | provisional-reference | Options and interruption | Qualification pending | Preserve contracts; qualify prospectively. |
| PAR-8 | provisional-reference | Temporally extended exploration | Qualification pending | Preserve contracts; qualify prospectively. |
| PAR-9 | research-only | Intra-option value learning | Qualification pending | Preserve contracts; qualify prospectively. |
| PAR-10 | research-only | Derived exploration rate | Qualification pending | Preserve contracts; qualify prospectively. |
| PAR-11 | provisional-reference | Bounded-disruption retirement | Qualification pending | Preserve contracts; qualify prospectively. |
| PAR-12 | research-only | Ranked learned subtasks | Qualification pending | Preserve contracts; qualify prospectively. |
| PAR-13 | provisional-reference | Option models | Qualification pending | Preserve contracts; qualify prospectively. |
| PAR-14 | provisional-reference | Background planning | Qualification pending | Preserve contracts; qualify prospectively. |
| PAR-15 | demoted | Differential control | Qualification pending | Preserve contracts; qualify prospectively. |

### PAR-1 · SwiftTD

[Source](https://rlj.cs.umass.edu/2024/papers/RLJ_RLC_2024_111.pdf). Execution owner: `Acorn.SwiftTd`.

Adaptive sparse TD with per-feature step sizes. Projection, trace pruning and meta-register re-anchoring are declared adaptations. The contracts below describe their finite-word state and update semantics.

**Adaptation and rationale.** Binary unique ActiveSet inputs specialize the paper’s feature factors to one on the active set; sparse eligible-set iteration avoids full sweeps. The scaled trace increment is bounded by the overshoot budget, not the sum of raw step sizes. Projection admits stored weights; pruning and re-anchoring control finite-state storage but alter the unconstrained recurrence.

**Contract and composition.** AcornVerif.MetaGradient states the hand-transcribed recurrence and discrepancy identities; external transcription fidelity remains assumed. AcornVerif.CurrentLearner and AcornVerif.CurrentLearnerArithmetic link state/update contracts to the executed owner.

**Refutation attempt.** The recorded independent review challenged overshoot, sparse cost, register timing, transcription and bounds. It established that the budget concerns scaled trace increments, that the paper also uses sparse loops, and that re-anchoring withdraws the weight increment. It rejected attributing gamma-derived value bounds to log step sizes. These distinctions limit the claim here.

### PAR-2 · Swift-Sarsa

[Source](https://arxiv.org/abs/2507.19539). Execution owner: `Acorn.Sarsa`.

On-policy per-action learners with semi-Markov credit. The declared Sarsa substitution does not implement every control variant; corrected meta-gradient and duration credit must retain their executed owners.

**Adaptation and rationale.** One persistent value-difference register and per-action learners specialize the step-size machinery to on-policy control. Semi-Markov duration catch-up is needed at meta decisions; primitive credit uses executed actions each learning step. The eligibility set, not only the active feature set, owns update cost.

**Contract and composition.** AcornVerif.CurrentControl and AcornVerif.CurrentTemporal connect to execution. AcornVerif.CurrentPower.pow_one_word supplies the one-step power reduction. Tie handling treats values within the admitted numerical band as tied. The corrected meta-register recurrence is a stated departure from the printed listing.

**Refutation attempt.** Independent review checked the chosen-action update, shared register and one-step reductions, and found the undeclared register deviation, eligible-set cost unit and approximate tie band. The corrected register discipline is the recorded source adaptation.

### PAR-3 · Horde

[Source](http://www.incompleteideas.net/papers/horde-aamas-11.pdf). Execution owner: `Acorn.Demon`.

Parallel GVF prediction enters representation. Cumulants and horizons are declared D5; recursive changing features and policies limit transfer of fixed-policy analysis.

**Adaptation and rationale.** Parallel bounded GVFs specialize the broader Horde architecture; predictions feed other features to support an online representation. Fixed horizons/targets are D5 and on-policy updates replace the full general off-policy construction. Changing predictions, policies and adaptive steps violate fixed-feature/stationary assumptions.

**Contract and composition.** AcornVerif.CurrentPrediction and Acorn.Handcrafted.PredictionControl own bounded predictions and their use. Bucket admission constrains the output range; reachability is a separate property. The policy, representation and step sizes evolve during the run.

**Refutation attempt.** Independent review challenged attribution, convergence hypotheses, target specializations and reachability. It rejected applying fixed-policy analysis with adapted steps and rejected inferring reachability from a range proof. The terms predictions as knowledge describe this implementation rather than a quoted paper theorem.

### PAR-4 · Generate and test

[Source](http://www.incompleteideas.net/papers/MS-AAAIws-2013.pdf). Execution owner: `Acorn.Features`.

Fixed random projection generation over a hand-authored channel layout. Generation and bounded-disruption retirement are distinct mechanisms; only imprint units are eligible for retirement.

**Adaptation and rationale.** The fixed bank generates random projections over D1 channels to keep storage bounded and construction reproducible. This is the generator half; PAR-11 owns the local tester. Candidate features still have learned output weights, so their fixed input projections do not make utility estimation impossible.

**Contract and composition.** Acorn.Features and Acorn.FeatureLifecycle admit dimensions, unique active indices and replacement identity. The construction does not implement every tester in the source; tester selection must respect continuing operation and absence of additional tuned thresholds.

**Refutation attempt.** Independent review checked generator/reset mechanics and rejected the argument that fixed random units cannot be tested because they have no learned parameters: their output weights are learned. The admitted mechanism is bounded generation; representation quality is the subject of F3.

### PAR-5 · Reward-respecting subtasks

[Source](https://arxiv.org/abs/2202.03466). Execution owner: `Acorn.Options`.

Skills receive host reward with learned stopping bonuses. Ranked hashed slots select candidate subtasks using learned magnitudes.

**Adaptation and rationale.** Host reward remains in each skill’s cumulant, with a learned feature-specific attainment bonus where ranking finds a candidate. This supports reward-respecting subtasks without a manually selected subgoal list. The hashed-slot magnitude is a proxy, and the neutral fallback differs from the paper’s nonzero prescribed stopping value.

**Contract and composition.** Acorn.Options and Acorn.FeatureRanking own the stopping/selection definitions; AcornVerif.Options states the return identities. Bonus and host-value coordinates must match the policy/sample owner.

**Refutation attempt.** Source review checked strict comparison, stopping equations and neutral fallback. It classified the stopping function as an adaptation rather than an exact instance of the paper at zero bonus; subsequent composition review traced the policy/sample ownership instead of inferring learned-value accuracy from return algebra.

### PAR-6 · Potential-based shaping

[Source](https://ai.stanford.edu/~ang/papers/shaping-icml99.pdf). Execution owner: `Acorn.Options`.

Finite-return coordinate identities preserve the stated terminal and bootstrap terms. Shared-stopping identities do not establish host-policy invariance with changing critics or an arbitrary stopping objective.

**Adaptation and rationale.** Potential shaping uses the source’s discount-coordinate relation. Finite activations must include actual terminal/bootstrap terms; subtracting an initial potential is insufficient to establish policy invariance when the stopping objective changes. Inverse coordinates are needed before comparing option and host estimates.

**Contract and composition.** AcornVerif.Options and the executed Acorn.Options definitions own the terminal telescoping and shared-stopping identities. These compare the stated returns under their hypotheses, not arbitrary objectives or moving critics.

**Refutation attempt.** Independent review rejected a finite-telescoping argument used as a policy-invariance proof, corrected the activation-total interval and identified the missing inverse shaping coordinate at interruption. The retained identities concern the actual terminal and common-coordinate quantities.

### PAR-7 · Options and interruption

[Source](http://www.incompleteideas.net/papers/SPS-aij.pdf). Execution owner: `Acorn.Temporal`.

Typed option lifecycle and semi-Markov updates retain actual accumulated reward and duration. Shared units and strict advantage govern interruption.

**Adaptation and rationale.** Option-selecting updates accumulate actual reward and duration at decision boundaries. Trace catch-up is a local extension that decays registers without intermediate increments; it is not attributed wholesale to the options theorem. Primitive control uses PAR-9 credit rather than a second catch-up update.

**Contract and composition.** Acorn.Temporal, Acorn.Handcrafted.AgentEpisodes and AcornVerif.CurrentTemporal own lifecycle/time-base contracts. Acorn.Features.CreditGap supplies register decay identities. Strict interruption compares compatible quantities; inaccurate critics do not gain a policy-improvement guarantee.

**Refutation attempt.** Independent review attacked k-step trace decay and found that the stated no-increment decay composes mathematically. It identified the Dutch-register time-base mismatch and interruption quantity substitution, and separated the local trace extension from the source’s semi-Markov backup.

### PAR-8 · Temporally extended exploration

[Source](https://arxiv.org/abs/2006.01782). Execution owner: `Acorn.Exploration`.

Persistent exploration has a bounded duration. The local capped duration law is D3; support and useful goal discovery are separate obligations from probability admission.

**Adaptation and rationale.** Persistent action runs follow a capped floor-inverse-uniform duration law. It is a tail-equivalent surrogate for the published zeta law, chosen as the explicit local D3 construction; it is not exact source sampling. Serving a run is deterministic, so a universal positive support floor is unavailable at those steps.

**Contract and composition.** Acorn.Exploration and AcornVerif.Exploration own the actual duration/range definitions and stated mathematical distribution scope. The duration and normalization theorems state their action-set and distribution assumptions.

**Refutation attempt.** Independent review checked the inverse-uniform off-by-one and normalization argument, and rejected exact-zeta, implicit-cap and overbroad action-domain wording.

### PAR-9 · Intra-option value learning

[Source](http://www.incompleteideas.net/papers/SPS-aij.pdf). Execution owner: `Acorn.Handcrafted.TemporalControl`.

Primitive action learners receive the executed stream, including option steps. This is an on-policy Sarsa specialization with actual terminal/span semantics; it is not the full off-policy intra-option algorithm.

**Adaptation and rationale.** On-policy Sarsa credit updates the primitive learner from each executed learning-step action, including option execution. This uses otherwise discarded experience without replay; it is a local specialization rather than the source’s full off-policy option-augmented Q-learning algorithm. Frozen control excludes updates explicitly.

**Contract and composition.** Acorn.Handcrafted.TemporalControl and AcornVerif.CurrentControl bind credit to the actual action/terminal semantics. AcornVerif.CurrentPower.pow_one_word closes the one-step duration reduction. Greedification with respect to an estimate is not policy improvement with respect to the true value function.

**Refutation attempt.** Independent review traced all credit branches for dropped rewards, wrong actions and duplicate updates. It rejected a source dangling equation reference, a theorem-shaped improvement claim and omission of the option-augmented maximization domain. The one-step power reduction has a universal implementation-linked owner.

### PAR-10 · Derived exploration rate

[Source](https://arxiv.org/abs/2006.01782). Execution owner: `Acorn.Exploration`.

The rate is derived from active optimizer state; duration remains D3. Empty eligibility, optimizer coupling, support and resource limits are explicit.

**Adaptation and rationale.** This is a local construction, not a rate formula taken from the cited duration paper. It derives a receiving controller’s probability from active optimizer state to remove a clock schedule without adding a separate intrinsic-reward channel or replay memory. It remains coupled to optimizer parameters; no universal exploration floor or independent tuning claim follows.

**Contract and composition.** Acorn.Exploration admits the rounded aggregate probability and configuration-indexed rails. Empty eligible sets use the declared fallback after transient clearing. Meta/skill rate reads do not occur on every world step, so their cost cannot be amortized as if they did. Duration remains D3.

**Refutation attempt.** Independent review rejected comparison against a nonexistent universal support guarantee: deterministic served exploration already lacks it, and removing an annealed floor broadens the limitation. It located the range obligation in the receiving configuration and final rounded mean, not merely individual log step sizes.

### PAR-11 · Bounded-disruption retirement

[Source](http://www.incompleteideas.net/papers/MS-AAAIws-2013.pdf). Execution owner: `Acorn.FeatureLifecycle`.

A conditional checked transaction replaces an eligible imprint projection and
clears dependent state. The exact machine prediction-change theorem concerns a
singleton active feature. Autonomous positive reachability and useful turnover
remain unqualified.

**Adaptation and rationale.** The local tester derives a receiving learner’s disruption threshold and requires small weight plus minimum step size in every consumer. Replacement-in-place bounds bank size; all trace and meta registers are cleared through the retirement transaction. A per-learner observation alone would admit a bypass.

**Contract and composition.** `Acorn.FeatureLifecycle.success_iff`, `refusal_iff`
and `candidate_first` own the receiver-bound, atomic transaction. At the actual
post-learning `Agent.retire` boundary, replacement occurs exactly when the mode
is not frozen, history has unused capacity and a strictly newer clock, and some
bank unit's hashed slot satisfies every reader's strict weight-magnitude bound
and numerical lower-rail equality. The first such unit is selected immediately;
this conditional selection statement assumes no future adaptation or fairness.
`CurrentReplacement.retirement_enabled_iff`, `agent_retirement_count` and
`act_history_count` compose those owners with the executing schedule. `Agent.act`
advances the clock, encodes the current bank with prior prediction feedback,
executes temporal selection and primitive/demon learning, then attempts retirement.
`Agent.act_execution` and `Agent.prefix_path` connect the same definitions to the
host input fold; callbacks and compiled native-route admission retain their
existing trust boundaries.

The scan includes nine primitive rows, four meta rows, all three skills' nine
policy rows and three model reader positions, and eleven demons: 60 reader
positions. Discounted models alias reward in the duration position, giving 57
physical learners; no stored consumer is bypassed. A unit is a projection-bank
position, whereas its hashed slot is shared weight storage. Replacing a projection
retains that unit-to-slot hash. `candidate_alias_minimal` proves that a later alias
can never be first candidate, for any state. Other early units can also precede a
particular candidate repeatedly if they become eligible again; there is no
fairness or distinct-unit retirement quota.

`CurrentRetirement` and `CurrentRetirementRounding` supply the singleton active
feature's exact rounded prediction change, not a bound for arbitrary ordered
binary32 sums, new generated activations, action selection or long-run return.
`CurrentLearner.retire_registers` and the complete-consumer/reset owners cover
stored legality, knowledge and transient clearing; feature-reference and refresh
owners retain temporal/objective identity and fresh encoding order. These safety
claims do not establish sufficient evaluation, utility, or eventual floor learning.

**Exposure and writes.** The following boundaries determine the actual stored
reader's adaptation history; inactive features and inactive readers differ.

| Owner/boundary | Effect relevant to reachability |
|---|---|
| `NumericState.initial` | Zero weights and role-derived portable-log initial beta. `initial_above_floor` checks strict machine ordering for all three roles, independent of the criterion. |
| `firstLoopElement` | Updates only eligible indices. Projects weights and beta; weight clipping reanchors beta and clears the local meta-gradient inputs. Rounded meta-updates need not decrease beta. |
| `secondLoopElement` | Updates active indices of the selected learner; decreases beta only when the ordered active-alpha sum strictly exceeds its receiving budget. Pruning and trajectory clear remove transients, not learned weights/beta. |
| Primitive/meta control | Each credited controller visits all rows' existing eligibility; only its chosen row runs loop two. A cold unselected primitive row has no eligibility, so even arbitrary shared error cannot adapt it. Meta credit occurs at meta boundaries, not every primitive action. |
| Skill policy/model | Only invoked skills learn. Begin clears policy transients and primes model traces; the first returned action skips a completed model transition. Later steps use actual activation age; terminal credit closes that owner. Neutral skills remain readers. Discounted model input is the base set; differential input also includes the age indicator. |
| Planning | Updates meta option weights, not beta or primitive learners. Model prediction is read-only. |
| Assignment refresh | Complete identity includes the bonus word. A change installs a fresh skill policy/model and resets its meta row. Detached terminal credit belongs to the old objective. `installed_veto` identifies the immediate cold-model veto; subsequent learning is a separate boundary. |
| Retirement/restore | Retirement resets every reader of the slot to zero weight and initial beta with all per-index registers cleared. Restore admits primary knowledge and clears transients, preserves admitted history, and starts models cold. `restored_veto` rules out immediate eligibility from primary checkpoint admission alone. |

`CurrentControl.credit_initial` and `CurrentReplacement.initialized_path_refuses`
prove the cold primitive-row obstruction on actual finite input paths, with no
reward-sign, numeric-regularity or policy-fairness premise. Inputs may include
environment accounting, attempt-triggered refresh requests and stop; clear and
restore delimit a different exposure history. The omitted action is read from
executed decisions, not supplied as a policy choice. `short_prefix_refuses` proves
non-vacuity for every action prefix of length below nine; the induction also covers
longer prefixes omitting an action. This is a class of executions, not permanent
global blockage. An inactive slot may still have eligibility from prior exposure,
and another projection or authored feature may activate the same hash slot.

**Short invocations.** A second obstruction persists through terminal weight
credit. A demon reader with initial beta has an actual portable alpha below
1/19990. `CurrentRetirement.initial_demon_no_overshoot` bounds the ordered rounded
sum and excludes overshoot on at most 1900 active slots. Starting a model
trajectory clears `p` and `h`; its first returned option action performs no model
step. If it then ends, terminal credit sees zero `p`, so the finite meta product
adds zero to beta. Clipping also reanchors beta to the same initial word. The
terminal clear removes the sensitivity assembled during that credit before the
next invocation. `one_action_trajectory_cold` proves this with a finite target
of magnitude at most 2^32 and arbitrary legally stored weights, deriving the
intermediate finiteness from the actual initialization, prediction and arithmetic.
It assumes neither zero reward nor a guard outcome.

`CurrentReplacement.first_option_model`, `ending_option_model`,
`one_action_models_beta` and `model_begin_beta` connect the result to the actual
model callbacks and every finite repetition. `reward_model_veto` then blocks the
complete ensemble regardless of other consumers' exposure or stored weights.
The enclosing full-agent scheduling argument is structural, as set out beside
these proofs: idle and primitive decisions, served exploration, planning and
prediction reads leave models alone; only invoked skills receive these callbacks;
unchanged assignments retain the model, changed assignments create another cold
one, and detached credit cannot rewrite its replacement. Induction before a
putative first retirement therefore rules it out when all option invocations end
before a second returned action and their initiation encodings satisfy the bound.
This enclosing short-invocation argument is not a separate machine-checked
`AgentPath` theorem; the omitted-primitive result above is.

These input/exposure conditions are non-circular and describe an inhabited class
at the admitted callback interface. `Skill.goal_ends` makes goal feedback a
sufficient early-ending condition independently of the selected action.
`quiet_patch_sparse` bounds every default-size observation with both optional
food/deer tile channels absent by 1712 encoded features, allowing all imprint
units to activate and arbitrary kinds, task coordinates, inventory and cached
predictions. Every world-produced reward meets the finite target premise
(`world_reward_regular`). This does not prove that the endogenous world and
curriculum generate every such callback sequence, or that short invocations
occur forever. Longer invocations and denser encodings are outside this result.

The causal limitation is trajectory sensitivity being cleared while learned
weights persist, combined with a tester that requires a lower-rail beta in every
reader. Mere invocation count, primitive action coverage, nonzero terminal credit
or small weight does not remove it. A possible correction must derive which
sensitivity state belongs to stored weights across an invocation boundary.
[SwiftTD](https://rlj.cs.umass.edu/2024/papers/RLJ_RLC_2024_111.pdf) Appendix A.2,
equations (28)–(32), and Algorithms 1 and 3 supply the
sensitivity recurrence; they do not specify Acorn's begin/terminal/pruning reset
policy. Retaining an auxiliary register alone would conflict with
`CurrentLearner.Supported`, which currently requires all nine registers to be
zero outside eligibility. A corrected boundary would need a revised support and
readiness contract, an exact machine update correspondence, clipping/pruning and
objective-reset laws, and a progress result for the complete consumer schedule.
No such behavioral correction is implemented here. A separate utility or
maturation criterion would require its own semantics and admission; deleting
the floor condition or a reader is not a justified repair.

**Candidate episode boundary and realization gap.** The local machine identity
`CurrentRetirement.episode_sensitivity_anchor` makes the alignment obligation
precise. If trajectory registers `p`, `z`, `zBar` and `hOld` are zero and both
`h` and `hTemp` contain the same finite word H, the existing non-overshooting
second-loop element gives a finite `p` numerically equal to H and leaves beta
unchanged. Write `a = (eta / eta) * exp(beta)` and
`z = 0 + a * (1 - 0)`, with every operation evaluated in binary32. Its exact
stored `hTemp` is `(H - 0 * (z - a)) - H * a`, and `zBar` is
`0 + a * ((1 - 0) - 0)`. These are ordered word expressions; the theorem does
not replace them with real arithmetic or assert that all intermediate words
are finite. The next unclipped first-loop visit reads this `p` in
`project(beta + ((metaStep / exp(beta)) * (delta - vDelta)) * p)` and assembles
`(hTemp + delta * zBar) - zDelta * vDelta` before pruning. Clipping instead
reanchors beta and zeros the incoming sensitivity terms. This is a conditional
local law, not a modified episode callback or a path from initialization.

A candidate boundary would transfer the post-credit `hTemp` to both `h` and
`hTemp`, clear `hOld`, the six trajectory registers, eligibility and aggregates,
and retain weights/beta. Its proposed support contract separates those six
trajectory registers from the three sensitivity registers; readiness still
requires unique eligibility and nonzero eligible traces. Pruning, clipping,
retirement, objective replacement and restore retain their deliberate forgetting
semantics. This requires deriving the transfer *after* clipping/pruning, not
recovering discarded pre-credit sensitivity. The existing full-reset `clear`
contract is unchanged. Policy `beginOption`/`Controller.terminal` need a separate
shared-error, off-row derivation as well as model begin/terminal: aligning only
models cannot establish complete-reader progress. None of this proposed boundary
contract is installed in executing code.

The positive composition obligation is a stable ownership window in which every
physical reader receives sufficiently many actual finite meta increments m with
`-1 <= m <= -2^-18`, other beta writes do not increase it, and the same hashed
slot's weights are strictly below each receiver's threshold at a common scan.
The proposed addition margin `betaNext <= max(floor, beta - 3*2^-20)` and the
realization of its premises both remain unproved; neither is an admitted progress
theorem. In particular, two candidate input constructions fail:

- The sparse no-food observations used above give the `near_food` demon only
  zero cumulants (`Cumulant.eval`, signal 5). In the finite-arithmetic branch of
  a zero-knowledge trajectory, zero prediction/error and sensitivity propagate
  zero meta increments. Such a visit has m = 0, contradicting `m <= -2^-18`.
  With initial beta, the existing sparse-sum bound also excludes overshoot.
  This rejects that candidate under its regularity premise; it does not supply
  a new universal trace-finiteness or full-agent persistence theorem.
- Independently prescribing alternating signed targets is incompatible with the
  callbacks. Every demon cumulant is an indicator, and the discounted model's
  continuation target is gamma times the projected nonnegative meta-policy
  maximum. Native goal endings additionally force reward one, so forcing every
  invocation to end by goal cannot independently alternate its reward-model
  terminal targets. Raw callback admission is broader than native-world output.

A realizable family must therefore derive negative residual-times-sensitivity
products from these coupled targets and actual policy draws, with simultaneous
small weights and stable ownership. The anchor identity does not discharge that
obligation, justify a behavior change, or select disposition A, B or C. These
failed candidate premises do not establish that substantial redesign is needed.

The symbolic `CurrentReplacement.booleanObservation` / `booleanResult` family
uses eleven independent Boolean inputs at the admitted callback boundary.
`boolean_cumulants` identifies every actual signal with its corresponding bit;
`boolean_encoding_bound` bounds every resulting encoding by 1656 active slots
when tilings are at most eight and bank size at most 512, for arbitrary admitted
feedback predictions and bank contents. The count is 122 tile words, two
energy/day words, two no-task words, six inventory words and at most eleven
prediction words, followed by the existing encoder bound. `boolean_prefix_admitted`
constructs an endpoint and `AgentPath` through the actual `Agent.runPrefix` for
every finite Boolean input list, including from `Agent.initial`. Actions, RNG,
planning writes, feedback and retirement remain those of the existing agent.
This is an inhabited input language, not an eligibility or native-world witness:
its independently chosen axe, day and goal bits need not obey world dynamics.

`neutral_interruption_iff` gives the actual discounted neutral stopping comparison
under finite predictions and remaining duration: current policy maximum is
strictly below the stopping estimate. `neutral_terminal_error_nonnegative`
uses the executed terminal shaping and binary32 subtraction: when the finite
saved value is no greater than that estimate, their numerical difference has
magnitude at most 512, and the carried `vDelta` is zero, the error is nonnegative.
The 512 envelope is the existing rounded-subtraction theorem's domain, not an
assertion about arbitrary predictions. `first_option_policy` composes the actual
begin, draw and first temporal credit: all policy weights are unchanged, the
saved value is the drawn action's original prediction, and the shared accumulator
is zero. `clear_values_step` derives this from empty first-loop eligibility and
the second loop's write set, for arbitrary raw credit words and either criterion.
The remaining terminal composition must relate that saved prediction to the
next ordered policy maximum and its stopping comparison; no positive sensitivity
is inferred from current `begin`.

Longer invocations remain a candidate under the current mechanism. The first
returned action skips model credit, but later continuations execute the first
and second loops and can transfer `hTemp` through `h` into `p`. Their necessary
progress condition uses the actual coupled model error, including saved
prediction and `vDelta`; repeated exposure does not imply a negative product or
a decrement that survives rounding. No initialized Boolean prefix currently
establishes those margins and simultaneous strict-small-weight bounds for all
57 physical learners (60 reader observations) at one retirement boundary.
Staggered progress must also bound positive drift, planning writes and resets;
aliases, bank-order selection, event capacity and clock admission still apply.
These auxiliary contracts do not establish initialized joint progress or justify
any runtime correction.

**Refresh interference at the executed scan.**
`CurrentReplacement.TwoRefreshChanges` requires a pending refresh and two distinct
skill slots whose full `sameAssignment` comparisons against the current
Demon-0 `rankAssignments` are false, including the stored bonus bits.
`act_two_refresh_changes` proves that, for the discounted criterion, a callback
with these incoming conditions and a returned meta-decision records no retirement
and leaves every slot ineligible. The actual `selectWithOperations` closes a
previous option before refreshing, preserving its objective identity and the
ranking inputs. The installation fold initializes both changed models; planning
and meta credit preserve them, and dispatch writes at most one skill. The other
model survives `finish` cold. `cold_model_refuses` therefore rejects the
**pre-retirement** transaction, and `retire_cold_model` makes the actual retirement
call an identity. This is not an inference from a post-replacement reset.

The proof follows `TemporalControl.step` and `Agent.act`, including the actual
encoding, policy draw, closing path and common credit. Its domain allows arbitrary
observations and raw reward words and requires no sparse encoding, fairness or
assumed floor attainment. The returned meta-decision identifies an executed free
boundary; served exploration, hierarchy-disabled selection and continuing options
return none. Two changed identities ensure an untouched witness regardless of
the draw. A sole changed-and-selected skill is outside this obstruction. The
premises are operational comparisons, but no initialized native path realizing
them is established here. This conditional result narrows a candidate common
eligibility window: such a window cannot coincide with this refresh class. It
neither settles longer invocations nor establishes permanent blockage, positive
complete-reader reachability, or necessity of a new utility architecture.

**Initialized zero sector and continuation bootstrap.**
`CurrentRetirement.ZeroKnowledge` constrains stored weights, per-index
`deltaWeight`, and carried `vOld`/`vDelta` to the two finite zero encodings.
The actual constructor satisfies it. The executed first-loop traversal, including
swap-remove pruning, preserves it under zero error and update accumulator;
the second loop preserves zero weights and sums only zero updates. Consequently
actual zero-reward `step`, `beginTrajectory`, and zero-target `terminalStep`
preserve this sector for arbitrary active sets and raw trace/sensitivity words.
No beta-initiality, floor attainment or raw-register finiteness follows.

Separate numerical contracts supply prerequisites for a finite-register argument.
`CurrentState.log_step_beta_interval` places every admitted beta in `[-24,0]`.
`CurrentPortable.exp_floor_word` follows the actual classifier, reduction,
ordered polynomial and normal narrowing; `CurrentLearnerArithmetic.alpha_lower`
then gives the numerical lower bound `2^-40` for every legally stored alpha.
Together with `alpha_numeric`, this is a finite positive bound, not an
ideal-function approximation or alpha-monotonicity theorem.
`mul32_nonnegative_error` and `div32_normalization_error` retain explicit
`2^-20` local operation budgets; `trace_increment_small` composes the executing
normalization denominator and alpha multiplication into `0 <= q <= 1.01`.
The actual ordered alpha sum supplies its finite-rate premise.
`meta_scale_finite` derives finite execution of the meta-step/alpha quotient for
every legal beta. `discounted_demon_decay` checks the configured g99 demon's
actual rounded product of gamma and lambda is finite and in `(0,0.941]`.
For finite operands and exact intermediate magnitude at most `2^M`,
`0 <= M <= 40`, `mul32_finite_error` and `sub32_finite_error` derive finite
packing and error at most `2^(M-24)`. `div32_finite_error` retains the larger
existing division radius `2^(M-22)` and requires a numerically nonzero denominator.
None of these contracts bounds arbitrary incoming traces/sensitivities or
establishes finite-register closure under learning. Exceptional later meta products,
beta projection and overshoot remain mechanisms that an execution-linked
reachability or obstruction argument must cover.

`CurrentRetirement.ColdBox` states the candidate single-demon register bounds for
the g99 discounted configuration and capacity at most 16384. It reuses zero
knowledge, support/reference legality, eligible uniqueness and signed-zero
sensitivities. `cold_box_initial` proves the actual constructor's base case;
`cold_box_clear` proves preservation by actual transient clearing. The predicate
does not require admission readiness at callback boundaries; the base cases assert
no finiteness of arbitrary uncleared or restored states.
The local `cold_first_weight` and `cold_first_meta` contracts derive finite signed-zero
updates and no clipping before projection; `cold_first_beta` then preserves the
visited beta word. Strictly negative legal rails exclude zero-sign ambiguity in
that word identity. `cold_first_trace` and `cold_first_registers` retain actual
decay, rounding and pruning comparisons; `cold_first_pruned` combines the executed
clear/retain branch with a finite visited trace in `[0,61]` and zero knowledge.
Actual `learnFirstLoop` empties stored eligibility before traversing a separate
worklist. The proof-only `ColdWork` observes `ColdBox` with that worklist installed
as eligibility, without changing the executing state. `cold_work_entry` and
`cold_work_finish` bridge the actual entry/final installations;
`cold_work_contract` supplies existing support, reference and uniqueness facts.
`cold_work_first_element` transfers the local contracts without assuming an
intermediate `ColdBox` of the executing state. `cold_work_first` and
`cold_work_prune` preserve all bounds through one member visit and actual
clear/swap-remove, using existing frame/support/uniqueness owners.
`cold_work_go_preserves` follows the actual recursive first-loop equations,
carrying `ColdWork` through member/prune steps and installing the final worklist.
`cold_box_first_preserves` derives public first-loop `ColdBox` preservation from
the actual stored-empty entry. Both use the configured decay and signed-zero
error/accumulator; neither assumes a desired output invariant. All-word beta
tracking remains unproved across the traversal.
`ColdTracePrefix` records `[0,61]` only for positions before the actual cursor.
`cold_work_go_trace_bounds` uses unique visits and actual swap-remove framing:
a swapped-in tail at the unchanged cursor remains unprocessed. At termination,
listed indices satisfy the completed prefix and unlisted indices are zero by
support. `cold_box_first_trace_bounds` derives the empty prefix at actual public
entry, so callers need no extra processed-prefix premise. Its final `[0,61]`
bounds combine with `ColdBox` preservation for finiteness; `Ready` alone is not
the numeric proof. Second-loop and begin/step/terminal preservation remain
unproved. No beta progress or complete-reader replacement result follows.

The zero-knowledge proof includes exceptional operands: zero products yield signed
zero or NaN, and the actual weight projection maps NaN to zero while clipping
clears `deltaWeight`. Private intermediate classification uses the standard
logical float model's canonical NaN. Public conclusions concern finite zero
storage; native IEEE arithmetic, NaN classification/projection, and compiler
correspondence retain the trust boundary in `Acorn.Arithmetic`. The proof uses
unpacked constructor cases, not word or trajectory enumeration.

`zero_continuation_agent_initial` connects this sector to every actual initialized
discounted skill's continuation learner. `zero_continuation_skill_begin`,
`zero_continuation_skill_step`, and `zero_continuation_end` follow the concrete
model operations. A positive reward alone cannot change continuation weights
when the terminal meta value is zero: reward and continuation have different
executed targets. `zero_continuation_close` preserves all retained continuation
learners through the actual close, including discarded detached-owner results.
These statements impose no independently selected action or finite-trace premise.

`CurrentControl.ZeroController` carries the zero numerical rows and shared Sarsa
lags. `zero_values_step` follows the actual all-row first credit, optional restart
clearing, and selected-row second loop. The old snapshot and reward being zero
suffice even for arbitrary bootstrap and decay words: `zero_first_snapshot`
includes zero-or-NaN errors in the projection/clipping argument, avoiding a
separate portable-power finiteness assumption for this controller property.
`zero_draw_policy_step` uses the actual RNG draw and its producing snapshot for
arbitrary duration. `zero_snapshot_best` derives the old maximum from stored rows;
`zero_continuation_close_snapshot` uses precisely that old meta snapshot in the
actual discounted close, rather than postulating an independent terminal word.

`zero_ranking_advance` derives Demon-0's zero target from the actual reward
indicator in `PredictionControl.advance`, while leaving all other demons and
observation-dependent feedback unrestricted. Its zero weights exclude every
candidate in `rankAssignments`, including aliases. `zero_neutral_refresh` then
proves that consuming a request with already-neutral skills preserves the entire
consumer/representation/cache/closing state; no assignment reset is introduced.
These are actual component transitions from compatible zero-sector constructors,
not an assembled native learning trajectory.

`ZeroModel` covers both actual discounted scalar learners through construction,
begin, continuing zero reward and zero-reward/zero-meta termination.
`zero_model_target` derives the fresh projected planning target from those stored
learners for arbitrary actual age-augmented inputs. `zero_plan_identity`,
`zero_controller_plan` and `zero_planning_controller` then prove whole numerical
state, controller and ordered planning-fold identities respectively. Cache,
error and planning-clock observations may change; cached predictions never supply
the target. These identities require incoming zero sectors, without constraining
beta, traces, caches or gain.

`zero_gap_accumulate` preserves signed-zero deferred reward at every stored
byte age under each current value rule. It reuses `CurrentPower.pow_unit` for all
UInt32 exponents and checks only the four closed rule choices; finite-power
multiplication preserves both IEEE zero signs. Closed/skip/close retain or clear
the reward by construction, including saturation of the byte counter.
`neutral_potential` identifies the actual neutral-interest coordinate;
`zero_neutral_targets` checks the executed discounted cumulants.
`zero_neutral_terminal_snapshot` consumes the actual old meta snapshot and
preserves the neutral option policy, including frozen activation, assuming its
previous potential is false.

`ZeroNeutralSkill` combines the actual neutral interest, all policy rows/shared
lags and both discounted model learners. `zero_neutral_skill_initial` derives it
from the real constructor. `zero_neutral_skill_begin` composes the actual
begin/first-action result: the token freezes the cleared or frozen policy, model
begin primes both learners, and the age-zero action omits model credit. The
result has age one and false previous potential, for arbitrary rate and RNG.
`zero_neutral_skill_continuing` inverts the actual continuing decision to identify
its features, neutral potential and producing policy snapshot, then follows that
token through credit and the pre-increment model-age guard. This proves branch
closure; it does not assert that the branch occurs or supplies action coverage.
`zero_neutral_skill_end_snapshot` preserves the whole skill through termination:
policy and continuation use the same old meta value, while the reward model
consumes raw reward. Frozen modes and all terminal reasons retain their actual
write behavior. These endpoints preserve objective identity using the existing
owner equations.

`ZeroSkillState` adds the actual table and stored-phase boundary: all retained
skills satisfy that sector, and any stored active option has false previous
potential. `zero_skill_state_with_skill` preserves other option slots and phase;
`zero_skill_state_potential` derives admission from the actual selected table
entry. `zero_skill_state_dispatch` covers every successful actual meta dispatch,
including primitive selection, and follows the selected option's actual
begin/token installation. `zero_skill_state_continuing` starts from the stored
activation and actual continuing decision, clears occupancy, installs its step,
and preserves the returned coordinate through the optional meta-span increment.
These claims
do not prescribe a favorable owner, action or token.

`zero_skill_state_close_snapshot` preserves this table/phase invariant using the
current pre-close meta snapshot, whose controller must separately satisfy
`ZeroController`. Only a retained owner requires neutral coordinate premises;
the detached-owner branch discards its terminal result without imposing a zero
sector on that old owner. `zero_skill_state_close_active` derives the previous
coordinate and owner from stored occupancy, then clears phase and closes with
that old snapshot, leaving idle occupancy. This is still a partial state
invariant: primitive/meta learners, ranking demons, gaps, refresh and retirement
need their own joined callback composition.

`ZeroRankedState` joins the skill table/phase sector, primitive and meta
controllers, Demon-0 and the actual deferred meta reward. `zero_ranked_initial`
proves this predicate of `Agent.initial` with the current host
`researchProfile .ranked` and discounted criterion, for every feature
configuration, dimension and planning selection. The proof composes existing
constructor results and the actual neutral-interest table; it supplies no
favorable restored state, token or action. The other ten demons, beta and
unconstrained raw registers remain outside the predicate. This establishes the
constructor base case only.

`zero_ranked_prepare` preserves the joined predicate through actual
`TemporalControl.prepareSelection` for arbitrary active features and signed-zero
reward. Rate advancement and fresh model observations affect unconstrained
fields; `zero_gap_accumulate` handles the actual reward accumulation at every
stored gap age using the criterion's executed rule. `zero_ranked_draw_credit`
then proves consecutive actual `drawMeta` and `learnMeta` preserve the full join.
It uses `zero_draw_policy_step` with the same producing snapshot, receiver RNG,
owed gap reward and closing duration. No independently supplied decision or
reward creates a favorable endpoint. This theorem covers consecutive calls;
intervening writes in general boundary composition need their own frames.
`zero_ranked_refresh` lifts the existing neutral-refresh identity through actual
`refreshFree`, preserving joined storage while acknowledging the request.
`zero_ranked_plan` covers actual `planFree` with either concrete configured
`planningBoundary`; zero model targets preserve the complete meta controller,
while cache, error and planning-clock updates remain unconstrained.
`zero_ranked_dispatch` starts with the receiver's actual meta draw and follows
successful `dispatchMeta` through its own credit and selected primitive or skill
installation. The existing skill-table theorem supplies the final phase and
neutral skill sector; all other joined fields retain their actual credit result.
`zero_ranked_boundary` composes these owners for a successful ordinary discounted
`atBoundary` with no pending close. It uses `refresh_closing_none` to derive that
refresh cannot insert an intervening close before the produced meta credit.
These are preservation statements conditional on the executed successful result,
not proofs of action coverage, eventual selection or complete callback reachability.
`zero_ranked_serve` preserves the join for every successfully served exploratory
action, including its actual next phase, skipped meta span and cleared diagnostic
fields. `zero_ranked_continuing` consumes the stored active phase and actual
continuing token, using the same pre-step meta snapshot for comparison and reported
values. `zero_ranked_close_active` lifts the stored-owner close result to the full
join and idle phase; its terminal value is the old pre-close meta snapshot.
`zero_ranked_selection` composes actual preparation and every successful
`selectWithOperations` branch with the concrete model and planning owners.
It keeps served exploration first, derives neutral potential from the current
skill table, follows the actual continuing/ending result, and only dispatches a
new boundary after discounted close. Features, goal, declared payload and RNG
are unrestricted; incoming reward must be signed zero and the state must satisfy
the joined predicate. The proof does not assert successful action coverage or
that a goal callback escapes served exploration.

`zero_ranked_finish` joins actual primitive and Demon-0 completion through
`TemporalControl.finish_eq` and the recorded state's actual prediction view.
The profile-bound `creditMatches` field forces primitive per-step credit;
`zero_controller_step` covers its actual chosen action under either ownership
flag and signed-zero reward. Discounted centering returns that reward, and the
subsequent host gain/pending update preserves controller knowledge. The same
`PredictionControl.advance` supplies the existing Demon-0 zero-target proof;
other demons and observational fields remain unrestricted. Meta, skill/phase
and gap sectors are framed through the actual completion writes.
`zero_ranked_step` inverts successful actual selection and feeds its returned
state and decision to that completion. `zero_ranked_aligned_step` then uses the
actual wrapper's carried step equation under its explicit alignment premise,
reusing existing totality instead of constructing a parallel execution witness.
These establish local zero-reward step closure.

`CurrentRetirement.zero_retire` proves actual slot retirement preserves zero
knowledge through eligibility removal, register clearing, zero weight projection,
beta re-anchoring and aggregate clearing. It assumes no negligible/cold beta.
`zero_controller_retire` and `zero_model_retire` lift that result through complete
controller and discounted model storage, retaining the model's reader alias.
`zero_ranked_retire` covers both outcomes of actual receiver-bound retirement:
refusal is unchanged; success uses `Lifecycle.success_iff` to identify the actual
admitted replacement, then follows its complete consumer reset. Skills retain
neutral interests; the actual references retain phase and deferred reward.
There is no distinct-hash-slot assumption and no zero-weight retirement veto.
`zero_ranked_act` composes that result with clock advancement and the actual
`Agent.act_execution` correspondence. Its features are the advanced receiver's
current-bank frame; the correspondence supplies the actual local step and its
alignment/episode witnesses before retirement. One zero-reward action therefore
preserves the joined predicate for arbitrary observation and goal.

`RankedSurvivalPrefix` records successful edges of the actual first survival
attempt. Each edge requires successful `Attempt.sense`, uses its actual callback
choice, and requires that action's actual world transition before accounting.
`ranked_survival_native_step` checks correspondence with the optimized native
selection/environment stages; IO scheduling, observer delivery and successful
execution remain external boundaries. The relation adds no runtime history.
`survival_prefix_clock` derives physical time equal to the bounded attempt counter
from initial time zero. The UInt64 cap prevents wrap in this attempt; actual
survival completion produces zero reward before its positive duration and exactly
one at completion. `zero_ranked_initial_survival` specializes the resulting
zero-sector induction to successful `World.initial` and actual `Agent.initial`.
The action producing the terminal reward still consumes the previous zero reward.
The standard curriculum starts with survival duration 200. These conditional
invariants support the bounded initialized existence result below. A later
positive learning callback and complete-reader eligibility remain separate;
restored knowledge is outside the cold-construction result.

`finish_carried` proves successful attempt finalization retains the entire raw
result for every goal family. Existing `Attempt.start_carried` retains it when
the next goal is installed; a nonempty new attempt ignores carried completion
at counter zero. Thus its first successfully sensed callback consumes the old
terminal reward with the new goal's observation. Achievement advances to the next
goal; allowing two attempts does not repeat an achieved survival goal. A repeated
survival epoch requires actual curriculum/cycle progression, not an attempt-count
premise. At a final or stopping campaign boundary there is no extra learning
callback: recording a positive environment/attempt reward alone does not establish
positive learning exposure. A new campaign initializes its raw carry to zero,
even when it loads admitted agent storage. This is a finite-invocation exposure
limit, not permanent global replacement blockage or evidence for redesign.
Reach, collect and craft goals use the same completion-to-reward producer and
carry path; their actual body/inventory predicates can produce positive rewards.
The survival counter argument does not assert all native rewards are zero.

`CurrentRunner.survival_plan_exists` proves actual campaign admission for any
curriculum with at least two entries and a request with at least 200 steps and
two goals, including attempt-count normalization. `initial_cursor_exists` and
`achieved_next_goal` derive the actual cursor choices; `standard_first_goals`
identifies survival then wood collection for every seed and standard world.
These supply plan admission and cursor progression to the initialized survival
specialization below. Subsequent positive learning still needs its own composition.
`CurrentWorld.standard_config_exists` admits every supported standard side;
`standard_body_translation` excludes signed overflow within the actual sensor
radius, and `standard_spiral_coordinates` covers all actual spiral offsets and
closed cardinal directions. `word32_conversion` bounds the actual direct word
conversion by existing normalization/packing correspondence. `standard_scale_bounds`
places the actual constructor's scale in `[4, 2^29]`; `octave_scale_double` and
`standard_octave_scales` retain finite positivity through four actual scale
multiplications, with the loose upper bound `2^(29 + 2*count)`. This is a rounding
envelope, not an assertion of exact doubling. `coordinate_float_bound` handles
the actual sign-bit construction for coordinate magnitude at most `2^32`;
`coordinate_quotient_bound` then proves finite division and quotient magnitude
at most `2^32` for any finite scale at least four. The coordinate domain contains
the proposed standard-world margin `[-201, side + 201]`.

`floor_cast_neighbor` carries the quotient bound through the existing floor
magnitude enclosure, exact widening and executed signed quotient/clamp. Its
unsigned integer quotient is below `2^32 + 1`, excluding the maximal signed
endpoint and admitting the neighbor increment. `standard_terrain_success`
discharges both actual lattice admissions and the sample hypotheses of
`standard_terrain_of_samples`, using the existing recursive-fold composition.
It proves terrain success for every actual standard configuration, every salt
and every position with both coordinates in `[-201, side + 201]`. It assumes
neither sample success nor a chosen action/seed trajectory. No terrain quality,
walkability or allocation feasibility follows. The construction and bounded-step
compositions below use this terrain result. Arbitrary custom raw
scales remain outside this standard-configuration success theorem.

`standard_tileKind_success` preserves terrain success through the actual regrowth
classification. `standard_observeTile_success` derives each sensor coordinate
from the typed body and finite patch indices; arbitrary occupancy values and
deer coordinates cannot refuse observation. `standard_observe_success` composes
both actual row-major vector traversals structurally. The result covers
every state of an admitted standard configuration, without a restored-state or
learning-reachability premise. `CurrentRunner.standard_sense_success` derives
strict step room from the actual unfinished predicate and typed step bound,
then constructs the same owned input returned by `Attempt.sense`.
`standard_start_sense_success` discharges unfinishedness for any positive-cap
`Attempt.start`, even with a carried terminal result. The bounded environment-step
admission below is separate from learner callbacks and initialized-prefix composition.

`CurrentWorld.standard_countKindNear_success` proves the actual radius-four scan
succeeds for any tile kind and in-box center, using structural induction through
the checked range/list traversal correspondence. It derives every translated
coordinate's terrain margin without enumerating the cells.
`standard_considerSpawn_success` covers arbitrary signed coordinates and prior
candidates. Out-of-box coordinates return before terrain; admitted coordinates
complete both scans and the walkability/score branches. No minimum count,
walkable candidate or improved score is assumed. `standard_selectSpawn_success`
composes all three actual spiral loops using the checked traversal bridge with
the executed optional-return/current-best accumulator. The signed admissions
come from `standard_spiral_coordinates`; candidate handling retains the box
check before terrain access. Both loop continuation and early-return branches
succeed, including the legal center fallback after a complete scan. This is
spawn admission, not a terrain-quality or best-score guarantee.

`DeerInBox` describes every deer entry's coordinates in `[0, side)`, separately
from the population's typed capacity bound. `standard_placeDeer_success`
preserves this property from an in-box population through the actual two-draw
placement, including nonwalkable draws and full-capacity insertion refusal.
`standard_initializeDeer_success` carries it through the configured finite loop
using the original world and the changing population/RNG pair. The existing
range traversal proof now preserves an explicit invariant; its constant-true
specialization serves the scan and spawn claims. `standard_initial_success`
derives the empty population premise and composes both actual constructors,
proving successful standard-world construction with in-box initial deer.
The existing initial-fields theorem supplies the other construction fields.
`PositionWithin` expresses the signed per-coordinate envelope `[-n, side + n)`;
`deerInBox_iff_positionWithin` identifies its zero-step population case with
`DeerInBox`. `standard_wanderDeer_success` proves actual single-deer success and
an envelope advance by at most one for `n < 200`, for arbitrary world state and
RNG under the stated envelope premise. Closed direction deltas and the standard
side bound establish signed translation admission; the candidate fits the
proved terrain margin. The actual movement and walkability branches retain
their returned position and RNG without a probability or walkability premise.
`standard_wanderPopulation_success` lifts this result through the actual ordered
vector traversal under the RNG state transformer. Checked vector/array/list
correspondence and structural list induction retain the original world for
every entry and thread one produced RNG into the next invocation. The theorem
returns exact population length, the per-entry advanced envelope, and an
explicit ordered list-traversal equality with the same final RNG. Each entry
advances its envelope once, irrespective of population size.

`standard_foodTrials_success` admits any finite actual food search for standard
worlds and arbitrary RNG, retaining two-draw order and the first-grass-or-none
branches without a grass-existence premise. `standard_spawnFood_success` retains
the actual due/capacity guard, its branch without draws, and typed insertion.
`standard_passiveChange_success` composes population wandering before food,
preserving deer length and the advanced envelope. Its statement identifies the
intermediate deer RNG and the subsequent food result separately; the final RNG
may include food draws. World time, harvest state and goal carry no additional
hypotheses.

`standard_performAction_success` admits every actual action for arbitrary standard
worlds. Movement retains box rejection before terrain access; accepted positions
admit the actual enterable query, including boat/walkability refusal. Harvest uses
the typed facing position and existing harvest-key admission. Crafting failure,
insufficient food and bounded inventory/food operations retain their actual return
branches. `standard_payAndAct_success` includes exhaustion recovery and otherwise
uses the actual energy-updated world, without positive-energy assumptions.
`standard_step_success` composes this active result with `passiveChange` on the
actual acted world at its advanced time. Every action succeeds when input deer
satisfy `PositionWithin n` with `n < 200`; output length is unchanged and every
deer satisfies `PositionWithin (n + 1)`. Existing `World.step_clock`, `step_goal`
and `step_completion` supply the single final wrapping increment, goal/origin
preservation and returned completion flag. This is not a nonwrapping clock or
arbitrary-time deer-envelope theorem.

`CurrentReplacement.standard_ranked_survival_exists` discharges initialized
prefix existence for every actual standard configuration, typed feature
configuration/dimension/planning choice and cap at least 200. It selects one
successful `World.initial` result before quantifying over every length `n ≤ 200`,
with the actual cold ranked discounted `Agent.initial` and initial raw zero.
Structural induction constructs the existing `RankedSurvivalPrefix`: unfinishedness
follows from carried completion and remaining capacity, actual sensing admits the
input, the callback selects its action, and checked world admission supplies the
same `OwnedEnvironment.record` edge. No action list or successful-prefix premise
is supplied. Exact steps/time, goal/origin, deer length/envelope, raw-result
coherence, reward and completion are retained; the attempt is finished exactly
at 200. Nonterminal movement, harvest and other event fields need not be empty.
Existing zero-sector preservation applies through the goal-producing action.

`standard_campaign_survival_exists` derives actual standard configuration from
supported side bounds and actual campaign admission from requests with at least
200 steps and two goals. The actual initial cursor selects survival; the native
cold ranked discounted scalar constructor and initial behavior word specialize
the core theorem to a completed first prefix. The core prefix theorem itself
needs only the cap bound, not the two-goal request. At step 200 the environment
produces and carries reward one; its callback consumed the preceding zero reward.
`recordEnvironment` records lifetime accounting, not a new learning act. The
pure native-linked result does not assert successful IO, allocation, scheduling,
observer delivery or checkpoint restoration. The following composition supplies
the next callback; numerical bootstrap and complete-reader eligibility remain
separate obligations.

`standard_positive_callback_exists` starts from that actual completed prefix.
It derives successful `Attempt.finish` using actual observation admission and
identifies the exact `recordAttempt` update, terminal frame and achieved outcome.
World and the complete raw result are retained; accounting preserves the incoming
joined zero sector. The actual non-stopping `atAttemptBoundary` advances the
cursor to wood collection at index one, attempt zero and the same cycle.
`Attempt.start` installs that goal with origin at world time 200, resets the step
counter and preserves the entire carried result. Positive cap admits actual
sensing despite the carried done flag; no assumption says wood is still needed.
The theorem identifies both the selected agent and primitive action with the
actual finished agent's `Agent.act` on that observation, reward one and done true.
No extra world step or independently chosen action occurs. Other terminal event
fields retain their actual values. This proves positive-input exposure, not a
nonzero learned weight or a negative meta-update. The false stop argument names
the pure continuing branch; it does not assert that native stop, observer,
checkpoint or other IO effects return. No post-positive zero-sector assertion
is made.

The internal first-positive dispatch branch and positive learner image remain
unproved. In the ordinary discounted option-ending branch, the terminal
meta snapshot is read before close, refresh, planning and new meta credit; a
later positive meta update cannot change that earlier continuation target.
Served primitive exploration has priority over the goal check and may defer a
pending refresh until after Demon-0 reward learning. Thus a first goal does not
universally imply a free boundary or neutral ranking. The actual goal-action
owner, produced meta snapshot, and later policy/model bootstrap must be derived;
component zero closure does not supply those premises or a common eligibility
window for all 57 physical learners. No runtime behavior or disposition changes.

**Lifetime and persistence.** Every success appends exactly one event.
`FeatureHistory.LegalHistory`, `record_count`, `full_refuses`,
`record_excludes_same_clock` and `saturated_record_refuses_forever` limit ordinary
learning to the remaining bank-sized event quota and strictly increasing UInt64
timestamps. After recording at the saturated clock, no clock advance admits
another event. `Representation.identity` binds the bank and generator continuation
to reconstruction from the original seed and the entire event sequence; restoring
that admitted sequence does not renew it. Clearing or truncating history is not
a compatible replenishment scheme. Renewable turnover requires a separately
specified bounded reconstruction/persistence authority.

With bank size U, reader count R and storage dimension D, a scan visits at most
U times R slot predicates. Reset traverses those readers and their bounded eligible
storage; generator work draws 32 samples. The retained transcript has at most U
events, and reconstruction makes at most U replacement draws after bank creation.
These structural bounds do not imply indefinite liveness or physical latency.

**Refutation attempt.** Review attacked candidate thresholds on units and the all-consumer condition. It rejected using a pruning increment or a horizon-times-step scale as the threshold and found that every consumer must satisfy the predicate. The admitted derived guard introduces no new tuned interval or replacement rate.

The direct-write `retirement_predicate_reachable` theorem establishes single-reader
predicate inhabitation; it supplies no learning prefix. Positive reachability after
all readers receive adequate exposure remains **UNRESOLVED**, including simultaneous
floor attainment in the ordinary ranked discounted composition. The omitted-primitive
obstruction above also applies to other profiles/criteria because their actual
selection and credit branches preserve the proved primitive-row invariant. No
reward benefit, convergence, default promotion or change of utility semantics is
inferred from these proofs.

### PAR-12 · Ranked learned subtasks

[Source](https://arxiv.org/abs/2202.03466). Execution owner: `Acorn.FeatureRanking`.

Streaming ranking over GVF weight slots drives coalesced refresh at a free decision boundary. Complete assignment identity invalidates dependent knowledge. Hash collisions and proxy meaning limit interpretation; spatial comparison remains D2.

**Adaptation and rationale.** Ranking uses learned predictive weight magnitude to choose distinct tied blocks and derive attainment bonuses. Coalescing requests until a free boundary preserves an ending activation’s objective; full assignment identity invalidates dependent knowledge even when only the bonus changes. The rationale is bounded streaming discovery without an authored subgoal list.

**Contract and composition.** Acorn.FeatureRanking, Acorn.FeatureRefresh and AcornVerif.CurrentFeatureConsumers own selection/refresh and identity. Zero scores yield neutral skills rather than arbitrary noise. Scalar scores identify magnitudes; feature identity belongs to the assignment key.

**Refutation attempt.** Independent review challenged tied candidates, bonus-only changes, early-stream zeros and stopping invariance. It retained block exclusivity and neutral fallback, required complete assignment invalidation, and limited shaping invariance to trajectories with the same stopping value.

### PAR-13 · Option models

[Source](https://arxiv.org/abs/2104.08543). Execution owner: `Acorn.Models`.

Scalar models use bounded storage and explicit reward, duration and continuation targets. Sampled policy alignment and age-conditioned aggregate targets are local approximations; aligned expectation-model identities do not transfer automatically.

**Adaptation and rationale.** Scalar reward, duration and continuation models use linear storage instead of a full feature-transition model. This trades representation expressiveness for bounded memory. Maximizing scalar approximations does not inherit linear expectation-model equivalence; sampled policy alignment and age-bearing inputs constrain target meaning.

**Contract and composition.** Acorn.Models, Acorn.FeatureModelInput and AcornVerif.CurrentModels own model inputs, target bounds and terminal behavior. Targets retain raw reward/duration units; changing policies and continuations remain approximations. The terminal-discount discrepancy has a universal characterization in the model/proof owners.

**Refutation attempt.** Independent review rejected transferring fixed-linear equivalence through the implemented maximum. It traced terminal discount, actual meta-decision ownership and repeated-option age conditioning, retaining the storage rationale while narrowing convergence and accuracy claims.

### PAR-14 · Background planning

[Source](https://arxiv.org/abs/2202.03466). Execution owner: `Acorn.Planning`.

A fixed number of signed model backups occurs at decision boundaries without replay.

**Adaptation and rationale.** A fixed number of model backups at decision boundaries supplies planning without replay. Signed correction permits downward as well as upward value adjustment, while projection preserves stored-weight legality and trace registers remain unchanged.

**Contract and composition.** Acorn.Planning and AcornVerif.CurrentModels bind the three-backup schedule, primitive separation and preserved trace/lag registers to execution. Scalar continuation models and moving targets preclude an inherited fixed-point or coupled convergence guarantee.

**Refutation attempt.** Independent review examined error propagation, moving targets, trace ownership, work bounds and one-sided correction. The review retained signed updates and distinguished numerical containment from model quality.

### PAR-15 · Differential control

[Source](http://www.incompleteideas.net/book/the-book-2nd.html). Execution owner: `Acorn.Average`.

Reward minus estimated gain times duration supplies the continuing criterion. Gamma is one; existing rails impose a numerical budget. The reward-residual gain update and changing scalar models are specified below.

**Adaptation and rationale.** The continuing criterion uses reward minus estimated gain times duration with gamma one. The reward-residual gain variant is used with a shared control criterion; existing value rails are a local numerical approximation because general differential values have no discount-derived bound. Model queries carry actual policy/sample and activation-age meaning.

**Contract and composition.** Acorn.Average, Acorn.Models, Acorn.Planning, AcornVerif.AverageReward and AcornVerif.CurrentModelArithmetic own gain/return identities, the bound obstruction, model targets and stored arithmetic. The two-state family characterizes the obstruction to a transition-independent differential-value bound; the stored rail is an explicit numerical approximation.

**Refutation attempt.** Independent review traced every gain/value write, post-planning action ownership, repeated activation, raw target units and age-zero queries. Discrepancy identities distinguish known semantic incompatibilities from unmeasured usefulness. The integration remains demoted.
