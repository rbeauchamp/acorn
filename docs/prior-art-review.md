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

The arithmetic proof includes exceptional operands: zero products yield signed
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

Full initialized native zero-sector composition and the first-positive endpoint
remain unproved. In the ordinary discounted option-ending branch, the terminal
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
