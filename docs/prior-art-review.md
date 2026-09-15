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

A conditional checked transaction replaces an eligible imprint feature and clears dependent state. Its guard preserves the admitted disruption budget; reachability and useful turnover remain unqualified.

**Adaptation and rationale.** The local tester derives a receiving learner’s disruption threshold and requires small weight plus minimum step size in every consumer. Replacement-in-place bounds bank size; all trace and meta registers are cleared through the retirement transaction. A per-learner observation alone would admit a bypass.

**Contract and composition.** Acorn.FeatureLifecycle and AcornVerif.CurrentRetirement/CurrentRetirementRounding own the actual all-consumer guard, finite-word rounding and state transition. Conditional safety is separate from autonomous reachability, useful turnover and eventual retirement.

**Refutation attempt.** Review attacked candidate thresholds on units and the all-consumer condition. It rejected using a pruning increment or a horizon-times-step scale as the threshold and found that every consumer must satisfy the predicate. The admitted derived guard introduces no new tuned interval or replacement rate.

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
