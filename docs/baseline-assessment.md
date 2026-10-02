# Baseline assessment

Acorn's first goal is a baseline agent built from the current state of the prior
art in continual learning and planning. This page records an assessment of how
far the implementation meets that goal, measured against the published OaK and
Alberta Plan designs, and the conformance work it recommends.

The assessment was made against `main` at commit 86ce779 (2026-09-28), from
the executed definitions and the primary literature. No agent run informed it.
Status notes record what has changed since; the
[Acorn roadmap](https://github.com/users/rbeauchamp/projects/10) tracks the remaining work.

**Claim status.** Every claim below carries one of these labels:

- **Machine-checked**: a Lean theorem over the executed definitions, compiled
  by `./scripts/verify.sh` on the head that introduced it.
- **Argued**: derived by hand from the executed definitions or a closed form;
  not machine-checked.
- **Assumed**: a stated modelling assumption, such as an idealized random
  number generator.
- **UNKNOWN**: an irreducibly empirical quantity with no observation yet.

The findings are labelled F-A to F-F; the numbered F1 to F4 in the
[frontier](frontier.md) are research questions.

## Answer

**Partly.**

- **Learners: met.** Every one of Acorn's 57 learners is SwiftTD or Swift-Sarsa,
  transcribed with declared corrections
  ([PAR-1](prior-art-review.md#par-1--swifttd),
  [PAR-2](prior-art-review.md#par-2--swift-sarsa)). This matches OaK's
  requirement that each learned weight has its own meta-learned step size.
  GVF predictions are fed back as features, and nothing is replayed.
- **Architecture: shape only.** The FC-STOMP chain (feature construction,
  subtasks, options, models, planning) is wired, but two links run on local
  substitutes that drop the property their source relies on: the option models
  and planning. U3 replaced a third, the feature tester, with the published
  one. A composition defect (F-A) erased option learning until U1 repaired it,
  and a locally derived exploration rate made
  about 90% of early primitive steps random until U2 replaced it (F-C).
  Options learned only while executing until U4 (F-F).
- **Learning: UNKNOWN.** Whether the agent learns anything in its world has not
  been observed.

The defects survived for an instructive reason. Acorn's proofs state safety and
admission properties, such as "the stored state stays legal" or "this identity
holds". They did not state functional ones, such as "a skill keeps its learning
unless its unit changes" or "the planning backup equals the Bellman backup under
the current value". Proof-first development can state exactly these; the
missing invariants are the algorithmic ones. U1 added the first of them.

## Baseline scorecard

Verdicts:

- **Faithful**: matches the published mechanism up to declared,
  semantics-preserving adaptations.
- **Adapted**: a local change that keeps the mechanism's role.
- **Substituted**: a local construction that drops the property the source
  relies on.
- **Missing**: not present.

| Prior art | Alberta Plan / OaK role | In Acorn | Verdict | Evidence and consequence |
|---|---|---|---|---|
| IDBD → SwiftTD [[1]](#r1) [[2]](#r2) | Step 1; per-weight meta-learned step sizes | Every learner | **Faithful** | `NumericState.step` and its two loops transcribe Algorithm 1 of [[2]](#r2), with corrections declared in PAR-1. |
| Swift-Sarsa [[3]](#r3) | Step 4 (declared Sarsa in place of actor-critic) | Primitive, meta and option policies | **Faithful** | `Controller.valuesStep`: per-action value vectors sharing one error. The actor-critic departure is declared. |
| Horde / GVFs [[4]](#r4) | Step 3 | 11 fixed on-policy GVFs whose bucketed predictions are re-encoded as features | **Adapted, partial** | Horde learns each prediction from the snippets of experience relevant to it, which "requires off-policy learning", and uses GQ(λ) ([[4]](#r4) §4). Acorn's questions are fixed and on-policy ([D5](learned-only-binding.md#d5--prediction-targets--step-2)). Feeding predictions back is a genuine, limited predictive state. |
| Generate and test: generator [[5]](#r5) | Step 2 | 512 random projections over the 11 × 11 tile-kind patch and the task words | **Adapted** (after U3) | Before U3 the generator read only the kind patch; it now also reads the task words (`observationPatch`, `taskContext`), so units can conjoin task and layout. Inventory and energy are still excluded (F-D). |
| Generate and test: tester [[5]](#r5) [[6]](#r6) | Step 2: evaluate features and discard the less promising | Contribution utility over every stored reader, a maturity age and a declared replacement rate | **Adapted** (after U3) | U3 replaced the absolute, conjunctive guard with the published relative tester ([PAR-11](prior-art-review.md#par-11--generate-and-test-tester), [D7](learned-only-binding.md#d7--feature-tester-schedule--step-2)); turnover follows from the rate by construction over eligible units (`Lifecycle.test_accrual`, F-E). Adaptations: eq. (2) without the mean correction, and the rate accrued per eligible unit as in the authors' released code. |
| Reward-respecting subtasks [[7]](#r7) | Step 10: highest-ranked features become subtasks | Three slots from the positive Demon-0 weights of imprint units, with held bonuses | **Adapted** (after U1) | U1 made candidates sign-correct, the bonus held, and identity the unit alone. One deviation remains: subtasks are not restricted to features whose weight is sometimes high and sometimes low ([PAR-12](prior-art-review.md#par-12--ranked-learned-subtasks)). |
| Potential-based shaping [[8]](#r8) | Option learning aid | Present | **Faithful** | [PAR-6](prior-art-review.md#par-6--potential-based-shaping), with limits declared. |
| Options and interruption [[9]](#r9) | Step 10: option learning off-policy | Three options, 128-step cap, interruption, SMDP meta-credit | **Adapted** (after U4) | Before U4 only the executing option learned (F-F). Every option that is not executing now learns from the action taken ([PAR-17](prior-art-review.md#par-17--off-policy-option-learning)). The meta-controller's option values still learn by SMDP credit alone. |
| Intra-option primitive credit [[9]](#r9) | Data reuse | Primitive Sarsa learns from every executed step | **Adapted** | [PAR-9](prior-art-review.md#par-9--intra-option-value-learning). One of the links that genuinely supports the rest. |
| Option models [[7]](#r7) [[10]](#r10) | Step 10; the model predicts the state at option termination | Scalar reward and continuation models | **Substituted** | There is no transition part (`Model.terminal`). The continuation's terminal target is a meta-controller value, so it is a value estimator, not a model (F-B). |
| Planning [[7]](#r7) | Steps 7 to 10: imagined outcomes evaluated by the value functions | Three signed backups toward r̂ + ĉ at the current features, at free boundaries | **Substituted** | `PlanningResult.backup` has no look-ahead with the current value function; it distils a second estimator of the meta values (F-B). |
| Search control [[11]](#r11) | Step 9 | — | **Missing** | Planning happens only at the current state. |
| εz-greedy [[12]](#r12) | Step 9 exploration | Capped 1/n-tail duration ([D3](learned-only-binding.md#d3--exploration-duration--step-9)) and, since U2, a declared rate ε = 0.01 ([D6](learned-only-binding.md#d6--exploration-rate--step-9)) | **Adapted** (after U2) | The duration law is a tail-equivalent surrogate for the published zeta law. At 86ce779 the rate was a local derivation with no published source, starting near 0.63 (F-C); U2 ([#23](https://github.com/rbeauchamp/acorn/pull/23)) replaced it with a value the source uses. |
| Average reward [[13]](#r13) | Steps 5 to 7 | Selectable differential control, demoted; gain updated from the reward residual | **Adapted, partial** | Differential Q-learning updates the average-reward estimate with the TD error ([PAR-15](prior-art-review.md#par-15--differential-control)). Average-reward GVFs are absent. |
| Reward centering [[14]](#r14) | Steps 5 and 6 | — | **Missing** | A cheap, general fix for discounted methods with discount near 1. Acorn uses γ = 0.99 throughout. |
| Learned agent state [[15]](#r15) | Perception | Only the fed-back GVF buckets | **Missing** | Severe partial observability (an 11 × 11 view of a 1024 × 1024 world) with no learned memory. |
| Off-policy learning [[4]](#r4) [[7]](#r7) | Steps 3 and 10 | Options only | **Adapted, partial** (after U4) | Option policies learn by tree backup [[21]](#r21) and option models along frames whose action was selected with the option's own distribution ([[9]](#r9) §5). GVFs about other policies remain on-policy ([#16](https://github.com/rbeauchamp/acorn/issues/16)). |
| Utility feedback [[20]](#r20) | Step 11: feedback that assesses the utility of every element and replaces the least useful | — | **Missing (declared)** | The complete OaK loop is outside the implementation ([design](design.md#implementation-scope)). |
| Nonlinear continual learning [[6]](#r6) [[16]](#r16) | Continual deep learning | Linear learners only | **Missing** | Outside the baseline's scope, and the current research front. |

**Score.** Of 19 rows: 3 faithful (the learning core plus shaping), 9 adapted,
2 substituted (models, planning) and 5 missing, counting U3's tester and generator
and U4's off-policy option learning as adapted. The frontier and design
acknowledge utility feedback and learned agent state, and design Step 3 and
[PAR-3](prior-art-review.md#par-3--horde) declare the on-policy specialization
of the prediction questions; the other three missing rows
(search control, reward centering and nonlinear continual learning) were not
previously recorded.

Correctness of what exists (state legality, admission, numeric containment and
the proved identities) is strong and machine-checked. The weakness is fidelity
and composition, which the proofs did not state and so could not catch.

## Composition findings

Two links genuinely support the rest of the system:

- **SwiftTD under every learner.** Per-weight credit assignment protects each
  learner from the roughly 1,300 active features, most of them irrelevant to it.
- **Horde feedback and primitive credit on option steps.** Predictions become
  features, and executed option steps train the primitive controller (PAR-9).

The defining STOMP loop (subtask → option → model → planning → better
decisions) exists structurally. The findings below describe how it was broken
or neutralized. All six are argued from the executed definitions; none is
machine-checked or observed. The repairs of F-A, F-C, F-E and F-F are
machine-checked by the U1 to U4 theorems cited under each.

### F-A · Subtask churn erased options, models and meta rows

**Status: resolved by U1.** Argued at 86ce779; the repair is machine-checked.

At 86ce779, a subtask's identity compared both its unit and the exact bits of its
bonus, and the bonus was the unit's current Demon-0 weight magnitude, re-read at
every refresh. Any identity change reinstalled the skill with a zero policy and
model and reset its meta-controller row. Demon 0 updates a unit's weight on every
step where the unit has a nonzero trace and the TD error is nonzero; a trace lasts
about 190 steps before pruning (γλ = 0.99 × 0.95, pruned at a factor of 10⁻⁵).
A top-ranked unit is frequently active, so its bonus word differed at almost
every refresh. Refresh becomes pending on every achieved attempt and every new
curriculum cycle (`Refresh.request`). Success therefore reset the option policy,
model and meta row of most selected subtasks, returned their step sizes to their
initial values, and raised their exploration rates back to the initial rate
(F-C). The source instead sets the bonus weight to one of its higher values "so
that an option can be learned in preparation for the times at which it is high"
([[7]](#r7) §2, p. 8).

U1 made identity the unit alone (`Assignment.same`) and made refresh slot-stable.
`FreeDispatch.refresh_retains` proves, for every state and every Demon-0 weight
array, that the first slot holding a still-ranked unit keeps its policy, model,
cached prediction and meta-controller row, and that its held bonus never
decreases. A slot is now reinstalled only when its unit leaves the ranking or is
retired. How often that happens is UNKNOWN: it depends on the stream.

### F-B · The option model is a value estimator, so planning cannot plan

**Status: open; U5 addresses it.** Argued.

- **What the source specifies.** An approximate option model has a reward part
  r̂(x, o) and a transition part n̂(x, o) ≈ E[γᴷ x(S_K)] ([[7]](#r7) §4,
  eqs. (14)–(15)). Planning backs up r̂(x, o) + v̂(n̂(x, o), w) with the *current*
  weights w, by approximate value iteration ([[7]](#r7) §5, eq. (19)). When the
  value function is linear in the features, planning with an expectation model
  instead of a distribution model loses nothing ([[10]](#r10) §4); the same work
  shows that a *linear* expectation model is not always enough ([[10]](#r10) §5.1).
- **What Acorn's continuation learns.** It learns with cumulant 0, and its
  terminal target is γ times the meta-controller's value, at termination, of the
  meta action drawn there (`Model.terminal`, `PolicyDecision.continuation`). So
  ĉ(x, o) ≈ E[γᴷ Q_meta(x_K, O′)], with O′ the meta action drawn at termination
  and Q_meta as it was when each termination was learned.
- **What planning computes.** Planning moves Q_meta(x, o) toward r̂ + ĉ
  (`ModelPrediction.target`, `PlanningResult.backup`). That is an intra-option TD
  estimate of the SMDP Sarsa target for Q_meta(x, o). Planning therefore distils a
  second estimator of the same quantity at the current state.
- **The information limit.** A change in Q_meta at an outcome state reaches ĉ
  only through new real terminations of that option from each initiation
  context. With an expectation model, the same change reaches every predecessor
  on the next backup. Acorn's planning adds intra-option generalization and
  nothing else, so it cannot deliver the benefit that motivates planning in the
  source: fast adaptation when much of the environment's transition dynamics is
  stable ([[7]](#r7) §1). That needs a model of the stable dynamics, which Acorn
  does not learn.
- **The source's design presumption.** The source presumes option models to be
  accurate and stable while the approximate value function is not
  ([[7]](#r7) §5, p. 17). Acorn's continuation is exactly as unstable as the
  value function, by construction.
- **Scope.** Planning runs three backups per free boundary at the current
  features, never during options or served exploration. There is no search
  control (Step 9) and no planning on every step.
- **Why a scalar was chosen.** A dense expectation model over 16,384 features
  would need 16,384² ≈ 2.7 × 10⁸ weights per option. The Alberta Plan's answer
  is Step 8(d): a ranking of features that also determines which features enter
  the environment model ([[20]](#r20) p. 9).

This also explains why earlier target-contract reviews found no defect in the
model callbacks ([F1](frontier.md#f1--option-model-quality)). The callbacks
compute their target correctly; the target is the wrong quantity.

### F-C · The derived exploration rate started near 0.63

**Status: resolved by U2 ([#23](https://github.com/rbeauchamp/acorn/pull/23)).** Argued at
86ce779; the repair is machine-checked.

At 86ce779, every research profile except the annealed comparison used the
derived rate:

- **The rule.** The rate is the mean, over eligible features, of the normalized
  log step size ν = (β − ln η_min) / (ln η − ln η_min), falling back to its
  value at the initial β when nothing is eligible
  ([PAR-10](prior-art-review.md#par-10--derived-exploration-rate)).
- **Initial values.** With α_init = 5 × 10⁻⁵, η = 0.1 and η_min = 10⁻¹⁰,
  ν = 0.633. Option learners, with α_init = 10⁻⁴ and η = 0.25, give ν = 0.638.
- **Share of exploratory steps.** Persistent exploration serves D steps with
  P(D ≥ n) = 1/n capped at 128, so E[D] = H₁₂₈ ≈ 5.43. By a renewal argument,
  the fraction of primitive steps spent exploring is
  εE[D] / (εE[D] + 1 − ε) ≈ 0.90 while ε ≈ 0.63.
- **Options and the meta-controller.** Options act randomly on about 64% of their
  own steps, without persistence; the meta-controller chooses uniformly on about
  63% of its decisions.
- **No early decay.** With about 1,300 active features, Σα_init ≈ 0.065 < η, so
  the overshoot decay does not act at initialization; only the meta-gradient can
  lower β.
- **Unknown then.** How fast ε would fall in a run depended on the stream, and a
  reinstalled slot started again from the initial rate.

The published method declares ε for each experiment rather than deriving it: for
example 0.01 on CartPole, and 0.01 after an initial decay for the Atari agents,
with zeta-distributed durations (μ = 2) ([[12]](#r12) §4.1, Appendix B).

U2 made a declared ε = 0.01 the default as a new departure,
[D6](learned-only-binding.md#d6--exploration-rate--step-9): the primitive
controller, the meta-controller and every option read it in every research
profile except the annealed comparison, which keeps its schedule. PAR-10's
derived rate remains a research-only selection through the native rate words,
and the mutation-audit pins for the declared-rate and differential arms were
re-recorded. `TemporalControl.declared_rates` proves that, under the declared
rate policy, every consumer reads the declared word at every state, and
`TemporalSupport.branch_exact` that each exploration branch is an exact rational
comparison with that word.
`TemporalSupport.declared_branch_card` counts exactly the source words that
explore. Under an assumed uniform, independent draw, which the deterministic
generator does not supply, `ez_duration_mean` gives a mean run length of H₁₂₈ and
`declared_share_lt` bounds the expected exploratory share of primitive-boundary
cycles below 6%.

### F-D · The representation barely expresses task-dependent preferences

**Status: U3 ([#9](https://github.com/rbeauchamp/acorn/issues/9)) extended the
generator input to the task words; whether the bank finds the needed
conjunctions is UNKNOWN.** Argued for the pre-U3 representation, conditional on
equal prediction buckets and on no hash collision between layout features and
the other words.

Every raw feature is exactly one of: a hashed single sensor word, an imprint
over tile kinds, or one of 99 prediction buckets (11 questions × 9 levels)
(`observationWords`, `rawEncode`). All of them are hashed into the same 16,384
slots (`FeatIdx.fromHash`), and `unique` merges raw features that share a slot.
Tile words and imprints do not depend on the task, and task words do not depend
on the tile layout. The eight tilings are eight hashed copies of the same word;
they add robustness to collisions, not conjunctions.

**Lemma.** Suppose that in s and s′ no active slot is shared between a tile or
imprint feature and a task, inventory, energy, day or prediction word. Then
Q_a = u_a·φ(tiles, imprints) + v_a·ψ(task, inventory, energy, day, buckets),
where ψ holds every active slot outside φ. Take actions a and b and states s and
s′ that differ only in tile layout and have equal bucket features. If task τ₁
prefers a at s and b at s′, and task τ₂ prefers the reverse, no weights
represent both.

*Proof.* ψ(s) = ψ(s′) under each task, so the ψ term cancels in the difference
between s and s′. With d = (u_a − u_b)·(φ(s) − φ(s′)), τ₁ needs d > 0 and τ₂
needs d < 0. ∎

The standard curriculum places "collect wood" directly before "collect stone"
(`rawStandardCurriculum`); a tree on one side and a stone on the other, then the
mirror image, is this case. The designed escape is for the buckets to separate s
from s′ within each task, and they are coarse, undirected predictions. The other
escape is incidental: when a word active under only one of the tasks (a
differing task word such as the item code, or a differing inventory, energy, day
or prediction word) shares a slot with a tile or imprint feature present in only
one of s and s′, that slot's weight enters d under one task and not the other.
The meta-controller can still learn task-dependent option preferences, since
v_o·ψ(τ) is representable. Because the generator read only the kind patch, even
working retirement could not discover task × layout conjunctions. U3's imprints
also read the task words, so the lemma's hypothesis that imprints do not depend
on the task no longer holds for units that sample them.

### F-E · The retirement tester works against turnover

**Status: resolved by U3 ([#9](https://github.com/rbeauchamp/acorn/issues/9)),
which replaced the tester.** Argued for the earlier guard.

The published testers guarantee turnover with a replacement rate and protect new
units with a maturity age or an initialization at an order statistic
[[5]](#r5) [[6]](#r6). Acorn's earlier guard had four properties that worked
against turnover:

- **Distance to the floor.** It required β on the absolute floor ln 10⁻¹⁰. The
  initial β is ln(5 × 10⁻⁵), 13.1 nats above it, and one overshoot-decay step
  moves β by ln 0.999.
- **All readers at once.** The floor had to hold in all 57 learners (60 reader
  positions) at one scan.
- **No rate.** It had no replacement rate.
- **Reinstallation undoes progress.** Reinstalling a slot returns its nine
  option-policy learners, two model learners and one meta-controller row to the
  initial β. Before U1 this happened at most refreshes; now it happens when a
  slot's unit leaves the ranking.

Whether this conjunction is ever reachable was the question of issue
[#3](https://github.com/rbeauchamp/acorn/issues/3), closed as superseded when
U3 started; the issue and its kept branch record its evidence. U3's published
tester answers it by construction, and its safety obligation is local: a new
unit enters with zero outgoing weight in every reader
([PAR-11](prior-art-review.md#par-11--generate-and-test-tester)).

Turnover by construction is proved over eligible units: a replacement occurs
within ⌈period/k⌉ tests whenever at least k units are eligible at each
(`run_turnover`). Issue 9's wording over mature units does not hold, because a
unit held as an option objective is mature but not eligible away from a free
boundary and accrues no credit (U1's hold rule). The three slots hold at most
three units, so a replacement occurs within ⌈period/(k − 3)⌉ tests whenever at
least k > 3 units are mature at each (`run_mature_turnover`).

### F-F · Options learn from almost none of the experience

**Status: resolved by U4 ([#10](https://github.com/rbeauchamp/acorn/issues/10)).**
Argued at 86ce779; what the repair writes is machine-checked; the resulting
option quality is UNKNOWN.

At 86ce779 an option's policy and model updated only on steps where that option
was executing (`Skill.stepTemporal`). The Alberta Plan's Step 10 says option
learning "will need to be done off-policy" [[20]](#r20); the reward-respecting
subtasks paper updates every subtask's option off-policy on every step
([[7]](#r7) §3, eq. (10)), and intra-option learning updates every option
consistent with each action taken ([[9]](#r9) §§5–6). Combined with F-A's resets
and F-C's random option actions, options plausibly stayed near their initial
values. That extent is observable but was not observed.

U4 makes every option that is not executing learn from the action actually
taken, on every step of a learning hierarchy
([PAR-17](prior-art-review.md#par-17--off-policy-option-learning)). The
[U4 section](#what-u4-changed) lists what changed and what is proved.

**Verdict on composition.** The components coexisted far more than they
supported one another. The chain was wired, but F-A cut it periodically, F-B
neutralizes its planning end, F-F starved its option end until U4 and F-E left
its feature-construction end inert until U3.

## Measured against the published OaK and Alberta Plan designs

- **Matches.**
  - OaK asks that "all of its components learn continually" and that "each
    learned weight has a dedicated step-size parameter that is meta-learned
    using online cross-validation" [[17]](#r17). Acorn matches both.
  - Oak Lab's algorithms "learn in real-time without storing or replaying data"
    [[18]](#r18). Acorn matches this: batch size one, no replay, IDBD-family credit
    assignment.
  - A small agent in a big world [[19]](#r19): about a million weights against a
    1024 × 1024 world seen through an 11 × 11 window.
- **Models.** The Alberta Plan's base agent has a transition model that "predicts
  the state at the time the option terminates and the cumulative reward along the
  way", and imagined outcomes "are then evaluated by the value functions"
  ([[20]](#r20) p. 4). Acorn's model predicts no state (F-B).
- **Planning.** "On every step there will be some amount of planning"
  ([[20]](#r20) p. 4), with search control as Step 9. Acorn plans only at free
  boundaries, at the current state.
- **Subtasks and options.** Step 10 makes the highest-ranked features into
  reward-respecting subtasks, and its learning processes "will need to be done
  off-policy" ([[20]](#r20) pp. 9–10). Acorn's subtasks churned until U1 (F-A), and
  until U4 its options learned only while executing (F-F).
- **Feature finding.** Step 2 asks for a way of evaluating features and
  "discarding the less promising so as to make room for new ones"
  ([[20]](#r20) p. 7). Before U3, Acorn's tester did not rank and was not shown to
  replace (F-E); U3's tester ranks by contribution utility and replaces at a
  declared rate.
- **Temporal uniformity.** The plan's meta-algorithms for constructing
  representations or subtasks "operate on every time step" ([[20]](#r20) p. 2). Acorn
  triggers ranking from host attempt and cycle events. This is a mild, undeclared
  departure.
- **The route to representation search.** Swift-Sarsa is presented as opening
  the door to learning representations "by searching over hundreds of millions of
  features in parallel" [[3]](#r3), leaning on step-size credit assignment over
  large feature sets. Acorn's representation is 16,384 hashed slots; until U3
  its generator never saw the task.
- **Evaluation.** Every source above establishes usefulness empirically: SwiftTD
  on Atari prediction, Swift-Sarsa on an operant-conditioning benchmark,
  reward-respecting subtasks with planning curves in grid worlds. Acorn has no
  observation of learning. Under its proof-first policy that is deliberate, but
  whether the agent learns in its world is irreducibly empirical and still open.

Going by the published designs, the agent they describe differs from Acorn at the
model and planning links; U3 and U4 brought the feature-testing and
option-learning links to adapted forms of the published mechanisms. The foundation is
theirs: SwiftTD everywhere, reward-respecting feature-attainment subtasks, GVF
predictions as features, and continual operation without replay. Acorn's
machine-checked state legality and admission have no counterpart in that work.

## Conformance sequence

The recommended next step is baseline conformance: make each STOMP link do what
its source says, cheapest decisive fix first. Each unit is justified by
derivation, not measurement.

| Unit | Change | Source | Size | Decisive because | Status |
|---|---|---|---|---|---|
| U1 | Stable, sign-correct subtasks | [[7]](#r7) §2 eq. (4); Alberta Step 10 | S | Every later link lives in the state F-A erased | **Landed** ([#8](https://github.com/rbeauchamp/acorn/pull/8)) |
| U2 | Published εz-greedy with a declared ε of 0.01, replacing the derived rate in the default | [[12]](#r12) | S | Initial behaviour was about 90% random (F-C) | **Landed** ([#23](https://github.com/rbeauchamp/acorn/pull/23)) |
| U3 | Published tester: contribution utility with maturity and a replacement rate over imprints, and a generator input that includes task channels | [[5]](#r5) [[6]](#r6) | M | Makes turnover reachable by construction and lets feature finding reach task conjunctions (F-D, F-E) | **Landed** ([#9](https://github.com/rbeauchamp/acorn/issues/9)) |
| U4 | Options learn from every step: tree-backup learning of every option's policy, and model learning along frames whose action was selected with the option's own distribution | [[9]](#r9); [[7]](#r7) §3–4; [[21]](#r21); Alberta Step 10 | M | Removes F-F's data starvation | **Landed** ([#10](https://github.com/rbeauchamp/acorn/issues/10)) |
| U5 | Expectation model over a ranked small feature subset, with approximate value iteration and bounded search control over recent feature vectors | [[7]](#r7) §4–5; [[10]](#r10); Alberta Steps 8(d) and 9 | L, research | Only this makes planning plan (F-B) | Open ([#11](https://github.com/rbeauchamp/acorn/issues/11)) |
| U6 | Smallest prospective observation: the ranked agent against a uniform-random comparator, pre-registered, after U1 and U2 | [Scientific evidence](../CONTRIBUTING.md#scientific-evidence) | S | Answers whether it learns at all | Open ([#12](https://github.com/rbeauchamp/acorn/issues/12)); needs owner authorization |

U3 supersedes issue 3's reachability program: replacing the local tester with a
published one makes turnover reachable by construction, which removes the
question rather than answering it. Issue 3 was closed as superseded when U3
started, and its branch and in-progress evidence are kept.

The roadmap also tracks the missing published pieces that no unit covers:

- reward centering ([#13](https://github.com/rbeauchamp/acorn/issues/13));
- the Differential Q-learning TD-error update of the average-reward estimate
  ([#14](https://github.com/rbeauchamp/acorn/issues/14));
- search control beyond U5's minimum ([#15](https://github.com/rbeauchamp/acorn/issues/15));
- off-policy GVFs ([#16](https://github.com/rbeauchamp/acorn/issues/16); a
  [design proposal](off-policy-gvfs.md) is under review);
- learned agent state ([#17](https://github.com/rbeauchamp/acorn/issues/17));
- utility feedback ([#18](https://github.com/rbeauchamp/acorn/issues/18));
- nonlinear continual learning ([#19](https://github.com/rbeauchamp/acorn/issues/19)).

### What U1 changed

- **Sign.** Only units whose signed Demon-0 weight is positive are candidates, and
  that positive word is both score and bonus (`candidateOfWeight`). The `Bonus`
  type makes every selected bonus positive and finite at ranking, checkpoint
  admission and the diagnostic driver (`Bonus.finite_positive`).
- **Identity.** Objective identity is the unit alone (`Assignment.same`).
- **Held bonus.** The bonus is held from selection and, while the unit stays
  ranked, raised at each refresh to the current weight when that is larger: a
  running maximum of the weights seen at refreshes (`Assignment.retain`).
- **Slot stability.** A still-ranked unit keeps its slot and its learned state;
  only slots whose unit left the ranking are reinstalled (`rankAssignments`).
- **Retirement.** A held unit is retired only at a free boundary, where every
  slot holding it is released to the neutral objective
  (`FeatureRuntime.retire_releases`, `FeatureRuntime.retire_occupied`).
- **Distinct units.** No two slots hold the same unit, from admission on:
  every pending refresh leaves them distinct whatever it starts from
  (`FreeDispatch.refresh_distinct`), and the initial state and every step carry
  distinctness within alignment (`TemporalControl.initial_aligned`,
  `TemporalControl.step_total`); checkpoint admission refuses an image whose
  slots repeat one. U1's checkpoint format 15 added the held bonus word and
  refused earlier generations.

Machine-checked: `FreeDispatch.refresh_retains`, `FreeDispatch.refresh_distinct`,
`Bonus.finite_positive`, `CurrentTemporal.attained_stopping` (the executed attained
stopping value is at least the estimate for finite estimates within the
prediction cap), `Assignment.words_roundtrip`, and the unchanged
`FreeDispatch.install_closing_owner` and `FreeDispatch.install_retains_owner`.
U1 does not establish that options now learn useful behaviour, how often units
leave the ranking, or that a hashed-slot weight is a good attainment target.

### What U4 changed

- **Every step.** After selection and before primitive credit, each option that
  is not executing learns from the action the agent actually took
  (`TemporalControl.followOptions`). The executing option keeps its on-policy
  update, and frozen and primitive-only profiles do no option learning.
- **Policies.** Each option's action-value policy takes tree-backup credit
  [[21]](#r21): the error bootstraps from the option's own expected value and
  earlier traces decay by the option's own probability of the action taken
  (`Controller.backupStep`). No probability of the behaviour enters.
- **Models.** Each option's model learns along runs of frames whose action was
  selected with the option's own distribution ([[9]](#r9) §5, p. 202): the
  behaviour's reported masses equal the option's
  (`Skill.followTemporal`, `PolicySnapshot.consistent`). The importance ratio of
  [[7]](#r7) eq. (17) is then one, and the model's target is the option as executed.
- **Stops.** The executing option's stopping decision applies to the stored
  trajectory, whose age advances on every followed frame. A stop credits the
  stopping value at zero trace decay ([[7]](#r7) §3), releases the remaining
  traces and continues from the current frame.
- **Starts.** An option the meta-controller selects first settles the transition
  it was following (`Skill.settleFollowing`), so none is discarded uncredited.
- **Ownership.** The trajectory belongs to the skill; a fresh, released or
  restored skill has none, so nothing observed under one objective is credited
  to its replacement. Terminal credit assignment is unchanged; selection gains
  only the settling step.
- **Checkpoint and pins.** The trajectory is process-local, so the checkpoint
  format is unchanged. All three audit pins changed, because option policies and
  models now change on every step.

Machine-checked: `Controller.valuesStep_eq_creditStep`,
`CurrentTemporal.follow_executing` and `CurrentTemporal.step_executing` (the
executing option's update is unchanged), `PolicySnapshot.mass_bounded` (the trace
correction lies in [0, 1]), `CurrentTemporal.follow_inactive`,
`CurrentTemporal.follow_frame`, `CurrentControl.stop_step_empty`,
`CurrentModels.stop_trajectory_empty` and `CurrentLearner.release_idle` (work),
`PolicySnapshot.consistent_mass`, `CurrentTemporal.follow_age`,
`CurrentTemporal.follow_cap`, `CurrentTemporal.follow_live_model` and
`CurrentTemporal.follow_idle_model` (consistency and age),
`CurrentTemporal.settle_continuing` and `CurrentTemporal.settle_ending` (starts), and
`FreeDispatch.install_unlinked`, `Ensemble.release_unlinked` and
`Ensemble.restore_unlinked` (ownership). U4 does not establish convergence of
tree backup under linear function approximation with adaptive step sizes, the
meaning of the step-size adaptation under the corrected trace decay, how often
a frame's behaviour has the distribution of an option that is not executing,
or that option policies and models improve. Each option that is not executing
costs about one executing-option step on every frame. The meta-controller's option values still
learn by SMDP credit alone ([[9]](#r9) §6, eq. (21)).

### Alternatives weighed

- **Continue the retirement reachability program (issue 3): no.** Its object is a
  local guard that departs from every published tester. A reachability proof
  would not yield representation search: turnover would still be rare and not
  utility-ranked, and the generator would still be blind to the task. Issue 3
  recorded that neither initialized joint eligibility nor a persistent veto was
  established. U3 dissolves the question.
- **U5 first: no.** It is the most mission-relevant capability, but it is
  research-sized, and before U1 the churn would have erased the models it needs.
- **Measure now: no.** The derived defects would dominate the result, and
  measuring before fixing derivable defects replaces proof obligations with
  observation. U6 measures after U1 and U2.
- **[Regula](https://github.com/rbeauchamp/regula) adoption and gate hygiene:
  later** ([#20](https://github.com/rbeauchamp/acorn/issues/20),
  [#21](https://github.com/rbeauchamp/acorn/issues/21),
  [#22](https://github.com/rbeauchamp/acorn/issues/22)). They are mission-neutral
  maintenance, and Regula adoption waits on Regula's own blockers. New admission
  code should prefer structural recursion, which avoids the well-founded-recursion
  helpers one of those blockers concerns.
  **Status: Regula is adopted.** The [Regula audit](verification.md#regula-audit)
  states what is audited and how to run it.
- **Learned agent state first: no.** It is large and changes every learner's
  input; it follows U5.

## What each claim rests on

- **Machine-checked.** Acorn's existing theorems (state legality, admission and
  the identities cited in the PAR entries) and the U1, U2, U3 and U4 theorems
  cited above. The assessment inspected the earlier theorems' statements without
  recompiling them; U1's, U2's, U3's and U4's were compiled by the verification
  run on each change's head. U2's distributional results hold under the assumed
  uniform, independent draw listed below.
- **Argued.** F-A to F-F, including F-C's initial derived rate, E[D] = H₁₂₈, the renewal
  fraction of about 0.90, and F-D's lemma (conditional on equal prediction
  buckets and no layout collision). None is machine-checked.
- **Assumed.**
  - An idealized uniform, independent random draw for the renewal fraction and
    for U2's distributional results; the deterministic generator does not
    supply one.
  - Uniform hashing for the roughly 1,300 active features.
  - Faithful transcription of the paper equations recorded in earlier reviews.
- **UNKNOWN.** Whether the agent learns in its world; how often refreshes occur
  and units leave the ranking; option and model quality; the benefit of
  planning; the benefit of any of U1 to U5; how often a frame's behaviour has the
  distribution of an option that is not executing. Each depends on the
  experience stream, so no derivation from the definitions can settle it.

## References

Section, equation and page locators refer to the versions linked here.

1. <a id="r1"></a>Richard S. Sutton, "Adapting bias by gradient descent: An
   incremental version of delta-bar-delta", AAAI 1992
   ([PDF](http://www.incompleteideas.net/papers/sutton-92a.pdf)).
2. <a id="r2"></a>Khurram Javed, Arsalan Sharifnassab and Richard S. Sutton,
   "SwiftTD: A Fast and Robust Algorithm for Temporal Difference Learning",
   RLJ | RLC 2024, Algorithm 1
   ([PDF](https://rlj.cs.umass.edu/2024/papers/RLJ_RLC_2024_111.pdf)).
3. <a id="r3"></a>Khurram Javed and Richard S. Sutton, "Swift-Sarsa: Fast and
   Robust Linear Control", 2025, abstract and §2
   ([arXiv:2507.19539v1](https://arxiv.org/abs/2507.19539v1)).
4. <a id="r4"></a>Richard S. Sutton, Joseph Modayil, Michael Delp, Thomas Degris,
   Patrick M. Pilarski, Adam White and Doina Precup, "Horde: A Scalable Real-time
   Architecture for Learning Knowledge from Unsupervised Sensorimotor
   Interaction", AAMAS 2011, §4, pp. 763–764
   ([PDF](http://www.incompleteideas.net/papers/horde-aamas-11.pdf)).
5. <a id="r5"></a>A. Rupam Mahmood and Richard S. Sutton, "Representation Search
   through Generate and Test", AAAI Workshop on Learning Rich Representations
   from Low-Level Sensors, 2013: first tester (replacement fraction ρ, maturity
   threshold µ) and third tester (step-size order statistic), pp. 3–4
   ([PDF](http://www.incompleteideas.net/papers/MS-AAAIws-2013.pdf)).
6. <a id="r6"></a>Shibhansh Dohare, J. Fernando Hernandez-Garcia, Parash Rahman,
   A. Rupam Mahmood and Richard S. Sutton, "Maintaining Plasticity in Deep
   Continual Learning", §6, eqs. (2)–(8)
   ([arXiv:2306.13812v3](https://arxiv.org/abs/2306.13812v3)); published with
   Qingfeng Lan as "Loss of plasticity in deep continual learning", Nature 632
   (2024) ([doi:10.1038/s41586-024-07711-7](https://doi.org/10.1038/s41586-024-07711-7)).
7. <a id="r7"></a>Richard S. Sutton, Marlos C. Machado, G. Zacharias Holland,
   David Szepesvari, Finbarr Timbers, Brian Tanner and Adam White,
   "Reward-Respecting Subtasks for Model-Based Reinforcement Learning",
   Artificial Intelligence 324 (2023)
   ([arXiv:2202.03466v4](https://arxiv.org/abs/2202.03466v4)).
8. <a id="r8"></a>Andrew Y. Ng, Daishi Harada and Stuart Russell, "Policy
   invariance under reward transformations: Theory and application to reward
   shaping", ICML 1999
   ([PDF](https://ai.stanford.edu/~ang/papers/shaping-icml99.pdf)).
9. <a id="r9"></a>Richard S. Sutton, Doina Precup and Satinder Singh, "Between
   MDPs and semi-MDPs: A framework for temporal abstraction in reinforcement
   learning", Artificial Intelligence 112 (1999), §5 (intra-option model
   learning) and §6 (intra-option value learning)
   ([PDF](http://www.incompleteideas.net/papers/SPS-aij.pdf)).
10. <a id="r10"></a>Yi Wan, Zaheer Abbas, Adam White, Martha White and
    Richard S. Sutton, "Planning with Expectation Models", IJCAI 2019
    ([arXiv:1904.01191v4](https://arxiv.org/abs/1904.01191v4)).
11. <a id="r11"></a>Richard S. Sutton, Csaba Szepesvári, Alborz Geramifard and
    Michael Bowling, "Dyna-Style Planning with Linear Function Approximation and
    Prioritized Sweeping", UAI 2008, §4
    ([arXiv:1206.3285](https://arxiv.org/abs/1206.3285)).
12. <a id="r12"></a>Will Dabney, Georg Ostrovski and André Barreto,
    "Temporally-Extended ε-Greedy Exploration", ICLR 2021
    ([arXiv:2006.01782v1](https://arxiv.org/abs/2006.01782v1)).
13. <a id="r13"></a>Yi Wan, Abhishek Naik and Richard S. Sutton, "Learning and
    Planning in Average-Reward Markov Decision Processes", ICML 2021, §2,
    eqs. (3)–(4) ([arXiv:2006.16318v3](https://arxiv.org/abs/2006.16318v3));
    Richard S. Sutton and Andrew G. Barto, *Reinforcement Learning: An
    Introduction*, second edition (2018), §10.3, Exercise 10.8, p. 251
    ([book](http://incompleteideas.net/book/the-book-2nd.html)).
14. <a id="r14"></a>Abhishek Naik, Yi Wan, Manan Tomar and Richard S. Sutton,
    "Reward Centering", RLJ | RLC 2024
    ([arXiv:2405.09999](https://arxiv.org/abs/2405.09999)).
15. <a id="r15"></a>Khurram Javed, Haseeb Shah, Richard S. Sutton and Martha
    White, "Scalable Real-Time Recurrent Learning Using Columnar-Constructive
    Networks", JMLR 24 (2023)
    ([paper](https://www.jmlr.org/papers/v24/23-0367.html)).
16. <a id="r16"></a>Mohamed Elsayed et al., "Streaming Deep Reinforcement
    Learning Finally Works" ([arXiv:2410.14606](https://arxiv.org/abs/2410.14606)).
17. <a id="r17"></a>Richard S. Sutton, "The OaK Architecture: A Vision of
    SuperIntelligence from Experience", NeurIPS 2025 invited talk
    ([abstract](https://neurips.cc/virtual/2025/invited-talk/109601)).
18. <a id="r18"></a>Oak Lab, "Mission" ([page](https://oaklab.ai/mission)),
    read 2026-09-29.
19. <a id="r19"></a>Khurram Javed and Richard S. Sutton, "The Big World Hypothesis
    and its Ramifications for Artificial Intelligence", 2024
    ([Oak Lab](https://oaklab.ai/posts/the-big-world-hypothesis.html)).
20. <a id="r20"></a>Richard S. Sutton, Michael Bowling and Patrick M. Pilarski,
    "The Alberta Plan for AI Research"
    ([arXiv:2208.11173v3](https://arxiv.org/abs/2208.11173v3)).
21. <a id="r21"></a>Doina Precup, Richard S. Sutton and Satinder Singh,
    "Eligibility Traces for Off-Policy Policy Evaluation", ICML 2000, §4,
    Algorithm 2 and Theorem 3
    ([PDF](http://incompleteideas.net/papers/PSS-00.pdf)).
