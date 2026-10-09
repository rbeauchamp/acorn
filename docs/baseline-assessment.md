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

- **Learners: met, with one declared exception.** Apart from the off-policy
  questions, every one of Acorn's full-width learners (57), and every row
  of the option models' transition parts, is SwiftTD or Swift-Sarsa,
  transcribed with declared corrections
  ([PAR-1](prior-art-review.md#par-1--swifttd),
  [PAR-2](prior-art-review.md#par-2--swift-sarsa)). This matches OaK's
  requirement that each learned weight has its own meta-learned step size.
  The off-policy questions, which no decision reads, adapt no step size
  ([PAR-18](prior-art-review.md#par-18--off-policy-questions)).
  GVF predictions are fed back as features, and nothing is replayed.
- **Architecture: wired, with declared adaptations.** The FC-STOMP chain (feature
  construction, subtasks, options, models, planning) is wired. Two links ran on
  local substitutes that dropped the property their source relies on, the option
  models and planning, until U5 replaced them with expectation models over a
  ranked feature subset and backups under the current values (F-B). U3 replaced
  a third, the feature tester, with the published one. A composition defect
  (F-A) erased option learning until U1 repaired it, and a locally derived
  exploration rate made about 90% of early primitive steps random until U2
  replaced it (F-C). Options learned only while executing until U4 (F-F).
- **Learning: two observations, each refuted at its horizon; otherwise
  UNKNOWN.** In one pass of the curriculum from a fresh agent, the agent
  achieved more goals than a uniform-random policy on 4 of 20 seeds
  ([U6](#conformance-sequence)). Over four cycles of the curriculum, its
  attempts to reach a target shortened by more than that policy's on 0 of 20
  seeds: of 160 reach visits the agent achieved one and the policy none
  ([U7](#conformance-sequence)). Neither observation shows that the agent
  cannot learn; whether it learns on goals it does achieve, or over a longer
  horizon, has not been observed.

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
| IDBD → SwiftTD [[1]](#r1) [[2]](#r2) | Step 1; per-weight meta-learned step sizes | Every learner except the off-policy questions | **Faithful** | `NumericState.step` and its two loops transcribe Algorithm 1 of [[2]](#r2), with corrections declared in PAR-1. The off-policy questions are the declared exception ([D4](learned-only-binding.md#d4--learner-parameters--step-1), [PAR-18](prior-art-review.md#par-18--off-policy-questions)): they run `GradientLearner.step` with one prescribed step size per transition and adapt none, because the per-step energy inequality they are chosen for measures the weights in a norm that a per-weight step size enters. |
| Swift-Sarsa [[3]](#r3) | Step 4 (declared Sarsa in place of actor-critic) | Primitive, meta and option policies | **Faithful** | `Controller.valuesStep`: per-action value vectors sharing one error. The actor-critic departure is declared. |
| Horde / GVFs [[4]](#r4) | Step 3 | 11 fixed on-policy GVFs whose bucketed predictions are re-encoded as features, and the same 11 questions about each option's policy learned off-policy | **Adapted** (after [#16](https://github.com/rbeauchamp/acorn/issues/16)) | Horde learns each prediction from the snippets of experience relevant to it, which "requires off-policy learning", and uses GQ(λ) ([[4]](#r4) §4). Acorn's questions are fixed ([D5](learned-only-binding.md#d5--prediction-targets--step-2)); those about the options' policies learn with GTD2-MP at trace parameter zero on frames whose action was selected with the option's own distribution ([PAR-18](prior-art-review.md#par-18--off-policy-questions)). No decision reads them yet. Feeding the on-policy predictions back is a genuine, limited predictive state. |
| Generate and test: generator [[5]](#r5) | Step 2 | 512 random projections over the 11 × 11 tile-kind patch and the task words | **Adapted** (after U3) | Before U3 the generator read only the kind patch; it now also reads the task words (`observationPatch`, `taskContext`), so units can conjoin task and layout. Inventory and energy are still excluded (F-D). |
| Generate and test: tester [[5]](#r5) [[6]](#r6) | Step 2: evaluate features and discard the less promising | Contribution utility over every stored reader, a maturity age and a declared replacement rate | **Adapted** (after U3) | U3 replaced the absolute, conjunctive guard with the published relative tester ([PAR-11](prior-art-review.md#par-11--generate-and-test-tester), [D7](learned-only-binding.md#d7--feature-tester-schedule--step-2)); turnover follows from the rate by construction over eligible units (`Lifecycle.test_accrual`, F-E). Adaptations: eq. (2) without the mean correction, and the rate accrued per eligible unit as in the authors' released code. |
| Reward-respecting subtasks [[7]](#r7) | Step 10: highest-ranked features become subtasks | Three slots from the positive Demon-0 weights of imprint units, with held bonuses | **Adapted** (after U1) | U1 made candidates sign-correct, the bonus held, and identity the unit alone. One deviation remains: subtasks are not restricted to features whose weight is sometimes high and sometimes low ([PAR-12](prior-art-review.md#par-12--ranked-learned-subtasks)). |
| Potential-based shaping [[8]](#r8) | Option learning aid | Present | **Faithful** | [PAR-6](prior-art-review.md#par-6--potential-based-shaping), with limits declared. |
| Options and interruption [[9]](#r9) | Step 10: option learning off-policy | Three options, 128-step cap, interruption, SMDP meta-credit | **Adapted** (after U4) | Before U4 only the executing option learned (F-F). Every option that is not executing now learns from the action taken ([PAR-17](prior-art-review.md#par-17--off-policy-option-learning)). The meta-controller's option values still learn by SMDP credit alone. |
| Intra-option primitive credit [[9]](#r9) | Data reuse | Primitive Sarsa learns from every executed step | **Adapted** | [PAR-9](prior-art-review.md#par-9--intra-option-value-learning). One of the links that genuinely supports the rest. |
| Option models [[7]](#r7) [[10]](#r10) | Step 10; the model predicts the state at option termination | A reward part, a transition part over at most 63 ranked feature slots, and a shared residual with one deviation per meta action for the value the ranked slots do not carry | **Adapted** (after U5) | Before U5 there was no transition part, and the continuation was a value estimator (F-B). Each row of the transition part is now the source's TD update ([[7]](#r7) eq. (17)) with the terminal target γ·x_j that eq. (15) requires; the ranked subset, the residual with its per-action deviations and the action-value nominal are declared adaptations ([PAR-13](prior-art-review.md#par-13--option-expectation-models)). |
| Planning [[7]](#r7) | Steps 7 to 10: imagined outcomes evaluated by the value functions | Backups of every option's value toward r̂ plus the nominal value of each action's v̂(n̂, w) + residual, with the current weights, at free boundaries | **Adapted** (after U5) | Before U5 the backup had no look-ahead with the current value function (F-B). `PlanningResult.lookAhead` now applies the meta-controller's current weights to the predicted slots; each option's action value is backed up and the maximum is the meta-controller's choice ([PAR-14](prior-art-review.md#par-14--background-planning)). |
| Search control [[11]](#r11) | Step 9 | A sweep over the 128 most recent earlier feature vectors, one per decision boundary, against the order they were written in | **Adapted, minimal** (after U5) | Before U5 planning happened only at the current state. The store holds feature vectors only. Priorities and other strategies are open ([#15](https://github.com/rbeauchamp/acorn/issues/15)). |
| εz-greedy [[12]](#r12) | Step 9 exploration | Capped 1/n-tail duration ([D3](learned-only-binding.md#d3--exploration-duration--step-9)) and, since U2, a declared rate ε = 0.01 ([D6](learned-only-binding.md#d6--exploration-rate--step-9)); a persistent run may start at every decision, whichever layer acts | **Adapted** (after U2) | The duration law is a tail-equivalent surrogate for the published zeta law. At 86ce779 the rate was a local derivation with no published source, starting near 0.63 (F-C); U2 ([#23](https://github.com/rbeauchamp/acorn/pull/23)) replaced it with a declared 0.01. That is the source's CartPole setting (Appendix A, p. 14). Its Rainbow-based Atari agents reach 0.01 only at the end of a schedule: ε "follows a linear decay schedule 1.0 to 0.01 over the course of the first 4M frames" (Appendix B.3, p. 15; Table 2, p. 16). D6 keeps the constant and removes the decay. Counting one step as one frame, ε on that schedule is still about 0.99 after the 34 000 steps a first pass can take, so a whole first pass lies inside the phase D6 removed. The source's Algorithm 1 (p. 14) applies the persistent draw to the agent's one behaviour policy. Acorn's primitive control and executing options both make that draw, and a run an option begins interrupts it; until [#58](https://github.com/rbeauchamp/acorn/issues/58) only primitive control did, so while the meta-controller held options the mechanism rarely ran ([first-pass consequences](#f-c--the-derived-exploration-rate-started-near-063)). |
| Average reward [[13]](#r13) | Steps 5 to 7 | Selectable differential control, demoted; gain updated from the reward residual | **Adapted, partial** | Differential Q-learning updates the average-reward estimate with the TD error ([PAR-15](prior-art-review.md#par-15--differential-control)). Average-reward GVFs are absent. |
| Reward centering [[14]](#r14) | Steps 5 and 6 | — | **Missing** | A cheap, general fix for discounted methods with discount near 1. Acorn uses γ = 0.99 throughout. |
| Learned agent state [[15]](#r15) | Perception | Only the fed-back GVF buckets | **Missing** | Severe partial observability (an 11 × 11 view of a 1024 × 1024 world) with no learned memory. |
| Off-policy learning [[4]](#r4) [[7]](#r7) | Steps 3 and 10 | Options and the questions about their policies | **Adapted, partial** (after U4 and [#16](https://github.com/rbeauchamp/acorn/issues/16)) | Option policies learn by tree backup [[21]](#r21) and option models along frames whose action was selected with the option's own distribution ([[9]](#r9) §5). Each option's questions about its own policy learn along the same frames with a gradient-TD correction ([PAR-18](prior-art-review.md#par-18--off-policy-questions)). The option models still learn semi-gradient along those frames, without that correction. |
| Utility feedback [[20]](#r20) | Step 11: feedback that assesses the utility of every element and replaces the least useful | — | **Missing (declared)** | The complete OaK loop is outside the implementation ([design](design.md#implementation-scope)). |
| Nonlinear continual learning [[6]](#r6) [[16]](#r16) | Continual deep learning | Linear learners only | **Missing** | Outside the baseline's scope, and the current research front. |

**Score.** Of 19 rows: 3 faithful (the learning core plus shaping), 12 adapted,
none substituted and 4 missing, counting U3's tester and generator, U4's
off-policy option learning, U5's models, planning and search control and the
off-policy questions of #16 as adapted. At the assessed commit the models and planning were substituted and
search control was missing. The frontier and design acknowledge utility feedback
and learned agent state, and design Step 3 and
[PAR-3](prior-art-review.md#par-3--horde) declare the on-policy specialization
of the questions about the behaviour; the other two missing rows (reward centering and
nonlinear continual learning) were not previously recorded.

Correctness of what exists (state legality, admission, numeric containment and
the proved identities) is strong and machine-checked. The weakness is fidelity
and composition, which the proofs did not state and so could not catch.

## Composition findings

Two links genuinely support the rest of the system:

- **SwiftTD under every learner except the off-policy questions.** Per-weight
  credit assignment protects each such learner from the roughly 1,300 active
  features, most of them irrelevant to it.
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
every refresh. A refresh then ran after every achieved attempt and every new
curriculum cycle. Success therefore reset the option policy,
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
retired. How often that happens is UNKNOWN: it depends on the stream. Since
[#57](https://github.com/rbeauchamp/acorn/issues/57) the refresh runs at every free
dispatch, so a unit that leaves the three ranked score blocks is replaced at the next
free dispatch rather than after the next achieved attempt.

### F-B · The option model is a value estimator, so planning cannot plan

**Status: addressed by U5 for the ranked share of an outcome's value**
([#11](https://github.com/rbeauchamp/acorn/issues/11)): the value at the ranked
slots is read from the current weights, and the rest is still a learned value
estimate, the residual
([#48](https://github.com/rbeauchamp/acorn/issues/48)). The
[U5 section](#what-u5-changed) lists what changed and what is proved. The finding
below describes the assessed commit. Argued.

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
example 0.01 on CartPole ([[12]](#r12) Appendix A, p. 14), and for the
Rainbow-based Atari agents a schedule in which ε "follows a linear decay schedule
1.0 to 0.01 over the course of the first 4M frames, remaining constant after
that" ([[12]](#r12) Appendix B.3, p. 15; Table 2, p. 16), with zeta-distributed
durations (μ = 2) ([[12]](#r12) Appendix B, p. 14).

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
generator does not supply, `ez_duration_mean` gives a mean run length of H₁₂₈, and
`declared_share_gt` and `declared_share_lt` bound the expected exploratory share
of the behaviour's cycles between 4.6% and 6%.

Two consequences of D6 bore on a first pass. The first remains and is not
conformance with the source; the second was repaired:

- **The first pass lies inside the phase D6 removed.** A first pass of the
  standard curriculum takes at most 34 000 steps. Counting one step as one
  frame, the source's Atari schedule gives ε = 1 − 0.99 × 34 000 / 4 000 000
  ≈ 0.99 when such a pass ends, 0.85% of the way through the decay. D6's 0.01
  is the value that schedule holds only after 4M frames. The CartPole agent
  does use 0.01 from its first step.
- **Persistence reached one layer until [#58](https://github.com/rbeauchamp/acorn/issues/58).**
  The source's Algorithm 1 ([[12]](#r12) p. 14) has one behaviour policy: at
  every step with no run in progress it starts a run with probability ε,
  whichever action is greedy. Through U6, Acorn's agent started a run only in
  `TemporalControl.choosePrimitive`, reached when the meta-controller delegates
  to primitive control or the profile has no hierarchy; an executing option
  explored one step at a time. In two diagnostic traces of U6's run, options
  acted on 33 354 of the 33 800 steps after the first reward and on 10 361 of
  10 363, and 0.95% and 0.93% of steps were exploratory; in the first,
  persistent runs served 10 steps from 4 starts. The traces are reruns of two
  recorded seeds (16265277883658242538 and 8789851314873071931) with per-step
  telemetry; they are diagnostics, observed on those two seeds before the
  repair, and not study evidence. An executing option now makes the persistent
  draw too, and a run it begins interrupts it
  ([D3](learned-only-binding.md#d3--exploration-duration--step-9),
  [PAR-8](prior-art-review.md#par-8--temporally-extended-exploration)).
  `CurrentTemporal.select_persistent` proves every decision is a served step
  of a run or one persistent draw, whichever layer selects the action. The
  exploratory share a run of the repaired agent shows has not been observed
  and is UNKNOWN, as is any effect on achievement.

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
neutralized its planning end until U5, F-F starved its option end until U4 and
F-E left its feature-construction end inert until U3.

## Measured against the published OaK and Alberta Plan designs

- **Matches.**
  - OaK asks that "all of its components learn continually" and that "each
    learned weight has a dedicated step-size parameter that is meta-learned
    using online cross-validation" [[17]](#r17). Acorn matches both, except
    that the off-policy questions adapt no step size
    ([PAR-18](prior-art-review.md#par-18--off-policy-questions)).
  - Oak Lab's algorithms "learn in real-time without storing or replaying data"
    [[18]](#r18). Acorn matches this: batch size one, no replay, IDBD-family credit
    assignment.
- **Agent and world size.** "The big world hypothesis says that in many
  decision-making problems the agent is orders of magnitude smaller than the
  environment" [[19]](#r19). Acorn's standard setting does not have that
  relation in bits: about three million learned parameters, more than a third
  of them the off-policy questions' weights, hold 94.4 million bits, and the
  whole state of a 1024 × 1024 world fits in fewer than 67.7 million (argued).
  What is machine-checked, over declared model inputs, is a counting statement:
  a table with one entry per element of the declared product of position,
  facing, energy, day phase and craft flags would need at least 90,000 times
  the agent's parameters. The agent senses the world through an 11 × 11 window.
  The [parameter-budget proofs](../lean/AcornVerif/ParameterBudget.lean) own
  the parameter count, that margin and the derivation of the bit bound.
- **The agent and its world.** The composed agent is written against an
  interface, not against the grid world
  ([design](design.md#the-interface-between-the-agent-and-a-world)). A world fixes
  the shape of its symbol array, the horizons of its prediction signals, an action
  count, a word bound, the first channel of the agent's prediction feedback
  words and its timing, and delivers one percept per step: a frame and the reward of the preceding
  transition. The grid world is one instance
  (`Grid.interface`), and `Agent.grid_inputs` states what that instance feeds each
  learner in terms of the host's own channel, signal and potential definitions. The
  [correspondence proofs](../lean/AcornVerif/GridCorrespondence.lean) show the
  host's step under the default step order, construction and restoration equal to a
  frozen composition over host observations (`act_eq`, `callback_eq`, `initial_eq`,
  `restore_eq`). Four bindings
  to the grid world remain. Two are to its way of running. One of those is
  outside the interface: a saved image is not an exact image of the agent (the
  option models and the off-policy questions start afresh). Its timing is not one:
  the grid world declares that it waits for the agent (`Grid.interface_timing`),
  the Microduck's world declares a wall clock with a cycle and a latency
  (`Microduck.interface_timing`, [design](design.md#the-time-a-world-declares)),
  and the executable `microduck-host` runs that world's host loop at the declared
  pace. The step itself is two functions, and under the `plan-after-act` and
  `act-then-learn` step orders a host releases the action between them, with
  planning after the action and, under `act-then-learn`, every write that reads the
  reward after it as well
  ([design](design.md#the-two-parts-of-a-step)); every value that either native
  loop returns agrees with one pure fold of whole steps, in its run state and
  outcome or in its refusal with the learned stage of a refused pass
  (`runAttempt_complete`). One is carried by the frame: the host's achievement flag still ends an
  option, as a field that the coder does not read (`frame_congr`); it is declared
  as departure [D8](learned-only-binding.md#d8--achievement-event--step-10). Two
  are inside the agent's own modules, which import no world: the lifetime
  accounting records reward and attempts under the grid curriculum's four task
  families and attempt cycles (`Agent.recordEnvironment`, `Agent.recordAttempt`),
  as observations no decision reads (`act_learners`), and the evaluation mode
  `withoutReachRelation` is named for the grid world's reach relation, which only
  the grid adapter omits from its frame
  words. A second world, the Microduck, has an instance of the interface and an
  adapter, and the executable `microduck-host` runs the agent in it against the
  vendor's simulator; no run of it is recorded as a measurement, so that an agent
  learns in another world is not an observation.
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
  representations or subtasks "operate on every time step" ([[20]](#r20) p. 2). At
  86ce779 Acorn triggered the subtask ranking from host attempt and cycle events, an
  undeclared departure that was not mild in a first pass. A request was pending
  only after an achieved attempt or a new curriculum cycle, and was consumed at
  the next free boundary. The ranking admits only units of positive
  reward-prediction weight (`candidateOfWeight`), the only nonzero reward is an
  achievement's, and a decision selects before the prediction learners see its
  reward (`TemporalControl.step`). A request consumed in the decision that
  followed the first achievement therefore found every weight zero,
  installed nothing and was cleared, and the next request waited for the next
  achievement. In a diagnostic trace of seed 16265277883658242538 of U6's run
  the three options had no subtask for the first 31 000 of 34 000 steps; in one
  of seed 8789851314873071931, for the first 422 of 10 563
  ([#57](https://github.com/rbeauchamp/acorn/issues/57)). The traces are
  diagnostics of those two seeds, not study evidence. The option models were not
  affected: they take the feature ranking at every free boundary
  (`rerankModels`). The
  subtask ranking now runs at every free dispatch and reads no host event. A free
  dispatch is a decision that draws a meta decision. A hierarchical agent draws one
  whenever it serves no committed exploration run and no option is active
  (`TemporalControl.select_drawn`). The decision at which an active option ends is also
  a free dispatch, by the definition of `TemporalControl.selectWithOperations`, and
  every free dispatch records its meta decision (`TemporalControl.atBoundary_interest`).
  The decision is then taken with the slots holding
  exactly the ranked candidates' units, one slot per candidate, for the Demon-0 weights
  the decision started from (`TemporalControl.select_assigns`,
  `TemporalControl.select_occupancy`). Three limits remain. The ranking does not run
  on a step that continues an option or serves an exploration run. Selection runs
  before the reward delivered with a decision is learned, so a candidate that reward
  creates is installed at the next free dispatch, not at that decision. A
  primitive-only profile draws no meta decision (`TemporalControl.primitive_undrawn`).
  Its selection returns before the refresh, so it assigns no subtask; that is read from
  the definition of `TemporalControl.selectWithOperations` and is not a stated theorem.
- **The route to representation search.** Swift-Sarsa is presented as opening
  the door to learning representations "by searching over hundreds of millions of
  features in parallel" [[3]](#r3), leaning on step-size credit assignment over
  large feature sets. Acorn's representation is 16,384 hashed slots; until U3
  its generator never saw the task.
- **Evaluation.** Every source above establishes usefulness empirically: SwiftTD
  on Atari prediction, Swift-Sarsa on an operant-conditioning benchmark,
  reward-respecting subtasks with planning curves in grid worlds. Acorn has two
  observations of learning, [U6](#conformance-sequence) and
  [U7](#conformance-sequence), each refuted at its horizon. Under its
  proof-first policy so few observations are deliberate, but whether the agent
  learns on goals it does achieve, or over a horizon longer than U7's four
  cycles, is irreducibly empirical and still open.

Going by the published designs, the agent they describe differs from Acorn at the
model and planning links; U3 and U4 brought the feature-testing and
option-learning links to adapted forms of the published mechanisms. The foundation is
theirs: SwiftTD under every learner except the off-policy questions,
reward-respecting feature-attainment subtasks, GVF
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
| U5 | Expectation model over a ranked small feature subset, with approximate value iteration and bounded search control over recent feature vectors | [[7]](#r7) §4–5; [[10]](#r10); Alberta Steps 8(d) and 9 | L, research | Only this makes planning plan (F-B) | **Landed** ([#11](https://github.com/rbeauchamp/acorn/issues/11)) |
| U6 | Smallest prospective observation: the ranked agent against a uniform-random comparator, pre-registered, after U1 and U2 | [Scientific evidence](../CONTRIBUTING.md#scientific-evidence) | S | Answers whether it achieves more than chance in one curriculum pass | **Run: refuted at this horizon** ([result](studies/first-pass-vs-chance/results.md), [protocol](studies/first-pass-vs-chance/protocol.md), [#12](https://github.com/rbeauchamp/acorn/issues/12)). Authorized and run on 2026-10-03 at commit 6ac4eec. Of 20 seeds: W 4, losses 9, ties 7, M 0; 95% interval for the fraction of wins 0.057 to 0.437 |
| U7 | Prospective observation over repeated visits: the ranked agent against a uniform-random comparator that follows the same four-cycle campaign in its own copy of the world, pre-registered | [Scientific evidence](../CONTRIBUTING.md#scientific-evidence) | M | Answers whether its attempts to reach a target shorten over repeated visits, and by more than chance's do | **Run: refuted at this horizon** ([result](studies/repeated-visits-vs-chance/results.md), [protocol](studies/repeated-visits-vs-chance/protocol.md), [#61](https://github.com/rbeauchamp/acorn/issues/61)). Authorized and run on 2026-10-04 as revision 2 at commit 96e3f6b. Of 20 seeds: W 0, losses 1, ties 19, M 0; 95% interval for the fraction of wins 0.000 to 0.169 |

U3 supersedes issue 3's reachability program: replacing the local tester with a
published one makes turnover reachable by construction, which removes the
question rather than answering it. Issue 3 was closed as superseded when U3
started, and its branch and in-progress evidence are kept.

U6's [protocol](studies/first-pass-vs-chance/protocol.md) compares the two over
one pass of the curriculum, the longest horizon on which the core's
random-policy diagnostic was a matched comparator when it was written. The
owner authorized revision 1 on 2026-10-03, and it was run that day at commit
6ac4eec, the commit that registered it. The [result](studies/first-pass-vs-chance/results.md) is
**refuted at this horizon**: in most worlds the agent does not achieve more
goals than chance in its first pass. Of 20 seeds, all with a valid outcome, the
agent achieved at least one more goal than the comparator on 4 (W), fewer on 9
and the same number on 7, with none missing (M = 0); the exact 95% interval for
the fraction of seeds that are wins is 0.057 to 0.437. The result does not show
that the agent does worse than chance in most worlds: the interval for the
fraction of losses, 0.230 to 0.685, contains 1/2. Whether the agent learns over
repeated visits to a goal stays UNKNOWN under that protocol, because a
comparison over several cycles needs a comparator that follows the same
campaign in one persistent world.

U7's [protocol](studies/repeated-visits-vs-chance/protocol.md) asks that
question. The comparator now follows the agent's whole campaign: the same
admitted plan and attempt-boundary function, in a second copy of the initial
world carried from attempt to attempt
([outcome CSV](design.md#outcome-csv)). Because inventory and tools persist, an
arm can achieve more goals in a later cycle on what it kept, without anything
being learned, so the protocol compares the steps of each arm's first two
visits to the two reach goals with those of its next two, over four cycles and
20 new seeds. A seed counts for the agent only when its own attempts shorten
and shorten by more than the comparator's. Revision 1 was registered and never
run. Revision 2 keeps its seeds, estimand, margin and decision rule and runs
the sources that include the exploration change of
[#73](https://github.com/rbeauchamp/acorn/pull/73); the owner authorized its
execution at the commit that registers it only, whose `lean/` and `scripts/`
trees must equal those of d3bc6e0, the commit by which #73 landed the change
for [#58](https://github.com/rbeauchamp/acorn/issues/58), and the protocol's
first block refuses any other. It discloses that, between the two
registrations, the design pass for
[#69](https://github.com/rbeauchamp/acorn/issues/69) evaluated the generated
world at its seeds without running an agent or a comparator, and that its
result is a comparison with one named policy, not evidence that the reach
goals need continual learning.

The owner authorized execution after issue 58 landed, as revision 2 at its
registering commit, and it was run on 2026-10-04 at commit 96e3f6b, the commit
that registered it. The [result](studies/repeated-visits-vs-chance/results.md)
is **refuted at this horizon**: in most worlds the agent's reach attempts do
not shorten over repeated visits by at least 300 steps per attempt and by at
least 300 more than chance's. Of 20 seeds, all with a valid outcome, none is a
win (W = 0), one is a loss and 19 are ties, with none missing (M = 0); the
exact 95% interval for the fraction of seeds that are wins is 0.000 to 0.169.
Almost no reach attempt reached its target: of 160 reach visits the agent
achieved one, on its first visit to the near target on one seed, and the
comparator none, so on 19 seeds every cost is the cap and both improvements
are 0. The result does not show that the agent cannot learn the reach goals.
It is rewarded for a goal only on achieving it, so with one achievement it
received almost nothing to learn them from, and what its attempts do once it
reaches targets was not observed. It does not show that the agent does worse
than chance: the interval for the fraction of losses is 0.001 to 0.249. And it
is a comparison with one named policy, not evidence about need. The results
record also discloses a second generator-only evaluation at the study's
seeds, made by the validation of
[#74](https://github.com/rbeauchamp/acorn/pull/74) after registration, which
ran no agent or comparator on them. Whether the agent learns on goals it does
achieve, or over a longer horizon, stays UNKNOWN.

The roadmap also tracks the missing published pieces that no unit covers:

- reward centering ([#13](https://github.com/rbeauchamp/acorn/issues/13));
- the Differential Q-learning TD-error update of the average-reward estimate
  ([#14](https://github.com/rbeauchamp/acorn/issues/14));
- search control beyond U5's minimum ([#15](https://github.com/rbeauchamp/acorn/issues/15));
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
  every refresh leaves them distinct whatever it starts from
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

### What U5 changed

- **Transition part.** Each option's model has a transition part: for each of at
  most 63 ranked feature slots, a learner that predicts whether the slot is
  active when the option stops, discounted by the time until then, from the
  ranked slots active now and a constant input. Each row takes the source's
  update, TD with cumulant zero ([[7]](#r7) §4, eq. (17)), as an ordinary SwiftTD
  learner (`Transition.step`, `Transition.terminal`). Its terminal target is
  γ·x_j, which eq. (15) requires; eq. (17) as printed passes x_j
  (`option_model_terminal_discount_correction`).
- **Ranked subset.** The slots are those of the ranked score blocks of positive
  Demon-0 weight, the subtask ranking continued from 3 entries to 63
  ([[20]](#r20) Step 8(d), p. 9). The width of 64 positions follows from a
  memory budget: the largest power of two for which the rows of all three
  transition parts fit in one weight vector (`rankWidth_budget`,
  `rankWidth_maximal`). The last position is the constant input.
- **Residual.** The value function reads every active feature, so for each meta
  action the model also predicts that action's value at the outcome's unranked
  slots. It does so in two parts that add up exactly: a shared residual, which
  the full-width continuation learner predicts (`Transition.residual`), and a
  deviation per action, which a small learner predicts from the ranked positions
  and a bias (`Transition.outcome`). Predicting the deviations from the ranked
  positions alone is a declared approximation of UNKNOWN accuracy; full-width
  learners per action are
  [#47](https://github.com/rbeauchamp/acorn/issues/47).
- **Backup.** For each meta action the value of the predicted outcome is the
  current value weights at the predicted slots plus the shared residual plus that
  action's deviation; the maximum or mean over actions is taken after, and
  planning moves the option's value toward r̂ plus the result
  (`Transition.outcomeValues`, `PlanningResult.lookAhead`). Before rounding, a
  change in a ranked slot's value weight for any action moves that action's
  value at the next look-ahead by the change times the slot's predicted
  activity, with no new termination of the option; the executed word follows
  within its rounding allowance. A predecessor's own value moves when planning
  next backs it up.
- **Search control.** Each learning frame is recorded, when it completes, in a
  store of the 128 most recent feature vectors. Each decision boundary backs up
  every option at the current vector and at one stored earlier vector; the
  stored position moves one step per boundary against the write order
  (`planningBoundary`, `RecentFeatures.advance`). The store holds no action,
  reward or successor.
- **Change of subset.** Every free decision boundary installs the current ranking
  in every model; a slot that stays ranked keeps its position and its row's
  weights from every other retained slot, and a retired ranked slot vacates its
  position (`Transition.rerank`, `Transition.retire`). A slot is held at one
  position only, by a field of the ranking's type.
  [PAR-13](prior-art-review.md#par-13--option-expectation-models) records the
  cadence this replaced.
- **Selection name and pins.** `--planning expectation` replaces `scalar`. The
  transition part is process-local like the other model learners, so the
  checkpoint format is unchanged. All three audit pins changed, because the
  model targets and the planning backups changed.

Machine-checked: `CurrentPlanning.outcome_value_rounding`,
`CurrentPlanning.discounted_backup_rounding` and
`CurrentPlanning.differential_backup_rounding` (the executed backed-up value
against the exact expression, with its rounding bound, for at most 64 ranked
positions; the discounted bound holds for every model state with no further
hypothesis, and the differential bound scales with the magnitude of the values
the backup returns, which `CurrentPlanning.differential_backup_relative` states
for every model state),
`CurrentPolicyMean.expected_sandwich` (the executed tie-window mean of
differential control against the convex combination it approximates),
`CurrentPlanning.expectation_linear`, `CurrentPlanning.expectation_maximum_le`,
`CurrentPlanning.expectation_maximum_eq`,
`CurrentPlanning.expectation_sandwiched` and
`CurrentPlanning.expected_expectation` (what an expectation model keeps under a
maximum or a tie-window mean over action values),
`CurrentPlanning.outcome_value_propagation`,
`CurrentPlanning.outcome_decomposition` and
`CurrentPlanning.deterministic_outcome` (the dependence of every exact
per-action value on the value weights, before rounding, and that the shared
residual and the deviations lose nothing of a share), `CurrentPlanning.transition_storage`,
`CurrentPlanning.transition_table`, `CurrentPlanning.transition_budget`,
`CurrentPlanning.complete_budget`, `CurrentPlanning.default_budget` and
`CurrentPlanning.default_width` (storage),
`CurrentPlanning.ranked_input_work`, `CurrentPlanning.row_work`,
`CurrentPlanning.deviation_work`, `CurrentPlanning.changed_work` and
`CurrentPlanning.boundary_work` (work),
`CurrentPlanning.differential_target_bound` (the differential backed-up value
stays finite for every state), `RankedFeatures.slot_unique`,
`CurrentPlanning.indicator_exact`, `CurrentPlanning.rerank_retained`,
`CurrentPlanning.rerank_weights`, `CurrentPlanning.rerank_deviations`,
`CurrentPlanning.retire_vacated` and `FreeDispatch.refreshModels_retains` (the
ranking and a change of subset),
`FeatureRuntime.retire_recent` (stored frames after retirement),
`RankedFeatures.input_membership` (a row reads exactly the active ranked slots
and the constant input), and
`CurrentModels.planning_primitive`, `CurrentModels.planning_traces` and
`CurrentModels.planning_lags` (what planning leaves alone). U5 does not
establish what share of an outcome's value the ranked slots carry, that the
models or the per-action deviations become accurate, that planning with a
learned linear model is stable ([[10]](#r10) §5.1 and §7.1), or that planning
improves decisions.

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
- **UNKNOWN.** Whether the agent learns on goals it does achieve, or over a
  horizon longer than U7's four cycles; how often refreshes occur
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
