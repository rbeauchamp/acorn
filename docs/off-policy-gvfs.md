# Off-policy GVFs: design proposal

This page proposes a design for issue
[#16](https://github.com/rbeauchamp/acorn/issues/16), "Learn GVFs off-policy".
It is a proposal for review. Nothing here is implemented, admitted or scheduled,
and the page describes no current behaviour except where it says so. It was
written against `main` at commit a71ed08. No agent run informed it.

**Where it stands.** The issue's design pass has four questions: the method,
how per-weight step-size adaptation composes with it, which target policies to
ask about, and how the change relates to U4. The proposal proposes an answer on
the target policies and, within the method, on how to handle importance ratios;
both are choices put to the reviewer under
[Decisions requested](#decisions-requested). It relates the result to U4. It
does not yet pass the [admission bar](prior-art-review.md#admission-standard):
the learner it describes has no gradient correction, and a fresh-context
[refutation attempt](#refutation-attempt) established that the admission
standard does not let that be deferred. The method's correction, and its
composition with per-weight step sizes, is the design work still owed.
[Admission status](#admission-status) gives the criterion-by-criterion account.

**Claim status.** Claims carry the labels of the
[baseline assessment](baseline-assessment.md):

- **Machine-checked**: an existing Lean theorem over the executed definitions.
- **Argued**: derived by hand here; not machine-checked. Every new claim on this
  page is at most argued.
- **Assumed**: a stated modelling assumption.
- **UNKNOWN**: an irreducibly empirical quantity with no observation yet.

## Summary

A **general value function (GVF)** predicts the discounted sum of a signal under
a policy. Acorn's eleven GVFs ask about the policy the agent is following. Issue
16 asks for GVFs about other policies, learned from the same stream, which is
**off-policy** learning: the **target policy** (the one the question is about)
differs from the **behaviour policy** (the one choosing actions).

The proposal is:

1. **Targets.** Ask the existing eleven signals about each option's *greedy*
   policy: "what would this signal be if the agent took option *o*'s greedy
   action from here on?" An **option** is a learned policy that can choose
   actions over several steps ([design](design.md#agent-configurations)).
2. **Ratios.** Clip the importance ratio at one. For a deterministic target the
   clipped ratio is a Boolean: one when the action taken is one the target
   would take, zero otherwise. The learner therefore runs only over stretches
   of the stream that are consistent with the option, and a stretch ends by
   bootstrapping from the current prediction.
3. **Learner entries.** Each transition is one of three SwiftTD entries that the
   option models already use. The change adds no learner arithmetic. It does
   need a trace clear that costs `O(active)` and not `O(d)`. The invariant
   such a clear relies on is already machine-checked; the one new kernel
   obligation is that the sparse clear equals the present one under it.
4. **Correction.** The result is a semi-gradient method and inherits the known
   off-policy instability. A gradient correction is required before admission.
   This page identifies its starting point and does not design it.

The reasons, in brief:

- With a deterministic target only one action has a nonzero ratio, so bounding
  or clipping the ratio cannot change which policy is evaluated. It changes
  only how histories are weighted.
- The unclipped ratio reaches 900 in Acorn, and SwiftTD's rate bound can absorb
  that only by slowing every update several hundred times.
- The clipped form reads no behaviour probability, so persistent exploration's
  served steps need no special statement.

[Decisions requested](#decisions-requested) lists the eight choices a reviewer
is asked to accept or change.

## What Acorn does now

- **Questions.** The eleven signals are the closed family `Cumulant` in
  [Cumulants](../lean/Acorn/Handcrafted/Cumulants.lean), each with one of three
  discounts (0.99, 0.95 or 0.90) from `demonDiscount`. The family is declared
  departure [D5](learned-only-binding.md#d5--prediction-targets--step-2).
- **Learner.** `DemonBank.step` in [Demon](../lean/Acorn/Demon.lean) applies one
  SwiftTD `step` per signal on every primitive step, from
  `PredictionControl.advance`, which `TemporalControl.finish` calls after the
  step's action has been selected. A **demon** is the learner of one GVF.
  Demons use trace parameter 0.95, rate budget 0.1 and initial step size
  5·10⁻⁵ (`Config.lambda`, `Config.eta`, `Config.alphaInitial`).
- **Policy.** The predictions are about whatever acted. Nothing corrects for the
  difference between that and any other policy
  ([PAR-3](prior-art-review.md#par-3--horde)).
- **Who acts.** A primitive action comes from one of four sources
  (`TemporalSource`): the primitive controller's draw, the first action of a
  persistent exploration run, a served continuation of such a run, or the
  executing option's own policy. A **research profile** is a named combination
  of agent mechanisms ([design](design.md#agent-configurations)). In every
  research profile but the annealed comparison, the one that prescribes an
  exploration-rate schedule in place of the declared rate, each source that
  draws a primitive action is ε-greedy over nine actions with the declared
  rate ε = 0.01
  ([D6](learned-only-binding.md#d6--exploration-rate--step-9)); ties within a
  window of 10⁻⁶ of the maximum share the greedy mass
  (`PolicySnapshot.candidates`). A served continuation draws nothing: it
  repeats the committed action (`ExploratoryRun.serve`).

## What the sources specify

Each locator below was read on the page for this proposal; see
[Source verification](#source-verification).

- **Horde** defines a GVF by a target policy, a termination function, a signal
  and a terminal signal, states that learning from the relevant snippets of
  experience needs off-policy learning, and uses GQ(λ): a main weight vector, a
  second weight vector and a trace scaled by the ratio of target to behaviour
  probability, with two scalar step sizes [[1]](#r1). Its demons are
  action-value functions over state-action features. It also remarks that
  behaviour seldom matches a target policy for more than a few steps in a row.
- **Intra-option model learning** updates the model of every option whose
  policy is consistent with the action taken. The method requires the option's
  policy to be deterministic and uses no importance ratio. It is given for the
  one-step, tabular case with a fixed option; the source says trace versions
  may be possible and does not specify one [[4]](#r4).
- **V-trace** truncates both the ratio on the error and the ratio in the trace,
  each at its own level, and admits a trace parameter. In the tabular case its
  fixed point is the value of a policy that depends on the truncation level
  [[8]](#r8). The collision study describes that general form for prediction
  in words and investigates a simplified variant, **Vtrace(λ)**, that caps
  only the ratio in the trace, at one, and leaves the ratio on the error
  uncapped [[7]](#r7). TDRC's authors describe Vtrace as TD with its
  importance ratios clipped at one, and report that it is slightly worse than
  TD because of the bias it introduces and that it does not prevent divergence
  on Baird's counterexample [[6]](#r6).
- **Reward-respecting subtasks** learns every subtask's value function and its
  option model off-policy on every step with a per-step ratio and an
  accumulating trace scaled by that ratio, with no gradient correction
  [[5]](#r5). Its experiments use an equiprobable behaviour over four actions and
  trace parameter zero, so its ratios are at most four.
- **True online GTD(λ)** is the published off-policy form of the true online
  TD(λ) that SwiftTD extends. Its derivation substitutes the product of the
  ratio and the step size for the step size, and the product of the ratio and
  the trace decay for the trace decay [[2]](#r2).
- **TDRC** and **TDRC(λ)** are gradient-TD methods whose second weight vector
  shares the main step size and carries a regularization term, which removes the
  second step-size parameter [[6]](#r6) [[7]](#r7). TDRC's updates are not
  gradients; its published property is convergence under the hypotheses of its
  Theorem 3.1. Its prediction experiments adapt a vector of step sizes with
  Adagrad.
- **Emphatic TD(λ)** keeps one weight vector and scales updates by a follow-on
  trace that is multiplied by the previous step's ratio [[7]](#r7).

None of the sources read here composes an off-policy correction with step-size
adaptation of SwiftTD's meta-gradient kind [[3]](#r3). Issue 16 assumes no
published SwiftTD variant and asks the design pass to decide the composition.
This was not a literature search.

## The obstacle: importance ratios in Acorn

Write π for a target policy, b for the behaviour at a step and ρ = π(a)/b(a)
for the ratio at the action a taken. All of this section is **argued**.

### How large the ratio gets

At a drawing step the acting source gives every action at least mass ε/9.

- **Greedy target.** If the target takes one action a\*, the ratio is 1/b(a\*)
  when a = a\* and zero otherwise. It is at most 9/ε = 900, attained when the
  acting source's greedy set excludes a\* and the source explores into it. That
  event has probability ε/9, about 0.0011, in such a state.
- **ε-soft target.** If the target is option *o*'s own ε-greedy policy, its
  greedy action has mass at most 1 − ε + ε/9, so ρ ≤ 9/ε − 8, about 892.

Issue 16 states the general bound, the inverse of the behaviour's least action
probability; these are its values here. The median ratio is unremarkable. The
mass is in the rare event.

### SwiftTD's rate bound cannot absorb it

SwiftTD bounds the correction ratio τ = Σ αᵢ over the active features by the
budget η, scaling the trace increment by min(1, η/τ) [[3]](#r3). The published
off-policy form replaces each step size α by ρα [[2]](#r2), so the correction
ratio of an off-policy update is ρτ. There are two ways to bound it.

- **Bound the realized product**, scaling by min(1, η/(ρτ)). The scale then
  depends on the action through ρ, and in expectation action a is weighted by
  b(a)·min(ρ(a)τ, η) and not by π(a)τ. For a stochastic target that evaluates a
  different policy, one in which under-sampled actions are under-weighted. For
  a deterministic target only one action has a nonzero ratio, so the policy is
  unchanged and the state is reweighted by min(τ, b(a\*)·η). The method still
  reads b(a\*), and the trace decay still carries the factor ρ, up to 900 per
  step, before any bound applies.
- **Bound the worst case**, scaling by min(1, η/(ρ_max τ)). The scale no longer
  depends on the action. Every state then moves at expected rate η/ρ_max per
  visit, about 1.1·10⁻⁴. At initialization τ is about 0.065 (about 1,300 active
  features at 5·10⁻⁵ each; the [baseline assessment](baseline-assessment.md)
  gives both figures), so learning is about 585 times slower than on-policy.
  The collision study states the general form of this trade [[7]](#r7).

### Emphatic TD has no bound

The follow-on trace is F ← ρ_prev·γ·F + 1 [[7]](#r7). One step with ρ = 900
multiplies it by 891 at γ = 0.99, and nothing in the stream bounds how often
that happens. Issue 16 asks that every update's size have a derivable bound;
this method has none here.

### Served exploration and ε-soft targets

On a served continuation the behaviour is a point mass on the committed action.
An ε-soft target gives every action positive probability, so its expectation
needs outcomes of actions the behaviour cannot take at that step, and no ratio
supplies them. A greedy target does not have this problem: its ratio on a served
step is one if the committed action is its own and zero otherwise. This is the
reason the proposal asks about greedy policies.

## Proposed mechanism

### Questions

For each of the three option slots and each of the eleven signals, one new
learner predicts that signal, at its existing discount, under the slot's
**greedy** policy: 33 learners. The target policy is learned (it is the
option's), and the signal family stays D5's.

The learners belong to the slot's `Skill`, beside its policy and model, so
whatever replaces a slot's option also replaces its questions.

### Consistency

Fix a step. For option *o*, let T be its candidate set at the step's features:
the actions whose value is within the tie window of *o*'s best value, which is
what `PolicySnapshot.candidates` computes. T is taken from *o*'s policy weights
as they stand at the moment the step's primitive action is fixed:

- for the executing option, T is the candidate set of the snapshot its action
  is drawn from (the one held in its `OptionContinuation`), which precedes that
  step's own policy write in `Skill.optionStep`. That snapshot's values already
  reach the dispatcher: `TemporalControl.stepOption` copies them into
  `TemporalDecision.values`, and the candidate set reads only the values and
  the tie window, not the snapshot's ε;
- for every other slot, T is computed from the slot's policy, which nothing
  writes between that moment and the dispatcher. Writes that precede the
  action, such as the terminal write to an option that has just ended, are
  included.

The step is **consistent with *o*** when the action taken is in T. The test
reads no behaviour probability. It does read the decision's source
(`TemporalSource`), to choose which values supply T: `TemporalDecision.values`
holds an option's drawing snapshot only on that option's own step, and on
every other step holds the primitive controller's values, which supply no
slot's T. If no value is comparable, T is empty and no action is consistent.

### Dispatch

Each slot keeps one flag, *live*, saying whether its learners hold a trajectory
whose last action was consistent. On each primitive step, with features x,
arriving signal value c and the learner's raw prediction v(x):

| *live* | step consistent | entry applied to each of the slot's learners |
|---|---|---|
| yes | yes | `step` with x and c |
| yes | no | `terminal` with target c + γ·v(x) |
| no | yes | `beginTrajectory` with x |
| no | no | none |

The flag then becomes the step's consistency. `step`, `terminal` and
`beginTrajectory` are existing constructors of `SwiftTd.Entry` in
[SwiftTd](../lean/Acorn/SwiftTd.lean); `Model.begin`, `Model.step` and
`Model.terminal` in [Models](../lean/Acorn/Models.lean) already apply the same
three to the option models, and each is permitted in every phase
(`SwiftTd.Permitted`).

The call at a step credits the *previous* transition, as every SwiftTD entry
does. So a transition is credited exactly when its own action was consistent,
and a state is traced exactly when the action taken from it is consistent.

The second row is the cut. `terminalStep` applies the first update loop with
error target − previous prediction, then clears the traces. When the target is
built from the raw ordered prediction `linearPrediction` of the pre-entry
state, that error is the word `step` computes, so earlier states receive the
same credit they would have received, and no later error reaches them.

The third row need not clear anything (**argued**). Whenever *live* is false
the learner's transients are already `TransientState.zero`: a fresh learner
starts there, `terminalStep` ends there, and `retireIndex` on a clear state
leaves it clear. On such a state `beginTrajectory`'s clear changes nothing, and
`step` with x and any signal word produces the same state (obligation 2),
because the first loop does nothing on an empty eligible list. So the third row
could apply `step` in place of `beginTrajectory`. The table keeps
`beginTrajectory`; the substitution is a choice for the implementing change,
and it affects only the cost stated under [Integration](#integration).

### What it learns

Model the step's action as drawn from a distribution b that may depend on the
whole history (**assumed**: the generator is deterministic, and this is the
idealized draw that the exploration results of U2 also assume). The following
are **argued**, for a T fixed before the draw.

**One step.** For any quantity X determined by the action and its outcome,

> E[ 𝟙(a ∈ T)·X | history ] = b(T) · E[ X | history, a drawn from b restricted to T ].

Both sides are the sum of b(a)·E[X | a] over a in T. So the gated update is
the expected update for the policy "b restricted to T", scaled by the
history-measurable weight b(T). When T has one action that policy is *o*'s
greedy action, whatever b is. When T has several, it is a greedy policy for
*o* whose tie-breaking is the acting source's.

**Many steps.** In the forward view with the weights held fixed, the expected
update of a state traced at one step is b(T) at that step times the error
toward a return that, at each later step, continues with weight λ·b(T) of that
step and otherwise bootstraps from the prediction at the state the last
consistent action reached. It is a λ-return for the restricted policy whose
trace parameter varies along the stream.

**The gate is the ratio clipped at one.** For the restricted policy the ratio
is 1/b(T) on T and zero off it, so min(1, ρ) is the indicator of T. The
mechanism is therefore V-trace with both truncation levels at one: reference
8's target, eq. (1), with the trace parameter of its Remark 2 [[8]](#r8). The
collision study describes the same general form in words (p. 23), and its
Appendix A prints a rule that matches it only when the printed larger-of is
read as smaller-of [[7]](#r7). The variant that study investigates is a
different algorithm: it leaves the ratio on the error uncapped, so its
empirical results on Vtrace(λ) do not concern this mechanism. V-trace's
tabular fixed-point policy, evaluated at that level for this target, is the
target itself wherever b(T) > 0.

What follows from this:

- **The weight is a Boolean.** There is no ratio to bound.
- **No behaviour probability is read.** The nominal masses in
  `PolicySnapshot.probabilities` are not exact probabilities of the finite-word
  draws; this method does not depend on them.
- **Served exploration is not a special case.** It is the statement with b a
  point mass, so b(T) is one or zero.
- **No coverage assumption is needed for an update to be well defined.** Where
  the behaviour cannot take a candidate action, b(T) is zero and the state gets
  no update. Its predecessors still bootstrap from its prediction, which is
  then whatever generalization gives it. [Limits](#limits) states the cost.
- **On-policy data is used.** When *o* itself executes and its candidate set
  is nonempty, its non-exploratory action is in T, so its own steps train its
  questions, cut only at its exploratory steps.
- **An untrained option asks the on-policy question.** All nine values of a
  fresh or reinstalled option tie at zero, so every action is consistent and
  its learners behave as cold on-policy demons until its values separate by
  more than the tie window.

b(T) is not a correction that restores a chosen weighting; it *is* the
weighting. The learner weights histories by how often the behaviour is there
and agrees with the option.

### Published basis and adaptation kinds

Following the [material adaptation contract](prior-art-review.md#admission-standard):

- **Equivalent specialization: the clip.** V-trace with both truncation levels
  at one, for a target that is deterministic up to ties, has the Boolean weight
  above [[8]](#r8). The collision study describes that general form and
  investigates a different variant, which is an alternative and not this basis
  [[7]](#r7). The same rule, update every option consistent with the action
  taken, is intra-option model learning's [[4]](#r4).
- **Published variant: state values.** Horde's demons are action-value
  functions. Off-policy prediction of state values is the collision study's
  setting [[7]](#r7). A state-value question about π answers "follow π from
  here", not "take this action, then follow π".
- **Local approximation: the learner.** The sources use an accumulating trace
  and a scalar step size. This proposal uses SwiftTD's true online update,
  per-weight step sizes and rate bound, as the on-policy demons do. Inside a
  consistent stretch the learner is the on-policy learner bit for bit
  (obligation 2). Each cut clears the step-size adaptation's registers along
  with the traces; [Limits](#limits) states the consequence.
- **Local approximation: function approximation.** V-trace's fixed-point
  statement and the consistency rule's source are tabular. With shared features
  the weighting b(T) changes the answer; see [Limits](#limits).
- **Local approximation: a learning target.** The sources evaluate a given
  policy. Here the target is the greedy policy of an option that is still
  learning, so the question moves as the option does. The on-policy demons
  already track a moving behaviour.
- **Local approximation: ties.** A tie makes the target "the acting source's
  choice among *o*'s tied actions". [Decisions requested](#decisions-requested)
  offers a canonical tie-break instead.
- **Equivalent specialization: discount.** A constant discount in place of a
  termination function.
- **Missing mechanism, named.** Gradient correction. See
  [Admission status](#admission-status).

## Integration

These are the intended owners, for sizing and review; the implementation change
would settle the details.

- **Storage.** `Skill` in [FeatureConsumers](../lean/Acorn/FeatureConsumers.lean)
  gains a `DemonBank` over the existing layout and the *live* flag.
- **Retirement, yes; utility, no.** `Skill.readers` and `Skill.retire` extend
  over the bank, so a replaced feature's weight is zeroed in the new learners as
  in every other reader. `Skill.stored` does not extend over it. `Skill.stored`
  feeds `Lifecycle.score`, the feature tester's utility, so including the bank
  would let these predictions decide which features are replaced: a feedback
  path into the representation, and a way for weights held at a rail to make a
  feature look permanently useful. The cost of excluding it is that a feature
  useful only to these questions can be replaced.
- **Step.** The dispatcher runs where the on-policy demons do, in
  `TemporalControl.finish`, after selection has fixed the action. It needs one
  thing that step does not expose today: the signal values, which
  `PredictionControl.advance` computes and does not return. That is the one
  interface change. The executing option's candidate set needs none:
  `TemporalControl.finish` already receives the `TemporalDecision`, whose
  `TemporalDecision.values` on an option step are the drawing snapshot's
  values. Each signal should still be evaluated once per transition.
- **Candidate sets.** One `Controller.predictAll` call for each slot that is
  not executing.
- **Sparse clear.** See the cost paragraph.
- **Lifecycle.** A reinstalled slot gets a fresh bank through `Skill.initial`.
  Frozen profiles dispatch nothing. `Ensemble.restore` leaves the bank cold, as
  it leaves the models, so the checkpoint format does not change.
- **Selection.** A core selection beside `PlanningSelection`, off by default.
- **An observer.** With the bank outside the tester's utility, no feedback into
  features and no random draw, the bank affects no decision and no other
  component, whether or not it is selected. Its predictions are visible only
  through diagnostics until a later change adds a reader.

**Cost (argued).**

- **Storage.** A learner stores eleven words per feature index (weight, log step
  size and nine transient registers) over 16,384 indices: 180,224 words. The
  agent has 57 learners under discounted control, 10,272,768 words; 33 more add
  5,947,392. In bytes that is about 24 MB added at four bytes a word and about
  48 MB if the runtime stores each array slot in eight. Which holds was not
  measured.
- **Work, as the kernel stands: not `O(active)`.** `terminalStep` and
  `beginTrajectory` both call `clearTransient`, which installs
  `TransientState.zero`: nine fresh registers of 16,384 words. Every cut and
  every restart therefore costs `O(d)` per learner, about 1.6 million word
  writes for a slot's eleven learners, and a slot's consistency can change on
  every step. The option models pay the same cost today, once per option
  boundary.
- **The restart's cost is avoidable with the kernel unchanged (argued).** By
  the observation under [Dispatch](#dispatch), the third row can apply `step`
  in place of `beginTrajectory`; on a clear state `step` is bounded by the
  active set. Only the cut then pays `O(d)`, and only the cut needs the sparse
  clear.
- **Work, with a sparse clear: `O(active)`.** The clear would visit only the
  indices on the eligible list, zero their registers with
  `clearFeatureRegisters`, empty the list and reset the two scalars `vOld` and
  `vDelta`, which `TransientState.zero` also zeroes. It equals `clearTransient`
  on any state in which every register is zero off the eligible list
  (**argued**: after it, an index on the list has been zeroed and an index off
  it was already zero).
- **The invariant already holds (machine-checked).** That every register is
  zero off the eligible list is `AcornVerif.CurrentLearner.Supported`, one half
  of `CoreInv`. `entry_core` proves every `SwiftTd.Entry` preserves it,
  `admitted_core` and `learner_invariant` give it for every admitted learner,
  and `AcornVerif.CurrentFeatureConsumers.managed_schedule` gives it for every
  `Managed` learner, the type a `DemonBank` stores. The new obligation on the
  proven kernel is only the sparse clear's definition and its equality with
  `clearTransient` under `Supported`.
- **Per step, with the sparse clear.** At most three `predictAll` calls (27
  ordered sums over the active set) and at most 33 entries, each bounded by the
  eligible and active sets. There is no auxiliary weight vector in this
  proposal; the correction would add one.

## Proof obligations

None of these exists yet. Obligations 1 to 7 would be Lean theorems over the
executed definitions in an implementing change.

1. **Dispatch.** Every transition of a slot's bank is one of the four table
   rows, hence an admitted `SwiftTd.Entry`; and the cut's error word equals the
   word `step` computes from the same state, features and signal, given the
   target built from `linearPrediction`.
2. **Reduction.** On a state with clear transients, `step` and
   `beginTrajectory` produce the same state; so on a stream that stays
   consistent the bank's learners equal on-policy demons started at the same
   point, bit for bit.
3. **Membership and frame.** The consistency test holds exactly when the action
   is in `PolicySnapshot.candidates`; and no write to a non-executing slot's
   policy lies between the action being fixed and the dispatcher.
4. **Self-consistency.** When an option's candidate set is nonempty, its
   non-exploratory draw is consistent with it. This follows from the existing
   `reservoir_nonempty`.
5. **Sparse clear.** The sparse clear equals `clearTransient` on every state
   satisfying `Supported`. The invariant itself is not owed: it is
   machine-checked for every `Managed` learner by `managed_schedule`.
6. **Work, storage and observation.** The counts of the cost paragraph, from
   the structure. With the selection off, `Agent.act` produces the same result;
   with it on, every decision and every other component is unchanged.
7. **Lifecycle.** `FreeDispatch.refresh_retains` extends to the bank; the
   retirement statement `replace_zero` covers the new readers; restoration
   yields a cold bank with the flag clear.

Two further statements are about an idealized model and not the executed
learner: exact arithmetic, fixed weights and the idealized draw. `AGENTS.md`
does not accept such a theorem as verification of the implementation without a
checked correspondence, and none is proposed. They explain the design and stay
**argued**.

- **Expectation identity.** The one-step and many-step statements of
  [What it learns](#what-it-learns).
- **Obstruction.** The family of [Limits](#limits).

## Limits

### No convergence guarantee, and a characterized instability

The method is semi-gradient: it follows the error and ignores how the weights
move the bootstrap target. Off-policy, that can be unstable, and clipping the
ratio does not help: TDRC's authors report divergence of the clipped method on
Baird's counterexample [[6]](#r6). The following family shows the same failure
inside Acorn's own feature class, binary features with a common step size. It
is **argued**.

Take K ≥ 2 states. State k has two active features: a shared one, with weight
w₀, and its own, with weight wₖ. The consistent action leads from each of them
to one successor state in which all K + 1 features are active. The signal is
zero and no step at the successor is consistent, so it is never updated. With
W the sum of the own weights, the successor's prediction is w₀ + W, and the
expected update of each of w₀ and W, per unit step size and weighting the K
states equally, is

> K(γ − 1)·w₀ + (Kγ − 1)·W.

The direction w₀ = W is therefore scaled by 2Kγ − K − 1 per unit step size,
and grows whenever

> γ > (K + 1) / (2K).

The threshold is 3/4 at K = 2 and falls toward 1/2. All three of Acorn's
discounts exceed 3/4. With zero signal the origin is a fixed point, so the
growth needs nonzero weights or a nonzero signal. The successor need not have
more active features than its predecessors: two such groups whose successor has
only the two shared features active give the same factor.

Stored weights cannot leave their range, because every write passes
`Weight.project`, so the failure would appear as weights held at a rail and
predictions that mean nothing: containment is not accuracy.

One state is not enough. With binary features, a single updated state whose
successor shares m of its n active features has its error scaled by γm − n per
unit step size, which is negative. The instability needs several updated
states that share features with a rarely updated successor.

That precondition is structural. Every cut bootstraps from a state that is not
updated on that visit, and where the behaviour's greedy action differs from the
option's, b(T) is about ε/9, so such states are updated about 890 times less
often per visit than their consistent predecessors. When option *o* executes,
its steps are consistent and those states are updated. How often the dangerous
weighting persists in a run is UNKNOWN; it depends on the stream and on how
often each option executes.

### The weighting changes the answer

- **A starved successor.** In the tabular case, let the option's action lead
  from s₀ to s₁ and from s₁ to a signal of one, with b(T) = 0 at s₁. The
  prediction at s₁ keeps its initial value, zero, and s₀ is trained toward
  γ·0. The true value at s₀ is γ. Each update is an unbiased sample of its
  bootstrapped target; the prediction is still wrong.
- **Aliasing.** Let two histories share a feature vector with equal
  probability. In the first b(T) is 0.9 and the option's action yields one; in
  the second b(T) is 0.1 and it yields zero. The gated fixed point is 0.9. The
  value of the option's action at that feature vector under the visit
  distribution, which an unclipped ratio would learn, is 0.5.
- **Slow where the behaviour disagrees.** Where the acting source's greedy
  action differs from the option's, the gated learner moves at expected rate
  b(T)·τ per visit, about 7·10⁻⁵ at initialization. The worst-case-bounded
  ratio method moves at about 1.1·10⁻⁴ there. The gate's advantage of about
  585 is confined to states where the behaviour agrees with the option.

### Step-size adaptation is mostly inert in short stretches

Each cut clears the meta-gradient registers with the traces. After a restart
the first step-size write needs the meta-trace register to be nonzero, which
takes three consecutive consistent actions and features that recur across them
(`firstLoopElement`, `secondLoopElement`). Stretches shorter than that learn at
whatever the step sizes already are. Horde notes that behaviour seldom matches
a target for more than a few steps [[1]](#r1), so for an option that rarely
executes the per-weight adaptation would seldom act.

### Other limits

- **Nothing reads the predictions yet.** Whether they are useful is UNKNOWN.
- **The baseline scorecard row would read Adapted** even with a correction:
  Horde's demons are action-value functions under GQ(λ).
- **Ties make the target depend on the acting source**, as stated above.
- **The expectation identity is conditional on the idealized draw and on fixed
  weights.**

## Admission status

Against the five criteria of the
[admission bar](prior-art-review.md#admission-standard):

| Criterion | Status | Why |
|---|---|---|
| Sound | Argued | The expectation identity survived the refutation attempt in the fixed-weight forward view. The clip's equivalence, the identification with V-trace, was re-derived against reference 8 in the second review and held; that review corrected its attribution to reference 7. |
| In-setting | Passes | One stream, batch size one, no replay, no target network, no resets. |
| Compatible and non-degenerate | **Fails** | The off-policy instability of semi-gradient learning is a known degeneracy. The standard requires a correction with a formal characterization and closure; disclosure does not clear it. |
| Affordable | Conditional | Fails with the kernel's present clear; passes once the sparse clear is defined and proved equal to it (obligation 5). The invariant that equality needs is already machine-checked. |
| Buildable | Partly | The gated learner is specified. The correction is not. |

So the gated learner cannot be admitted alone, and issue 16 stays open until the
correction is designed.

### The correction still owed

What can be said now is **argued**, at trace parameter zero, for Markov
features and fixed weights:

- Conditioned on being consistent, a step is a sample of the target's own
  action at a state drawn with weighting b(T) times the visit distribution. The
  consistent sub-stream is data with ratio one from a different state
  distribution.
- A gradient-TD method run on that sub-stream with ratio one is therefore the
  published method unchanged, for the projected Bellman error under that
  weighting. TDRC's theorem [[6]](#r6) is stated for independent samples of
  that form.
- Running it on the sub-stream is not the same as substituting the gate for
  the ratio in the printed rules. The secondary weights must skip inconsistent
  steps entirely. If their regression term runs on every step, its second
  moment is taken over all visits while the error's is taken over consistent
  ones, and the product is no longer the gradient form.

What the next design pass must decide:

- how traces across a consistent stretch, with the cut, enter the correction;
- how the second weight vector takes SwiftTD's per-weight step sizes and rate
  bound, which no source read here specifies;
- the storage: at least one more weight vector per learner, and its registers;
- what formal closure means here. The published theorems assume fixed policies
  and features, independent samples and decreasing step sizes [[6]](#r6). Acorn's
  options, features and step sizes all change, so PAR-3's existing caution
  applies: a correction would carry a property of a frozen snapshot, not a
  convergence theorem for the agent.

## Alternatives weighed

| Alternative | Verdict | Reason |
|---|---|---|
| Unclipped ratios, semi-gradient TD(λ), as reward-respecting subtasks uses | No | Same instability as the proposal, plus ratios up to 900 and the rate-bound trade. |
| GQ(λ) or GTD(λ) with unclipped ratios, as Horde uses | Not now | Has the correction. Keeps the ratio of 900 and the rate-bound trade, reads behaviour probabilities that are only nominal, and has no published composition with SwiftTD's step sizes. |
| Ratios bounded by SwiftTD's rate bound on the realized product, greedy target | No | Reweights states by min(τ, b·η), which is no worse than the gate's b·τ, but reads the behaviour probability and lets the trace grow by up to 900 per step before the bound. |
| ε-soft option policies as targets | No | No ratio supplies the missing actions on served steps. |
| Emphatic TD(λ) | No | The follow-on trace has no bound at these ratios. |
| Tree Backup(λ) for prediction, or Vtrace(λ) as the collision study investigates it | No | For a deterministic target the two coincide: each gates the trace as proposed but keeps the unclipped ratio, up to 900, on the error [[7]](#r7). |
| Action-value GVFs with expected backups | Not now | No ratio at one step, but nine weight vectors per question and the same instability without a correction. |
| Trace parameter zero | No | Removes ratio products but not the single ratio of 900, and gives up traces for no gain once the weight is Boolean. |
| The gate with a regularized gradient correction | Required next | See [The correction still owed](#the-correction-still-owed). |

## Relation to U4 and U5

[U4](https://github.com/rbeauchamp/acorn/issues/10) asks that every option's
policy and model learn from every step. The option models already learn through
`Model.begin`, `Model.step` and `Model.terminal` on the executing option's own
trajectory. Running the same three over consistent stretches of any behaviour,
with the option's real termination as a further terminal, is U4's model half.
This proposal's dispatcher is that mechanism with termination absent, so U4
could reuse it, and U4 would meet the same admission question about the
correction. U4's other half, learning the option *policies* off-policy, is an
action-value question this proposal does not address.

[U5](https://github.com/rbeauchamp/acorn/issues/11)'s expectation model is a
family of such questions with termination, one per ranked feature. Nothing here
decides it.

## Decisions requested

1. **Targets.** Each option slot's greedy policy (proposed), or the options'
   ε-soft policies, or other policies.
2. **Ratios.** Clipped at one, which is the consistency gate (proposed), or
   unclipped ratios under a gradient-TD method.
3. **Admission path.** The gated learner is not admitted alone; the corrected
   learner is designed next and the two are admitted together (proposed). The
   alternative is to read the admission standard as allowing the gated learner
   to land first as an unselected research integration.
4. **Questions.** All eleven signals for each of three options (proposed), or
   the reward signal only, at about a tenth of the cost.
5. **Ties.** Any candidate action is consistent (proposed), or a canonical
   first-candidate tie-break. The second gives a deterministic target, as the
   consistency rule's source requires, and discards eight of every nine of an
   untrained option's own steps, since all nine actions tie at zero.
6. **Observer.** Outside the feature tester's utility, with no feedback into
   features, off by default (proposed), or counted in the utility.
7. **Checkpoint.** Bank left cold on restore, as the models are, with no format
   change (proposed), or persisted like the on-policy demons under a new format.
8. **Order.** Before U4, so that U4 reuses the dispatcher (proposed).

## Source verification

Every locator in [References](#references) was read on the page on 2026-10-01
for this proposal, in the linked version. Three limits apply.

- Reference 2's page numbers are those of the linked proceedings file, which
  carries no printed page numbers.
- Reference 7 gives Vtrace(λ) twice, and the two rules differ. Appendix A
  (p. 14) prints the larger of the ratio and one as the factor on the whole
  trace, with no ratio on the error. Clipping at one is the smaller, as
  reference 8 defines it and reference 6 describes it; read as the smaller,
  that rule is the gate. Appendix C.4 (p. 23, eqs. (28) and (30)) caps only
  the previous step's ratio in the trace and keeps the uncapped ratio on the
  error. It says this simplified variant is the one investigated, and
  describes in words the general form that also caps the ratio on the error.
  This page rests the gate on reference 8 and on that general form, and
  treats the investigated variant as an alternative.
- The statement that no source composes these methods with SwiftTD's step-size
  adaptation covers the eight references and SwiftTD's sections 5 and 6 only.

## Refutation attempt

*Refutation attempt.* A fresh-context reviewer, instructed only to break the
first draft of this proposal, read it against the code at a71ed08 and against
the cited pages. It built and ran nothing. Its findings that changed the
proposal were then checked against the code and the pages before the changes
below were made.

**What it found, and what changed.**

| Finding | Change |
|---|---|
| Each cut and restart calls `clearTransient`, which is `O(d)`. The draft claimed every entry was bounded by the eligible and active sets. | Cost paragraph corrected; sparse clear added as obligation 5, which the second review below narrowed to the equality. |
| Extending `Skill.stored` over the bank feeds the feature tester's utility, contradicting "no consumer". | The bank is retired with the other readers and excluded from the utility. |
| The draft disclosed the instability and deferred the correction, which the admission standard does not allow, and applied that standard to its rivals. | Verdict changed: [Admission status](#admission-status). |
| The draft called its trace handling a local construction and said the ratio "only reweights states", which is false above trace parameter zero. | Replaced by the identification with the ratio clipped at one, read on the page in references 7 and 8; the second review below corrected what reference 7 supports. |
| "Nothing is biased" overclaimed, and the comparison billed the ε-soft target's problems to ratio methods under a greedy target. | Obstacle section recomputed for both targets; two counterexamples added to [Limits](#limits). |
| The gate is slower than the worst-case-bounded ratio where the behaviour disagrees with the option. | Stated in [Limits](#limits). |
| Each cut clears the step-size adaptation's registers. | Stated in [Limits](#limits). |
| The candidate set was defined "before any learner write of the step", which the call order cannot provide for an option that ends and restarts within a step. | Redefined at the moment the action is fixed; frame condition added to obligation 3. |
| The dispatcher needs the signal values, which the step does not expose. The finding also named the drawing snapshot; the second review below showed its values are already exposed. | The signal values are recorded as the one interface change. |
| The expectation identity and the obstruction are model statements, not theorems over the executed definitions. | Removed from the Lean obligations and labelled argued. |
| TDRC's experiments adapt a vector of step sizes with Adagrad, so "no source combines these with per-weight adaptation" was too broad; two paraphrases of reference 6 said more than the page. | Reworded. |
| The adaptation labels omitted function approximation and the learning target, and called state values an equivalent specialization. | Labels redone. |
| Byte figures assumed four bytes a word. | Storage given in words, with both byte readings. |
| Wording: the issue's ratio bound, the trace remark in reference 4, Horde's step sizes, which sources draw over nine actions, the empty candidate set, the untrained option. | Corrected in place. |

**What it attacked that survived.**

- The cut's error word equals the word `step` computes, provided the target is
  built from `linearPrediction` of the pre-entry state.
- `step` and `beginTrajectory` agree on a state with clear transients, for
  every reward word.
- The timing: the action is fixed before the demons run, a consistent
  transition is credited to its own state and to earlier consistent ones, and
  an inconsistent transition is credited to none.
- The one-step identity, and the many-step statement in the fixed-weight
  forward view.
- The arithmetic of the ratio bounds, the rate-bound trade and the follow-on
  trace.
- The obstruction family's algebra and threshold. The reviewer found it
  reachable under the mechanism and found the equal-count variant now stated.
- The learner counts, the restore behaviour of the models, the existence of
  the cited declarations, and the page locators of references 1 to 7.

**Second review.** A second independent review read the revised page against
the code at a71ed08, against issue 16 and against the cited pages of
references 6, 7 and 8. It built and ran nothing. Each finding below was checked
against the source before the change was made.

| Finding | Change |
|---|---|
| The page said no theorem states that every register is zero off the eligible list and called the invariant a new obligation. It is `AcornVerif.CurrentLearner.Supported`, machine-checked for every admitted and every `Managed` learner. The described sparse clear also left `vOld` and `vDelta` unreset, so it did not equal `clearTransient`. | Summary, cost paragraph, obligation 5 and the Affordable row now cite the existing theorems; the obligation is the equality alone, and the sparse clear resets both scalars. |
| The page said the step does not expose the executing option's drawing snapshot. `TemporalControl.stepOption` already copies its values into `TemporalDecision.values`, which `TemporalControl.finish` receives. | [Consistency](#consistency) and [Integration](#integration) corrected: one interface change, the signal values. |
| The Sound row said the clip's equivalence survived the refutation attempt, which contradicts the paragraph below; and "Where it stands" said two of the issue's four questions were settled. | Sound row and "Where it stands" reworded: the page proposes answers on targets and ratio handling and leaves the correction and the step-size composition owed; the Sound row no longer says the identification survived the first review. |
| The page cited reference 7 as the online trace form of the gate. Reference 7's Appendix A rule matches the gate only with its larger-of read as smaller-of, and the variant it investigates (Appendix C.4, p. 23) caps only the trace and keeps the uncapped ratio on the error. The identification with V-trace and its fixed-point claim were re-derived against reference 8 and held. | The gate rests on reference 8 and on the general form reference 7 describes. The investigated variant joins Tree Backup(λ) under [Alternatives weighed](#alternatives-weighed). [Source verification](#source-verification) and reference 7's locators record both rules. |
| A restart need not clear: whenever *live* is false the transients are already clear, so `step` equals `beginTrajectory` there and only the cut needs the sparse clear. | Recorded as argued under [Dispatch](#dispatch) and in the cost paragraph; the proposed table is unchanged. |
| The page relied on "research profile", "the annealed comparison", "option" and "demon" without defining them. | Glossed or linked at first use. |

**What was not checked.** The runtime's memory layout; the sections of
SwiftTD outside those cited; issues 10 and 11 beyond their baseline rows. The
second review did not re-read references 1 to 5. The identification with
V-trace, the admission table and the notes on the correction were written
after the first review. The second review re-derived the identification and
corrected the Sound row; the admission table and the notes on the correction
have not had a refutation attempt of their own.

## References

1. <a id="r1"></a>Richard S. Sutton, Joseph Modayil, Michael Delp, Thomas
   Degris, Patrick M. Pilarski, Adam White and Doina Precup, "Horde: A Scalable
   Real-time Architecture for Learning Knowledge from Unsupervised Sensorimotor
   Interaction", AAMAS 2011, §3 (GVF definition, p. 763) and §4 (off-policy
   learning and GQ(λ), pp. 763–764)
   ([PDF](https://www.ifaamas.org/Proceedings/aamas2011/papers/A6_R70.pdf)).
2. <a id="r2"></a>Hado van Hasselt, A. Rupam Mahmood and Richard S. Sutton,
   "Off-policy TD(λ) with a true online equivalence", UAI 2014, Theorem 1
   (file p. 3), GTD(λ) (file p. 6), Theorems 3 and 4 and their proofs (file
   p. 7)
   ([PDF](https://www.auai.org/uai2014/proceedings/individuals/324.pdf)).
3. <a id="r3"></a>Khurram Javed, Arsalan Sharifnassab and Richard S. Sutton,
   "SwiftTD: A Fast and Robust Algorithm for Temporal Difference Learning",
   RLJ | RLC 2024, §5.2 with eqs. (6)–(7) (the overshoot bound) and Algorithm 1
   ([PDF](https://rlj.cs.umass.edu/2024/papers/RLJ_RLC_2024_111.pdf)).
4. <a id="r4"></a>Richard S. Sutton, Doina Precup and Satinder Singh, "Between
   MDPs and semi-MDPs: A framework for temporal abstraction in reinforcement
   learning", Artificial Intelligence 112 (1999), §5, pp. 201–203: the
   deterministic-policy requirement (p. 201), eq. (18) and the consistency rule
   (p. 202), consistency for deterministic options (p. 203)
   ([PDF](https://people.cs.umass.edu/~barto/courses/cs687/Sutton-Precup-Singh-AIJ99.pdf)).
5. <a id="r5"></a>Richard S. Sutton, Marlos C. Machado, G. Zacharias Holland,
   David Szepesvari, Finbarr Timbers, Brian Tanner and Adam White,
   "Reward-Respecting Subtasks for Model-Based Reinforcement Learning",
   Artificial Intelligence 324 (2023), §3: eq. (5) and the update procedure
   (p. 9), the ratio (p. 10), eq. (10) and the experiment's behaviour and trace
   parameter (p. 11); §4: eq. (17) (p. 14)
   ([arXiv:2202.03466v4](https://arxiv.org/abs/2202.03466v4)).
6. <a id="r6"></a>Sina Ghiassian, Andrew Patterson, Shivam Garg, Dhawal Gupta,
   Adam White and Martha White, "Gradient Temporal-Difference Learning with
   Regularized Corrections", ICML 2020, eqs. (5)–(6) and the shared step size
   (pp. 3–4), Theorem 3.1 and its hypotheses (pp. 4–5), the Adagrad step sizes
   and the remark on Vtrace (p. 5)
   ([arXiv:2007.00611v4](https://arxiv.org/abs/2007.00611v4)).
7. <a id="r7"></a>Sina Ghiassian and Richard S. Sutton, "An Empirical
   Comparison of Off-policy Prediction Learning Algorithms on the Collision
   Task", 2021, §3 on ratio products and step size (p. 4), Appendix A update
   rules for TDRC(λ) (p. 13) and for Emphatic TD(λ), Tree Backup(λ) for
   prediction and Vtrace(λ) (p. 14), Appendix C.4 eqs. (28)–(30) with the
   general and the investigated forms of Vtrace(λ) (p. 23)
   ([arXiv:2106.00922v2](https://arxiv.org/abs/2106.00922v2)).
8. <a id="r8"></a>Lasse Espeholt, Hubert Soyer, Remi Munos, Karen Simonyan,
   Volodymyr Mnih, Tom Ward, Yotam Doron, Vlad Firoiu, Tim Harley, Iain
   Dunning, Shane Legg and Koray Kavukcuoglu, "IMPALA: Scalable Distributed
   Deep-RL with Importance Weighted Actor-Learner Architectures", 2018, §4.1:
   eq. (1) and the truncated weights, eq. (3) and the fixed-point policy
   (p. 3), Remark 2 on the trace parameter (p. 4)
   ([arXiv:1802.01561v3](https://arxiv.org/abs/1802.01561v3)).
