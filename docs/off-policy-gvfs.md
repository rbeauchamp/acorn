# Off-policy GVFs: design proposal

This page proposes a design for issue
[#16](https://github.com/rbeauchamp/acorn/issues/16), "Learn GVFs off-policy".
It is a proposal for review. Nothing here is implemented, admitted or scheduled,
and the page describes no current behaviour except where it says so. It was
written against `main` at commit a71ed08. No agent run informed it.

**Where it stands.** The page answers the issue's four design questions: the
method, how per-weight step-size adaptation composes with it, which target
policies to ask about, and how the change relates to U4.
[Admission status](#admission-status) sets the design against each criterion of
the [admission bar](prior-art-review.md#admission-standard). Four criteria
are argued to pass. The third, non-degeneracy, has its correction and its
formal characterization here and its closure owed: the standard asks for a
theorem over the executed code, which only an implementing change can supply.
That change owes the theorems under [Proof obligations](#proof-obligations).
Three earlier drafts were refuted and a fourth corrected;
[Refutation attempt](#refutation-attempt) records how.

**Claim status.** Claims carry the labels of the
[baseline assessment](baseline-assessment.md):

- **Machine-checked**: an existing Lean theorem over the executed definitions.
- **Argued**: derived by hand here; not machine-checked in this repository.
  Every new claim on this page is at most argued.
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
2. **Ratios.** Use no importance ratio. A transition trains option *o*'s
   questions exactly when its action is one *o*'s greedy policy would take. The
   first gradient-TD paper calls this sub-sampling.
3. **Method.** Learn from those transitions with GTD2-MP, a published
   gradient-TD method with a second weight vector that takes an extragradient
   step, at trace parameter zero.
4. **Step sizes.** One step size for both vectors, capped on each step by a
   rate bound of SwiftTD's kind. No per-weight adaptation in this change.

The reasons, in brief:

- With a deterministic target only one action has a nonzero ratio, so dropping
  the ratio cannot change which policy is evaluated. It changes only how
  histories are weighted.
- A learner without a gradient correction can diverge off-policy. The page
  shows this inside Acorn's own feature class.
- In exact arithmetic, one GTD2-MP step never increases the joint distance
  from the two weight vectors to any pair that explains the step's signal. That
  holds on every transition, for every stream, with no assumption about
  policies, features or sampling. The plain GTD2 step lacks the property. It is
  the formal characterization the admission standard asks a correction to
  have, and it is why this method is chosen over others.
- The inequality is stated in a norm that a changing per-weight step size
  would change, so adaptation is left out.

[Decisions requested](#decisions-requested) lists the ten choices a reviewer is
asked to accept or change.

## What Acorn does now

- **Questions.** The eleven signals are the closed family `Cumulant` in
  [Cumulants](../lean/Acorn/Handcrafted/Cumulants.lean), each with one of three
  discounts (0.99, 0.95 or 0.90) from `demonDiscount`. The family is declared
  departure [D5](learned-only-binding.md#d5--prediction-targets--step-2).
- **Learner.** `DemonBank.step` in [Demon](../lean/Acorn/Demon.lean) applies one
  SwiftTD `step` per signal on every primitive step of a profile that is not
  frozen, from `PredictionControl.advance`, which `TemporalControl.finish`
  calls after the step's action has been selected. In a frozen profile
  `PredictionControl.advance` steps no demon. A **demon** is the learner of one
  GVF.
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
- **GTD2** is a one-step gradient-TD method for state values with linear
  features [[9]](#r9). It keeps a main weight vector and a second one that
  estimates the expected TD error given the features, and it descends the
  mean-square projected Bellman error. Its setting takes the first state of
  each transition independently from an arbitrary distribution, and the
  transition from a stationary policy; the paper says this corresponds to
  off-policy learning. Its convergence theorem assumes independent samples,
  decreasing step sizes and two nonsingular matrices. In on-policy experiments
  it is slower than TD and than the same paper's TDC, and it converges on
  Baird's counterexample where TD diverges.
- **GTD2-MP** writes GTD2 as stochastic gradient steps on a saddle-point
  problem and replaces the step by an extragradient one: a trial step to a
  midpoint, then a step from the original point along the midpoint's direction
  [[10]](#r10). The collision study gives the rules with traces and two step
  sizes as Proximal GTD2(λ). On its off-policy task at trace parameter zero,
  Proximal GTD2 reached the lowest error of the gradient-TD methods it
  compares, which include TDC and TDRC; it was more sensitive to the step size
  than all of them but GTD2; and it alone showed an error that dipped and then
  rose. The authors suggest it may not have converged to the minimum of the
  projected Bellman error [[7]](#r7). Reference 10 also:
  - projects both weight vectors onto bounded closed convex sets after each
    step, in its analysed versions of GTD and GTD2;
  - analyses averaged iterates for independent samples, and leaves samples
    generated online by an agent to future work;
  - describes rejected sampling, which it attributes to the original
    gradient-TD papers: a transition is rejected, and the weights are not
    updated, when the target policy gives its action probability zero. It
    calls this inefficient when the policies differ much;
  - states that a biased estimate of the importance ratio can cause large
    estimation error;
  - notes that TDC appears to have no explicit saddle-point form, and
  - reports GTD2-MP improving on GTD2 on Baird's counterexample with constant
    step sizes.
- **Sub-sampling** is the first gradient-TD paper's formulation of off-policy
  learning [[11]](#r11). For a deterministic target policy it discards every
  transition whose action is not the target's and treats the rest as
  transitions of the target policy, with no importance ratio. Its setting is a
  single continuing trajectory with no resets, with states visible only
  through their features. It proves convergence of its algorithm on the
  sub-sampled process, assuming the behaviour takes the target's action with
  positive probability in every state. It notes that the weighting of states
  is then the sub-sampled process's own, and that weighting by the ratio
  instead may match the target policy's value function better.
- **Intra-option model learning** updates the model of every option whose
  policy is consistent with the action taken. The method requires the option's
  policy to be deterministic and uses no importance ratio. It is given for the
  one-step, tabular case with a fixed option [[4]](#r4).
- **V-trace** truncates both the ratio on the error and the ratio in the trace,
  each at its own level [[8]](#r8). TDRC's authors describe Vtrace as TD with
  its importance ratios clipped at one, and report that it does not prevent
  divergence on Baird's counterexample [[6]](#r6).
- **Reward-respecting subtasks** learns every subtask's value function
  off-policy on every step with a per-step ratio and no gradient correction,
  and its option models likewise [[5]](#r5). Its experiments use an
  equiprobable behaviour over four actions and trace parameter zero, so its
  ratios are at most four.
- **True online GTD(λ)** is the published off-policy form of the true online
  TD(λ) that SwiftTD extends. Its derivation substitutes the product of the
  ratio and the step size for the step size [[2]](#r2).
- **TDRC** is a gradient-TD method whose second weight vector shares the main
  step size and carries a regularization term [[6]](#r6). Its updates are not
  gradients; its convergence theorem holds under conditions on that term and
  on the step-size ratio. Its prediction experiments adapt a vector of step
  sizes with Adagrad, and it reports GTD2 as the slowest of the methods it
  compares.
- **Emphatic TD(λ)** keeps one weight vector and scales updates by a follow-on
  trace that is multiplied by the previous step's ratio [[7]](#r7).

None of the sources read here composes an off-policy correction with step-size
adaptation of SwiftTD's meta-gradient kind [[3]](#r3). Issue 16 assumes no
published SwiftTD variant and asks the design pass to decide the composition.
This was not a literature search.

## Why not importance ratios

Write π for a target policy, b for the behaviour at a step and ρ = π(a)/b(a)
for the ratio at the action a taken. All of this section is **argued**.

**How large the ratio gets.** At a drawing step the acting source gives every
action at least mass ε/9.

- *Greedy target.* If the target takes one action a\*, the ratio is 1/b(a\*)
  when a = a\* and zero otherwise. It is at most 9/ε = 900, attained when the
  acting source's greedy set excludes a\* and the source explores into it. That
  event has probability ε/9, about 0.0011, on such a step.
- *ε-soft target.* If the target is option *o*'s own ε-greedy policy, its
  greedy action has mass at most 1 − ε + ε/9, so ρ ≤ 9/ε − 8, about 892.

Issue 16 states the general bound, the inverse of the behaviour's least action
probability; these are its values here.

**A rate bound cannot absorb it.** SwiftTD bounds the correction ratio τ = Σ αᵢ
over the active features by a budget η [[3]](#r3). The published off-policy
form replaces each step size α by ρα [[2]](#r2), so the correction ratio of an
off-policy update is ρτ. Bounding the worst case, ρ_max·τ ≤ η, keeps the update
unbiased and makes every state move at expected rate η/ρ_max per visit, about
1.1·10⁻⁴. With about 1,300 active features at 5·10⁻⁵ each (the
[baseline assessment](baseline-assessment.md) gives both figures), τ is about
0.065, so that is about 585 times slower than on-policy. Bounding the realized
product instead makes the scale depend on the action; the method then reads the
behaviour probability, which Acorn's nominal masses only approximate, and a
biased ratio is itself a published hazard [[10]](#r10).

**Emphatic TD has no bound.** Its follow-on trace is F ← ρ_prev·γ·F + 1
[[7]](#r7). One step with ρ = 900 multiplies it by 891 at γ = 0.99. Issue 16
asks that every update's size have a derivable bound; this method has none
here.

**ε-soft targets cannot be ratio-corrected on served steps.** On a served
continuation the behaviour is a point mass on the committed action. An ε-soft
target gives every action positive probability, so a ratio-weighted update
needs outcomes of actions the behaviour cannot take at that step. With a
greedy target and no ratio, a served step is simply used or not, according to
whether the committed action is the target's. The histories it is not used on
get no weight; [Limits](#limits) states what that costs.

## Why not a learner without a correction

Semi-gradient learning follows the TD error and ignores how the weights move
the bootstrap target. Off-policy, that can be unstable, and dropping or
clipping the ratio does not help: TDRC's authors report divergence of the
clipped method on Baird's counterexample [[6]](#r6), and the GTD2 paper shows
TD diverging on it [[9]](#r9). The following family shows the same failure
inside Acorn's own feature class, binary features with a common step size. It
is **argued**.

Take K ≥ 2 states. State k has two active features: a shared one, with weight
w₀, and its own, with weight wₖ. The target's action leads from each of them to
one successor state in which all K + 1 features are active. The signal is zero
and the successor is never updated, because the behaviour never takes the
target's action there. With W the sum of the own weights, the successor's
prediction is w₀ + W, and the expected semi-gradient update of each of w₀ and
W, per unit step size and weighting the K states equally, is

> K(γ − 1)·w₀ + (Kγ − 1)·W.

The direction w₀ = W is therefore scaled by 2Kγ − K − 1 per unit step size,
and grows whenever

> γ > (K + 1) / (2K).

The threshold is 3/4 at K = 2 and falls toward 1/2. All three of Acorn's
discounts exceed 3/4. The successor need not have more active features than
its predecessors: two such groups whose successor has only the two shared
features active give the same factor.

The precondition is structural: states where the behaviour seldom takes the
option's action are seldom updated, while their predecessors may be updated
often. Where the acting source's greedy action differs from the option's, the
option's action is taken with probability ε/9, one step in 900, when another
option acts. Under the primitive controller, persistent exploration raises
that to about one step in 170: the baseline assessment's renewal formula puts
about 5.2% of primitive steps in exploration runs at ε = 0.01, each run
repeating one uniformly drawn action. Every weight write passes `Weight.project`, so the
failure would appear as weights held at a rail and predictions that mean
nothing: containment is not accuracy.

The first two drafts of this page proposed exactly such a learner, SwiftTD run
over consistent stretches of the stream. The admission standard requires a
correction for a known degeneracy, and disclosure does not clear it.

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
  reach `TemporalControl.finish`: `TemporalControl.stepOption` copies them into
  `TemporalDecision.values`, and the candidate set reads only the values and
  the tie window, not the snapshot's ε;
- for every other slot, T is computed from the slot's policy, which nothing
  writes between that moment and the update. Writes that precede the action,
  such as the terminal write to an option that has just ended, are included.

The step is **consistent with *o*** when the action taken is in T. The test
reads no behaviour probability. It does read the decision's source
(`TemporalSource`), to choose which values supply T: `TemporalDecision.values`
holds an option's drawing snapshot only on that option's own step, and on
every other step holds the primitive controller's values, which supply no
slot's T. If no value is comparable, T is empty and no action is consistent.

### The corrected step

A learner keeps two weight vectors over the feature indices: the main weights
w, whose sum over the active features is the prediction, and the second
weights u. Both pass `Weight.project` on every write.

One step takes a transition: the active set x at the earlier step, the active
set x′ at the later step, the signal value c that arrived with x′, and the
learner's discount γ, which lies between zero and one. There are two
constants, a step size α and a rate budget η.

If x is empty the step does nothing. Otherwise, once per transition, shared
by every learner:

1. **Classes.** Split the indices into those only in x, those only in x′ and
   those in both, with counts n₁, n₂ and n₁₂.
2. **Step.** h = min(α, η / (|x| + |x′|)).

Then for each learner:

3. **Read.** y is the sum of w over x, y′ the sum of w over x′, and p the sum
   of u over x, each an ordered sum in the set's stored order, as SwiftTD's
   are.
4. **Error.** δ = c + γ·y′ − y.
5. **Midpoint.** τ = h·|x| and κ = h·(n₁ + γ²·n₂ + (1 − γ)²·n₁₂). Then
   p_m = p + τ·(δ − p), δ_m = δ − κ·p and e_m = δ_m − p_m.
6. **Second weights.** Add h·e_m to u at every index of x.
7. **Main weights.** Add h·p_m to w at each index only in x, subtract γ·h·p_m
   at each index only in x′, and add (1 − γ)·h·p_m at each index in both. Each
   index is written once.

Without the projection, this is Algorithm 2 of [[10]](#r10) with ratio one
and the step h. That algorithm forms midpoint vectors and reads two inner products from them; p_m
and δ_m are those two inner products, which are affine in p and δ, so the
midpoint vectors are never formed. Plain GTD2 [[9]](#r9), eqs. (8) and (9), is
steps 6 and 7 with δ − p in place of e_m and p in place of p_m.

### Dispatch

The agent keeps one copy of the previous step's active set, and for each slot
one flag, *armed*, saying whether the previous action was consistent with that
slot. On each primitive step of a profile that is not frozen, with the current
active set x′ and the arriving signal values:

- for each armed slot, apply one corrected step to each of its eleven learners,
  with the stored set as x;
- then set each slot's flag to the current step's consistency and store x′.

A transition is therefore used exactly when its own action was consistent. A
flag starts clear, so the first step after start or restore updates nothing,
and a reinstalled slot starts with a clear flag. There are no traces, so
nothing is cut or cleared.

### What it learns

Model the step's action as drawn from a distribution b that may depend on the
whole history (**assumed**: the generator is deterministic, and this is the
idealized draw that the exploration results of U2 also assume). The following
are **argued**, for a T fixed before the draw.

**The gate.** For any quantity X determined by the action and its outcome,

> E[ 𝟙(a ∈ T)·X | history ] = b(T) · E[ X | history, a drawn from b restricted to T ].

Both sides are the sum of b(a)·E[X | a] over a in T. So a consistent
transition is a sample of the policy "b restricted to T", and the histories are
weighted by b(T). When T has one action that policy is *o*'s greedy action,
whatever b is. When T has several, it is a greedy policy for *o* whose
tie-breaking is the acting source's. For this restricted policy the importance
ratio is 1/b(T) on T and zero off it, so the gate is also that ratio clipped
at one.

This is sub-sampling [[11]](#r11), and it gives the one-step conditional
expectations of the gradient-TD setting: transitions of the evaluated policy
from first states with some weighting [[9]](#r9) [[10]](#r10). It does not
give that setting's fixed weighting or its stationary policy, and the source's
assumption that the behaviour takes the target's action with positive
probability in every state fails on served steps.

**The fixed point.** The mean of the corrected step vanishes where
E[h·e_m·x] = 0 and E[h·p_m·(x − γx′)] = 0, with the expectations over
consistent transitions. The step h, and τ and κ with it, vary with the sizes
and the overlap of the active sets and sit inside the expectations. In the
special case of independent samples whose active sets all have the same sizes
and the same overlap, so that h, τ and κ are constants, write
A = E[x(x − γx′)ᵀ], C = E[x xᵀ] and b = E[c·x]. The two conditions then reduce
to

> ((1 − τ)² / (1 − τ + κ))·AᵀC⁻¹(b − A·w) + τ·E[δ·(x − γx′)] = 0,

whose solution minimizes that first coefficient times the mean-square
projected Bellman error plus τ times the mean squared TD error. As the step
size goes to zero the second term vanishes and the point is the TD fixed point
for the weighting, as for GTD2. At a constant step it is the minimizer of the
blended objective. The weight τ is at most η, and about 0.05 at typical sizes.
It weights the objectives, not the displacement: the blended minimizer need
not lie between the two minimizers, and where the problem is ill-conditioned
it can sit farther from the TD fixed point than the squared-TD-error minimizer
does. Where some weight vector makes every TD error zero, the two objectives
share that minimizer and the blend changes nothing. Clipping is ignored here:
the statement is for weights that stay inside the range. [Limits](#limits)
states what the blend costs.

What follows from the gate:

- **There is no ratio to bound.** Issue 16's bounded-ratio obligation holds
  trivially: the weight on a transition is zero or one.
- **No behaviour probability is read.** The nominal masses in
  `PolicySnapshot.probabilities` are not exact probabilities of the finite-word
  draws; this method does not depend on them.
- **Served exploration is not a special case.** It is the statement with b a
  point mass, so b(T) is one or zero.
- **On-policy data is used.** When *o* itself executes and its candidate set
  is nonempty, its non-exploratory action is in T, so its own steps train its
  questions.
- **An untrained option asks the on-policy question.** All nine values of a
  fresh or reinstalled option tie at zero, so every action is consistent until
  its values separate by more than the tie window.

b(T) is not a correction that restores a chosen weighting; it *is* the
weighting. The learner weights histories by how often the behaviour is there
and agrees with the option.

### The energy inequality

This is the property that answers the instability. It is **argued**. Its
algebra is given as a Lean file in the [appendix](#appendix-the-algebra-in-lean),
which compiles against the repository's pinned Mathlib and is not part of the
repository's checked corpus.

All of it is in exact arithmetic; obligation 1 owes the rounding term.

Fix any main weight vector w\* inside the weight range, and measure a learner
by N = |u|² + |w − w\*|², the squared joint distance from (u, w) to (0, w\*).
For a transition write a = x − γx′ as a vector, with entries 1, −γ and 1 − γ on
the three classes, so that κ = h·|a|². Write q = aᵀ(w − w\*), e = δ − p, and
ε = c − aᵀw\*, the TD error w\* leaves on this transition. Then e = ε − q − p.

**Zero residual.** If ε = 0, steps 6 and 7 without projection change N by
exactly

> −h·[ 2·p_m² + τ·e² + κ·p² − τ·(τ·e + κ·p)² − κ·τ²·e² ].

The two subtracted terms are at most τ·(τ + 2κ)·(τ·e² + κ·p²), so the change
is at most

> −h·[ 2·p_m² + (1 − τ·(τ + 2κ))·(τ·e² + κ·p²) ],

which is not positive whenever τ·(τ + 2κ) ≤ 1.

*Derivation.* Step 6 changes |u|² by h·(2·p·e_m + τ·e_m²), and step 7 changes
|w − w\*|² by h·(2·q·p_m + κ·p_m²), because x has |x| ones and a has squared
length |a|². Substituting p_m = p + τ·e, e_m = (1 − τ)·e − κ·p and
e = −(p + q) gives the first display. This is the standard extragradient
identity, specialized: the step's linear part is a skew term, which preserves
N to first order, plus a term that only shrinks u.

**The guard holds by construction.** The step gives τ = h·|x| ≤ η. Every entry
of a has square at most one because γ is between zero and one, so
κ ≤ h·(|x| + |x′|) ≤ η. Then τ·(τ + 2κ) ≤ 3η², which is 0.03 at η = 0.1.

**Projection.** `Weight.project` clips a finite word to a symmetric range,
coordinate by coordinate. Clipping a coordinate never moves it away from a
point inside the range, and both 0 and w\* are inside it. The midpoint is
computed in scalars and never written, so each weight is written once, and the
two changes above are each an upper bound after clipping. `Weight.project`
sends a NaN to zero, which is not a clip; obligation 2 owes that no word of
the step is NaN or infinite.

**Nonzero residual.** The step is an affine map of (u, w − w\*) whose linear
part is the zero-residual step. The residual adds a push of squared length
h·ε²·(τ·(1 − τ)² + κ·τ²), which is at most h·τ·ε² when κ ≤ 2 − τ. So for any
w\* in the range,

> √N after ≤ √N before + |ε|·√(h·τ) ≤ √N before + |ε|·√(α·η).

**What it rules out.** The bound holds on every corrected step, whatever the
features, signals, policies and consistency pattern. So along any sequence of
corrected steps √N grows by at most the sum of |ε|·√(α·η). With w\* = 0 the
residual ε is the signal c itself, so under a zero signal |u|² + |w|² never
increases. The instability family above has a zero signal and growing weights;
under the corrected step it cannot occur. Geometric growth of the weights from
their own bootstrap, which is what divergence means here, is impossible.

Three qualifications:

- N is a joint quantity. The main weights alone can move away from w\* on a
  step while u moves toward zero by more.
- Growth at most linear in the accumulated residual remains possible, and the
  weight range contains it.
- Retirement and reinstallation are not corrected steps. They set weights to
  zero, which cannot increase |u|² + |w|² but can increase the distance to a
  nonzero w\*.

**Why not plain GTD2.** With steps 6 and 7 using δ − p and p, the same
calculation gives a change of −h·[(2 − κ)·p² − τ·e²]. At p = 0 that is
+h·τ·e²: the step moves u and leaves w, so N grows. The extragradient step is
what removes this. GTD2's published guarantee is of a different kind, a
convergence theorem for independent samples and decreasing step sizes
[[9]](#r9).

**Per-weight step sizes.** The same argument holds for any fixed positive
per-weight step sizes, with each squared coordinate in N divided by its step
size. It does not survive a step size that decreases: the weights stay put and
the measure of them grows. This is why step sizes are not adapted here.

### Published basis and adaptation kinds

Following the [material adaptation contract](prior-art-review.md#admission-standard):

- **Published variant: the method.** GTD2-MP at ratio one [[10]](#r10),
  Algorithm 2. It coincides with Proximal GTD2(λ) [[7]](#r7) at trace
  parameter zero, ratio one and equal step sizes. Horde's GQ(λ) is in the same
  gradient-TD family, with traces and action values [[1]](#r1). *Reason for
  this member:* it is the published form with the per-step inequality above. Plain GTD2 lacks it. TDC is reported to have
  no explicit saddle-point form [[10]](#r10), and TDRC shares TDC's main
  update.
- **Published variant: the gate.** Sub-sampling for a deterministic target
  [[11]](#r11), which [[10]](#r10) calls rejected sampling. Intra-option model
  learning uses the same rule for deterministic option policies [[4]](#r4).
  *Reason:* it needs no ratio and no behaviour probability. *Consequence:* the
  weighting of histories is the sub-sampled process's own, b(T) times the
  visit distribution, as the source says.
- **Published variant: state values.** Horde's demons are action-value
  functions [[1]](#r1). The gradient-TD sources here are stated for state
  values [[9]](#r9) [[10]](#r10) [[11]](#r11). *Consequence:* a question about
  π answers "follow π from here", not "take this action, then follow π".
- **Local approximation: projection.** The source's analysed GTD and GTD2
  project both vectors onto bounded closed convex sets after each step
  [[10]](#r10), Algorithm 1, and it prints GTD2-MP without projection. Here
  the final writes are clipped to Acorn's weight range and the midpoint is
  not. *Reason:* every weight write in Acorn passes the projection; the
  midpoint is never written, and projecting it would need the midpoint
  vectors and a second pass. *Consequence:* the energy inequality covers this
  placement. The fixed-point statement does not cover clipping, and none of
  the source's bounds is claimed.
- **Local approximation: the last iterate at a constant step.** The source's
  analysis outputs a step-size-weighted average of the iterates and takes a
  step size that shrinks with the sample count; its Baird experiment uses a
  constant one. Acorn's continuing setting uses the last iterate and a constant
  cap. *Consequence:* the source's finite-sample bound does not apply, and the
  mean fixed point is the blend of [What it learns](#what-it-learns).
- **Local approximation: the rate bound.** The step is the smaller of α and
  η/(|x| + |x′|), SwiftTD's bound [[3]](#r3) applied to both active sets.
  *Reason:* it makes the inequality's guard hold by construction.
  *Consequence:* at typical sizes the second term binds, so the step is
  normalized by the number of active features and weights transitions by its
  reciprocal.
- **Local approximation: consecutive samples from a changing agent.** The
  sources assume a stationary policy and a fixed weighting, and mostly
  independent samples [[9]](#r9) [[10]](#r10); the sub-sampling source treats
  a single trajectory and features that hide the state [[11]](#r11). Acorn's
  transitions are consecutive and the target is the greedy policy of an option
  that is still learning. No published convergence
  or finite-sample statement survives. The energy inequality needs none of
  those assumptions. With shared features the weighting b(T) changes the
  answer; see [Limits](#limits).
- **Local approximation: ties.** The source requires a deterministic target
  [[11]](#r11). A tie makes the target "the acting source's choice among *o*'s
  tied actions". *Reason:* an untrained option ties on all nine actions, and a
  fixed tie-break would discard most of its own steps. *Consequence:* on tied
  steps the target depends on who acted. Decision 6 offers a canonical
  tie-break instead.
- **Equivalent specialization: discount.** A constant discount between zero
  and one in place of a termination function. The guard uses that range.
- **Not composed: per-weight step-size adaptation.** See the last paragraph of
  [The energy inequality](#the-energy-inequality) and decision 4.

## Integration

These are the intended owners, for sizing and review; the implementation change
would settle the details.

- **Kernel.** A new learner type beside SwiftTD's, holding two weight vectors
  and no transient registers, with the corrected step as its one learning
  entry. This is new learner arithmetic, with its own proofs.
- **Storage.** `Skill` in [FeatureConsumers](../lean/Acorn/FeatureConsumers.lean)
  gains a bank of eleven such learners and its *armed* flag, so `Skill.initial`
  gives a reinstalled slot a fresh bank and a clear flag. The previous active
  set is stored once, with the learned consumers and not among the
  process-local references: retirement must edit it, and the machine-checked
  `FeatureRuntime.retire_references` says retirement leaves the references
  unchanged.
- **Retirement, yes; readers and utility, no.** `Skill.retire` extends over the
  bank: a replaced feature's weights, both vectors, are zeroed, and its index
  is dropped from the stored active set. `Skill.readers` and `Skill.stored`
  do not extend over it. Their element type is the SwiftTD learner, which the
  new learner is not, and `Skill.stored` feeds `Lifecycle.score`, the feature
  tester's utility, so including the bank would let these predictions decide
  which features are replaced. Two consequences: the retirement theorem
  `replace_zero` ranges over readers, so the bank needs a companion statement;
  and a feature useful only to these questions can be replaced.
- **Index classes.** `SwiftTd.ActiveSet` is an unordered list without
  repeats. Splitting two of them into the three classes in work proportional
  to their sizes needs a membership structure: one mark per feature index,
  all clear between steps, set over x′ and cleared again within the step. It
  is stored once.
- **Step.** The updates run where the on-policy demons do, in
  `TemporalControl.finish`, after selection has fixed the action. They need the
  signal values, which `PredictionControl.advance` computes and does not
  return.
- **Candidate sets.** One `Controller.predictAll` call for each slot that is
  not executing.
- **Lifecycle.** Frozen profiles update nothing. `Ensemble.restore` leaves the
  bank cold, the flags clear and the stored set empty, as it leaves the models
  cold, so the checkpoint format does not change.
- **Selection.** A core selection beside `PlanningSelection`, off by default.
- **An observer.** With the bank outside the tester's utility, no feedback into
  features and no random draw, the bank affects no decision and no other
  component, whether or not it is selected. Its predictions are visible only
  through diagnostics until a later change adds a reader.

**Cost (argued).**

- **Storage.** A learner stores two words per feature index over 16,384
  indices: 32,768 words. Thirty-three learners add 1,081,344 words. The marks
  add one per index, and the stored active set one index list. In bytes the
  weights are about 4.3 MB at four bytes a word and about 8.7 MB if the runtime
  stores each array slot in eight. Which holds was not measured. For
  comparison, an existing SwiftTD learner stores eleven words per index, and
  the agent's 57 learners under discounted control hold 10,272,768.
- **Work.** Per step: at most three `predictAll` calls (27 ordered sums over
  the active set), one classification pass over the two active sets, and at
  most 33 corrected steps of three sums and two write passes each. Everything
  is proportional to the active sets. Nothing is proportional to the weight
  space. This meets issue 16's `O(active)` work.

## Proof obligations

None of these exists yet. Each would be a Lean theorem over the executed
definitions in an implementing change.

1. **Energy.** For the executed corrected step, read through the real values
   of its words: the zero-residual inequality and the residual bound of
   [The energy inequality](#the-energy-inequality), with projection included
   and an explicit term for finite-word rounding.
2. **Finiteness.** With finite weights and a finite signal, every word of the
   step is finite, so each projection is a clip.
3. **Guard.** The step makes τ and κ at most η, from the structure of the
   step, the absence of repeats in `SwiftTd.ActiveSet` and the discount's
   range.
4. **Classes and single write.** The three classes partition the union of the
   two active sets, each index is written once, and the marks are all clear
   after the step.
5. **Membership and frame.** The consistency test holds exactly when the action
   is in `PolicySnapshot.candidates`; and no write to a non-executing slot's
   policy lies between the action being fixed and the update.
6. **Self-consistency.** When an option's candidate set is nonempty, its
   non-exploratory draw is consistent with it. This follows from the existing
   `reservoir_nonempty`.
7. **Work, storage and observation.** The counts of the cost paragraph, from
   the structure. With the selection off, `Agent.act` produces the same result;
   with it on, every decision and every other component is unchanged.
8. **Lifecycle.** `FreeDispatch.refresh_retains` extends to the bank; a
   companion to `replace_zero` covers both weight vectors; a retired index is
   absent from the stored active set; a reinstalled slot has a clear flag;
   restoration yields a cold bank, clear flags and an empty stored set.

Three further statements are about an idealized model and not the executed
learner: independent samples, exact arithmetic and the idealized draw.
`AGENTS.md` does not accept such a theorem as verification of the
implementation without a checked correspondence, and none is proposed. They
explain the design and stay **argued**.

- **The gate identity** of [What it learns](#what-it-learns).
- **The fixed point** of [What it learns](#what-it-learns).
- **The instability family** of
  [Why not a learner without a correction](#why-not-a-learner-without-a-correction).

## Limits

### No convergence theorem

The energy inequality bounds growth. It does not say the weights converge, or
to what. The published statements assume independent samples and either
decreasing step sizes or averaged iterates [[9]](#r9) [[10]](#r10); Acorn's
options, features and behaviour all change, its samples are consecutive, and
it uses the last iterate at a capped step. The fixed-point statement above is
for a frozen snapshot with independent samples. PAR-3's existing caution about
convergence applies unchanged.

### A constant step blends in the squared TD error

At a constant step the extragradient step's mean fixed point blends the
mean-square projected Bellman error with the mean squared TD error, at weight
about τ. Minimizing the squared TD error from single samples is known to give
the wrong answer when transitions are stochastic or states are aliased: it
pulls a state's value toward its predecessors' as well as its successors'
[[9]](#r9). Acorn's features are aliased, so the blend is a real bias in
Acorn's conditions. Its weight is bounded by the rate budget and vanishes as
the budget does. The displacement of the fixed point is not bounded by that
weight: along directions where the projected Bellman error is nearly flat the
blended term decides the answer, and the fixed point can lie outside the
segment between the two minimizers. The collision study's authors suggest
that Proximal GTD2 may not have converged to the minimum of the projected
Bellman error on their task [[7]](#r7), which is consistent with a blend and
does not establish one. How far the result sits from the TD fixed point in a
run is UNKNOWN. Decision 10 asks whether to accept it at the demons' budget or
lower the budget for these learners.

### The weighting changes the answer

- **A starved successor.** In the tabular case, let the option's action lead
  from s₀ to s₁ and from s₁ to a signal of one, with b(T) = 0 at s₁. No
  transition out of s₁ is ever used, so nothing ties the prediction at s₁ to
  that signal. The true value at s₀ is γ. The learner settles on some pair
  with the prediction at s₀ equal to γ times the prediction at s₁, and from
  zero weights that pair is zero.
- **Aliasing.** Let two histories share a feature vector with equal
  probability. In the first b(T) is 0.9 and the option's action yields one; in
  the second b(T) is 0.1 and it yields zero. The gated answer is 0.9. The
  value of the option's action at that feature vector under the visit
  distribution, which an unclipped ratio would learn, is 0.5.
- **Slow where the behaviour disagrees.** Where the acting source's greedy
  action differs from the option's, the option's questions are trained on
  about one step in 170 under the primitive controller and one in 900 under
  another option. Reference 10 makes the same point about rejected sampling.

### Slower than the alternatives

- **No traces.** A signal reaches earlier states one step per update. Horde
  notes that behaviour seldom matches a target for more than a few steps
  [[1]](#r1), which limits what traces could add for an option that rarely
  executes, but an executing option's long stretches would benefit.
- **The main weights move only through the second weights.** GTD2 is reported
  slower than TD and TDC [[9]](#r9) [[6]](#r6). GTD2-MP is reported faster
  than GTD2 on Baird's counterexample [[10]](#r10). On the collision task
  Proximal GTD2 reached lower error than TDC and TDRC at trace parameter zero
  but was more sensitive to its step size, and TDRC was the easiest to use
  [[7]](#r7).
- **No step-size adaptation.** The on-policy demons adapt a step size per
  weight; these learners do not.

Whether the predictions become accurate enough to use, and how fast, is
UNKNOWN.

### Other limits

- **Nothing reads the predictions yet.** Whether they are useful is UNKNOWN.
- **The baseline scorecard row would read Adapted.** Horde's demons are
  action-value functions under GQ(λ) with ratios and traces; these are
  state-value functions under GTD2-MP with rejected sampling and none.
- **Ties make the target depend on the acting source**, as stated above.
- **The gate identity is conditional on the idealized draw.**

## Admission status

Against the five criteria of the
[admission bar](prior-art-review.md#admission-standard). Each row is this
page's argued position; none is a verdict. The verdict is the maintainer's,
and admission is recorded with the implementing change.

| Criterion | Position | Why |
|---|---|---|
| Sound | Argued | The corrected step is a published algorithm, read on the page, with three local changes: the step rule, clipping of the final writes, and use of the last iterate. The gate identity is derived above. The energy inequality's algebra is in the appendix as a Lean file a reader can compile. |
| In-setting | Argued | One stream, batch size one, no replay, no target network, no resets, bounded work per step. |
| Compatible and non-degenerate | Characterized; closure owed | The known degeneracy is the off-policy instability of semi-gradient learning. The correction is GTD2-MP's second weight vector and extragradient step. Its formal characterization is the energy inequality. Closure at the strongest layer is a universal theorem over the executed step, obligations 1 to 3, and it can exist only with the implementation. |
| Affordable | Argued | Work proportional to the active sets; two words per index per learner. |
| Buildable | Argued | The step is specified to the arithmetic, and the index classes to a named structure. No mechanism is left to invent. |

Three things on this page weigh against admission and are the maintainer's to
judge:

- **The blend.** The standard says a nonzero update is insufficient if it
  learns the wrong quantity. At a constant step the fixed point minimizes an
  objective that carries the squared TD error at weight about τ, and that
  error's minimizer is biased under aliasing. It is a property of the
  published method at a constant step and vanishes with the step. Decision 10.
- **The weighting.** Sub-sampling answers under its own weighting of
  histories, not the visit distribution. The aliasing example gives 0.9 where
  a ratio-corrected learner gives 0.5, and a state the behaviour never leaves
  by the option's action is never learned. The source of sub-sampling says the
  ratio weighting may match the target's value function better
  [[11]](#r11). This page's position is that the ratio's cost in Acorn
  outweighs that; decision 2.
- **Closure before code.** The standard asks for closure of a known
  degeneracy, and says disclosure does not clear it. What this page supplies
  is the correction and its characterization, not a theorem over executed
  definitions. Approving the design is a decision to build toward obligations
  1 to 3, not an admission.

Usefulness, accuracy and learning speed are UNKNOWN. The contract allows
uncertain usefulness to remain.

## Alternatives weighed

| Alternative | Verdict | Reason |
|---|---|---|
| SwiftTD over consistent stretches, with traces and no correction (the first two drafts) | No | Semi-gradient: the instability family applies and the admission standard requires a correction. Its trace clears were also proportional to the weight space. |
| Plain GTD2 on the consistent transitions | No | A step can increase N. Its guarantee needs independent samples and decreasing step sizes. No blend at a constant step. |
| GTD2 with its two updates in sequence (the third draft) | No | Has a per-step inequality and the same kind of blend, but is unpublished. GTD2-MP is the closer published construction and costs the same. |
| TDC or TDRC on the consistent transitions | Not now | Reported faster than GTD2 [[9]](#r9) [[6]](#r6), and TDRC the easiest to use on the collision task [[7]](#r7). No per-step inequality is known for either: the main update contains the semi-gradient term, which can raise N on a step, and TDC is reported to have no explicit saddle-point form [[10]](#r10). TDRC's theorem is conditional on its regularization and step-size ratio [[6]](#r6). |
| Proximal GTD2(λ) or GQ(λ) with traces | Not now | The argument here does not extend to traces: with a trace the step is no longer the extragradient step of one transition's operator. A trace version needs its own closure. |
| Unclipped ratios with any of the above | No | Ratios up to 900, the rate-bound trade, and dependence on behaviour probabilities that are only nominal. |
| ε-soft option policies as targets | No | Cannot be ratio-corrected on served steps. |
| Emphatic TD(λ) | No | The follow-on trace has no bound at these ratios. |
| V-trace, or Tree Backup(λ) for prediction | No | Semi-gradient. |
| Action-value GVFs with expected backups | Not now | No ratio at one step, but nine weight vectors per question, doubled by the correction. |
| Adapted per-weight step sizes read from the matching on-policy demon | Follow-up | Reuses SwiftTD's adaptation without a new meta-gradient. A decreasing step size breaks the inequality's norm, so it needs its own closure. Reading them once when a slot's bank is created keeps the inequality, at the cost of one more vector per learner. |

## Relation to U4 and U5

[U4](https://github.com/rbeauchamp/acorn/issues/10) asks that every option's
policy and model learn from every step on which the option's policy is
consistent with the action taken. Its conformance text uses the consistency
rule; its design pass is still to choose between a consistency test and an
importance ratio. It meets the same instability once an option learns from
steps it did not take. It does not follow that this design is U4's mechanism.
U4's stated obligations include two this design does not meet:

- **Reduction.** On the executing option's own steps U4's update must reduce
  to the current on-policy updates, which use traces. The corrected step is a
  different learner with a different fixed point.
- **Stochastic option policies.** U4 asks for a published off-policy
  correction for the action actually taken when an option's policy is
  stochastic. This design evaluates the option's greedy policy and uses no
  correction.

What U4 could reuse is the consistency test and its frame condition
(obligation 5). Whether U4's models should keep SwiftTD and face the admission
question, or move to the corrected step and give up reduction, is U4's design
pass. U4's other half, learning the option *policies* off-policy, is an
action-value question this proposal does not address.

[U5](https://github.com/rbeauchamp/acorn/issues/11)'s expectation model is a
family of such questions with termination, one per ranked feature. Nothing here
decides it.

## Decisions requested

1. **Targets.** Each option slot's greedy policy (proposed), or the options'
   ε-soft policies, or other policies.
2. **Ratios.** None: a transition is used when its action is consistent
   (proposed), or unclipped ratios.
3. **Method.** GTD2-MP at trace parameter zero (proposed). The alternatives
   are plain GTD2, which has no blend and no per-step inequality, and TDC or
   TDRC, which are reported faster than GTD2 and easier to use, and for which
   no per-step inequality is known.
4. **Step sizes.** h = min(α, η/(|x| + |x′|)) for both vectors, with the
   demons' α = 5·10⁻⁵ and η = 0.1 (proposed). Per-weight adaptation is left to
   a follow-up.
5. **Questions.** All eleven signals for each of three options (proposed), or
   the reward signal only, at a tenth of the cost.
6. **Ties.** Any candidate action is consistent (proposed), or a canonical
   first-candidate tie-break. The second gives a deterministic target, as the
   consistency rule's source requires, and discards eight of every nine of an
   untrained option's own steps, since all nine actions tie at zero.
7. **Observer.** Outside the feature tester's utility, with no feedback into
   features, off by default (proposed), or counted in the utility.
8. **Checkpoint.** Bank left cold on restore, as the models are, with no format
   change (proposed), or persisted like the on-policy demons under a new format.
9. **Relation to U4.** Independent of U4: this change neither waits for it nor
   settles it (proposed).
10. **The blend.** Accept the constant-step blend at the demons' budget, where
    its weight is about 0.05 (proposed), or give these learners a smaller
    budget, which lowers the weight and the learning rate in proportion.

## Source verification

Every locator in [References](#references) was read on the page on 2026-10-01
for this proposal, in the linked version. Five limits apply.

- Reference 2's page numbers are those of the linked proceedings file, which
  carries no printed page numbers.
- Reference 7 gives Vtrace(λ) twice, and the two rules differ: Appendix A
  (p. 14) and Appendix C.4 (p. 23). This page relies on neither. It relies on
  reference 7 for the rules of Proximal GTD2(λ) and of the alternatives, and
  for its empirical remarks on the gradient-TD methods.
- Reference 10 was read in its arXiv version; its venue is taken from
  reference 7's bibliography. It attributes rejected sampling to two earlier
  papers. One is reference 11, where the passage was found. The other is
  reference 9, where no such passage was found.
- Reference 11's page numbers are those of the linked file.
- The statement that no source composes these methods with SwiftTD's step-size
  adaptation covers the eleven references and SwiftTD's sections 5 and 6 only.

## Refutation attempt

*Refutation attempt.* The proposal has had four reviews. Each read the page
against the code at a71ed08 and against the cited pages. None built or ran the
repository's code; where a review checked algebra by machine or searched
numerically, that is stated.

**First review**, of the first draft: a fresh-context reviewer instructed only
to break it. That draft ran SwiftTD over consistent stretches with no
correction and proposed deferring the correction. Findings that bear on the
present design:

| Finding | Effect on the present design |
|---|---|
| The draft disclosed the instability and deferred the correction, which the admission standard does not allow. | The correction is now the design. |
| Each trace clear is proportional to the weight space. | The present design has no traces. |
| Extending `Skill.stored` over the bank feeds the feature tester's utility. | The bank is excluded from the utility. |
| "Nothing is biased" overclaimed; the weighting changes the answer. | The counterexamples under [Limits](#limits). |
| The candidate set was defined before any write of the step, which the call order cannot provide. | Defined at the moment the action is fixed, with a frame condition (obligation 5). |
| An expectation identity and an instability family are model statements, not theorems over executed definitions. | Listed apart from the Lean obligations and labelled argued. |

It attacked and did not break the gate identity, the ratio bounds, the
rate-bound arithmetic and the instability family's algebra and threshold.

**Second review**, of the second draft: a validation pipeline's review step, in
five passes. That draft still proposed the uncorrected learner. Findings that
bear on the present design:

| Finding | Effect on the present design |
|---|---|
| The executing option's drawing snapshot is already exposed in `TemporalDecision.values`. | Stated under [Consistency](#consistency). |
| The consistency test reads the decision's source. | Stated under [Consistency](#consistency). |
| The collision study's investigated Vtrace(λ) leaves the ratio on the error uncapped. | No longer a basis; see [Source verification](#source-verification). |
| Demons are not stepped in frozen profiles; project terms were undefined. | Corrected in place. |

**Third review**, of the third draft: a fresh-context reviewer instructed only
to break it. That draft proposed GTD2 with its two updates applied in
sequence, an order of this page's own. The reviewer machine-checked the
algebra in Lean and searched numerically for counterexamples.

| Finding | Change |
|---|---|
| A closer published construction, Proximal GTD2, has the same main update and was not weighed; the sequential order was labelled with a kind the contract does not have, and was not a published method. | The method is now the published GTD2-MP. Its inequality was re-derived and is in the appendix. |
| The admission table claimed criterion 3 was argued to pass on a named future obligation, cited a scratch file no reader could see, and said no contradiction was known while Limits described a bias under aliasing. | Table reworded: the row reads "closure owed", the blend and closure-before-code are put to the maintainer, and the algebra is in the appendix. |
| The U4 section claimed the design was the mechanism U4 needs. U4 requires reduction to the current update and a correction for stochastic option policies. | Section rewritten; decision 9 changed. |
| "This is GTD2's setting" overclaimed: the gate gives one-step conditional expectations, not independence or stationarity. The adaptation list omitted dependent samples, projection and the per-step scale. | Reworded; adaptations added. |
| The fixed-point equation holds only when the active sets have constant sizes, and α is inert at typical sizes. | Restated with the general conditions; the step is described as normalized. |
| "Never increases the distance" and "a zero signal can never move the weights away from the origin" overstate: only the joint quantity N is monotone. | Reworded, with a qualification. |
| The figures 890 and 900 ignored served exploration under the primitive controller. | Both cases stated. |
| The new learner is not the type `Skill.readers` holds; `FeatureRuntime.retire_references` forbids a retirement-edited set among the references; splitting the union needs a membership structure; the armed flag across a reinstall was unaddressed. | [Integration](#integration) and obligations 4 and 8 corrected. |
| `Weight.project` sends NaN to zero, which is not a clip. | Obligation 2 added. |
| The Summary's "every transition" is exact-arithmetic; rounding can raise N. | Qualified. |
| Retirement and reinstallation can increase the distance to a nonzero reference. | Qualification added. |
| Reference 5's cited pages do not cover option models; reference 9's ranking is from on-policy experiments; a discount outside zero to one breaks the guard. | Locator restored, qualifier added, range stated. |

It attacked and did not break: the zero-residual identity, the guard, the
projection argument, the residual bound and the per-weight statement for the
sequential step (machine-checked and searched over 200,000 random trials); the
gate identity; the instability family; the two weighting examples; every
arithmetic figure; the code facts; and the attributions at their locators.

**Fourth review**, of the fourth draft, which proposed GTD2-MP: a
fresh-context reviewer instructed only to break it. It compiled the appendix,
machine-checked the prose bounds the appendix omits, compared the scalar step
with a vector transcription of the published algorithm in exact rational
arithmetic, and computed exact mean maps on small enumerated problems.

| Finding | Change |
|---|---|
| The page said no source read compares GTD2-MP with TDC. The collision study does, on an off-policy task, and its authors suggest Proximal GTD2 may not have reached the projected-Bellman-error minimum. | Cited under the sources, [Limits](#limits), the alternatives and decision 3. |
| "It sits between the two minimizers" and "a bounded share, about τ" are wrong: τ weights the objectives, not the displacement. On one enumerated problem inside the page's special case the fixed point was 1.94 times as far from the TD point as the squared-TD-error minimizer. | Reworded in [What it learns](#what-it-learns), [Limits](#limits) and [Admission status](#admission-status). |
| Clipping only the final writes is not published; the entry was labelled a published variant. | Relabelled a local approximation, with its reason and consequence. |
| The fixed-point equation needs a constant overlap as well as constant sizes, because κ depends on the overlap. | Hypothesis corrected. |
| "No criterion is known to fail" and "the property the admission standard asks for" overstate against a row that reads "closure owed"; the list of things weighing against admission omitted the weighting. | Header, Summary and [Admission status](#admission-status) reworded; the weighting added. |
| Proximal GTD2(λ) has two step sizes; it equals Algorithm 2 only when they are equal. | Stated. |
| "Discarded, with no ratio" went beyond reference 10's sentence, and its attribution to the 2009 paper is not borne out by that paper. | The first gradient-TD paper was read and is now reference 11; the gate rests on its sub-sampling section. |
| The step divides by zero when both active sets are empty, and the order of the sums was unspecified. | An empty x skips the step; the sums are ordered. |
| The U4 section said U4 shares this consistency rule and that the current update is SwiftTD. | Reworded. |
| Reference 10 had no venue; two alternatives were dismissed with universal negatives; several adaptation entries lacked a reason or consequence, and state values were missing. | Corrected. |

It attacked and did not break:

- the scalar step against Algorithm 2 at ratio one, equal on 2,000 random
  trials in exact rational arithmetic;
- the appendix, which compiled with no axiom beyond Lean's three standard
  ones, and whose theorems state what the prose says;
- the reduction from vectors to scalars, the guard, the projection argument
  and the residual bound, with no violation in 40,000 exact-rational trials
  that included clipping, weights at a rail and a reference on the boundary;
- the instability family under the corrected step, where N fell monotonically;
- the gate identity, the general stationarity conditions and the limit of a
  vanishing step, against exact mean maps;
- the statements attributed to reference 10, the code facts and the figures.

In binary32, the executed word type, its simulation of the step showed N
rising by at most about 10⁻⁹ in relative terms on a step and falling over
30,000 steps. That is a diagnostic of its own transcription, not of repository
code, and it is the rounding term obligation 1 owes.

**Not attacked.** The changes made after the fourth review, including the
reading of reference 11, have had no refutation attempt of their own.

## Appendix: the algebra in Lean

The file below states the scalar identities behind
[The energy inequality](#the-energy-inequality). Its variables p, q, τ, κ and
ε are as in that section. It compiles against the repository's pinned
Mathlib (`cd lean && lake env lean` on a copy of it). It is not part of the
repository's checked corpus, and it is about real numbers, not the executed
words; obligation 1 is the statement that matters.

```lean
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Basic.Real.Basic

/-- Change of N per unit step for one corrected step with zero residual. -/
theorem mp_identity (p q τ κ : ℝ) :
    let e := -(p + q)
    let pm := p + τ * e
    let em := (1 - τ) * e - κ * p
    2 * p * em + τ * em ^ 2 + 2 * q * pm + κ * pm ^ 2
      = -(2 * pm ^ 2 + τ * e ^ 2 + κ * p ^ 2
          - τ * (τ * e + κ * p) ^ 2 - κ * τ ^ 2 * e ^ 2) := by
  intro e pm em; simp only [e, pm, em]; ring

theorem cross_term (e p τ κ : ℝ) :
    (τ + κ) * (τ * e ^ 2 + κ * p ^ 2) - (τ * e + κ * p) ^ 2
      = τ * κ * (e - p) ^ 2 := by
  ring

/-- The change is nonpositive whenever τ, κ ≥ 0 and τ(τ + 2κ) ≤ 1. -/
theorem mp_nonincreasing (p q τ κ : ℝ) (hτ : 0 ≤ τ) (hκ : 0 ≤ κ)
    (guard : τ * (τ + 2 * κ) ≤ 1) :
    let e := -(p + q)
    let pm := p + τ * e
    let em := (1 - τ) * e - κ * p
    2 * p * em + τ * em ^ 2 + 2 * q * pm + κ * pm ^ 2 ≤ 0 := by
  intro e pm em
  have id := mp_identity p q τ κ
  simp only at id
  have D : 0 ≤ τ * e ^ 2 + κ * p ^ 2 :=
    add_nonneg (mul_nonneg hτ (sq_nonneg _)) (mul_nonneg hκ (sq_nonneg _))
  have c1 : (τ * e + κ * p) ^ 2 ≤ (τ + κ) * (τ * e ^ 2 + κ * p ^ 2) := by
    have := cross_term e p τ κ
    have nn : 0 ≤ τ * κ * (e - p) ^ 2 :=
      mul_nonneg (mul_nonneg hτ hκ) (sq_nonneg _)
    linarith
  have c2 : τ * (τ * e + κ * p) ^ 2
      ≤ τ * ((τ + κ) * (τ * e ^ 2 + κ * p ^ 2)) :=
    mul_le_mul_of_nonneg_left c1 hτ
  have c3 : κ * τ ^ 2 * e ^ 2 ≤ κ * τ * (τ * e ^ 2 + κ * p ^ 2) := by
    have nn : 0 ≤ κ * τ * (κ * p ^ 2) :=
      mul_nonneg (mul_nonneg hκ hτ) (mul_nonneg hκ (sq_nonneg _))
    nlinarith [nn]
  have c4 : τ * (τ + 2 * κ) * (τ * e ^ 2 + κ * p ^ 2)
      ≤ τ * e ^ 2 + κ * p ^ 2 := by
    have := mul_le_mul_of_nonneg_right guard D
    linarith
  have sq : 0 ≤ (p + τ * e) ^ 2 := sq_nonneg _
  simp only [e, pm, em] at *
  nlinarith [c2, c3, c4, sq]

/-- The residual's push, per unit step, is at most τ·ε² when κ ≤ 2 - τ. -/
theorem push (τ κ ε : ℝ) (hκ : κ ≤ 2 - τ) :
    τ * ((1 - τ) * ε) ^ 2 + κ * (τ * ε) ^ 2 ≤ τ * ε ^ 2 := by
  have h1 : τ * ε ^ 2 - (τ * ((1 - τ) * ε) ^ 2 + κ * (τ * ε) ^ 2)
      = τ ^ 2 * ε ^ 2 * (2 - τ - κ) := by ring
  have h2 : 0 ≤ τ ^ 2 * ε ^ 2 * (2 - τ - κ) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (by linarith)
  linarith

/-- Plain GTD2: at p = 0 the change is +τ·q². -/
theorem gtd2_expands (q τ κ : ℝ) :
    let p : ℝ := 0
    let e := -(p + q)
    2 * p * e + τ * e ^ 2 + 2 * q * p + κ * p ^ 2 = τ * q ^ 2 := by
  intro p e; simp only [p, e]; ring

/-- The semi-gradient family: both aggregate coordinates get this update. -/
theorem family (K γ w0 W : ℝ) :
    K * (γ * (w0 + W)) - (K * w0 + W)
      = K * (γ - 1) * w0 + (K * γ - 1) * W := by ring
```

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
   parameter (p. 11); §4: eq. (17), option-model learning (p. 14)
   ([arXiv:2202.03466v4](https://arxiv.org/abs/2202.03466v4)).
6. <a id="r6"></a>Sina Ghiassian, Andrew Patterson, Shivam Garg, Dhawal Gupta,
   Adam White and Martha White, "Gradient Temporal-Difference Learning with
   Regularized Corrections", ICML 2020, eqs. (5)–(6) and the shared step size
   (pp. 3–4), Theorem 3.1 and its hypotheses (pp. 4–5), the Adagrad step sizes
   and the remarks on GTD2 and on Vtrace (p. 5)
   ([arXiv:2007.00611v4](https://arxiv.org/abs/2007.00611v4)).
7. <a id="r7"></a>Sina Ghiassian and Richard S. Sutton, "An Empirical
   Comparison of Off-policy Prediction Learning Algorithms on the Collision
   Task", 2021, §3 on ratio products and step size (p. 4), §8 on the
   gradient-TD methods (pp. 8–9), Appendix A update rules for Proximal
   GTD2(λ), Emphatic TD(λ), Tree Backup(λ) for prediction and Vtrace(λ)
   (p. 14), footnote 2 on names (p. 18), Appendix C.2 on Proximal GTD2(λ)
   (p. 20), Appendix C.4 eqs. (28)–(30) (p. 23)
   ([arXiv:2106.00922v2](https://arxiv.org/abs/2106.00922v2)).
8. <a id="r8"></a>Lasse Espeholt, Hubert Soyer, Remi Munos, Karen Simonyan,
   Volodymyr Mnih, Tom Ward, Yotam Doron, Vlad Firoiu, Tim Harley, Iain
   Dunning, Shane Legg and Koray Kavukcuoglu, "IMPALA: Scalable Distributed
   Deep-RL with Importance Weighted Actor-Learner Architectures", 2018, §4.1:
   eq. (1) and the truncated weights (p. 3)
   ([arXiv:1802.01561v3](https://arxiv.org/abs/1802.01561v3)).
9. <a id="r9"></a>Richard S. Sutton, Hamid Reza Maei, Doina Precup, Shalabh
   Bhatnagar, David Silver, Csaba Szepesvári and Eric Wiewiora, "Fast
   Gradient-Descent Methods for Temporal-Difference Learning with Linear
   Function Approximation", ICML 2009: the setting with an arbitrary
   first-state distribution (§2, p. 2), backward bootstrapping (§3, p. 3),
   eqs. (8) and (9) for GTD2 and eq. (10) for TDC (§4, p. 4), Theorem 1 and
   its proof (§5, pp. 4–5), the on-policy experiments and their ranking (§7,
   pp. 6–7) and Baird's counterexample (Figure 5, p. 8)
   ([PDF](https://icml.cc/Conferences/2009/papers/546.pdf)).
10. <a id="r10"></a>Bo Liu, Ji Liu, Mohammad Ghavamzadeh, Sridhar Mahadevan and
    Marek Petrik, "Finite-Sample Analysis of Proximal Gradient TD Algorithms",
    UAI 2015, in its 2020 arXiv version: rejected sampling (§2, p. 3), the projected algorithms and their
    averaged output (§4.1 and Algorithm 1, pp. 4–5), the feasible-set
    assumption and independent sampling (§4.2–4.3, p. 5), GTD2-MP and its
    extragradient reading (§5, Algorithm 2 and footnote 3, p. 7), biased
    ratios (§6.2, pp. 7–8), online samples left to future work (§6.3, p. 8),
    TDC (§6.4, p. 8) and the Baird experiment (§7.1, p. 8)
    ([arXiv:2006.14364v2](https://arxiv.org/abs/2006.14364v2)).
11. <a id="r11"></a>Richard S. Sutton, Csaba Szepesvári and Hamid Reza Maei,
    "A Convergent O(n) Algorithm for Off-policy Temporal-difference Learning
    with Linear Function Approximation", Advances in Neural Information
    Processing Systems 21 (2008): the sub-sampling formulation (§2,
    pp. 2–3), Assumption A1 and Theorem 4.2 (p. 5), weighting in place of
    sub-sampling (p. 6)
    ([PDF](https://papers.nips.cc/paper_files/paper/2008/file/e0c641195b27425bb056ac56f8953d24-Paper.pdf)).
