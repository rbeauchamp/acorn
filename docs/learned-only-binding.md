# Learned-only binding

The aim is for domain-specific choices on the action-selection path to be
learned from experience. This register makes the remaining authored choices
explicit. A **departure** is one such declared choice; it identifies a research
limitation and the code that owns it. See [the design](design.md#the-learning-loop)
for an introduction to the agent.

Undeclared hand-authored bias on the action-selection path is a defect.
Each declared departure identifies the authored choice and its replacement
conditions. Review checks declarations against the code that produces them.

The declared interface supplies observations, actions, task reward, boundaries
and immutable configuration. The action path includes feature construction,
value/prediction updates, option selection/interruption and planning. Host world,
control and observer machinery remain outside learned module ownership. No
handcrafted policy may be hidden in an observation, shaping term or model target.

Source and compiled gates enforce quarantine and composition roots. Every
constructor, restore and update must retain the indexed state predicate.
Acorn.Provenance declares signal origins; Acorn.Departure is the closed register.
Evaluation must separate training exposure, held-out populations and prior access.
The viewer reports outcomes for the selected run; evaluations specify their
comparison and target population.

## Departure register

### D1 · Hand-authored channels — Step 2

The channel layout is authored. Each world's adapter authors the words and symbols of its frames; the grid world's reads the tile-kind patch followed by the task words in their channel order, and projection features are generated over those symbols. For every world the agent adds its own prediction feedback words, bucketed on channels of their own; each world's adapter declares the first of those channels in its interface, and the grid world's declares `0x50`.

Loci: `Acorn.Handcrafted.Signals`, `Acorn.Handcrafted.Observation`, `Acorn.Handcrafted.GridWorld`, `Acorn.Handcrafted.FeatureProfile`, `Acorn.Handcrafted.PredictionControl`, `Acorn.Handcrafted.Agent`.

*Replacement:* Move the relevant decision into learned state or a justified
derivation while preserving the continuing setting, semantic compatibility,
state admission and bounded work. Technical replacement requires an explicit
reviewed contract; usefulness requires separate prospective qualification.

### D2 · Spatial potentials — Step 10

The ranked profile uses learned assignments; the spatial comparison uses authored potentials, which a world's frame carries and the grid world's adapter produces. F1–F3 describe the questions around model quality, planning and feature selection.

Loci: `Acorn.Handcrafted.Observation`, `Acorn.Handcrafted.GridWorld`, `Acorn.Handcrafted.FeatureProfile`, `Acorn.Handcrafted.TemporalProfile`, `Acorn.Handcrafted.TemporalControl`, `Acorn.Handcrafted.AgentAlignment`, `Acorn.Handcrafted.AgentEpisodes`, `Acorn.Handcrafted.Agent`.

*Replacement:* Move the relevant decision into learned state or a justified
derivation while preserving the continuing setting, semantic compatibility,
state admission and bounded work. Technical replacement requires an explicit
reviewed contract; usefulness requires separate prospective qualification.

### D3 · Exploration duration — Step 9

The duration law and cap are authored. The exploration rate is D6.

A run may start at every decision that serves none, whichever layer selects the
primitive action. Primitive control and an executing option both make the
persistent draw (`PolicySnapshot.drawPersistent`), as Algorithm 1 of Dabney,
Ostrovski & Barreto, *Temporally-Extended ε-Greedy Exploration*, ICLR 2021
([arXiv:2006.01782v1](https://arxiv.org/abs/2006.01782v1), PDF p. 14), applies
it to the agent's one behaviour policy
(`CurrentTemporal.select_persistent`). The meta-controller's draw selects the
acting layer and stays a single step over meta actions.

A hierarchy is Acorn's composition, so one choice is declared here: a run that
an executing option's draw begins interrupts the option.

- **Choice.** The option is the executing invocation of the frame it drew. The
  run's first served step ends that execution, recorded as an interruption, and
  the meta-controller decides again when the run is spent. A drawn run with no
  step left to serve is one exploratory step of the option, which continues.
  The run takes control before that step's goal and duration checks, so the
  interruption is the recorded reason even where one of them would have fired.
- **Reason, from the source.** §4.2 (PDF p. 5) makes the run an option of the
  behaviour that "takes action a for n steps and then terminates", and
  Algorithm 1 draws at every step with no run in progress. Starting runs only at
  option boundaries would confine the draw to the steps where no option acts,
  which is the defect [#58](https://github.com/rbeauchamp/acorn/issues/58)
  reports.
- **Reason, from Acorn's options.** Dispatch executes one occupancy at a time,
  and a served step consults no value function and no stopping decision
  (`CurrentTemporal.served_preempts`). An option kept executing through a run
  could not take its on-policy update, stopping decision or duration cap on
  those steps. An option suspended and resumed after the run would need its
  on-policy trace to span steps it did not select, and its invocation and the
  meta-controller's credit span would outlast their bounds.
- **Learning.** The run gives the interrupted option no terminal credit: the run
  is not one of its stopping conditions, and a stop invented there would make
  its values and model depend on the exploration rate. It is linked to the
  trajectory it was executing and learns from the served steps off-policy, as
  every option that is not executing does
  ([PAR-17](prior-art-review.md#par-17--off-policy-option-learning)), under its
  own stopping decision. Where that decision continues at the first served
  step, its model takes the credit the executing option would have taken
  (`CurrentTemporal.handoff_model`) and its policy takes tree-backup credit
  (`CurrentTemporal.handoff_policy`). Where it ends, the option is stopped as
  any followed option is (`CurrentTemporal.handoff_stop`).
- **Meta credit.** The meta-controller's span for the option closes at the first
  served step, and the rewards of the served steps are credited to no meta
  action. The span covers the option's own actions and is credited toward the
  option's own continuing return: its meta value at that frame where its
  stopping decision continues, and the frame's nominal meta value where that
  decision ends (`CurrentTemporal.takeover_value`). That is the return the
  option's model predicts and planning backs the same value toward, so sampled
  credit and planning keep one contract: the option run to its own stop.
  Closing toward the meta value of the state alone would credit the option with
  a stop its model does not make.

Loci: `Acorn.Handcrafted.TemporalControl`, `Acorn.Handcrafted.Agent`.

*Replacement:* Move the relevant decision into learned state or a justified
derivation while preserving the continuing setting, semantic compatibility,
state admission and bounded work. Technical replacement requires an explicit
reviewed contract; usefulness requires separate prospective qualification.

### D4 · Learner parameters — Step 1

Domain-general learner coefficients and numerical rails are prescribed; per-feature step sizes adapt during learning. The off-policy questions of [PAR-18](prior-art-review.md#par-18--off-policy-questions) adapt none: their step size is the smaller of the demons' initial step size and their rate budget divided by the transition's active slots. They learn from no transition in which either active set exceeds 2¹⁶ slots, the size their rounding analysis covers.

Loci: `Acorn.Handcrafted.PredictionControl`, `Acorn.Handcrafted.TemporalControl`, `Acorn.Handcrafted.Agent`.

*Replacement:* Move the relevant decision into learned state or a justified
derivation while preserving the continuing setting, semantic compatibility,
state admission and bounded work. Technical replacement requires an explicit
reviewed contract; usefulness requires separate prospective qualification.

### D5 · Prediction targets — Step 2

A world's interface declares its prediction targets and their horizons, and the agent adds one question of its own, whether the delivered reward is positive. The grid world declares ten targets, eleven questions in all. Prediction weights are updated from experience for these fixed questions. Each option also asks the same questions, at the same horizons, about its own policy, learned off-policy ([PAR-18](prior-art-review.md#par-18--off-policy-questions)).

Loci: `Acorn.Handcrafted.Signals`, `Acorn.Handcrafted.Observation`, `Acorn.Handcrafted.Cumulants`, `Acorn.Handcrafted.GridWorld`, `Acorn.Handcrafted.PredictionControl`, `Acorn.Handcrafted.TemporalControl`, `Acorn.Handcrafted.Agent`.

*Replacement:* Move the relevant decision into learned state or a justified
derivation while preserving the continuing setting, semantic compatibility,
state admission and bounded work. Technical replacement requires an explicit
reviewed contract; usefulness requires separate prospective qualification.

### D6 · Exploration rate — Step 9

Every research profile except the annealed comparison explores with one
declared rate, ε = 0.01, for the primitive controller, the meta-controller and
every option. The stored word is `0x3c23d70a`, exactly 10737418·2⁻³⁰. Dabney,
Ostrovski & Barreto, *Temporally-Extended ε-Greedy Exploration*, ICLR 2021
([arXiv:2006.01782v1](https://arxiv.org/abs/2006.01782v1)), use ε = 0.01 for
their linear Sarsa(λ) CartPole agent (Appendix A, PDF p. 14). Their
Rainbow-based Atari agents reach 0.01 only at the end of a schedule: ε "follows
a linear decay schedule 1.0 to 0.01 over the course of the first 4M frames,
remaining constant after that" (Appendix B.3, PDF p. 15; Table 2, PDF p. 16).
Their other domains use 0.05, 0.1 and 1/(N+1) (Appendix A, PDF p. 13).
A continuing agent has no clock for a schedule, so it keeps only the constant.
One rate for all three consumers is Acorn's composition choice.

The primitive controller and every option read the rate in the persistent draw
(D3): at every decision that serves no run, the layer selecting the primitive
action starts a run on the rate's branch (`TemporalSupport.select_declared`).
The meta-controller reads it in a single-step draw over meta actions. Under an
assumed uniform, independent draw, which the deterministic generator does not
supply, the expected exploratory share of the behaviour's cycles is between 4.6%
and 6% (`declared_share_gt` and `declared_share_lt` in `AcornVerif.Exploration`),
against exactly ε for a single-step draw (`explorationShare_single`). Persistence
never lowers the share below ε, for every rate in [0, 1] and every mean run length
of at least one step (`explorationShare_ge`). The effect on achievement is not
derivable, and no achievement claim is made.

One consequence follows, and it is not conformance with the source.

- **The decay is removed.** Counting one step as one frame, the Atari schedule
  gives ε = 1 − 0.99 × 34 000 / 4 000 000 ≈ 0.99 after 34 000 steps, the most a
  first pass of the standard curriculum takes. A whole first pass therefore
  lies inside the phase this declaration removes. Of the agents whose ε the
  source states as a number, only the CartPole agent uses 0.01 from its first
  step.

`TemporalControl.declared_rates` proves every consumer reads this word at every
state; `TemporalSupport.declared_branch_card` counts the source words that
explore. The annealed comparison's schedule and fixed option rate are also
declared here. Its option rate of 0.1 feeds the same persistent draw. On the
frames an option itself selects, the exploring branch is taken at 0.1 under the
idealized draw, and an option that would return k actions is uninterrupted with
probability 0.95^k. Evaluating the model above at a constant rate of 0.1 gives
about 0.38 as the exploratory share of complete behaviour cycles, served steps
after an interruption included; the annealed hierarchy mixes that rate with the
primitive controller's schedule, so the figure does not establish the share of
its whole stream. These figures are evaluations of the model, not theorems. The derived rate of
[PAR-10](prior-art-review.md#par-10--derived-exploration-rate) remains a
research-only selection.

Loci: `Acorn.Handcrafted.FeatureProfile`, `Acorn.Handcrafted.TemporalProfile`, `Acorn.Handcrafted.TemporalControl`, `Acorn.Handcrafted.Agent`.

*Replacement:* Move the relevant decision into learned state or a justified
derivation while preserving the continuing setting, semantic compatibility,
state admission and bounded work. Technical replacement requires an explicit
reviewed contract; usefulness requires separate prospective qualification.

### D7 · Feature tester schedule — Step 2

The generate-and-test tester's replacement rate, maturity threshold and utility
decay are declared: ρ = 10⁻⁴, accrued per eligible unit per step (one replacement
per 10 000 accrued eligible-unit steps), maturity threshold m = 1000 steps and
decay η = 0.99 (stored words `0x3f7d70a4`, the binary32 word nearest 0.99, and
`0x3c23d70a`, the word nearest 0.01, for the complement). These are the example
settings of continual backpropagation with Adam in Dohare, Hernandez-Garcia,
Rahman, Mahmood & Sutton, *Maintaining Plasticity in Deep Continual Learning*,
[arXiv:2306.13812v3](https://arxiv.org/abs/2306.13812v3) (2024), Algorithm 3,
p. 44; Algorithm 1 (p. 23) gives the same ρ and η with m = 100. The algorithms
scale ρ by the layer size; per-eligible-unit accrual follows the authors'
released implementation (PAR-11). Mahmood & Sutton,
*Representation Search through Generate and Test*, AAAI 2013 workshop, call the
rate and the maturity threshold tunable (p. 3) and use ρ = 1/200 in their
experiment (p. 4). The values are the source's workload settings, not derived
for Acorn. With m = 1000, `AcornVerif.Retirement.maturity_bias` proves
η^(m+1) < 5·10⁻⁵ for the stored decay word, so omitting the source's bias
correction (eq. (8), p. 21) changes no eligible unit's utility by more than that
fraction. `AcornVerif.Retirement.run_young` bounds the units younger than L steps
by ⌊(10⁴ − 1 + N·L)/10⁴⌋; for the 512-unit bank and L = m + 1 that is 52.
`AcornVerif.Retirement.run_turnover` gives a replacement within ⌈10⁴/k⌉ steps
whenever at least k units are eligible at each step. The same bound over mature
units does not hold, because a unit held as an option objective is not eligible
away from a free boundary and accrues no credit; the three slots hold at most
three units, so `run_mature_turnover` gives ⌈10⁴/(k − 3)⌉ steps whenever at least
k > 3 units are mature at each step.

Loci: `Acorn.Handcrafted.FeatureProfile`, `Acorn.Handcrafted.Agent`.

*Replacement:* Move the relevant decision into learned state or a justified
derivation while preserving the continuing setting, semantic compatibility,
state admission and bounded work. Technical replacement requires an explicit
reviewed contract; usefulness requires separate prospective qualification.

## Standing obligations

Preserve all seven declarations until an explicit replacement retires their actual
use. Adding a provenance constructor requires updating the closed register and
compiled quarantine inventory. Technical admission must satisfy the
[prior-art standard](prior-art-review.md#admission-standard), including material
adaptations and composition. Default promotion follows the separate
[qualification decision](prior-art-review.md#current-default-qualification):
PAR-9/10/12 are research-only; PAR-15 remains demoted and ineligible for default use.
