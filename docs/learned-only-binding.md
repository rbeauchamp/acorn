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

The channel layout is authored. Projection features are generated over those channels: the generator reads the tile-kind patch followed by the task words in their channel order.

Loci: `Acorn.Handcrafted.Observation`, `Acorn.Handcrafted.FeatureProfile`, `Acorn.Handcrafted.PredictionControl`, `Acorn.Handcrafted.Agent`.

*Replacement:* Move the relevant decision into learned state or a justified
derivation while preserving the continuing setting, semantic compatibility,
state admission and bounded work. Technical replacement requires an explicit
reviewed contract; usefulness requires separate prospective qualification.

### D2 · Spatial potentials — Step 10

The ranked profile uses learned assignments; the spatial comparison uses authored potentials. F1–F3 describe the questions around model quality, planning and feature selection.

Loci: `Acorn.Handcrafted.Observation`, `Acorn.Handcrafted.FeatureProfile`, `Acorn.Handcrafted.TemporalProfile`, `Acorn.Handcrafted.TemporalControl`, `Acorn.Handcrafted.AgentAlignment`, `Acorn.Handcrafted.AgentEpisodes`, `Acorn.Handcrafted.Agent`.

*Replacement:* Move the relevant decision into learned state or a justified
derivation while preserving the continuing setting, semantic compatibility,
state admission and bounded work. Technical replacement requires an explicit
reviewed contract; usefulness requires separate prospective qualification.

### D3 · Exploration duration — Step 9

The duration law and cap are authored. The exploration rate is D6.

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

The host defines reward/prediction targets and horizons. Prediction weights are updated from experience for these fixed questions. Each option also asks the same eleven questions, at the same horizons, about its own policy, learned off-policy ([PAR-18](prior-art-review.md#par-18--off-policy-questions)).

Loci: `Acorn.Handcrafted.Observation`, `Acorn.Handcrafted.Cumulants`, `Acorn.Handcrafted.PredictionControl`, `Acorn.Handcrafted.TemporalControl`, `Acorn.Handcrafted.Agent`.

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

Two consequences follow, and neither is conformance with the source.

- **The decay is removed.** Counting one step as one frame, the Atari schedule
  gives ε = 1 − 0.99 × 34 000 / 4 000 000 ≈ 0.99 after 34 000 steps, the most a
  first pass of the standard curriculum takes. A whole first pass therefore
  lies inside the phase this declaration removes. Of the agents whose ε the
  source states as a number, only the CartPole agent uses 0.01 from its first
  step.
- **Persistent runs start only when primitive control acts.** The source's
  Algorithm 1 (PDF p. 14) applies the persistent draw to the agent's one
  behaviour policy: at every step with no run in progress, a run starts with
  probability ε. Acorn's agent starts a run only in
  `TemporalControl.choosePrimitive`, which is reached when the meta-controller
  delegates to primitive control or the profile has no hierarchy. The
  meta-controller and an executing option use the plain draw
  (`PolicySnapshot.draw`), one exploratory step at a time. Under an assumed
  uniform, independent draw, which the deterministic generator does not supply,
  their model share is exactly ε (`explorationShare_single` in
  `AcornVerif.Exploration`). Once the meta-controller
  holds options the mechanism rarely runs: in two diagnostic traces of study
  first-pass-vs-chance r1 (seeds 16265277883658242538 and 8789851314873071931),
  0.95% and 0.93% of steps were exploratory
  ([#58](https://github.com/rbeauchamp/acorn/issues/58)). The traces are
  diagnostics of those two seeds, not study evidence.

`TemporalControl.declared_rates` proves every consumer reads this word at every
state; `TemporalSupport.declared_branch_card` counts the source words that
explore. The annealed comparison's schedule and fixed option rate are also
declared here. The derived rate of
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
