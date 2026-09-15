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

The channel layout is authored. Projection features are generated over those channels.

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

The duration law and cap are authored. The exploration rate is derived separately from optimizer state.

Loci: `Acorn.Handcrafted.FeatureProfile`, `Acorn.Handcrafted.TemporalProfile`, `Acorn.Handcrafted.TemporalControl`, `Acorn.Handcrafted.Agent`.

*Replacement:* Move the relevant decision into learned state or a justified
derivation while preserving the continuing setting, semantic compatibility,
state admission and bounded work. Technical replacement requires an explicit
reviewed contract; usefulness requires separate prospective qualification.

### D4 · Learner parameters — Step 1

Domain-general learner coefficients and numerical rails are prescribed; per-feature step sizes adapt during learning.

Loci: `Acorn.Handcrafted.PredictionControl`, `Acorn.Handcrafted.TemporalControl`, `Acorn.Handcrafted.Agent`.

*Replacement:* Move the relevant decision into learned state or a justified
derivation while preserving the continuing setting, semantic compatibility,
state admission and bounded work. Technical replacement requires an explicit
reviewed contract; usefulness requires separate prospective qualification.

### D5 · Prediction targets — Step 2

The host defines reward/prediction targets and horizons. Prediction weights are updated from experience for these fixed questions.

Loci: `Acorn.Handcrafted.Observation`, `Acorn.Handcrafted.Cumulants`, `Acorn.Handcrafted.PredictionControl`, `Acorn.Handcrafted.Agent`.

*Replacement:* Move the relevant decision into learned state or a justified
derivation while preserving the continuing setting, semantic compatibility,
state admission and bounded work. Technical replacement requires an explicit
reviewed contract; usefulness requires separate prospective qualification.

## Standing obligations

Preserve all five declarations until an explicit replacement retires their actual
use. Adding a provenance constructor requires updating the closed register and
compiled quarantine inventory. Technical admission must satisfy the
[prior-art standard](prior-art-review.md#admission-standard), including material
adaptations and composition. Default promotion follows the separate
[qualification decision](prior-art-review.md#current-default-qualification):
PAR-9/10/12 are research-only; PAR-15 remains demoted and ineligible for default use.
