# Learned-only binding

The aim is for domain-specific choices on the action-selection path to be
learned from experience. This register makes the remaining authored choices
explicit. A **departure** is one such declared choice; it identifies a research
limitation and the code that owns it. See [the design](design.md#the-learning-loop)
for an introduction to the agent.

Undeclared hand-authored bias on the action-selection path is a defect.
Declared departures are the research frontier. A declaration is necessary, not
proof of its scientific truth or permission to add arbitrary bias.

The declared interface supplies observations, actions, task reward, boundaries
and immutable configuration. The action path includes feature construction,
value/prediction updates, option selection/interruption and planning. Host world,
control and observer machinery remain outside learned module ownership. No
handcrafted policy may be hidden in an observation, shaping term or model target.

Source and compiled gates enforce quarantine and composition roots. Every
constructor, restore and update must retain the indexed state predicate.
Acorn.Provenance declares signal origins; Acorn.Departure is the closed register.
Evaluation must separate training exposure, held-out populations and prior access.
A live viewer fraction is not generalization or causal learning evidence.

## Departure register

### D1 · Hand-authored channels — Step 2

The channel layout is authored; generated projection weights do not make the input layout learned.

Loci: `Acorn.Handcrafted.Observation`, `Acorn.Handcrafted.FeatureProfile`, `Acorn.Handcrafted.PredictionControl`, `Acorn.Handcrafted.Agent`.

*Replacement:* Move the relevant decision into learned state or a justified
derivation while preserving the continuing setting, semantic compatibility,
state admission and bounded work. Technical replacement requires an explicit
reviewed contract; usefulness requires separate prospective qualification.

### D2 · Spatial potentials — Step 10

The ranked profile uses learned assignments; the explicit spatial comparison still uses authored potentials. A ranked proxy is not a guarantee of useful subtask discovery.

Loci: `Acorn.Handcrafted.Observation`, `Acorn.Handcrafted.FeatureProfile`, `Acorn.Handcrafted.TemporalProfile`, `Acorn.Handcrafted.TemporalControl`, `Acorn.Handcrafted.AgentAlignment`, `Acorn.Handcrafted.AgentEpisodes`, `Acorn.Handcrafted.Agent`.

*Replacement:* Move the relevant decision into learned state or a justified
derivation while preserving the continuing setting, semantic compatibility,
state admission and bounded work. Technical replacement requires an explicit
reviewed contract; usefulness requires separate prospective qualification.

### D3 · Exploration duration — Step 9

The duration law and cap remain authored. Deriving a rate from optimizer state does not retire the duration departure.

Loci: `Acorn.Handcrafted.FeatureProfile`, `Acorn.Handcrafted.TemporalProfile`, `Acorn.Handcrafted.TemporalControl`, `Acorn.Handcrafted.Agent`.

*Replacement:* Move the relevant decision into learned state or a justified
derivation while preserving the continuing setting, semantic compatibility,
state admission and bounded work. Technical replacement requires an explicit
reviewed contract; usefulness requires separate prospective qualification.

### D4 · Learner parameters — Step 1

Domain-general learner coefficients and numerical rails remain prescribed. They are not learned merely because the per-feature step size changes.

Loci: `Acorn.Handcrafted.PredictionControl`, `Acorn.Handcrafted.TemporalControl`, `Acorn.Handcrafted.Agent`.

*Replacement:* Move the relevant decision into learned state or a justified
derivation while preserving the continuing setting, semantic compatibility,
state admission and bounded work. Technical replacement requires an explicit
reviewed contract; usefulness requires separate prospective qualification.

### D5 · Prediction targets — Step 2

The host defines reward/prediction targets and horizons. Learned prediction weights do not make the questions learned.

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
adaptations and composition. Never infer default promotion from implementation,
a declaration or a digest. No agent configuration is qualified as an implicit
default; [PAR-9/10/12](prior-art-review.md#current-default-qualification) remain
research-only and PAR-15 remains demoted (ineligible for default use).
