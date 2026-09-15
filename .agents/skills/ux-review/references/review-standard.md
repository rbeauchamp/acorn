# UX scoring and source references

## Repository rules every lens applies

Read `AGENTS.md` and `docs/viewer-ux.md` §1 before reviewing. These are not
preferences:

- **INV-1 · observer and lifecycle supervisor.** The page must not affect
  agent decisions. Start/stop controls are permitted only within the lifecycle
  channel defined by INV-1 and INV-1b; no weights, actions, or learning inputs
  travel through that channel.
- **INV-2 · every timer is listed.** The spec enumerates every recurring timer
  on the page and the gate suite counts them. A finding that adds polling, an
  interval, or a clock-driven animation is invalid unless it names the spec
  sentence that changes with it.
- **INV-4 · never invent, never hide.** Where a quantity cannot be known yet,
  the page says so. A plausible number in place of an unknown one is the worst
  defect this page can have; an empty panel with a reason is not a defect.
- **Every number names its window.** A mean says what it averages over; a
  trend says which two ranges it compares; a live figure says it is live; a
  count says whether it is the run's or this browser's.
- **Describe the observed quantity.** Name the reported mechanism, value and
  window. Distinguish execution activity, forecasts and outcomes by defining
  each measure directly. Comparative benefit follows the promotion standard;
  captions use concrete descriptions and omit repeated disclaimers.
- **Every algorithm surface names its source** (`docs/viewer-ux.md` §10):
  work, equation, fetched page and a short quote, or a statement that the
  quantity is out of viewer scope. A source may sit one click away; it may not
  be absent, and a reviewer may not supply one from memory.
- **Red is for faults.** Identity, mode and evidence badges use the colours of
  what they say; the alarm colour is reserved for a refused frame, a non-finite
  value, a stopped core the operator did not stop, a stale stream.
- **Rationale yes, changelog no**, in captions and tooltips exactly as in
  comments. A tooltip that says what a thing used to do is a finding.
- **No scenario tests**, whatever a lens is tempted to ask for. A
  visual-regression harness is a scope expansion for the user to decide.

## Design references the lenses may cite

Each lens judges against a named body of practice so that a finding can be
checked rather than argued. Reviewers cite these works by name; they do not
quote page numbers they have not opened.

- **Accessibility.** W3C, *Web Content Accessibility Guidelines (WCAG) 2.2*,
  Recommendation, 2023. Success Criterion 1.4.3 (text contrast at least 4.5:1;
  large text 3:1), 1.4.11 (non-text contrast 3:1 for interface components and
  graphical objects), 1.4.1 (colour is never the only carrier of a meaning).
- **Usability heuristics.** Nielsen, *10 Usability Heuristics for User
  Interface Design*, Nielsen Norman Group, 1994: visibility of system status,
  match between the system and the real world, consistency and standards,
  recognition rather than recall, aesthetic and minimalist design, help users
  recognise, diagnose and recover from errors.
- **Graphical integrity.** Tufte, *The Visual Display of Quantitative
  Information*, Graphics Press, 1983 (2nd ed. 2001): data-ink, chartjunk, the
  lie factor, small multiples. Cleveland & McGill, *Graphical Perception:
  Theory, Experimentation, and Application to the Development of Graphical
  Methods*, Journal of the American Statistical Association 79(387), 1984:
  position on a common scale is read most accurately, then length, then angle
  and area, with hue and saturation last.
- **Colour-vision safety.** Okabe & Ito, *Color Universal Design (CUD): How to
  make figures and presentations that are friendly to Colorblind people*,
  2008: the eight-colour palette and the rule that a meaning carried by colour
  is also carried by shape, weight or label.
- **Dashboards.** Few, *Information Dashboard Design*, O'Reilly, 2006: the
  information needed for the reader's objective fits one screen and is read
  at a glance; everything else is a click away.
- **The audience's own words.** Sutton, *The OaK Architecture: A Vision of
  SuperIntelligence from Experience*, RLC 2025 keynote (recording published by
  Amii); Javed & Sutton, *The Big World Hypothesis and its Ramifications for
  Artificial Intelligence*, Finding the Frame workshop, RLC 2024; the mission
  sentence at oaklab.ai/mission, quoted in `docs/viewer-ux.md` UX-3. The
  prior-art lens uses the pins in `docs/viewer-ux.md` §10 and the README's
  reference list; terms are used as those works use them.
