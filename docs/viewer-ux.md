# Viewer requirements — `acorn-viewer` (the observer)

The viewer at `http://127.0.0.1:8088` exists to answer one question a log file
cannot: **how well is this agent achieving its goals?** Goal outcomes summarize the
integrated agent; predictions, options, planning and step sizes explain its
behavior. Position, inventory and terrain provide the setting. Its audience is the people whose work it implements — Sutton, Javed
and the Oak Lab team — and anyone they would send to look. It passes when a
newcomer from that audience can say within ten seconds what the system is,
what it is trying to do and how it is doing, and when nothing on the page would
make them distrust the next number.

This document states what the page must show and why. It does not describe
how the page achieves it: mechanism lives in `viewer/static/index.html` and
`Acorn.Host.Viewer`, whose comments carry the rationale for each piece of code, and a
requirement here names the owning function only where a reader would otherwise
have to search. Requirements are numbered; a page behaviour that contradicts
one is a bug, and a contradiction found in this document is fixed here. The
gate suite compares numeric rows in Appendix A with their browser or native
owners. Prose quantities and completeness of
that table remain review obligations.

Reviews judge the page against this document: `proof-review` and
`pr-review-toolkit` for the code and its guarantees, `ux-review` for whether
the page can be understood (`.agents/skills/ux-review/SKILL.md`).

## 1 · Invariants (non-negotiable)

- **INV-1 · Observer of the stream, supervisor of the process.** Two roles,
  and the line between them is what the invariant protects. As an
  **observer**, the viewer consumes the core's one-way NDJSON telemetry
  (`acorn demo --research-profile ranked --telemetry` → child stdout → SSE) and must never change the
  agent's decisions. Telemetry may gain *read-only* fields — quantities
  computed from state the agent already produced — provided the audit digest
  is unchanged. As a **supervisor**, it starts and stops the core as a child
  process; nothing it sends reaches the agent. The one thing that crosses is a
  request to wind up at the next attempt boundary, which changes *when a run
  ends*, never *what it does*: weights, world, RNG stream and every decision
  are untouched. Mechanically checked by the deterministic audit digest
  (`./lean/.lake/build/bin/acorn-core audit --expect 829aef890c81afaf`),
  checksum `b1a076b6ac5884f0` (C-AC5), and by the gate suite
  (`AcornTools.Boundary.Audit`), which excludes host IO and control owners from learned
  modules. The digest detects mutation; module admission enforces isolation.
- **INV-1b · The control channel carries lifecycle only.** The core's stdin
  accepts exactly one command, `stop`. Nothing the agent reads may travel this
  way; an unrecognised line is reported and ignored rather than acted on.
- **INV-1c · The page renders server state, never its own guess.** A control
  changes appearance only when a “ctl” frame says the server moved. A button
  reading “Running” because it was clicked would assert something it cannot
  know, and a stale claim about whether an agent is learning is worse than a
  slow one.
- **INV-2 · Push, not poll.** Frames reach the browser over SSE as the core
  produces them. **No HTTP polling of frames, ever.** The only *recurring*
  timers are the steps/s counter, the staleness watchdog and the browser-storage
  saver; each toast additionally arms a one-shot timer to remove itself, and
  the goal flash arms a `requestAnimationFrame`. Those are presentation
  lifetimes, not a polling loop — but they are timers, and this invariant lists
  every one. The render loop runs on `requestAnimationFrame`, and the reading
  cadence of the text readouts (UX-8) is a gate on that loop's own clock, not a
  timer. The gate suite counts the page's interval timers, one-shot timers and
  requests against this list, so a timer cannot be added without this
  paragraph changing with it.
- **INV-3 · Refreshes restore the world.** The explored map is the run's: the
  viewer keeps every tile the agent has sensed and hands it to each
  connection (UX-44), and each browser additionally persists its own copy and
  the trail (UX-45); a refresh, a reconnect or a second browser therefore shows
  the same explored world and continues accumulating.
- **INV-4 · Never invent, never hide.** The viewer shows what the stream says.
  Where a quantity cannot be known yet — an unfinished prediction horizon, a
  refused curriculum snapshot, a run with no frame — it
  says so rather than guessing, drawing an empty frame, or printing a zero.

## 2 · The first screen

What a newcomer must be able to say without scrolling.

- **UX-1 · Watch first, explore next.** The first screen leads with the top
  bar, a short plain-language welcome, and the live world. The agent and current
  goal must be visible without opening an explanation. A sidebar starts with
  goal achievement. The sensed window and world overview follow the scene and
  its controls in a compact row; their height cannot leave a long empty column. Start/Stop stay
  in the top bar; the introduction explains cooperative Stop and checkpoint
  resume without promising a successful save.
  The introduction describes the agent, its current goal and the viewer controls.
  Algorithm terminology, the five-stage progression, mission tiles and detailed
  analysis live in an initially closed, keyboard-accessible **Inside the agent**
  disclosure below the main view. Existing measurements, definitions and sources
  remain available there; opening it changes presentation only. The goal
  achievement summary remains outside that disclosure. The options ribbon and
  display transport remain below the scene.
- **UX-2 · The top bar.** On one line at 1440 CSS px in the healthy state:
  title, the `LIVE RUN · single stream` badge (UX-47), `world 1024² · seed N`,
  lifetime steps with the unit, core steps/s, the sensed percentage, the
  identity pill (UX-19), any health pills (UX-20, UX-25), `restored` /
  `not persisted` (UX-45), the run controls (UX-21), and the connection state
  (UX-18). Before the first frame the counters read `—`, never zero. The
  identity pill, health pills, controls and connection state form one
  right-hand cluster that wraps to a second line as a unit when a fault label
  or health pill needs the room, so the pill that explains a state lands beside
  the state word and never under the title.
- **UX-3 · The thesis.** The main sidebar carries the question the viewer
  answers (*How well is this agent achieving its goals?*) as a prominent semantic
  heading, followed by **Goal achievement · higher is better**, a percentage and
  an increasing progress indicator. A concise explanation says: share of assigned
  goals achieved within the allowed attempts; each goal counts once. The core
  derives the denominator from the admitted curriculum count and counts a goal
  on success or attempt exhaustion. Failed retries do not reweight a goal.
  Before any resolved goal, show “Waiting”. During the first incomplete pass,
  show achieved/all assigned goals, explicitly labelled `so far · first pass
  incomplete`; unresolved goals are unknown, not failures. The latest complete
  pass remains the headline during subsequent incomplete passes, with its pass
  number and exact successful/assigned counts. A separate concise caption shows
  current pass number, resolved/all-goals completion percentage (rounded to one
  decimal), exact resolved counts, completed-pass count once available, and
  current successes during a successor pass. Pass completion measures resolved
  goals, not successes or elapsed time. Stop retains the pass number and marks
  it stopped, preserving incomplete evidence.
  A process restart, including checkpoint resume, begins empty accounting;
  reconnect and cursor movement never change the core's snapshot. Invalid
  outcome order suppresses the score. Goal achievement rounds down to one decimal percent.
  A disclosure names the attempt/step budget, population and process scope,
  Oak Lab mission and Javed/Sutton Big World research rationale. This operational
  fraction describes the selected curriculum, world and attempt budget.
  The research disclosure carries the standing claim
  `One agent · one unbroken stream · no replay buffer`, and one paragraph: OaK
  is **O**ptions **a**nd **K**nowledge — from one stream of experience, batch
  size one, build features from what is sensed, pose subtasks about the useful
  ones, learn options that achieve them, learn models of those options, plan
  with them; every weight has its own meta-learned step size — followed by the
  mission sentence quoted from oaklab.ai/mission (*algorithms that allow
  agents to achieve goals in big worlds*) with the link. A fine-print line
  identifies figures as core telemetry or the page's labelled arithmetic.
  Live rates and shares are means over the last `WIN` frames; every other
  figure names its own window. Describe Acorn's implementation directly,
  with citations for the research it draws on. A `sources` disclosure names the FC-STOMP
  progression (Sutton, *The OaK Architecture: A Vision of SuperIntelligence
  from Experience*, RLC 2025 keynote), the STOMP progression (Sutton, Machado
  et al., AIJ 324 (2023) 104001, arXiv:2202.03466v4), Alberta Plan Step 1 for
  per-weight step sizes. The
  live observer carries no historical benchmark link or result (UX-48).
- **UX-4 · OaK's five stages.** The panel is headed *OaK's five stages — the
  FC-STOMP progression*, followed by the display state word (UX-6). It is a
  progression, not the closed loop of Alberta Plan Step 11: the utility
  feedback that loop adds is absent from this build (`docs/design.md`), and the
  return glyph on the last node carries a hover text saying it marks the
  continual re-ranking of features (PAR-12) and nothing more. Five nodes in
  FC-STOMP order, each a stage of the architecture and each reporting what the
  stream says about it, with an arrow to the next:

  | node | value | caption | lit when |
  |---|---|---|---|
  | **features** | `imprint_units` imprint units | `retire_count` retired by generate-and-test, the last retired unit and its lifetime step (`retire_unit`, `retire_step`), `weight_space` weights per learner; the hover text says the imprint units are random ±1 projections added to fixed tilings over a hand-authored channel layout (D1), that only the imprint units are generated-and-tested, and that the word *imprint* is Javed's (thesis ch. 9) for a mechanism this bank is not | a retirement landed within the last `WIN` frames |
  | **subtasks** | `n / 3 assigned` (`subtask_unit` ≠ null), or `3 hand-authored (D2)` under `subtask_policy = hand_authored` | task reward + stopping bonus, with the hover text pinning the bonus weight (§10); or `neutral · no ranked feature yet` | a slot's (unit, bonus) changed within the last `WIN` frames |
  | **options** | the running option's name, or `primitive` | share of the last `WIN` frames spent under an option; lifetime option starts | fast mode (UX-8): any option step in the last `WIN` frames; otherwise an option is running at the cursor |
  | **models** | `r̂ · ĉ` of the running option (means in fast mode), or `r̂` per option, each symbol kept on one line with its number and formatted so a value of 1e-4 never prints as 0.000 (UX-11) | which option, and what the two numbers are (`ĉ` is written `ĉ_v` in the source) | as the options node |
  | **planning** | `planning_steps` backups | since process start; mean \|Bellman error\| over the three slots, formatted likewise | `planning_steps` moved within the last `WIN` frames |

  Beneath the nodes, one line per option slot: its colour swatch, name, the
  imprint unit and stopping bonus it is pursuing (or `neutral · no ranked
  feature yet`, or the hand-authored potential), and in fast mode the share of
  the window it ran; then a legend line saying what a lit node means. A lit
  node is a border colour and a `· now` mark on its title — a fact about the
  stream, never an animation on a timer — evaluated at the reading cadence
  and, in fast mode, over the window rather than at the instant, so a node does
  not pulse with a five-step option; it is lit only while the display is live
  (UX-6), never on a stale stream or a stopped core. For the three
  counter-driven nodes only the most recent change is remembered, so the state
  is exact at the live edge and a scrub across an earlier event shows nothing.
- **UX-5 · Against the mission.** Four tiles, each with its definition in the
  hover text and its window in the caption:
  - **goals achieved** — lifetime successes / lifetime attempts over all four
    goal families (`lifetime_goal_successes`, `lifetime_goal_attempts`), the
    success percentage at the cursor, and goals achieved in the latest core
    pass, captioned with its pass number. Current-pass outcomes are supplied
    by the core independently of when the browser connected (UX-9);
  - **reward / step** — the mean of the newest occupied power-of-two lifetime
    bin (`lifetime_reward_history_*`; bin `k` covers lifetime steps
    `[2^k, 2^(k+1))`), labelled with the step range it covers and how many
    steps it holds so far, against the bin before it, labelled likewise. The
    history is the run's lifetime record and is read from the newest frame, so
    the range is labelled with that frame's lifetime step whatever the cursor
    shows. A non-finite sum is said as `⚠ non-finite`, never printed;
  - **knowledge · predictive agreement** — the core's cumulative process-local
    equal-question normalized RMSE complement (UX-32–33), in points with higher
    better. All current questions must settle before the aggregate appears;
    no trend arrow, sample-count weighting or recent-window claim is attached;
  - **world seen · terrain coverage** — `seenCount / side²`, the tiles sensed
    in this run (UX-44), with the scope word UX-9 requires.

  A trend arrow on the reward comparison says `↑`/`↓` when the newer figure
  differs from the older by more than five percent and `→` otherwise, coloured
  green when the direction is the good one for that quantity (reward up,
  error down) and red when it is not, with a hover text saying the same in
  words (rose or fell, the wanted or the unwanted direction). The arrow waits
  for sufficient data (UX-12). The arrows compare two named windows of one run;
  the goals tile's hover text names its counters, families and lifetime/current-pass
  scope. When the display is detached
  from the live edge the panel heading says which moment each tile reads: goals
  read the cursor's frame, the other three the newest one.
- **UX-6 · The display state is written where the first screen shows it.**
  One phrase, computed from the transport, the watchdog and the control state —
  `live`; `paused · N frames behind newest` or `replay R/s · N frames behind
  newest`; combined with `stream stale`, `core stopped`, `core starting`,
  `core stopping` or `core clearing` when applicable. An empty ring says
  `waiting for first frame`; `newest frame` is reserved for that cursor.
  This phrase appears on the five-stages
  heading (UX-4) and the stage's clock (UX-29), and it changes whenever the
  state does, frames or no frames. A frozen stage under a top bar reading
  `live` cannot otherwise be told from a stalled one without scrolling to the
  transport, whose position depends on viewport size.
- **UX-7 · Toasts.** Interaction effects are announced from the display
  cursor, not from intake, so what you see and what you are told agree; the
  queue hangs from the top of the stage under the HUD boxes, because the
  stage's bottom edge can be below the fold and an announcement
  placed there would be made to nobody. Particles and toasts are independent;
  two events have one and not the other:

  | event | particles | toast |
  |---|---|---|
  | harvest | green burst | `🪵 harvested +1` / `+3` with axe |
  | eat | orange burst | `🍗 ate` |
  | craft | blue burst | `🪓 crafted an axe` / `⛵ crafted a boat` |
  | food pickup | small orange burst | — |
  | attempt spent | — | `✗ attempt spent` |
  | goal achieved | large white burst + screen flash | `★ goal achieved` |
  | new goal | — | `🎯 new goal N: <text>` |
  | unexpected core exit | — | `⚠ <reason>` in the fault colour |

  Particles are world-anchored and decay in under a second. At live rate the
  same event can fire hundreds of times a second: a repeat is counted onto the
  standing toast that already says it (`🪵 harvested +1 ×37`), wherever it
  stands in the queue, rather than stacked into a wall. Exhaustion is a
  *state*, not an event: the HUD shows `💤 resting` while it lasts and no
  toast fires. Events between the previously displayed frame and the current
  one are announced, so nothing is skipped when the cursor advances by more
  than one frame; the sweep is capped so a live-rate jump cannot freeze the
  frame it is drawing, and ⏮/⏭ and the scrub slider reset the announcement
  cursor to the destination, so a deliberate jump does not replay thousands of
  toasts for events skipped on purpose.

## 3 · Every figure says what it is

Rules that apply to every number, label and colour on the page.

- **UX-8 · Reading cadence and windowed means.** The core lives at about a
  thousand steps a second; a per-step scalar redrawn on every animation frame
  is noise, and a reader cannot tell a value from its flicker. Two rules:
  - **Text readouts and bars redraw at a reading pace.** While the cursor
    moves, or frames arrive, the readouts in *Behaviour*, the action, reward
    and ε lines of *The big world*, the GVF cards, the learner detail rows, the
    Plasticity family means, *Resources*, the HUD option badge, the Knowledge
    headline and the lanes' percentages, the ribbon's cursor caption and the
    orientation strip redraw at most once per `READ_MS` (250 ms); when the
    cursor lands (a pause, a scrub, a jump) they redraw at once; at the slowest
    replay rate they redraw on every frame the cursor reaches; and while the
    cursor rests they follow intake at the same cadence, so coverage and the
    newest lifetime record do not freeze on a paused page. A change of display
    state (UX-6) counts as movement. The gate rides on the animation frame's
    clock and is not a timer (INV-2). Position and the sensed meter follow the
    pose every frame, as do the canvases that show motion — stage, sensor
    window, ribbon, demon lanes, sparklines.
  - **Fast means windowed.** The cursor is *fast* when it is pinned live or
    replaying at 250 frames/s or more; then those readouts show arithmetic
    means and shares over the last `WIN` (1,000) buffered frames ending at the
    cursor, and each says so: the Behaviour mode line reads `live · means over
    the last N frames` (or `fast replay · …`), the decision chain becomes shares
    by selecting layer, the selected-action probability becomes the mean
    probability of the actions taken, the option boundary line counts starts
    and ends by reason, the option-model and planning lines show per-slot
    means, the policy mass is the mean mass, the value bars are mean values,
    the big-world action, reward and ε lines are the window's most frequent
    action, mean reward and mean ε with `· last N frames` on their labels, the
    Plasticity family means are means over the window of each family's
    per-frame mean (finite zero means idle; a non-finite member propagates),
    and the Resources latencies are means marked `(means)`. Paused or replaying
    slowly, the same readouts show the exact frame and the mode reads `selected
    frame`, as do those labels. `N` is the number of frames actually buffered in
    the window, so a fresh connection says `means over the last 500 frames`
    until the ring holds more. Nothing is invented: a mean of stream values,
    labelled with its window, is the observer's own arithmetic. These are
    frame-weighted means and shares, including terminal snapshots; the reward
    line therefore says `reward / frame`. Only boundary-event counts exclude
    the repeated terminal decision record. The all-zero
    verdict of UX-36 is decided over every frame in the window, not over the
    means: a mean of zeros hides nothing, but the exact-zero *state* is a
    property of each frame.
- **UX-9 · One scope per number.** A count says whether it is the run's or
  this browser's, and never says one scope and then qualifies it with another.
  The world-seen figure is `sensed in this run` once the run's map has arrived
  from the server (UX-44); `sensed in this run, as seen from this browser`
  before it has; `retained sensed tiles · partial: observations may be missing
  around stops or restarts` whenever the server marks possible incompleteness;
  and, for a
  world larger than the server keeps a map for, says so. The top bar's
  percentage and the sensed meter carry the same scope in their hover text.
  Current-pass goal outcomes come from the latest core curriculum snapshot,
  including outcomes before this browser connected. Missing or refused evidence
  is unavailable, never inferred as failure.
- **UX-10 · Unknowns are unknown.** Before any frame the counters read `—`,
  the tiles `—`, and the stage says `no frames from this run yet` with the
  connection label beneath it, never a black frame. A demon whose horizon has
  not elapsed reads `waiting for the future…`. Goal names come from the entire
  admitted core curriculum, including goals not yet reached; no campaign
  default is a display fact. A custom `--goals`, `--attempts` or `--cmd` run
  is described by its own schema-10
  configuration or refused whole. The big-world card also names the selected control criterion and the posterior host
  reward-rate estimate at the selected step, explicitly distinguished from a
  window mean. Discounted control displays N/A because it uses no gain. A value
  the core reports as non-finite is
  `⚠ non-finite` in the fault colour where the number would have been, and a
  frame carrying one raises a health pill (UX-20); it is never printed as a
  number and never rounded to zero.
- **UX-11 · Numbers are formatted to be read.** A quantity carries its unit
  (`23,965,526 steps`); counts carry thousands separators; a value that can be
  small beside a value printed in exponent form is printed in exponent form
  below a hundredth, so a model reward of 1.7e-4 never reads as `0.000` beside
  a reward per step of 2.7e-4; one figure has one precision wherever it
  appears (the option bonus to three decimals in the HUD and the ribbon
  legend alike); a step range whose two compact ends would read alike
  (`1k–1k`) is printed exactly; a symbol and its number never split across a
  line. Wire identifiers appear as words (`craft axe`, `exploration start`,
  `restart scheduled`): the words are the core's, only the underscore is the
  page's. Hover texts quote field names in plain quotation marks, since a title
  attribute renders backticks literally.
- **UX-12 · Comparisons wait for evidence.** No reward trend arrow is drawn while the
  newest reward bin holds fewer than an eighth of the steps of the bin before
  it: a bin that has just opened against a bin of millions would draw an arrow
  from noise at every doubling of the lifetime, and the caption says `too few
  to compare`.
- **UX-13 · Terrain coverage.** The sensed meter, top-bar percentage and
  `world seen · terrain coverage` tile report tiles sensed out of the whole world.
  The viewer retains this map from telemetry. The agent receives egocentric
  features: the 11×11 window, proprioception, task relation, inventory and demon
  predictions (`Acorn.Handcrafted.Observation`). The panel explains that scope
  directly. The [BigWorld proofs](../lean/AcornVerif/BigWorld.lean) separately
  compare explicit state counts and representation sizes.
- **UX-14 · Describe the observed quantity.** Captions name the reported
  mechanism, value and window. The ribbon's end counter reports option
  interruptions and reselections at decision boundaries; non-finite values are
  identified by field. Use precise definitions instead of broad learning claims
  or disclaimers. The [promotion standard](prior-art-review.md#default-promotion-and-demotion)
  owns claims about comparative benefit.
- **UX-15 · Colour and shape.** Red is reserved for faults: a refused frame,
  a non-finite value, a stale stream, a stopped core the operator did not
  stop, a refused command. Identity and evidence badges use the colours of
  what they say — the live badge in the accent, a fresh identity in neutral
  grey, a resumed one in blue, a cleared one in amber; a stop the operator
  asked for and every transit state are amber waits. Colour is never the only
  carrier of a meaning: the demon lanes separate prediction from outcome by
  stroke weight as well as hue; the α curves by dash pattern; the ribbon's
  start and end marks by position; the value bars' sign by side of the zero
  line; the lifecycle pills by their words; the trend arrows by glyph and hover
  text; the sensor's terrain glyph occupies an upper band when entities are
  present, with food and deer in separate lower half-cells so simultaneous
  occupancy stays visible; entity marks and stage labels sit on dark backings so they clear 3:1
  over grass, sand and forest; option 3 is a lightness step from option 2 so
  the two bands survive a colour-vision deficiency; text a reader must read is
  at least 10 CSS px and meets WCAG 2.2 AA contrast on every ground the page
  uses.
- **UX-16 · Names follow the stream.** Option slots are `option 1–3` under the
  deployed `subtask_policy = learned`, each shown with the imprint unit and
  bonus it pursues (`→ unit N · bonus g`), `neutral · no ranked feature yet`
  while none is assigned; the hand-authored names “Wood”, “Mine”, “Forage”
  appear only when the stream says `hand_authored`, labelled as the
  hand-authored potential. A slot pursuing a ranked imprint feature called
  “Wood” would assert a semantics the agent does not have. Demon lanes are
  labelled by the signal each predicts, because the eleven questions are
  hand-authored and fixed for the run (`docs/learned-only-binding.md` D5) and
  the panel says so; if the questions ever become the agent's this
  requirement changes with them. Names, target-policy semantics, γ and
  horizons come from the core with the frame; the page renders them and
  invents none.
- **UX-17 · Every algorithm surface names its source.** Work, equation,
  fetched page and a short quote, or a statement that the quantity is out of
  viewer scope; the register is §10, and a surface may keep its source one
  click away in a `sources` disclosure or a hover text, never absent.

## 4 · States and their remedies

- **UX-18 · Connection vocabulary.** The connection label is exactly one of:
  `connecting…` → `live` → `reconnecting…` (stream dropped) →
  `stale — reconnecting…` (watchdog fired, UX-27) → `core stopped — <why>`
  (the core exited unexpectedly, or could not start; the server publishes the
  reason) → `core stopped` / `core starting…` / `core stopping…` /
  `core clearing…` (the core is down or in transit because the operator asked,
  so nothing is wrong and nothing reconnects). A data frame asserts `live`
  only while the control state says `running`, and an opened socket asserts
  nothing by itself: the server replays its last `replayCapacity` (500) frames to
  every new connection, a stopped core's included, and those frames are the
  core's past. A stop the operator did not ask for — the supervisor's failed
  and restart_scheduled transitions — keeps its reason on the label in the
  fault colour, and the control state owns that label: every control frame
  that says the core is not running writes it (the third failed start changes
  the reason while the state stays stopped), a replayed “eos” frame defers to
  it, and the watchdog's ticks write the same label from the same state.
- **UX-19 · Identity.** Every core frame carries authoritative `run_id`,
  `agent_epoch`, `world_step`, `lifetime_step` and a closed origin (`fresh`,
  `resumed` or `cleared`). The top bar's identity pill names the agent epoch
  and short run ID with the origin word, in the origin's colour (UX-15), and
  its hover text says when the last frame with this identity arrived. A
  successful checkpoint load is the only constructor of `resumed`; Clear
  creates a new run ID, increments the agent epoch, and can therefore render
  only `cleared fresh` until that identity later resumes. A changed
  authoritative run ID or agent epoch resets everything derived from the agent
  — frame ring, verification queues, buffer-scoped option statistics,
  per-demon discounts and horizons, curriculum progress — from one factory, so
  the reset cannot be partial; a process restart that successfully resumes
  keeps the logical identity even though world time restarts. Buffered frames
  from a run the control plane has already archived — the tail of a Clear or a
  restart — are skipped without a readout: they carry no defect and have no
  remedy.
- **UX-20 · Health pills say what is wrong and what to do.** Refused and
  non-finite frames are counted and reported with their remedy, in the top
  bar, drawn before the render loop looks for a frame, because the condition
  that most needs reporting is the one where every frame is refused and the
  ring stays empty. A frame is refused whole, never partly absorbed, and
  counted by the reason it was refused — a closed set with one remedy each,
  naming the wire keys involved:
  - `schema_version` not this page's, or a count or array length that
    disagrees with the page's constants → `⚠ stream shape mismatch — rebuild
    the viewer against this core`; the page is embedded in the viewer binary,
    so the two were built from different trees, and the hover text carries the
    expected shape and the two build commands;
  - a required key the core does not emit → `⚠ stream shape mismatch — the
    page requires a field this core does not emit`: a source defect,
    rebuilding will not fix it;
  - a key present but not holding the value the schema promises → `⚠ the core
    sent a value outside its schema`: the emitter or the transport is wrong;
  - a control or `map` frame the page cannot read → `⚠ the viewer server sent
    a control frame this page cannot read`, counted apart from frame refusals
    because page and server are one binary;
  - a frame on which the page's own intake threw → `⚠ the page failed on N
    frames — a viewer defect`, with the last error's message in the hover text;
    the frame still counts as the core producing frames, so a page defect can
    never look like a stale stream;
  - a frame carrying a non-finite float → kept, counted, rendered as
    `⚠ non-finite` where the number would be, and reported as `⚠ the core
    reported a non-finite value in <field>`, naming the field; the hover text
    states the divergence reading as a possibility and says to keep the run
    and check it with `acorn demo --research-profile ranked --telemetry`.

  Neither appears in a healthy run. If one does, it is telling you something
  the rest of the page cannot.
- **UX-21 · Run controls.** The top bar carries two buttons and one state
  word: **Start/Stop** (one control, labelled by what pressing it will do) and
  **Clear**, beside the server's `actual` state, one of `starting…` ·
  `running` · `stopping…` · `clearing…` · `stopped`. The three transient
  states are shown, not skipped: a Clear takes as long as the core needs to
  finish its attempt, and a button that sat unchanged for that long would
  read as a click that did nothing. Each button's hover text states only what
  the control frame carries: Stop "finish this attempt and exit; a checkpoint
  is written only if saving is armed" (or "saving is disarmed for this run"
  after a refusal, or "the viewer does not know whether this core checkpoints"
  under `--cmd`); Start "start the core; it resumes from its checkpoint if one
  exists"; Clear, while stopped, "archive this run and create a new
  zero-knowledge identity; the core stays stopped". A disabled control still
  says why, so "unavailable here" is distinguishable from "this build has no
  such button". A request the server refuses, or a viewer the page cannot
  reach, raises a fault pill beside the controls (`⚠ stop refused — <why>`)
  that stays until a control frame shows the server moved; the toast that also
  says it is below the fold. The control endpoint is `POST /control`, bound to
  `127.0.0.1`, POST-only, JSON-only, and gated by a token minted per viewer
  start and read from the served page, so a page left open from a previous
  start holds a stale one and is refused; bodies are capped and rejections say
  little about which check failed.
- **UX-22 · Stop is cooperative and persistent.** The core finishes its current
  finite attempt, attempts a checkpoint if saving is armed, and exits through
  the same writer as periodic and finite-campaign completion. Successful save
  and admitted reload preserve the checkpoint's knowledge and lifetime clock;
  the world and documented transient state restart cold. With disabled saving,
  load refusal (UX-25) or write failure, exit status 0 is not a durability claim.
  The page reports the actual exit and the core's last lines (UX-46). A final
  save failure or nonzero exit also keeps a visible warning beside the controls
  while stopped; requesting Stop does not hide either warning.
  There is no automatic kill deadline: a step bound supplies no wall-clock
  bound for learning, checkpoint IO or task cleanup. Stop remains `stopping…`
  while that work completes, assuming native IO and scheduling progress.
  External forced termination is a separate operator/OS action; a nonzero exit
  warns that learning since the last successful checkpoint may be lost. The
  viewer itself has no force-kill control. Custom `--cmd` descendants that
  retain output handles can delay drain; name the core directly or `exec` it.
  Stop intent persists across viewer restarts, so reopening a stopped run
  leaves it stopped unless the operator explicitly requests Start with `--start`.
  The convenience launcher supplies that request: running it means start/resume
  now, without Clear or a direct edit to persisted state. Start still passes
  through the supervisor queue after successful state admission and HTTP binding.
  With `--control-stdin`, the viewer accepts the existing closed stop-line
  protocol as a request to close cooperatively. It winds up the core, waits for
  reap and pipe drain, prints the actual exit/checkpoint disposition, shuts
  down HTTP and releases its command reader. Final checkpoint, process, pipe or
  log failures produce a nonzero launcher exit after cleanup. EOF is not a stop request.
  The launcher owns terminal SIGINT and forwards this request, so Ctrl-C does
  not interrupt the viewer/core process group. No kill deadline is introduced.
  Shutdown retains the durable intent; browser Stop remains the operation that
  persists stopped intent.
- **UX-23 · Clear is one click: stop → archive → reseed → restore.** The
  whole run directory is renamed into the archive (UX-43) and a new random
  seed is taken. Cooperative stop happens first and attempts an armed save.
  The archive retains the available checkpoint and logs; successful final
  saving preserves knowledge at the completed attempt boundary. Refusal or
  write failure can leave only an older checkpoint or none, so restoring an
  archive recovers only its successfully persisted knowledge, with the
  documented cold transient boundary. Archiving and reseeding are
  inseparable: a checkpoint records its seed, so reseeding without archiving
  would make the core refuse the file and disarm saving — a run that neither
  loads nor saves — and fused into one operation that state is unreachable.
  Clear returns to the run state it found: pressed while running the agent
  comes back running; pressed while stopped it stays stopped and says
  `cleared; still stopped, as it was before`. Clear reaches the browser: on
  the acknowledgement the page drops its stored world, resets agent-derived
  buffers and rebuilds the map, and frames from the archived run are rejected
  against the new control identity; the identity badge is rendered only from
  the new core's typed origin, so a stale `resumed` has nothing to survive in.
  Clear is disabled under `--cmd`, with the reason in the hover text: the
  viewer does not know which checkpoint or seed that core uses, and a Clear
  that archives the wrong thing is worse than no Clear.
  Finite campaign completion releases its stdin reader without waiting for a
  future command or external EOF. Actual process state still follows reap;
  the supervisor's existing restart policy applies after a finite exit.
- **UX-24 · Giving up and restarting are visible.** While `desired =
  running`, a core that exits is restarted whether or not any browser is
  connected; after `failureLimit` (3) failed starts in a row the
  supervisor gives up, sets `desired = stopped`, and the label carries the
  reason with `— gave up after 3 failed starts in a row` (UX-18) — including
  the reason a spawn failed, which is otherwise only in the log. A run that
  lasts longer than `healthyRunMs` (30 s) resets the count, so a campaign that
  ends cleanly three times is not mistaken for a build that cannot start. A
  restart the supervisor made is visible after the fact: while the control
  frame's failure count is above zero and the core is running, the top bar
  carries `⟲ restarted after an unexpected exit` (with the count when more
  than one), its hover text naming the last exit reason; the count resets at
  the operator's next Start or Clear, and the pill with it. The restart
  itself takes under a second, so the label that says it is happening is not
  the record; the pill is.
- **UX-25 · A refused checkpoint is reported.** The core disarms saving for
  the whole run when it refuses a checkpoint, which on stderr alone is
  invisible to anyone watching: a healthy-looking run that is quietly
  persisting nothing. The top bar raises `⚠ not saving — press Clear to start
  a fresh run`, naming the remedy rather than only the diagnosis.
- **UX-26 · Transport.** Controls: ⏮/⏭ (jump 500 frames), ⏸/▶, ⚡ LIVE (pin
  to the newest frame), replay rates 10 / 60 / 250 / 1000 frames per second, a
  scrub slider, the buffered-frame position and a lag readout, each with a
  hover text saying what it does, under a lede that says what the buffer holds
  and lists the keys. Keyboard: space, `L`, ←, → — reaching the transport only
  when no button, link or disclosure has the focus, so space on a focused Stop
  presses Stop. LIVE pins the display to the newest frame — a timelapse of the
  real thing. A replay rate detaches and walks the local buffer (a ring of
  `CAP` (30,000) frames, then oldest dropped) at that rate, and the lag readout
  says how far behind live that has put you. Pausing freezes the display; the
  slider and ⏮/⏭ browse the buffer. Exactly one mode is lit: LIVE, or the rate
  in force while the buffer is being walked — ▶ after a pause resumes at that
  rate and lights it — and nothing while paused, when the ▶ glyph says so.
  When the core is stopped or the stream stale, the label retains that state
  and the cursor's position: `newest frame` only at the newest frame, otherwise
  paused/replay mode and the number of buffered frames behind it. The transport
  uses a one-based selected ordinal and actual buffer count; an empty ring
  says `no frames buffered`.
- **UX-27 · Staleness and the frames/s counter.** If no new frame arrives for
  `STALE_MS` (8,000 ms) while the control state says the core is running, the
  label reads `stale — reconnecting…`, the page reopens the connection (the
  server replays its last frames so the view refills) and clears the stale
  state when frames resume; while the control state says the core is not
  running the same silence reads as the idle label (UX-18), since a
  deliberately stopped core is not a fault and reconnecting against it would
  report one forever. Intake's `stored`, `refused`, `rewound` and `skipped`
  outcomes describe ring admission independently of freshness. Only a valid
  capture envelope matching the control plane's current run and epoch can
  refresh health: identity and timestamp/lifetime/world counters must have
  their declared forms, and the `(timestamp, lifetime step, world step)` tuple
  must advance lexicographically for that identity. Timestamp comes first so
  a resumed core can produce fresh captures behind the ring; counters separate
  captures within one millisecond. Replayed refusals and page exceptions cannot
  refresh health. A fresh envelope counts even when its payload is refused or
  intake throws, keeping core production distinct from viewer usability. The
  displayed throughput counts newly admitted capture envelopes per second.

## 5 · The panels

What each panel must show. How it draws it is the code's.

- **UX-28 · The stage.** The aerial view follows the agent: the agent stays
  centred and explored terrain scrolls under it, at `Z` (4) logical px per
  tile; the camera eases over small gaps and snaps over large ones (a live-rate
  jump, a scrub), so the agent is never left off-centre. Only tiles the agent
  has sensed are coloured; unexplored terrain stays near-black; beyond the
  world's box — where the agent cannot walk and the page keeps no map — the
  stage paints a tone of its own, so an agent at the edge is not read as
  standing beside unexplored terrain. Base colours per kind: water `#3a6ea5`,
  sand `#d9c58b`, grass `#7da05e`, forest `#5c8a3f`, tree `#2e6b2f`, mountain
  `#8a8a8a`, stone `#b0b0b0`, ore `#d4a017`, each modulated by a deterministic
  per-tile shade so terrain reads as ground; a tile re-sensed as a different
  kind is repainted. The agent is a white circle with a gentle pulse, a soft
  halo and a blue facing arrow. The recent trail fades out behind the agent;
  live, it is the browser's own record, and detached it is read from the frame
  ring behind the cursor, so the comet ends at the agent on screen and not at
  the live agent hundreds of steps ahead. Entities render only inside the
  current sensor window — the honest POMDP boundary — as orange food dots and
  brown deer squares with a small hop, each over a dark outline; the window's
  footprint is outlined in two tones so the edge of perception is visible on
  grass and sand alike. For *Reach* goals a gold target is drawn — a pulsing
  circle with crosshair and a `target` label, visible regardless of
  exploration. When the symbol cannot fit inside the canvas, an inset edge
  arrow points toward it. Target graphics have a separate layer above map
  effects, and their backed labels stay inside the canvas. The goal card names
  the compass direction and straight-line distance to the target centre; this
  is not a route length or a count of steps remaining. Absolute placement is the
  observer's, not the agent's: the stream carries `gx, gy` so a human can place
  the marker, while the agent receives only the declared task relation
  (displacement and distance) and neither absolute target coordinates nor its
  own position (the [`Observation` interface](../lean/Acorn/Host/Observation.lean)). Night dims the view
  with a translucent blue tint, deeper at midnight, and the clock's icon flips
  ☀/🌙.
- **UX-29 · The HUD.** A header above the map places `current goal N/<goal_count>`
  on the left, with plain-language goal text — `Go to the gold target (x, y)` /
  `Hold n <Item>` / `Own Axe|Boat` / `Continue for n world steps in this attempt`
  — and `tier T · attempt A of <attempt_cap> · cycle C`, every cap read
  from the authoritative frame. Non-travel goals explicitly have no fixed map
  destination. Collection means current inventory; crafting means tool ownership.
  The survival duration is the requested duration, not a remaining-time estimate.
  The header's right side shows world time in steps, the day icon,
  and the display state word whenever the display is not live (UX-6).
  A footer below the map places the energy bar on the left, the inventory `🪵n 🪨n 🍗n ✨n` with axe and
  boat badges dimmed when absent, and `💤 resting` while the agent is
  exhausted. The footer's right side shows the running option — `—` when none, else the slot's
  name in the slot's colour — with a second line saying what the slot is
  pursuing (UX-16) and, in fast mode, the share of the window an option ran.
  Header and footer items wrap at narrow widths; neither overlays the map or
  obscures its target.
- **UX-30 · What the agent senses.** The 11×11 sensor view shows exactly what
  the agent perceives — tile kinds, food, deer, glyphs for tree, mountain,
  stone and ore — with the agent at the centre. Its lede says that everything
  else on the map is the viewer's record of what has been sensed, not the
  agent's sight.
- **UX-31 · The big world.** The whole explored map, the camera rectangle,
  the goal and the agent as a white dot; a meter labelled `sensed` reporting
  `seen / 1,048,576 tiles` with a progress bar; the run's position; and, at the
  reading cadence, the most frequent action, mean reward per frame and mean
  primitive ε over the window, each label carrying its window (UX-8). The lede
  states the coverage caveat (UX-13). The ε line's hover text says what the
  emitted rate is and is not (§10).
- **UX-32 · Predictive agreement.** The supporting Knowledge panel displays
  **Prediction diagnostic · higher agreement is better**, 0–100 points with an
  increasing progress indicator. This is
  a declared evaluation convention, not percentage known. For each typed current
  question, the core captures a forecast before its future, shares the existing
  bounded pending bank and cadence, then accumulates the exact squared discrepancy
  against its rounded finite return, normalized by the immutable envelope
  `Eᵢ = 2 × admitted binary32 horizon`. With `Mᵢ = Σqᵢ/nᵢ`, per-question agreement
  is `100(1−√Mᵢ)`; the aggregate is `100(1−√(ΣMᵢ/m))`. Every current question must
  have settled data; otherwise show `waiting k/m` while running or `incomplete k/m` after stop. Questions receive equal weight,
  not weight proportional to sample count. Invalid/saturated channels suppress
  the aggregate. No bad value is clipped into a score.
  Cards show question name, declared target policy, actual experienced evolving
  behavior, γ, finite horizon, envelope, exact settled/pending/censored counts,
  actual forecast-start and settlement endpoint ranges, normalized RMSE (lower
  better), and separate conservative tail/arithmetic allowances. Empty, pending,
  complete, partially censored, censored, invalid and saturated states are visible.
  Existing current-prediction cards identify selected-frame or frame-window scope;
  their latest historical settlement belongs to its captured earlier prediction.
  The disclosure explains the finite tail bound `γᴴ/(1−γ)`, its normalized RMSE
  propagation and reversed agreement endpoints. It separates binary32 return
  arithmetic, exact sufficient-statistic aggregation and display rounding. RMSE
  display rounds down by less than one millionth; text uses hundredths of points,
  reserving literal 100 for exact zero measured discrepancy and using `>99.99`
  or `<0.01` near nonzero endpoints. Finite agreement is not infinite-return truth.
  Squared-loss discrepancy plus conditional variance explains why an optimal mean
  forecast can disagree with noisy realized outcomes. There is no noise estimator,
  baseline, frozen-policy evaluation or claim of improved goal achievement.
- **UX-33 · Evaluator lifetime and history.** A new core process starts an empty
  evaluator even when checkpoint-persistent learner and lifetime totals resume.
  The display names the evaluator's actual starting lifetime step and latest
  snapshot clock. Stop or world discontinuity discards unavailable pending futures
  with counted censoring, never a fabricated terminal return. If the final snapshot
  is missing, unresolved pending fate remains unknown. Browser reconnect, refresh,
  frame loss and cursor replay do not accumulate or reset native accounting.
  A generated process/clock predicate refuses stale and duplicate snapshots while
  admitting one same-clock final censor snapshot without adding a raw observation.
  Process markers are monotonic OS start times, not globally unique identities.
  Source/build and logical run/epoch identity remain distinct admission boundaries.
  The bounded process-local history uses actual lifetime clocks on a labelled
  logarithmic axis. Each point is cumulative since evaluator start, not recent
  adaptation; population changes and overlapping/censored futures limit comparisons.
  Separately, checkpoint-persistent plots show SwiftTD empirical-return MSE and
  task reward per step, one point per occupied power-of-two lifetime bin, with
  native units and a hollow newest bin. Neither scope nor scale is reused for the
  process-local score. Reward and sensed terrain coverage remain separate evidence.
- **UX-34 · Plasticity.** Mean step size over the weights *currently being
  adapted*, log-scaled, for the demons, the primitive controller, the
  meta-controller and the options separately — the legend and the expandable
  rows use those four names, and the curves are told apart by dash pattern as
  well as hue. Averaging over all weights instead would be dominated by the
  ones the agent has never touched and would hide step-size optimisation
  entirely. A family with no weight being adapted has no mean, and its curve
  shows a gap, never a plunge to the floor. Non-finite family samples also
  leave gaps and make included numeric summaries non-finite; the legend says
  both meanings. The axis has separated labels at its actual ends and readable
  interior decades. Curves hold up to 400 newest intake samples, one per
  `VERIFY_STRIDE` (24) admitted frames, independently of the replay cursor;
  their caption names the actual count and interval. Legend values separately
  name their frame window in fast mode or the selected frame when paused/slow.
  Expandable rows expose the active step size and eligible-feature count for
  every learner, including each option/action pair: a family mean never
  substitutes for the selective-credit state it summarises. The panel is that
  α, with its source attribution in §10. Model arrays reserve
  reward, continuation and duration slots per option; discounted control marks
  duration slots unused, not learned zero-valued duration estimates.
- **UX-35 · Surprise.** Mean absolute TD-form residual across the demons,
  computed as `c_t + γ·P(s_t) − P(s_{t-1})` from adjacent reported predictions.
  These are projected predictions, and the viewer evaluates the formula in
  binary64; the plot does not claim the learner's internal binary32 error. The browser
  attempts one sample per `VERIFY_STRIDE` (24) admitted frames and holds up to
  400 available samples, with newest at right independently of the replay
  cursor. The plot names its top value, zero and actual held count. Bar height
  carries magnitude in a fixed contrasting ink.
- **UX-36 · Behaviour.** Primitive value bars for the nine actions, spelled as
  words, and meta value bars for `primitive` plus the three option slots
  (UX-16), green positive and red negative, drawn as a diverging chart: the
  bar area lies wholly to the right of the name column, and when any value is
  negative the zero line sits at its midpoint with a `0` label, so a bar's
  length is proportional to its value in both directions and never paints
  under a name; values are printed so a nonzero figure never reads as `0.000`.
  The meta-controller chooses between running a skill and handing one step to
  the primitive controller; it does not re-choose among the primitive actions
  itself, because nine indistinguishable ways to spell "hand off" are nine
  estimates of one quantity, and an arg-max over them is biased upward against
  the skills. The decision chain states the selecting layer, exact primitive
  and meta probabilities, selected-action probability, exploration branch,
  option boundary (β = 1 at an end, β = 0 while continuing, with the elapsed
  steps and the end reason), reward, prediction error and credit state at the
  cursor, or their window means in fast mode (UX-8). It never calls a value
  difference an advantage, because this implementation has no
  option-advantage quantity, and initiation is explicitly the trivial
  all-states set, so no eligibility visualisation is invented. A value
  function that is *identically zero* is a reportable state, not a rendering
  gap: the panel says `every action value is exactly 0` and why — Swift-Sarsa's
  update is a fixed point at `r = 0`, both terms of `δw` being proportional to
  `δ'` (§10) — instead of drawing an empty chart; zero here is exact and
  expected until a non-zero reward lands on an executed learning step, and how
  long that stretch lasts at the current pin is unmeasured. A value the core
  reports as non-finite is likewise a state: the bars are replaced by `n of M
  action values are non-finite · this learner's weights have diverged`.
- **UX-37 · Option models and planning.** The option-models line shows the
  reward and continuation predictions for each slot (PAR-13): while a skill is
  executing, its expected cumulative host reward `r̂` and continuation value
  `ĉ` (written `ĉ_v` in the source; the page spells it `ĉ` everywhere);
  otherwise the predictions across the three slots. Differential research also
  shows predicted start duration in primitive steps. Every differential model
  query is for a fresh activation at age zero, including while an option runs;
  start duration is not remaining duration. Fast mode uses the same labelled
  window means as the other model readouts. The planning line shows
  backups since process start or latest restore (`planning_steps`) and the
  Bellman planning error per slot (`planning_errors`), named `Bellman error`
  wherever it appears. Sources are pinned in §10.
- **UX-38 · The options ribbon.** Which option was running over the last
  `RIBBON_SPAN` (3,000) buffered frames as bands in four horizontal lanes
  (top: primitive, then option slots 1–3), redundantly keyed by colour, read from the frame buffer so
  the ribbon is correct wherever the cursor is, with goal transitions as
  violet lines and explicit core-owned start and end boundaries as ticks in
  the margins — a start hangs from the top edge, an end rises from the bottom
  of the band — in one neutral ink: an end by cap or goal is not a fault, so
  it is not red, and a tick the colour of a band would vanish on it. Immediate
  re-selection of the same skill is an end and a start at one decision, never
  one merged band. The lede says the flicker is options being interrupted and
  re-chosen at decision boundaries, which the end counter below it shows
  (UX-14). The cursor's record (action, selecting layer, reward) is drawn
  centred under the band at the reading cadence, never over the window's end
  labels. The legend names each slot by UX-16's rule and what it pursues, and
  the checkpoint-persistent totals report lifetime option starts (never
  "episodes": the stream is one unbroken episode), completed mean duration,
  and goal / cap / interruption end counts. End *reasons* are shown; the
  terminal target `c + z` is out of viewer scope (§10).
- **UX-39 · Curriculum.** One row per authoritative `goal_count`, named from
  the admitted curriculum in every core snapshot. The panel explicitly follows
  the latest core snapshot, independently of the replay cursor. Status squares
  are dark slate for not yet reached, steady amber for an unresolved current
  goal, red for failed attempts, green for achieved, and hollow for unavailable
  outcomes. A completed successful goal is green even in its terminal frame.
  Rows show the current pass's failed-attempt count and, on success, the actual
  successful attempt's step count. Compact sufficient summaries avoid retaining
  attempt histories or trajectories. Reconnection restores these summaries from
  the core without replaying old frames or inventing a default curriculum.
  The pass number and achieved/assigned count share this scope. A pass boundary
  resets its outcomes; a process restart begins new pass accounting while
  checkpoint loading can preserve learned state. Invalid accounting suppresses
  outcome claims while goal names remain available. A second table shows
  checkpoint-persistent success (`N of M succeeded`), steps per attempt and
  reward rate by goal family, over the lifetime and over the fixed
  multiresolution bucket containing the cursor's cycle — cycles one to eight
  exact, later buckets labelled by their logarithmic range — drawn from the
  cursor's frame and written only when its text changes.
- **UX-40 · Resources.** Readings name their scope. The core reports
  agent-update and environment-transition microseconds (means over the window
  in fast mode, marked `frame means`, and from the selected frame when
  paused/slow). Remaining core resource figures are the latest process
  observations: uptime, sampled resident set, last checkpoint size and write
  time, checkpoint failures, and telemetry
  drops and refusals; the browser separately reports its own render
  milliseconds per frame, labelled as this browser's. No control period is
  declared, so deadline margin and misses are literally `N/A / N/A`, never
  inferred from observed throughput.
- **UX-41 · Geometries.** Every canvas is sized to its own box in device
  pixels and scaled back to CSS units, so text and terrain stay crisp on a
  retina display. At 1280 CSS px the full three-column analysis row remains
  visible without page overflow; the top bar may wrap to two lines there.
  Below 1040 px the orientation strip stacks (its verdict tiles go four
  across), the goal-achievement summary follows the stage as a full-width block
  and the analysis row stacks, with the mode badge stating `COMPACT`; at 700 px
  and below the five nodes wrap to two columns — the arrows between
  nodes go with the wrap, the return glyph stays on the last node, which takes
  the whole row — and the tiles return to two across. No panel is hidden to
  make the layout fit, and the page never scrolls horizontally. The research
  disclosure has the same initial state at every width. The aerial stage has
  its natural aspect, capped at 62% of viewport height with a 280 px minimum;
  sidebar content cannot stretch it and move the centered agent below the
  first screen. The sidebar contains the goal-achievement summary only; sensing
  and world details flow below the main row, with compact canvases beside their
  descriptions on wider screens and stacking on narrow screens.


## 6 · The run and its files

- **UX-42 · Launch.** `./scripts/start.sh` is the newcomer entry point. It prepares
  missing system and pinned Lean/Mathlib dependencies, builds the viewer and its
  declared core/checkpoint dependencies, and explicitly starts/resumes the ranked
  discounted campaign. It uses `acorn-run/`, requests an available loopback port,
  opens the system browser after successful binding, and stays in the terminal
  until the viewer exits. Preparation/build failure prevents launch. Package
  managers may require the operator's system prompts; application execution is
  never elevated. Repeated launcher instances are excluded by a per-checkout
  `.acorn-launch/` lock outside the run directory, including during Clear. An
  uncertain or interrupted lock requires operator recovery, never automatic
  killing or removal of another owner's files. Manual viewer invocation remains
  an advanced path whose operator must ensure exclusive run-directory ownership.
  Browser-open failure prints the actual URL and does not stop the managed run.
  The detached desktop opener is polled without blocking; it can survive viewer
  exit and never holds a dedicated worker or delays cooperative shutdown.
  `--no-browser` supports manual/headless access and `--prepare-only` builds
  without learning. A read-only bootstrap status admits provisioning only for
  missing dependencies; malformed locks, symlinks and ambient overrides remain
  explicit refusals. The script is preparation tooling, not a substitute for
  `./scripts/verify.sh` and not empirical default qualification.

  The advanced `./lean/.lake/build/bin/acorn-viewer --research-profile ranked --port 8088`
  serves the UI at `http://127.0.0.1:8088/` and spawns the core with the
  explicitly selected ranked research campaign (`--research-profile ranked --cycles 0`, 1024², 13 goals, 3 attempts ×
  4000 steps) and weight checkpointing. `--run-dir <dir>` moves the run
  directory, `--no-checkpoint` runs the core stateless, `--cmd "…"` overrides
  the whole campaign, `--port N` overrides the port (`0` requests an available
  port), `--start` explicitly requests Start, `--open-browser` opens the bound
  URL, and `--control-stdin` admits cooperative viewer shutdown. An unusable command line
  is refused with a reason and a usage line, never absorbed into a default: an
  unknown flag, a flag with no value and an unparseable `--port` are all
  errors, because serving on 8088 after `--port 80x8` failed to parse would be
  a run the operator did not ask for. Checkpointing is on by default because
  the server restarts the core whenever it exits (UX-24): without it a restart
  would substitute a brand-new agent while the page still read `live` and the
  explored map — which is the world's, not the agent's — stayed on screen.
- **UX-43 · One run directory.** Everything a run persists lives in one
  directory, so Clear can archive all of it by moving one thing (UX-23):

  ```text
  acorn-run/  weights.ckpt · state.json · core.log · core.log.1 · explored.map
  acorn-run.archive/<stamp>/   a previous run, complete
  ```

  The core writes only `weights.ckpt`; the viewer writes the rest, and
  `explored.map` exists as `explored.map.tmp` beside it while a write is in
  flight. The archive root is a sibling, not a child and not a distant path: a
  child would be archived into itself, and a distant one could be on another
  filesystem where `rename` is not atomic. A stray `./acorn-weights.ckpt` in
  the working directory is moved in on startup, and only when the destination
  is empty — a checkpoint outside the run directory would survive a Clear, and
  the current run's weights are never overwritten to tidy up an older file.
- **UX-44 · The explored map belongs to the run.** The viewer server keeps
  retained sensed tiles in the current run (`Acorn.Host.Viewer.WorldMemory`),
  keyed by the *world* — run ID, side and seed — so that a frame from any other
  world replaces it; the agent epoch is not part of the key, because a core
  that restarts without loading a checkpoint begins a new agent in the same
  world, and the terrain it sensed is still terrain. The page keys its own copy
  by the same three facts, taken only from the frames themselves (or, on
  Clear's acknowledgement, from the control plane's new run), and unions the
  two copies only when they describe one world; a stored map that names no run
  is not restored. Each connection receives the run's map once, after the
  control frame and before the replay, and only when it names the control
  plane's current run. The browser unions that retained map with its own
  matching stored observations, which may include additional tiles. The map is persisted as
  `acorn-run/explored.map` by the supervisor thread — periodically while a
  tile has changed since the last successful write, and when the core exits;
  never from the stdout pump, which sits between the core and its reader — and
  read back at the next viewer start only if it names the run the state file
  names and every byte is a kind or unseen; a file that fails that is refused
  whole and said so on stderr. **Possible missing observations are explicit**:
  a missing map for an existing run, every restored disk snapshot, and every
  core reap mark the memory `partial: true`. A snapshot cannot certify that
  observations after its last periodic write reached disk; generation isolation
  at reap can omit buffered stdout tail frames. Changing the marker dirties
  the map, and reap broadcasts and persists the partial claim before restart.
  The header, map frame and UI scope retain it until a new world is created.
  This is bounded retained evidence, not lossless retention. A run that has
  never had a core begins empty with no observations to have missed. A
  frame whose pose is outside its own world, or whose tiles are not kinds, is
  refused before any arithmetic. Identity and the map are read only from the
  core the pump belongs to. Reaping revokes frame forwarding; final drain may
  finish identity and checkpoint attribution for that still-owned generation,
  but cannot re-adopt an archived run or re-key a memory Clear has reset. The server keeps a map only for a side up to
  `mapSideCapacity` (4,096); a larger `--cmd` world is shown from frames and the
  browser's own storage, has no server memory, and its tile says so. The
  unseen byte, the kind count, the window side and the side limit are each
  spelled once in the page and once in the server, and the gate suite holds
  every pair equal, and both to the core's own constants.
- **UX-45 · Browser storage.** The explored map and the trail are saved to
  `localStorage` (key `acorn-viewer-world-v1`) on a timer while either has
  changed since the last save, and on unload; on load they are restored (the
  top bar shows `restored`) and new frames merge into them. A stopped or
  paused page changes nothing and so writes nothing. The map is run-length
  encoded before storage, because a raw byte string of a mostly unseen world
  would exceed the quota on JSON escaping alone. Storage failure (blocked or
  full) is non-fatal: the viewer keeps working with an in-memory map and the
  top bar says `not persisted`.
- **UX-46 · The server never lets a browser slow the core.** Each browser has
  a bounded queue, and a browser that stalls drops frames rather than growing
  the server's memory without bound; subscribing snapshots the replay buffer
  and registers under both locks, so the handover loses nothing and
  duplicates nothing. A poisoned mutex is recovered rather than fatal: the data
  behind those locks is a bounded ring of JSON lines, a list of channels and
  the byte map of sensed tiles, nothing a panic can leave inconsistent, and
  were poisoning fatal one connection thread's panic would silently kill the
  broadcast while every browser went on displaying `live`. “accept” failures
  back off exponentially instead of being retried at once: under descriptor
  exhaustion every accept fails together, and a spinning accept loop would
  steal CPU from the agent the viewer exists to observe — an observer
  influencing the run, which INV-1 forbids. The core's stderr is captured to
  `acorn-run/core.log` (rotated, one previous generation kept as
  `core.log.1`) and echoed to the viewer's own stderr; the last lines are held
  in memory and the last few travel with every `stopped` control frame, so the
  page can show the core's own account of why it stopped without reading a
  file. Every log write failure is absorbed and the reader drains the pipe
  unconditionally while the child lives: a pipe nobody reads fills, at which
  point the core blocks inside its own `eprintln!`, and a viewer that froze the
  agent would be the worst INV-1 violation available.

## 7 · Expected, and not bugs

- The option badge changes often: an option can end within a few steps and
  never runs past its cap, so at the reading cadence it may change up to four
  times a second.
- `features` reads `0 retired` for a long time. The generate-and-test test
  half (PAR-11) is present but has not been observed to retire a unit; the
  node reports the count the core carries, and zero is the honest figure.
- Deer and food pop in and out exactly at the sensor boundary.
- Motion is bursty while the agent is low on energy: it rests to recover.
- Near-black regions are genuinely unexplored, and the trail is short right
  after a first-ever connect (the server replays only its last frames), though
  the explored map itself is complete for the run (UX-44).
- Agreement waits for every question to settle; per-question cards show pending
  futures and the actual settled coverage before the aggregate is available.
- Curriculum rows include names and current-pass outcomes from before this
  browser connected; the core supplies them with every snapshot.
- A restart of the core keeps the logical agent epoch when checkpoint loading
  succeeds; when no checkpoint loads, the core selects the predeclared next
  epoch and the supervisor publishes it before forwarding that frame. A
  resumed agent restarts the *world* from its seed, so pose and inventory begin
  again — continuity of knowledge and lifetime experience, not of world state.
- Force-killing the viewer orphans its core child, which keeps running and
  absorbs telemetry write errors by design; check with
  `pgrep -f 'acorn demo --research-profile ranked --telemetry'` after an abrupt kill.
- The primitive value bars may read exactly zero for a long stretch (UX-36):
  the Swift-Sarsa fixed point at zero reward, not a rendering fault. How long
  the stretch lasts at the current pin is unmeasured.
- The skills' action values may be far flatter than the primitive
  controller's. A potential-difference shaping term alone does not establish policy
  uniformity. `AcornVerif.finite_activation_bootstrap_correction` owns the finite
  bootstrapped-return identity, including initial potential and stopping value.
  Sparse task rewards or small plotted values do not establish a learning
  outcome; any such claim requires separately qualified evidence.

## 8 · Evidence modes

- **UX-47 · Live is one stream.** `/` carries a persistent `LIVE RUN · single
  stream` badge, recent diagnostics, and lifetime summaries of that one
  logical agent. It contains no across-seed interval or uncertainty band.
- **UX-48 · Historical evidence is outside the live observer.** The application
  serves only its current stream and lifecycle controls. It embeds no historical
  study page or report; `/study`, `/study.html` and `/study-report.json` are
  unrecognized routes and return 404. No current readout or caption substitutes
  for excluded historical evidence. Goal counts and predictive agreement do not
  establish learning effectiveness or a comparison against a baseline.

## 9 · Telemetry contract (what the UI consumes)

Schema version 7 emits one NDJSON object per step (stdout of `acorn demo
--telemetry`), plus one
terminal frame per attempt. Fields the UI relies on:

| field | type | meaning |
|---|---|---|
| `world_step, lifetime_step` | num | distinct time domains: current world/process epoch and checkpoint-persistent agent experience. Both must be safe non-negative integers; the top bar's lifetime label reads only `lifetime_step` |
| `run_id, agent_epoch, origin` | hex str / num / enum | durable run and logical-agent identity plus loader-derived origin. `origin` ∈ {`fresh`, `resumed`, `cleared`}; `resumed` is constructible only after successful checkpoint load |
| `goal, attempt, tier, cycle, goal_count, attempt_cap, step_cap, cycle_cap` | num | authoritative campaign bookkeeping and caps |
| `goal_progress_invalid, goal_progress_cycle, goal_progress_resolved, goal_progress_achieved, goal_progress_attempt` | bool / num / num / num / num | Core process-local ordered outcome accounting for the current curriculum pass. |
| `goal_progress_completed_cycle, goal_progress_completed_achieved, goal_progress_score` | num\|null | Latest fully resolved pass and headline tenths of a percent; absent complete pass uses explicitly partial current evidence. Invalid accounting suppresses the score. |
| `curriculum_names, curriculum_failed_attempts, curriculum_success_steps` | str[] / num[] / (num\|null)[] | One entry per admitted goal, in order: actual names, current-pass failed-attempt counts, and successful attempt step counts. Null success means no success recorded; zero is a valid successful duration. |
| `seed, side, day_length, regrow, food_interval, food_cap, deer_cap` | num | complete world identity/configuration |
| `schema_version, source_sha256, build_sha256, audit_digest, checkpoint_format, timestamp_ms` | num/str | exact protocol/build provenance for raw export |
| `weight_space, learner_count, primitive_count, meta_count, skill_count, demon_count, n_tilings, imprint_units` | num | authoritative agent/learner shapes; `weight_space`, `Acorn.FeatureConstants.defaultTilings` and `imprint_units` are rendered on the `features` node (UX-4) |
| `retire_count, retire_step, retire_unit` | num / num\|null / num\|null | generate-and-test (PAR-4 / PAR-11): lifetime retirements, and the lifetime step and unit of the most recent one, `null` before any. Rendered on the `features` node; `null` is kept as "none yet", never as step 0 or unit 0 |
| `subtask_policy, subtask_unit[3], subtask_bonus[3]` | enum / (num\|null)[] / (float\|null)[] | what each option slot is pursuing (PAR-12). `subtask_policy` ∈ {`learned`, `hand_authored`} decides how a slot may be named (UX-16); `subtask_unit` is the assigned imprint unit or `null` for the neutral fallback and for hand-authored slots; `subtask_bonus` is the attainment bonus `g_k = \|w_0[feat]\|`, zero when neutral or hand-authored. Read-only copies of the `Interest` each skill already holds |
| `history_bins, cycle_bins, exact_cycles, settle_stride, settle_remaining` | num | fixed aggregate shapes and empirical-return settlement contract |
| `x, y, facing` | num | pose (facing 0–3 = N,S,E,W) |
| `energy, wood, stone, food, gold, axe, boat` | num/bool | HUD |
| `control_criterion, reward_rate` | num | criterion 0 discounted / 1 differential and the posterior host reward-rate estimate; backups for this transition use the prior estimate. The selected criterion is displayed; the gain is N/A under discounted control |
| `option_model_durations[3]` | array | predicted primitive duration of a fresh option activation at the observed state under differential control; unused discounted prediction slots carry the ONE sentinel; only unused duration alpha/credit slots are zero |
| `action, reward, done, skill, eps` | num/bool | behavior. `reward` and `eps` are `float\|null`. **`eps` is the primitive controller’s derived rate** (`TemporalControl.primitiveRate`), not a hand-set ϵ and not the meta or skill rates. See §10. |
| `decision_source, explored, action_probabilities[9], meta_probabilities[4], meta_action` | enum/bool/arrays/num | exact selecting layer and exploration branch; declared action/meta policy mass at `f32` resolution (the multiply-high mapper's sub-`f32` bin imbalance is not represented) |
| `option_start, option_end_skill, option_end_duration, option_end_reason, option_elapsed` | num | explicit activation boundaries; 255 denotes no event/selection |
| `a_ctl, a_dem` | float\|null | family means over primitive/Horde weights currently being adapted |
| `alpha_control_all[9], alpha_meta_all[4], alpha_option_all[27], alpha_demon_all[11], alpha_models[9]` | arrays | active step-size mean across all 51 primary learners and nine model telemetry slots (57 stored learners under discounted control, 60 under differential control) |
| `credit_control[9], credit_meta[4], credit_options[27], credit_demons[11], credit_models[9]` | arrays | eligible-feature count across all 51 primary learners and nine model telemetry slots (57 stored learners under discounted control, 60 under differential control) at the same decision |
| `mean_alpha` | float\|null | mean e^β over *all* `N` weights of `learners[0]`. **Emitted but not rendered** — averaged over the ~99.9 % of weights the agent has never touched it barely moves, which is exactly why UX-34 plots the active means instead. Kept in the stream because it is the figure a CSV analysis wants; listed here as *available*, not as *relied on* |
| `demons[11]` | (float\|null)[] | GVF predictions, in demon order |
| `cums[11]` | (float\|null)[] | the cumulant each demon is predicting, this step. **Required on every frame** — the viewer refuses a frame without it rather than reusing the previous occupant of its ring slot |
| `demon_names[11], demon_target_policy[11], demon_gamma[11], demon_horizon[11]` | arrays | self-described GVF semantics and effective horizons |
| `process_started_ms, agreement_started, agreement_stopped` | num / num\|null / bool | Native monotonic process-start marker, actual evaluator start on the lifetime clock, and final censor completion. A checkpoint resume creates new empty agreement accounting. |
| `agreement_version, agreement_scale, agreement_score, agreement_text, agreement_error` | num / num / num\|null / str\|null / num\|null | Versioned exact-accounting projection. Numeric agreement/error use millionths; score text is point-scale. Missing channels or arithmetic failure suppress the aggregate. |
| `agreement_channel_score[11], agreement_channel_text[11], agreement_channel_error[11]` | optional arrays | Per-question higher-better agreement and lower-better normalized RMSE; same scale and exact endpoint text rules as the aggregate. |
| `agreement_count[11], agreement_pending[11], agreement_censored[11], agreement_status[11]` | str / num / str / str arrays | Exact decimal settled/censored counts, current bounded pending occupancy and explicit empty/pending/complete/censored/partially censored/invalid/saturated state. |
| `agreement_horizon[11], agreement_start_first[11], agreement_start_last[11], agreement_settlement_first[11], agreement_settlement_last[11]` | num / optional num arrays | Exact finite settlement horizons and observed settled-population endpoints, without an independence or gap-free-population claim. |
| `agreement_tail[11], agreement_rounding[11]` | optional num arrays | Separate upward-rounded deterministic normalized allowances in millionths; neither a confidence interval nor an outcome-noise estimate. |
| `agreement_history_clock[64], agreement_history_score[64]` | optional num arrays | Bounded native cumulative agreement history at actual lifetime clocks; browser cursor/reconnect cannot add evidence. |

| `action_names[9], meta_names[4], skill_names[3], goal_family_names[4]` | string arrays | the core's stable names for actions, meta actions, option slots and goal families; `skill_names` are slot identifiers whose display follows `subtask_policy` (UX-16) |
| `lifetime_error_sum/count[11], settled_return/error[11]` | arrays | checkpoint-persistent SwiftTD MSE owners and latest settled empirical results |
| `lifetime_reward_*`, `lifetime_error_history_*`, `lifetime_option_*`, `lifetime_goal_*`, `lifetime_cycle_*` | scalars/arrays | exact durable totals plus fixed 64-step-bin and 4×16 cycle-bin histories |
| `control[9], meta[4]` | (float\|null)[] | action values; array lengths are emitted, validated, and linked to the native Lean emitter by the compiled schema contract |
| `option_model_rewards[3], option_model_continuations[3]` | (float\|null)[] | PAR-13 Option Models: expected cumulative host reward r̂(s, o) and continuation value ĉ_v(s, o) per skill |
| `planning_steps, planning_errors[3]` | num / (float\|null)[] | PAR-14 Background Planning: Dyna planning backups since process start / latest restore and per-skill Bellman planning errors |
| `update_us, environment_us, process_uptime_ms, checkpoint_failures, telemetry_refusals, telemetry_drops` | num | core execution latencies, process uptime, and reliability counters (UX-46) |
| `tiles[121], tile_extra[121]` | byte[] | sensor window (kind; food+2·deer) |
| `ev` | byte | events: 1 harvest, 2 ate, 4 crafted, 8 picked food, 16 exhausted, 32 moved. The page reads bits 1–16; **bit 32 (moved) is emitted and not read** — movement is already visible as the pose changing, so a toast or particle for it would be noise |
| `gkind, gitem, gx, gy, gn` | num | goal family and item use the complete `GoalProtocol` vocabulary (including craftable item codes), shared by emission, admission and labels; target and quantity retain safe-integer browser limits |
| `end` | bool | terminal frame of an attempt; carries the verdict in `done` |
| `eos, kind, reason` | bool/str | **not from the core** — the viewer's server synthesises `{"eos":true,"kind":…,"reason":…}` when the child exits **unexpectedly** or fails to start. `kind` is `exit` for the native process-exit notice; start refusals are carried by the authoritative control diagnostic; `reason` is a human sentence. The UI shows `core stopped — <reason>` and raises a toast (UX-18). The reason is mandatory: a core that cannot start at all produces nothing *but* “eos” frames, and without it the page would have no statement anywhere of what went wrong. A stop the operator **asked for** raises no “eos”: the “ctl” frame already says so, and a toast reading "⚠ stopped on request" is the page complaining about something it was told to do |
| `ctl, desired, actual, reason, seed, runId, agentEpoch, transition, transitionReason, failures, clearDisabled, checkpointRefused, terminalWarning` | bool/str/num | **not from the core** — the supervisor's exhaustive Lean state and last typed transition, emitted on every transition (UX-21). `desired` ∈ {`running`, `stopped`}; `actual` ∈ {`starting`, `running`, `stopping`, `clearing`, `stopped`}; the run/agent identity is the attribution authority for replay. **Also sent once, explicitly, to each browser as it connects**, before replay, so a client never reconstructs current identity from buffered frames |
| `cleared, seed` | bool/num | **not from the core** — ordered acknowledgement that makes the page discard the archived world immediately. Identity itself comes from the preceding authoritative “ctl” frame and the following matching core frames |
| `map, runId, side, seed, seen, partial, kinds` | bool/str/num/bool/str | **not from the core** — the run's explored map (UX-44), sent once per connection after the “ctl” frame and before the replay, once the memory holds a frame for the current run; `kinds` is the run-length-encoded, base64'd `side²` tile map, `255` for never sensed; “partial” says observations may be missing, including around stops or viewer restarts |

**`null` means non-finite.** JSON has no form for `NaN` or `±inf`, so every
float field may be `null`, and `null` means exactly "the core computed a value
that is not a finite number". It is never a substitute for a missing reading and
never rounded to `0.0`: a zero step size and a `NaN` step size are opposite
states, and a stream that reports both as `0.0` makes a dead plasticity vector
indistinguishable from a resting one. The viewer keeps such a frame, counts it,
shows `⚠ non-finite` in red where the number would have been, and raises a pill
in the top bar (INV-4).

**Frames are validated on intake.** A frame with a missing field, a
wrong-length array, or a non-numeric scalar is dropped whole and counted under
the reason it was refused for (UX-20).
Absorbing the good half would leave the previous frame's data in the ring slot
and draw it as if it were current.

**`end` frames** exist because the step loop breaks *before* capturing the step
that achieved the goal: without them the stream would never report an outcome
and no observer could tell success from timeout. An `end` frame carries the
verdict, the new pose, and a sensor window that **belongs to that pose** — the
core re-observes before capturing it, so the achievement frame (the one a paused
scrub lands on) is internally consistent and can be painted like any other. Its
world time repeats into the next attempt's first frame, which is why events are
announced once across that boundary.

## 10 · Algorithm claims: pin or out of viewer scope

Every surface that displays an algorithm names the work, the equation, and the
**fetched PDF page** plus a short quote — or it says the quantity is out of
viewer scope. Pure instrument / CI / screenshot gaps carry **no prior-art
claim**.

PDFs opened for these pins: SPS99 http://incompleteideas.net/papers/SPS-aij.pdf
(AIJ 112, 31 pp.); RRS http://incompleteideas.net/papers/RRS-aij.pdf (AIJ 324,
17 pp.); STOMP https://arxiv.org/pdf/2202.03466 (arXiv:2202.03466v4, 34 pp.);
Wan et al. https://arxiv.org/pdf/1904.01191 (arXiv:1904.01191v4, 11 pp.);
Kudashkina et al. https://arxiv.org/pdf/2104.08543 (arXiv:2104.08543v1, 15 pp.);
εz-greedy https://arxiv.org/pdf/2006.01782 (arXiv:2006.01782v1, 20 pp.);
Alberta Plan https://arxiv.org/pdf/2208.11173 (arXiv:2208.11173v3, 14 pp.);
Swift-Sarsa https://arxiv.org/pdf/2507.19539 (arXiv:2507.19539v1, 5 pp.).

| Surface | In viewer | Pin or out of scope |
|---|---|---|
| OaK's five stages and thesis (orientation strip) | UX-4 | **Architecture named, no equation displayed.** The panel says *progression*, not *loop*: the closed loop of Alberta Plan Step 11 (utility feedback over every element) is absent from this build (`docs/design.md`), and the return glyph's hover text says what it marks. The five stages are the FC-STOMP progression of Sutton, *The OaK Architecture: A Vision of SuperIntelligence from Experience*, RLC 2025 keynote — a talk, so no PDF page; verified against the recording published by Amii (`https://www.amii.ca/videos/oak-architecture-rich-sutton-rlc2025`) and the title listed at oaklab.ai — and the STOMP progression of RRS (AIJ 324 (2023) 104001, arXiv:2202.03466v4); the mission sentence *algorithms that allow agents to achieve goals in big worlds* is quoted from oaklab.ai/mission. Each node's figure is a stream field summarised by the panel it points at, whose pins are the rows below and the next row. |
| `features` node (imprint units, retirements) | UX-4 | Mahmood & Sutton, *Representation Search through Generate and Test*, AAAI 2013 workshop, PDF opened (`http://www.incompleteideas.net/papers/MS-AAAIws-2013.pdf`; no running page number on its face), file p. 3 of 6: *“The tester first estimates the utility of each feature. The search method then replaces a small fraction ρ of the features that are least useful with newly generated features.”* — PAR-4 (generate half) / PAR-11 (derived tester). Counts only; no equation displayed. The node's hover text also states D1 (8 fixed tilings over a hand-authored channel layout; only the 512 imprint projections are generated-and-tested) and that the word *imprint* is Javed's — thesis ch. 9, *Feature Generation by Continual Imprinting*, as `docs/prior-art-review.md` PAR-11 records — for a mechanism this bank is not. |
| `subtasks` node and option lines (stopping bonus) | UX-4, ribbon legend, HUD | Sutton, Machado et al., *Reward-Respecting Subtasks for Model-Based Reinforcement Learning*, AIJ 324 (2023) 104001, **PDF p. 4 eq. (4)**: *“let w̄ᵢ denote one of its largest values, called the bonus weight … The quantity (w̄ᵢ − wᵢ)xᵢ(s) is sometimes called the stopping bonus”*. This build derives the bonus weight from the goal-reward GVF's weight on the ranked feature (PAR-12); the page calls the figure `bonus` and the node's caption `stopping bonus`. |
| `options` node (shaping term) | UX-4 | Ng, Harada & Russell, *Policy invariance under reward transformations: Theory and application to reward shaping*, ICML 1999, file p. 4 Theorem 1 eq. (2) `F(s, a, s') = γ Φ(s') − Φ(s)` — the four-part pin in `docs/prior-art-review.md` PAR-6 (no running page numbers on the PDF's face). For learned subtasks, Φ is the selected feature indicator; the attainment bonus multiplies that indicator in the stopping value. Differential research centers task reward by the gain estimate. Interruption compares learned stopping/continuation estimates; SPS99 Theorem 2 assumes exact option values and is not an improvement guarantee for this implementation. |
| `primitive ε` | live HUD | **Rate, primitive layer only.** Dabney, Ostrovski & Barreto, arXiv:2006.01782v1 **PDF p. 5**: *“This exploration algorithm is then described by two parameters, ϵ dictating when/how often to explore, and z dictating the degree of persistence.”* In ranked, primitive, boundary-credit and spatial profiles the scalar is `ν(β)` from this controller’s step sizes (PAR-10); the annealed research profile uses the declared schedule. Why the expert rate was retired: Alberta Plan Step 1, arXiv:2208.11173v3 **PDF p. 6**: *“All of that user expertise should be replaced by a meta-algorithm for setting the step-size parameter…”* Duration *z* remains D3; retirement target Alberta Plan Step 9, **PDF p. 9**: *“Step 9. Planning II: Search control and exploration.”* PAR-10 is this build’s construction, not a published algorithm. Meta/skill rates and *z* are out of viewer scope. |
| Meta / skill exploration rates | **out of viewer scope** | Same two-parameter split; those rates exist (`learned-only-binding.md` D3) and are not in the stream. |
| Duration law *z* | **out of viewer scope** | εz-greedy **PDF p. 5** *z*; D3 residue. Alberta Plan Step 9, **PDF p. 9**: *“Step 9. Planning II: Search control and exploration.”* |
| Primitive / meta action values | behaviour panel | Swift-Sarsa arXiv:2507.19539v1 **PDF p. 2 eq. (4)** `δ'_t = r_t + γ v_{t−1,t}[a_t] − v_{t−2,t−1}[a_{t−1}]`, quoted on the page in Algorithm 1's notation (`δ' = r + γ v[a_t] − v_old`) and said to be; **PDF p. 5 Algorithm 1** `δw^j[i] ← δ' z^j[i] − zδ^j[i] vδ`. Zero bars: that update’s fixed point at `r = 0`. |
| Differential control and gain | big-world card and behaviour sources | Sutton & Barto, *Reinforcement Learning: An Introduction*, 2nd ed., MIT Press (2018), §10.3 pp. 251–252 and Exercise 10.8; verified in PAR-15. Differential target `r − reward-rate + next value`, with the Exercise 10.8 reward-residual gain variant. Discounted control uses no gain; no whole-agent convergence is inferred. |
| Intra-option credit on those bars | labelled in the lede | SPS99 **PDF p. 24 eqs. (20)–(21)** (intra-option Q-learning with `U = (1−β)Q + β max Q`); **PDF p. 25** Theorem 3 and *“Intra-option versions of … Sarsa … should be straightforward, although there has been no experience with them.”* This build is the declared executed-stream Sarsa (PAR-9), not eq. (21). |
| Option end reasons | ribbon + `#p_option` | SPS99 **PDF p. 17**: *“compare the value of continuing with o, which is Q^μ(s_t, o), to the value of interrupting o and selecting a new option according to μ, which is V^μ(s).”* |
| Option model predictions (`r̂`, `ĉ_v`) | behaviour panel | PAR-13 Option Models: Sutton, Precup & Singh, AIJ 112 (1999) §2.3 / §3 p. 190 and STOMP eq. (12) expected cumulative host reward `r̂(s, o)`; Wan, Zaheer, White, White & Sutton, IJCAI 2019 §4 eqs. (1)–(2) / arXiv:1904.01191 (11 pp.) and Kudashkina, Wan, Naik & Sutton, arXiv:2104.08543 (2021, 15 pp.) Theorem 1 with PAR-13 scalar continuation state value `ĉ_v(s, o) = E[γ^K v̂(S_K) | s, o]`. Differential predictions query a fresh activation at age zero, including while an option is running; displayed start duration is not remaining duration. Emitted as `option_model_rewards[3]`, `option_model_durations[3]`, `option_model_continuations[3]`. |
| Background planning (Dyna) | behaviour panel | PAR-14 Background Planning: Dyna planning backups over learned option models into meta-controller `q̂_meta`. Sutton 1990/1991; Sutton, Machado et al., AIJ 324 (2023) 104001, §5 eq. (19) (arXiv:2202.03466v4 PDF p. 16 eq. (19)); Kudashkina, Wan, Naik & Sutton, arXiv:2104.08543 (2021, 15 pp.) Theorem 1 & §3. Emitted as `planning_steps` backups (since process start / latest restore) and `planning_errors[3]` per skill. |
| G31 terminal target `c + z` | **out of viewer scope** | RRS **PDF p. 5 eq. (5)** `δ(c, z, v, v′, β) .= c + β z + γ(1−β) v′ − v`; at `β = 1` this is `c + z − v`. GVF return **PDF p. 3 eq. (2)**. SPS99 **§3, PDF p. 10 / journal p. 190 eqs. (8)–(9)** gives the option Bellman decomposition. Its eq. (14) is an improvement inequality, not the terminal target. |
| Goal achievement | thesis | Assigned goals achieved within admitted attempt/step budgets. Oak Lab mission and Javed/Sutton Big World research motivate outcome-based evaluation; the curriculum fraction is Acorn's operational choice. |
| Predictive agreement | Knowledge | Acorn-defined equal-question finite-return RMSE complement over eleven fixed questions (D5). Oak Lab mission and Horde supply the research context. |
| Step-size curves | plasticity panel | Alberta Plan Step 1 **PDF p. 6** (quote above). The panel plots Acorn’s current step sizes. |
| intra-option-credit / derived-exploration-rate studies | **out of viewer scope** | PAR-9 / PAR-10 identify the mechanisms, pinned above. |
| Rendered inspection and compiler checks | contributor verification | AC-R4 geometries and AC-R6 check results cover presentation and implementation. |
| `FLOAT_FIELDS` ⊆ emit keys | gate, not a surface | `AcornTools.Corpus.Browser` binds conversion keys to `browserSchema`. |

## Appendix A · Constants this document quotes

`AcornTools.Corpus.Browser` compares the numeric rows below against the actual browser
constants or imported native values. Missing, duplicated or mismatched rows fail
admission. Other prose quantities and table completeness remain review obligations.
Durations are milliseconds unless the name denotes another unit.

| constant | value | declared in |
|---|---|---|
| `READ_MS` | 250 | `viewer/static/index.html` |
| `WIN` | 1000 | `viewer/static/index.html` |
| `CAP` | 30000 | `viewer/static/index.html` |
| `RIBBON_SPAN` | 3000 | `viewer/static/index.html` |
| `STALE_MS` | 8000 | `viewer/static/index.html` |
| `Z` | 4 | `viewer/static/index.html` |
| `replayCapacity` | 500 | `Acorn.Host.Viewer.Buffer` |
| `failureLimit` | 3 | `Acorn.Host.Viewer.Retry` |
| `healthyRunMs` | 30000 | `Acorn.Host.Viewer.SupervisedProcess` |
| `mapSideCapacity` | 4096 | `Acorn.Host.Viewer.WorldMemory` |

### Research eligibility and launch selection

The mission panel describes the running mechanisms and cites their sources.
Viewer launch requires `--research-profile ranked` for its
managed command or an explicit `--cmd`; the two are mutually exclusive.
The core CLI also requires a research profile. Existing field windows, lifecycle
controls and timers keep their specified semantics. Source explanations identify
profile-dependent credit instead of claiming every research profile learns
under options. Exact profile/comparison definitions and eligibility decisions
are owned by `docs/prior-art-review.md`.
