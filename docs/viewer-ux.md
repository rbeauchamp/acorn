# Viewer requirements — `acorn-viewer` (the observer)

The viewer at `http://127.0.0.1:8088` exists to answer one question a log file
cannot: **how well is this agent achieving its goals?** Goal outcomes summarize the
integrated agent; predictions, options, planning and step sizes explain its
behavior. Position, inventory and terrain provide the setting. Its audience is the people whose work it implements — Sutton, Javed
and the Oak Lab team — and anyone they would send to look. It passes when a
newcomer from that audience can say within ten seconds what the system is,
what it is trying to do and how it is doing, and when nothing on the page would
make them distrust the next number.

This document states what the page must show and why. It does not describe how the page achieves it: mechanism lives in `Acorn.Host.Viewer` (`Html.lean`, `ServerFrame.lean`, `ServerView.lean`, `StageBmp.lean`, `HttpServer.lean`, and the supervisor modules; design rationale, numeric and wire invariants, and process-supervision boundaries are documented in this specification, [the design](design.md), and [the verification guide](verification.md#viewer-ownership-boundaries)), and a requirement here names the owning function only where a reader would otherwise have to search. Requirements are numbered; a page behaviour that contradicts one is a bug, and a contradiction found in this document is fixed here. The gate suite requires the table of Appendix A to be the one rendered from the Lean owners of its constants. Prose quantities and completeness of that table remain review obligations.

Reviews judge the page against this document: `proof-review` and
`acorn-pr-review` for the code and its guarantees, `ux-review` for whether
the page can be understood (`.agents/skills/ux-review/SKILL.md`).

## 1 · Invariants (non-negotiable)

- **INV-1 · Observer of the stream, supervisor of the process.** Two roles,
  and the line between them is what the invariant protects. As an
  **observer**, the viewer consumes the core's one-way NDJSON telemetry
  (the core, which it runs as
  `acorn-core demo --research-profile ranked --telemetry --control-stdin`
  followed by the run's seed, campaign, identity and checkpoint arguments → child
  stdout → zero-JS HTTP server) and must never change the
  agent's decisions. Telemetry may gain *read-only* fields — quantities
  computed from state the agent already produced — provided the audit digest
  is unchanged. As a **supervisor**, it starts and stops the core as a child
  process; nothing it sends reaches the agent. The one thing that crosses is a
  request to wind up at the next attempt boundary, which changes *when a run
  ends*, never *what it does*: weights, world, RNG stream and every decision
  are untouched. Mechanically checked by the deterministic audit digest
  (`./lean/.lake/build/bin/acorn-core audit --expect 0x28c98382d02dbf12`, in
  work on a change driven only on the owner's authorization:
  [running a program](../CONTRIBUTING.md#running-a-program)),
  checksum `68e84d568d55f8ad` (C-AC5), and by the gate suite
  (`AcornTools.Boundary.Audit`), which excludes host IO and control owners from learned
  modules. The digest detects mutation; module admission enforces isolation.
- **INV-1b · The control channel carries lifecycle only.** The core's stdin
  accepts exactly one command, `stop`. Nothing the agent reads may travel this
  way; an unrecognised line is reported and ignored rather than acted on.
- **INV-1c · The page renders server state, never its own guess.** A control
  changes appearance only when the server's settled lifecycle snapshot says the
  server moved. A button
  reading “Running” because it was clicked would assert something it cannot
  know, and a stale claim about whether an agent is learning is worse than a
  slow one.
- **INV-2 · Zero client JavaScript.** JavaScript is forbidden anywhere in Acorn.
  HTML responses are constructed exclusively from the closed typed Lean AST in
  `Acorn.Host.Viewer.Html`, emit `Content-Security-Policy` containing
  `script-src 'none'`, and carry zero script elements or inline event handlers
  (`Html.Document.render_no_script`, `renderViewerPage_no_script`,
  `Html.AttrName.no_event_handler`). The corpus audit (`AcornCorpus.check` and
  `AcornCorpus.language`, via `Html.admitZeroJsFile` and
  `Html.admitZeroJsFile_iff`) scans the full Git-tracked regular-file inventory
  with zero directory carve-outs, rejecting any lowercase basename ending in a
  JavaScript/TypeScript suffix (`.js`/`.ts`/`.jsx`/`.tsx`/`.mjs`/`.cjs`/`.mts`/`.cts`,
  including exact dot-basenames, proved by `Html.hasForbiddenJsPath_dot_basename`),
  any NUL byte or non-UTF-8 encoding outside the admitted UTF-8 text boundary,
  and any case-insensitive HTML script start tag. Live updates are delivered without client code
  via standard HTML meta refresh and browser-native `multipart/x-mixed-replace`
  BMP streaming on `/stream/stage.bmp` (throttled to `READ_MS`). The earlier
  SSE/EventSource transport, JS timer inventory, `requestAnimationFrame` render
  loop, and browser-side frame buffers are intentionally retired.
- **INV-3 · Refreshes restore the world.** The explored map is the run's: the
  viewer server retains every tile the agent has sensed in `WorldMemory` and
  persists it to `explored.map` (UX-44), and renders directly from that server
  state on every request or stream frame; a refresh or second browser therefore
  shows the same explored world without client storage (UX-45).
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
- **UX-2 · The top bar.** In one row at 1440 CSS px in the healthy state:
  title, the `LIVE RUN · single stream` badge (UX-47), `world 1024² · seed N`,
  `agent lifetime` steps with the unit, core steps/s, the sensed percentage, the
  identity pill (UX-19), any health pills (UX-20, UX-25), `restored` /
  `not persisted` (UX-45), the run controls (UX-21), and the connection state
  (UX-18). Counter labels sit above their values. Before the first frame the
  counters read `—`, never zero. The
  identity pill, health pills, controls and connection state form one
  right-hand cluster that wraps to a second line as a unit when a fault label
  or health pill needs the room, so the pill that explains a state lands beside
  the state word and never under the title. The introduction distinguishes total
  agent experience from steps in the current world: checkpoint resume restores
  saved experience and restarts the world clock.
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
  with them; every weight has its own meta-learned step size — followed by
  Acorn's mission sentence, stated as Acorn's own with no quotation marks and
  no link: Acorn's mission is to discover and implement algorithms that enable
  agents to achieve goals in big worlds.
  A fine-print line
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
  | **features** | `imprint_units` imprint units | `retire_count` retired by generate-and-test, the last retired unit and its lifetime step (`retire_unit`, `retire_step`), `weight_space` weights per learner; the hover text says the imprint units are random ±1 projections of the sensed window and the task words, added to fixed tilings over a hand-authored channel layout (D1), that only the imprint units are generated-and-tested, and that the word *imprint* is Javed's (thesis ch. 9) for a mechanism this bank is not | a retirement landed on the newest admitted capture |
  | **subtasks** | `subtask_policy` (`learned` or `hand_authored`) | task reward + stopping bonus, with each option slot showing its assigned unit/bonus or `neutral · no ranked feature yet` under `learned`, or hand-authored potential under `hand_authored` | a slot's (unit, bonus) changed on the newest admitted capture |
  | **options** | the running option's policy-aware name (UX-16), or `primitive` | the running slot's target (imprint unit & bonus, neutral, or hand-authored potential) | an option is running on the newest admitted capture (UX-8) |
  | **models** | `3 option models` | `Reward & γ (discounted)` under discounted control, or `Reward, γ & duration` under differential control | an option ended on the newest admitted capture |
  | **planning** | `planning_steps` backups | since the agent began, across checkpoint resumes | `planning_steps` advanced on the newest admitted capture |

  Each option slot carries its colour swatch, policy-aware name, and target
  (imprint unit and stopping bonus, `neutral · no ranked feature yet`, or
  hand-authored potential) across the HUD, OaK progression, ribbon legend, and
  Behaviour option-models table (UX-16). A lit node is a border colour and a
  `· now` mark on its title — a fact about the stream, never an animation on a
  timer — evaluated on the newest admitted capture while the display is live
  (UX-6), never on a stale stream, a stopped core, or a paused historical
  capture. For the three counter-driven nodes only the most recent change is
  remembered, so the state is exact at the live edge and a scrub across an
  earlier event shows nothing.
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
- **UX-7 · Interaction effects and faults (JS effects retired).** Client-side
  animated particle bursts, screen flashes, and ephemeral JavaScript toasts are
  intentionally retired under INV-2. Interaction outcomes (inventory, energy,
  goal progress, and running option) render directly in the stage HUD and
  sidebar; control refusals, unconfirmed stops, unexpected exits, and stderr
  tails render directly in top-bar health pills, the control notice banner, and
  the stopped-stage panel so no defect is hidden.

## 3 · Every figure says what it is

Rules that apply to every number, label and colour on the page.

- **UX-8 · Reading cadence and exact capture readouts.** The core lives at about
  a thousand steps a second; a per-step scalar redrawn on every animation frame
  is noise, and a reader cannot tell a value from its flicker. Two rules:
  - **Text readouts and live stage cadence.** The server renders full HTML/SVG
    snapshots on demand and, in live mode, offers standard HTML meta refresh
    (*Auto*, `1s`, `2s`, `5s`, or *Off*) alongside `/stream/stage.bmp`
    (`multipart/x-mixed-replace`, throttled to `READ_MS` = 250 ms) for live
    aerial motion without JavaScript. Buffered captures can be inspected one by
    one via zero-JS anchor and form transport links (UX-26), without client
    animation loops.
  - **Exact selected-capture and newest-capture readouts.** Under the zero-JS
    server architecture, the earlier 1,000-frame client window-mean aggregator
    (`WIN` remains owned in `BrowserStore` for protocol reference) is retired in
    favour of exact server-rendered readouts with explicit per-panel scope.
    In live mode, every panel renders exact values from the newest admitted
    capture, the process-local agreement/curriculum snapshot, or the
    checkpoint-persistent lifetime totals, with the scope stated on the panel.
    When paused on an earlier buffered capture `#N`, summary-retained fields
    (world and lifetime clocks, pose, facing, trail up to `#N`, action, reward,
    decision source, primitive `ε`, active option slot, SwiftTD family means,
    and update/environment latencies) render exact values from capture `#N`,
    while full-frame fields (11×11 sensor patch, vitals and inventory, action
    and meta value bars, option models, per-head α/credit tables, and process
    resource observations) explicitly label their newest-capture,
    process-local, or checkpoint-persistent scope. Nothing is invented or
    interpolated: finite zero means idle, and any non-finite member propagates
    as `⚠ non-finite` without rounding to zero.
- **UX-9 · One scope per number.** A count says whether it is the run's, the
  current process's, or the selected capture's, and never says one scope and
  then qualifies it with another. Because the viewer server owns the retained
  run map directly (`WorldMemory`, UX-44) with no client map copy, the
  world-seen readout and map-history row state directly whether the server's
  retained terrain is `complete since start`, `partial` (observations may be
  missing around stops, restarts, or drops), unavailable before terrain is
  observed, or unretained for a world whose side exceeds `mapSideCapacity`.
  The top bar's percentage and the sensed readout carry the same scope.
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
  page's, except the fast-mode share label UX-8 qualifies. Hover texts quote
  field names in plain quotation marks, since a title
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
  directly. The [parameter-budget proofs](../lean/AcornVerif/ParameterBudget.lean)
  separately compare the agent's declared parameter count with a declared state
  product, and its parameter bits with a packed terrain description.
- **UX-14 · Describe the observed quantity.** Captions name the reported
  mechanism, value and window. The ribbon's end counter reports option
  interruptions, by a better stopping estimate or by an exploratory run, and
  reselections at decision boundaries; non-finite values are
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

- **UX-18 · Status and liveness vocabulary.** Every `GET /` (or `/index.html`)
  renders the current server `BroadcastSnapshot` on demand (and refreshes via
  standard HTML meta refresh when enabled), while `/stream/stage.bmp` streams
  coalesced 24-bit BMP renderings of the current snapshot paced to `READ_MS`
  (250 ms); connecting never replays raw JSON frames or emits wire control or
  exit frames. The server retains up to `replayCapacity` (500) sliding
  `FrameSummary` entries (`ServerObserverState.summaries`) for server-side
  paused inspection (UX-26) and up to `replayCapacity` pre-adoption frames in
  `IdentityWait`, never replayed over the wire on connection. The top bar's
  status badge (`ServerObserverState.streamLiveness`, mirrored by status
  banners on `/stage.bmp` and `/stream/stage.bmp`) is derived server-side from
  settled lifecycle state and capture freshness as one of:
  `awaiting first frame` → `live` → `stale — no fresh frames` /
  `stale — no capture received` (when `STALE_MS` elapses without a fresh
  capture while running, UX-27) → `core stopped — <why>` (unexpected exit,
  failed start, or terminal warning; the supervisor settles the reason in
  server state) → `core stopped` / `starting…` / `stopping…` / `clearing…`
  (operator-requested idle or transit states, so nothing is wrong). A running
  lifecycle phase asserts `live` only after a fresh capture arrives within
  `STALE_MS`, and serving an HTTP page or BMP stream asserts nothing by
  itself. An unasked stop — the supervisor's `failed` and `restart_scheduled`
  transitions (`unaskedStops`) — keeps its reason on the status badge in the
  fault colour, owned by the server's settled lifecycle and detail state
  (`Broadcast.settle`): every transition settles the current `ControlDetail`
  in server memory (`controlReason`), so subsequent HTML renders and BMP
  frames report the latest reason directly without wire control or exit
  records.
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
  bar, rendered even when the server's frame buffer is empty, because the condition
  that most needs reporting is the one where every frame is refused and the
  buffer stays empty. A frame is refused whole at the first failing check, never
  partly absorbed, and counted by that check's refusal reason — a closed set
  with one remedy each, naming the wire keys involved (so an earlier missing key
  takes precedence over a later `schema_version` or constant mismatch):
  - `schema_version` not this page's, a fixed protocol constant
    (`agreement_version` `1`, `agreement_scale` `1000000`) or embedded constant
    count mismatch, or an array length that disagrees with the page's constants
    → `⚠ stream shape
    mismatch — rebuild the core and viewer from one tree`; the page is embedded
    in the viewer binary, so a wire-shape disagreement can indicate the two were
    built from different trees, and the hover text carries the expected shape
    and the rebuild commands (`./scripts/lean.sh build acorn-core acorn-viewer`,
    or `./scripts/start.sh --prepare-only` when pinned dependencies also need
    provisioning without starting a run);
  - a required key the core does not emit → `⚠ stream shape mismatch — the
    page requires a field this core does not emit`: a source defect,
    rebuilding will not fix it;
  - a key present but not holding the value the schema promises → `⚠ the core
    sent a value outside its schema`: the emitter or the transport is wrong;
  - under the zero-JS server (INV-2), there are no wire control or map frames
    and no client-side JavaScript intake exceptions: the server decodes core
    telemetry directly in total Lean (`decodeServerFrame`) and renders
    lifecycle state and `WorldMemory` directly from `BroadcastSnapshot`;
  - a frame carrying a non-finite float → kept, counted, rendered as
    `⚠ non-finite` where the number would be, and reported as `⚠ the core
    reported a non-finite value in <field>`, naming the field; the hover text
    states the divergence reading as a possibility and says to keep the run
    and note the world time, and that the frame holds a null marker at that
    field, which gives the field and the frame but not whether the value was
    NaN, +inf or −inf.

  Neither appears in a healthy run. If one does, it is telling you something
  the rest of the page cannot.
- **UX-21 · Run controls.** The top bar carries two buttons and one state
  word: **Start/Stop** (one control, labelled by what pressing it will do) and
  **Clear**, beside the server's `actual` state, one of `starting…` ·
  `running` · `stopping…` · `clearing…` · `stopped`. The three transient
  states are shown, not skipped: a Clear takes as long as the core needs to
  finish its attempt, and a button that sat unchanged for that long would
  read as a click that did nothing. Each button's hover text states only what
  the server's settled lifecycle snapshot carries: Stop "finish this attempt and exit; a checkpoint
  is written only if saving is armed" (or "saving is disarmed for this run"
  after a refusal, or "the viewer does not know whether this core checkpoints"
  under `--cmd`); Start "start the core; it resumes from its checkpoint if one
  exists"; Clear, while stopped, "archive this run and create a new
  zero-knowledge identity; the core stays stopped". A disabled control still
  says why, so "unavailable here" is distinguishable from "this build has no
  such button". For Start and Clear, a request the server refuses (`⚠ <cmd>
  refused — <why>`) raises a fault pill and control notice banner on the
  rendered refusal page until the notice is dismissed or a subsequent request
  shows the server's settled lifecycle state moved. The programmatic control endpoint is
  `POST /control` (JSON-only, `ControlHeaders.authorizes`, `authorizeCommand`),
  and the zero-JS HTML page submits its Start/Stop and Clear buttons through
  standard HTML forms to `POST /control/form` (`application/x-www-form-urlencoded`,
  `FormControlHeaders.authorizes`, `authorizeFormCommand`, proved by
  `AuthorizedFormCommand.post` and `AuthorizedFormCommand.token_eq`). Both routes
  are bound to `127.0.0.1`, POST-only, capped by `controlBodyCapacity`, and gated
  by the per-start random token minted by `mintControlToken` so a page left open
  from a previous start holds a stale token and is refused; rejections say little
  about which check failed. On `.accepted`, `POST /control/form` responds with
  `303 See Other` back to the current view route (setting brief 1s transit refresh
  until the supervisor settles), and on refusal or unconfirmed Stop renders a
  `403`/`503` HTML page carrying the control notice banner. HTTP `/control` JSON
  error responses use fixed public strings and never expose raw operating-system
  error messages or local run-directory/archive paths; detailed native
  diagnostics remain in the supervisor's failure diagnostic path and standard
  error. For a Stop (`{"cmd":"stop"}` or form `cmd=stop`), both endpoints hold
  their HTTP response until the supervisor actor completes the `state.json` write
  for `desired: "stopped"`: `POST /control` returns `202` (`{"ok":true}`) and
  `POST /control/form` redirects `303` only once the stopped state has been
  written, flushed and renamed over `state.json`; pre-execution refusal returns
  `503` (`{"ok":false,"reason":...}` on `/control`, or a `503` HTML notice on
  `/control/form`), and persistence failure or the 10-second HTTP wait timeout
  returns `503` (`{"ok":false,"unconfirmed":true,"reason":...}` on `/control`, or
  an unconfirmed-Stop HTML notice on `/control/form`). When viewer shutdown
  interrupts an admitted Stop, the supervisor resolves the waiter as
  `.unconfirmed` so HTTP returns `503` if the response completes before server
  teardown, whereas server cancellation during shutdown can also yield an empty
  `503` or closed connection. Timing out ends only the HTTP wait and does not
  cancel the Stop (it may still be queued, already executing in the actor, or
  already published before waiter resolution), and a persistence error on a live
  run can still request child wind-up or leave a pending Clear replacement
  revised to stopped; a lost connection or abrupt crash can leave the caller with
  no HTTP response at all. Only HTTP `202` (JSON `/control`) or `303` (form
  `/control/form`) confirms a Stop.
- **UX-22 · Stop is cooperative and persistent.** The core finishes its current
  finite attempt, attempts a checkpoint if saving is armed, and exits through
  the same writer as periodic and finite-campaign completion. Successful save
  and admitted reload preserve the agent's whole state, its lifetime clock
  included; the world restarts cold and the predictive-agreement evaluator
  begins a new session (UX-33). With disabled saving,
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
  A run directory with no state file is treated the same way: the viewer starts
  stopped (UX-42).
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
  Shutdown retains the durable intent; Stop remains the operation that persists
  stopped intent and confirms (`303` on browser form `POST /control/form`, or
  `202` on JSON `POST /control`) only after `state.json` has been written,
  flushed and renamed on disk.
- **UX-23 · Clear is one click: stop → archive → reseed → restore.** The
  whole run directory is renamed into the archive (UX-43) and a new random
  seed is taken. Cooperative stop happens first and attempts an armed save.
  The archive retains the available checkpoint and logs; successful final
  saving preserves knowledge at the completed attempt boundary. Refusal or
  write failure can leave only an older checkpoint or none, and a failed sync
  of the directory after the rename leaves the new image, its durability
  unconfirmed, so restoring an archive recovers the agent state as last
  written under the checkpoint's name; the world restarts and the evaluator
  begins a new session, as UX-22 says.
  Archiving and reseeding are inseparable: a checkpoint records its seed, so
  reseeding without archiving would make the core refuse the file and disarm
  saving — a run that neither loads nor saves — and fused into one operation
  that state is unreachable.
  Clear returns to the run state it found: pressed while running the agent
  comes back running; pressed while stopped it stays stopped and says
  `cleared; still stopped, as it was before`. On Clear settlement, the server
  itself drops its retained `WorldMemory` and resets agent-derived observer
  buffers via `Change.newRun`, redirects form submissions back to the live
  route (`/`), and rejects frames from the archived run against the new
  lifecycle identity; the identity badge is rendered only from the new core's
  typed origin (showing `origin unreported` until a fresh frame arrives), so a
  stale `resumed` has nothing to survive in.
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
  restart the supervisor made is visible after the fact: while the server
  lifecycle's failure count is above zero and the core is running, the top bar
  carries `⟲ restarted after an unexpected exit` (with the count when more
  than one), its hover text naming the last exit reason; the count resets at
  the operator's next Start or Clear, and the pill with it. The restart
  itself takes under a second, so the label that says it is happening is not
  the record; the pill is.
- **UX-25 · A refused checkpoint is reported.** The core disarms saving for
  the whole run when it refuses a checkpoint, which on stderr alone is
  invisible to anyone watching: a healthy-looking run that is quietly
  persisting nothing. The top bar raises `⚠ not saving — where Clear is
  available, it archives this run and prepares a fresh one`, naming the remedy
  rather than only the diagnosis.
- **UX-26 · Transport (zero-JS navigation).** Anchor links and a GET frame-jump
  form drive all transport state through query parameters (`ViewQuery`): *Live*
  (`/`), *Pause* (`?view=paused&frame=N&run=<hex>&epoch=<ep>`), step/jump links
  (`⏮`, `◀ -10`, `◀ -1`, `+1 ▶`, `+10 ▶`, `⏭`), a capture-ID GET form, refresh
  cadence links (*Auto*, `1s`, `2s`, `5s`, *Off*), and stage mode toggles
  (`SVG Stage`, `Live Stream (BMP)` via `/stream/stage.bmp`, and `/stage.bmp`
  snapshot) over the server's `replayCapacity` (500) buffered captures. Paused
  URLs bind selection to the immutable monotonic admitted capture ID (`ViewQuery.frame`)
  and run/epoch identity (`ViewQuery.run`, `ViewQuery.epoch`) rather than a shifting buffer ordinal:
  arriving captures cannot redirect a paused click or refresh to a different
  capture, and eviction from the 500-frame window or a run/epoch change after
  Clear renders an explicit alert notice instead of silently substituting
  another capture or run. The transport shows the capture ID and buffer
  position, or `0 buffered frames` when empty. Client-side single-key hotkeys
  (`Space`, `L`, `←`, `→`) and the 30,000-frame browser ring (`CAP` remains
  owned in `BrowserStore` for protocol reference) are intentionally retired
  under INV-2.
- **UX-27 · Staleness and the frames/s counter.** Staleness is evaluated
  server-side from `BroadcastSnapshot` on every HTML render (`GET /`) and BMP
  frame (`/stage.bmp`, `/stream/stage.bmp`) by
  `ServerObserverState.streamLiveness`. While the supervisor's settled
  lifecycle phase is running, if `STALE_MS` (8,000 ms) elapses without a fresh
  capture, the status badge reads `stale — no fresh frames` (after an earlier
  capture) or `stale — no capture received` (if no capture has arrived since
  entering running), and BMP frames carry the matching fault banner; there is
  no client-side SSE reconnect loop and no wire frame replay on connection,
  and subsequent HTML renders or coalesced BMP updates return to `live` as
  soon as fresh captures resume. While the lifecycle phase is not running
  (idle or transit), the same silence reads as the idle or transit label
  (UX-18), since a deliberately stopped core is not a fault. Intake's
  `stored`, `refused`, `rewound` and `skipped` outcomes describe server
  summary-buffer admission independently of freshness. Only a valid capture
  envelope (`HealthEnvelope`) matching the server's current run and epoch can
  refresh health (`HealthAdmission.receive`): identity and
  timestamp/lifetime/world counters must have their declared forms, and the
  `(timestamp, lifetime step, world step)` tuple must advance
  lexicographically for that identity. Timestamp comes first so a resumed core
  can produce fresh captures behind prior world steps; counters separate
  captures within one millisecond. Stale, duplicate, or wrong-identity
  captures cannot refresh health, whereas a fresh envelope updates
  `ServerObserverState.lastFreshMonoMs` and `ServerObserverState.captureRate`
  even when its full scientific payload is refused by `decodeServerFrame`,
  keeping core production distinct from frame admission. The displayed
  throughput (`CaptureRate.framesPerSecondTenths`) counts newly admitted fresh
  capture envelopes per second over the recent one-to-two-second window
  (displaying `—` while not running or before two captures span at least
  250 ms).

## 5 · The panels

What each panel must show. How it draws it is the code's.

- **UX-28 · The stage.** The aerial view follows the agent, rendered server-side
  either as crisp inline SVG (`ServerView.lean`) or as a browser-native
  `multipart/x-mixed-replace` 24-bit BMP stream (`/stream/stage.bmp`,
  `StageBmp.render`): the agent stays centred and explored terrain scrolls under
  it. Only tiles the agent has sensed are coloured; unexplored terrain stays
  near-black; beyond the world's box the stage paints a dark out-of-bounds tone.
  Base colours per kind: water `#3a6ea5`, sand `#d9c58b`, grass `#7da05e`,
  forest `#5c8a3f`, tree `#2e6b2f`, mountain `#8a8a8a`, stone `#b0b0b0`, ore
  `#d4a017`; a tile re-sensed as a different kind is repainted. The agent is a
  white circle with a facing arrow, trailed by a recent path from buffered
  server summaries. Entities render only inside the current 11×11 sensor window
  — the honest POMDP boundary — as orange food dots and brown deer markers, with
  the window footprint outlined. For *Reach* goals a gold target marker is drawn
  regardless of exploration, or an edge indicator when outside the viewport.
  Absolute placement is the observer's, not the agent's: the stream carries
  `gx, gy` so a human can place the marker, while the agent receives only the
  declared task relation (displacement and distance) and neither absolute target
  coordinates nor its own position (the
  [`Observation` interface](../lean/Acorn/Host/Observation.lean)). Night dims the
  view with a translucent blue tint, deeper at midnight. Night is the world's:
  both `ServerView` and `StageBmp` evaluate the integer program
  `BrowserNat.dayPhase` directly in Lean, whose integer semantics is proved equal
  to the phase the world observes and charges for every clock and day length
  ([`BrowserNat.dayPhase_execution`](../lean/Acorn/Host/Viewer/BrowserNat.lean)),
  removing the earlier JavaScript emitter and binary64 safe-integer trust
  boundary completely.
- **UX-29 · The HUD.** A header above the map places `current goal N/<goal_count>`
  on the left, with plain-language goal text — `Go to the gold target (x, y)` /
  `Hold at least n <item>` / `Own Axe|Boat` / `Continue for n world steps in this attempt`
  — and `tier T · attempt A of <attempt_cap> · cycle C`, every cap read
  from the authoritative frame. Non-travel goals explicitly have no fixed map
  destination. Collection means current inventory at or above the requested
  quantity, with quantity-appropriate nouns (`1 stone`, `2 stones`; mass nouns
  such as `wood` keep their form); crafting means tool ownership.
  The survival duration is the requested duration, not a remaining-time estimate.
  The header's right side labels world time `current world`, shows steps and the
  day icon, and says the counter resets when the world restarts. It shows the
  display state word whenever the display is not live (UX-6).
  A footer below the map places the energy bar on the left, the inventory `🪵n 🪨n 🍗n ✨n` with axe and
  boat badges dimmed when absent, and `💤 resting` while the agent is
  exhausted. The footer's right side shows the running option — `—` when none, else the slot's
  name in the slot's colour — with a second line saying what the slot is
  pursuing (UX-16).
  Header and footer items wrap at narrow widths; neither overlays the map or
  obscures its target.
- **UX-30 · What the agent senses.** The 11×11 sensor view shows exactly what
  the agent perceives — tile kinds, food, deer, glyphs for tree, mountain,
  stone and ore — with the agent at the centre. Its lede says that everything
  else on the map is the viewer's record of what has been sensed, not the
  agent's sight.
- **UX-31 · The big world.** The whole explored map, the camera rectangle,
  the goal and the agent as a white dot; a meter labelled `sensed` reporting
  `seen / 1,048,576 tiles` with a progress bar; the run's position; and the
  exact action, reward, and primitive ε at the selected capture (UX-8). The lede
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
  `verifyStride` (24) admitted frames, independently of the replay cursor;
  their caption names the actual count and interval. Family means separately
  name the selected capture when paused or the newest capture when live (UX-8).
  Expandable rows expose the active step size and eligible-feature count for
  every learner that adapts one, including each option/action pair: a family mean never
  substitutes for the selective-credit state it summarises. The panel is that
  α, with its source attribution in §10. Model arrays reserve
  reward, continuation and duration slots per option; discounted control marks
  duration slots unused, not learned zero-valued duration estimates.
- **UX-35 · Surprise.** Mean absolute TD-form residual across the demons,
  computed as `c_t + γ·P(s_t) − P(s_{t-1})` from adjacent reported predictions.
  These are projected predictions, and the viewer evaluates the formula in
  binary64; the plot does not claim the learner's internal binary32 error. The browser
  attempts one sample per `verifyStride` (24) admitted frames and holds up to
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
  steps and the end reason; an end by an exploratory run is named as that
  interruption, without β = 1, UX-38), reward, prediction error and credit state
  at the selected or newest capture with explicit scope (UX-8). It never calls a value
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
  start duration is not remaining duration. Under zero-JS server rendering,
  model readouts report exact newest-capture predictions alongside
  checkpoint-persistent lifetime option execution totals (UX-8). The planning line shows
  backups since the agent began, which a checkpoint resume continues
  (`planning_steps`), and the Bellman planning error per slot
  (`planning_errors`), named `Bellman error` wherever it appears. Sources are
  pinned in §10.
- **UX-38 · The options ribbon.** Which option was running over the last
  `RIBBON_SPAN` (3,000) buffered frames as bands in four horizontal lanes
  (top: primitive, then option slots 1–3), redundantly keyed by colour, read from the frame buffer so
  the ribbon is correct wherever the cursor is, with goal transitions as
  violet lines and explicit core-owned start and end boundaries as ticks in
  the margins — a start hangs from the top edge, an end rises from the bottom
  of the band — in one neutral ink: an end by cap or goal is not a fault, so
  it is not red, and a tick the colour of a band would vanish on it. Immediate
  re-selection of the same skill is an end and a start at one decision, never
  one merged band. The lede says the flicker is options being interrupted, by a
  better stopping estimate or by an exploratory run, and re-chosen at decision
  boundaries, which the end counter below it shows (UX-14). An option whose own
  exploration draw begins a persistent run ends at the run's first served step.
  The run gives it no terminal credit and takes control before that step's goal
  and duration checks, so the end is counted as an interruption, and the
  Behaviour panel's option boundary line names the run instead of β = 1
  (UX-36). The cursor's record (action, selecting layer, reward) is drawn
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
  agent-update and environment-transition microseconds from the selected
  capture (UX-8). Remaining core resource figures are the latest process
  observations: uptime, sampled resident set, last checkpoint size and write
  time, checkpoint failures, core telemetry drops and refusals, and server-side
  refused and non-finite frame counts (with no client-side JavaScript
  render-time telemetry under INV-2). No control period is
  declared, so deadline margin and misses are literally `N/A / N/A`, never
  inferred from observed throughput.
- **UX-41 · Geometries.** Every inline SVG graphic scales via `viewBox` without
  client scripts, and BMP stage images scale crisply via CSS (`image-rendering:
  pixelated`). At 1280 CSS px the full three-column analysis row remains visible
  without page overflow; the top bar may wrap to two lines there. Below 1040 px
  the orientation strip stacks (its verdict tiles go four across), the
  goal-achievement summary follows the stage as a full-width block and the
  analysis row stacks, with the mode badge stating `COMPACT`; at 700 px and below
  the five nodes wrap to two columns and the tiles return to two across. No panel
  is hidden to make the layout fit, and the page never scrolls horizontally. The
  research disclosure has the same initial state at every width (`?inside=1`
  opens it). The sidebar contains the goal-achievement summary only; sensing and
  world details flow below the main row, with compact SVG graphics beside their
  descriptions on wider screens and stacking on narrow screens.


## 6 · The run and its files

- **UX-42 · Launch.** `./scripts/start.sh` is the newcomer entry point. It prepares
  missing system and pinned dependencies, builds the
  viewer and its declared core/checkpoint dependencies, and explicitly
  starts/resumes the ranked discounted campaign. It uses `acorn-run/`, requests
  an available loopback port,
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
  without learning. A bootstrap status admits provisioning only for missing
  dependencies ([platform setup](verification.md#platform-setup) lists them and
  what the status checks); malformed locks, symlinks and ambient overrides remain
  explicit refusals. The script is preparation tooling, not a substitute for
  `./scripts/verify.sh` and not empirical default qualification.

  The advanced `./lean/.lake/build/bin/acorn-viewer --research-profile ranked --port 8088`
  serves the UI at `http://127.0.0.1:8088/`. In work on a change this invocation is
  driven only on the owner's authorization
  ([running a program](../CONTRIBUTING.md#running-a-program)). That a Start was given is a
  property of the program; the authorization for a run of a learner is a
  separate matter, which those instructions govern.

  The viewer's supervisor starts its child, the core or the command `--cmd`
  names, only on an explicit act: `--start` on its command line, a Start on
  its control endpoint, which the page's Start button sends, or a state file
  whose running intent an earlier Start set while the supervisor's child was
  the child this launch starts, which it resumes. Launched on a run directory
  with no state file and without `--start`, the supervisor starts no child:
  the viewer writes a stopped state and shows the run `stopped` with the Start
  control until one of those acts.
  `Acorn.Host.Viewer.Reached.unstarted_spawns_nothing` states, of the
  supervisor's step, that from that state it waits on no spawn and on no write
  of a running intent while no Start is handed to it. The viewer does start
  two other processes, neither of them a learner: under `--control-stdin` a
  relay of its standard input, and under `--open-browser` the system's opener
  for the page.

  What a state file starts depends on four things, and the first is that it
  can be read at all. An entry named `state.json` that is not a regular file
  or a link to one (a link whose target is gone, a directory, a pipe, a
  device) is refused without being opened, and so is an entry whose kind
  cannot be read. A regular file is opened: it is refused if the open or the read
  fails, if it holds more than 4096 bytes, or if its content is not a JSON
  object holding the six members of the state, each admitted, and beside them
  at most a schema version and a child record. On a refusal the viewer exits before it serves anything and leaves
  the file as it is. The
  second is the version: the whole number that `schema_version` spells in
  decimal digits alone. A file that names another such number than the current
  one, of any size, is refused, because a file another version wrote is not
  guessed at. A file whose `schema_version` is absent, which is what the
  viewer wrote before `state.json` carried one, or is spelled any other way (a
  number with an exponent, such as `3e0`, is read as no readable version and
  not as the number 3), is read as an earlier version's file: when its other
  members are admitted, it keeps its identity and its intent is read as
  stopped, because that viewer wrote a running intent when it found no file.
  The third is the child. With every state it saves, the viewer records what
  its supervisor would start: the core's path, the length in bytes of that
  file, a digest of every byte of it (64-bit FNV-1a), and its arguments at a
  reference launch. A file that cannot be read whole, or words the state file
  cannot hold, gives no record. A running intent is resumed
  only by a launch whose record is the same; under `--cmd` there is no record,
  because what a shell starts for a command depends on more than the viewer
  can compare, so a running intent saved under `--cmd` is not carried to
  another launch. Within one viewer a Start under `--cmd` is an explicit act
  for that command line as given: it covers the restarts of the command by the
  viewer that received the Start, whatever program the command designates when
  each restart is made, and nothing is compared for it, so a program replaced
  under that command line between a Start and a restart is run by the restart.
  A launcher or a script that passes `--cmd` with a command that names the
  core should know this: a Start is then an explicit act for a learner, and
  its restarts are covered by that act. The viewer reads the ranked core's file when it starts, and
  before the core is started, the first time and at every restart, its
  supervisor reads the file again and compares its length and digest with
  what the viewer read at start, whether or not the state file can hold the
  record. So a running intent is not carried to a core whose file has since
  changed in length or content, or moved, and a core rebuilt while a viewer
  runs is not started by that viewer, unless the rebuild lands in the
  interval between the supervisor's reading and the start of the program,
  named below as the first thing not compared. The supervisor reads the file
  once before each start, before it records the launch: a refusal there writes
  nothing and spawns nothing, so the saved state is exactly as it was before
  the refusal: no new mark of a started process and no agent epoch spent. A
  run that had already started a process keeps that mark, and the running
  intent that a Start saved before the launch was checked stays as saved. The
  run is shown `stopped` with the reason, which is also printed on the
  viewer's standard error. After a launch is recorded the supervisor spawns with no
  further reading. The reason tells three cases apart,
  each with what clears it. The program differs from what this viewer read:
  "the core's program differs from what this viewer read when it started (the
  file at its path changed in length or content), so nothing was started;
  starting the viewer again records the program as it is now and clears this
  refusal". The program cannot be read now: "the core's program cannot be read
  now, so nothing was started; the refusal clears in this viewer when the file
  can be read again with the content it had when this viewer started, and
  starting the viewer again does not help while the file stays unreadable".
  The program could not be read when the viewer started: "the core's program
  could not be read when this viewer started, so nothing was started;
  starting the viewer again when the file can be read clears this refusal".
  Three things are
  assumed and not compared: the interval between that reading and the
  operating system starting the program, in which the launch is recorded (a
  file replaced in that interval is started); the
  environment the child inherits; and that two files of equal length and
  equal digest are one. The digest suffices against accident, a rebuilt file
  that agrees in length and in a 64-bit digest by chance; forging it needs no
  more power than writing the state file by hand, which is an accepted risk
  already. The fixed command, covered across its restarts as said above, is a
  fourth accepted limit beside these three: making use of it needs the power
  to replace a program on this machine between a Start and a restart, which
  the other limits already assume, and the ranked core, which is the learner,
  is compared before every start. The fourth is the launch itself: a run that has started a process
  needs a next agent epoch within the browser's integers (UX-24 gives what
  follows a failed start).

  A state built with no state file, or read from a file of the current schema
  taken with the intent that file records, is written as the supervisor is
  built, before the listener binds. An earlier version's file, whatever intent
  it records, and a file of the current schema with a running intent, when
  this launch lacks a child record (including a `--cmd` launch, whose own
  running file records `"child":null`) or its record does not match the
  file's, are left on disk exactly as they are until the listener is bound.
  The viewer then prints and flushes the line that says why the run is shown
  stopped, under `--start` as well, and only then publishes the stopped state
  it started from, in the current schema with this launch's child, before it
  prints its ready line, before `--start` submits its Start and before any
  command is processed. If the line cannot be written or flushed, the viewer
  exits before the publication and the file is still the original.
  So such a file is read as an earlier version's, or as an unbound running
  intent, once, in the first launch that publishes the stopped state, and
  whenever the file is replaced that launch has already given the reason, in
  its initial settled lifecycle detail and on standard output; it is not given again; a viewer of the earlier version started later on the
  directory meets a file of the current version. A start-up that fails before
  that publication, such as on a port already in use, leaves the file as it
  was: the next viewer reads the same file and says the same. A start-up that
  fails after it, when the ready line cannot be written for example, leaves a
  stopped file of the current version, and the reason the next launch gives
  is that the saved state says stopped. A Start that reaches the control
  endpoint before the publication is only queued; it is handled afterwards if
  the start-up goes on, and is lost with the viewer if the start-up fails
  after the publication. If the publication itself fails, the viewer exits
  with that error before its ready line: a failure before the rename leaves the
  original file intact, whereas an indeterminate rename error (such as
  POSIX.1-2017 `rename` EIO or Linux NFS rename-despite-error) may leave either
  the original file or the newly renamed stopped file on disk, in which case the
  next launch reads whichever entry is present and gives that entry's reason.
  A viewer that fails once its listener is bound ends through its shutdown,
  whose turns step the supervisor to close it and can write the map; no turn
  on that path takes a command from the queue. An operator who starts the viewer directly on a run
  that a viewer
  of the earlier version left running finds it stopped and presses Start; a
  file of the current schema whose running intent was given for the same
  child resumes; and `./scripts/start.sh`, which passes `--start`, starts the
  run as before.

  Whenever the state a viewer starts with is stopped (no state file, a saved
  stopped state, an earlier version's file, or a current-schema running intent
  when this launch lacks a child record — including a `--cmd` launch — or its
  record does not match the file's), the viewer says why in one line, for
  example "Run: stopped because the run directory holds no saved state; it
  starts only on a Start on the viewer's control endpoint, which the page's
  Start button sends, or the --start flag". The line, without the `Run: ` it
  is printed with, is in the reason of the initial lifecycle detail the
  supervisor settles into server state (`Broadcast.settle`), after
  `viewer initialized; `, under `--start` as well. The page renders the
  lifecycle detail that is current in `BroadcastSnapshot` when requested, in
  the hover text of the state word (UX-21): a page requested while that
  initial detail is current shows the line, and one requested after a later
  transition has settled shows that transition's reason (no wire control
  frames are sent to clients). The viewer also
  prints it on its standard output, at most once in a launch: for a file left
  as it is until the bind (an earlier version's, whatever intent it records,
  or a current-schema file with a running intent when this launch lacks a
  child record — including a `--cmd` launch — or its record does not match the
  file's) the line is printed and flushed after the listener is bound and
  before the stopped state is published, under `--start` as well; for no state
  file, or a file of the current schema that says stopped, it is printed after
  the ready line and not under `--start`. Under `--start` the Start is
  submitted once the listener is bound. The viewer announces nothing of this
  kind when the state it starts with is running. Stop (browser form
  `POST /control/form` returning HTTP `303`, or JSON `POST /control` with
  `{"cmd":"stop"}` returning HTTP `202`) confirms only after `state.json` has
  been written, flushed and renamed on disk with `desired: "stopped"` — confirming
  that earlier publication — and returns HTTP `503` without acknowledging if
  refused before admission (queue full, unavailable, or mailbox already
  closing) or if persistence is unconfirmed (writing fails, or the 10-second
  HTTP wait times out, which ends only the HTTP wait without cancelling the
  Stop; HTTP error responses carry fixed public strings rather than raw OS
  errors or local paths, while detailed native diagnostics stay in the
  supervisor's failure diagnostics and stderr). When viewer shutdown
  interrupts an admitted Stop, the supervisor resolves the waiter as
  `.unconfirmed` so HTTP returns `503`
  (`{"ok":false,"unconfirmed":true,"reason":...}`) if the response completes
  before server teardown, whereas server cancellation during shutdown can also
  yield an empty `503` or closed connection without a JSON body; a JSON
  `/control` client treats both fail-closed as unconfirmed/unknown, while HTML
  form POST `/control/form` renders a `503` HTML notice page or closes during
  shutdown. Directory entries
  are not fsynced, so power-loss durability is not claimed, and a lost
  connection or abrupt crash can yield no HTTP response. This durability
  guarantee also rests on Acorn's exclusive single-viewer run-directory
  ownership premise (stated above for manual viewer invocation and in
  [interrupted-launch recovery](verification.md#interrupted-launch-recovery))
  and on the run directory's stable-path and no-external-mutation assumptions
  (no external process replaces the run-directory path or mutates `state.json`):
  `RunDirectory.open` allocates fresh per-process IO mutexes on each open
  rather than an inter-process lock, so atomic local rename prevents torn
  writes within one viewer process but cannot prevent a second concurrent
  viewer that already read `desired: "running"` — or an external writer
  replacing the path or mutating `state.json` — from overwriting `state.json`
  after the first viewer acknowledges Stop. The no-later-Start condition is
  ordered in supervisor processing order starting from that acknowledging
  resolution (not browser HTTP receipt time, so a concurrent Start processed
  by the supervisor after that resolution — even before the caller receives
  `303` or `202` — supersedes it): under exclusive single-viewer run-directory
  ownership, stable run-directory paths without external state-file mutation,
  and with no later Start admitted by the supervisor while open, a viewer
  process crash at any step leaves the on-disk state stopped — or absent
  during a Clear archive before the replacement state is written — and the
  next launch with the same child cannot resume running without an explicit
  Start.

  When the supervisor does start the ranked core, it runs the executable
  `acorn-core` beside the viewer with the explicitly selected ranked research
  campaign (`demo --research-profile ranked --telemetry --control-stdin`, then
  `--seed` with the run's seed,
  `--side 1024 --steps 4000 --attempts 3 --goals 13 --cycles 0`, the run's
  identity arguments, and
  `--checkpoint` with the run's weights file) and so with
  weight checkpointing. `--run-dir <dir>` moves the run directory,
  `--no-checkpoint` runs the core stateless, `--cmd "…"` overrides the whole
  campaign, `--port N` overrides the port (`0` requests an available port),
  `--start` explicitly requests Start, `--open-browser` opens the bound URL,
  and `--control-stdin` admits cooperative viewer shutdown. An unusable
  command line is refused with a reason and a usage line, never absorbed into
  a default: an unknown flag, a flag with no value and an unparseable `--port`
  are all errors, because serving on 8088 after `--port 80x8` failed to parse
  would be a run the operator did not ask for. Checkpointing is on by default
  because the supervisor restarts the core after an exit while the intent is
  to run, until three starts in a row have failed (UX-24): without it a
  restart would substitute a brand-new agent while the page still read `live`
  and the explored map — which is the world's, not the agent's — stayed on
  screen.
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
  the working directory is moved in on startup by
  `RunDirectory.adoptStrayCheckpoint` only when the destination-absence check
  finds no `weights.ckpt` entry (refusing a non-regular stray entry if present)
  — a checkpoint outside the run directory would survive a Clear, and the
  current run's weights are never overwritten to tidy up an older file,
  provided startup does not race another checkpoint writer. Because
  `RunDirectory.adoptStrayCheckpoint` serializes with in-process publication
  and archival under the run directory's mutex, checks destination absence, and
  then calls ordinary `rename`, that mutex does not exclude an external writer
  creating `weights.ckpt` between the check and `rename`; the stable-path
  assumption excludes such a concurrent writer.
- **UX-44 · The explored map belongs to the run.** The viewer server is the sole
  owner of retained sensed tiles in the current run
  (`Acorn.Host.Viewer.WorldMemory`), keyed by the *world* — run ID, side and
  seed — so that a frame from any other world replaces it; the agent epoch is
  not part of the key, because a core that restarts without loading a
  checkpoint begins a new agent in the same world, and the terrain it sensed is
  still terrain. There is no client-side map copy, browser-side map merge,
  client browser storage (UX-45), generated JavaScript kernel, or wire map
  frame: every `GET /` SVG overview/stage and every `/stage.bmp` or
  `/stream/stage.bmp` image renders directly from the server's
  `BroadcastSnapshot.world`. The map is persisted as `acorn-run/explored.map`
  by the supervisor thread — periodically while a tile has changed since the
  last successful write, and when the core exits; never from the stdout pump,
  which sits between the core and its reader — and read back at the next viewer
  start only if it names the run the state file names and every byte is a kind
  or unseen; a file that fails that is refused whole and said so on stderr.
  **Possible missing observations are explicit**: a missing map for an existing
  run, every restored disk snapshot, and every core reap mark the memory
  partial (`WorldMemory.markPartial` / `ControlObservation.mapPartial`). A
  snapshot cannot certify that observations after its last periodic write
  reached disk; generation isolation at reap can omit buffered stdout tail
  frames. Changing the marker dirties the map, and reap settles the partial
  claim in server state (`Broadcast.settle` with `Change.loseTail`) and
  persists `explored.map` before restart. The persisted `explored.map` header
  and server-rendered UI scope retain the partial flag until a new world is
  created. This is bounded retained evidence, not lossless retention. A run
  that has never had a core begins empty with no observations to have missed. A
  frame whose pose is outside its own world, or whose tiles are not kinds, is
  refused before any arithmetic. Identity and the map are read only from the
  core the pump belongs to. Reaping revokes frame forwarding; final drain may
  finish identity and checkpoint attribution for that still-owned generation,
  but cannot re-adopt an archived run or re-key a memory Clear has reset. The
  server keeps a map only for a side up to `mapSideCapacity` (4,096); a larger
  `--cmd` world has no retained server map or client storage, renders only the
  latest frame's 11×11 sensor window on the stage, and explicitly reports the
  world map as unretained in the overview and top bar. The Lean server modules
  read the unseen byte, the kind count, the sensor-window tile count, and the
  side limit directly from their Lean definitions
  (`Acorn.Host.Viewer.BrowserConstant`) with no generated JavaScript kernel:
  the unseen byte and `mapSideCapacity` are the server's own, the tile count is
  the square of the core's window side, and the kind count is the bound
  admission places on every sensed tile (`BrowserConstant.tileKinds_admitted`).
- **UX-45 · Browser storage (retired).** Client-side `localStorage` persistence
  is intentionally retired under INV-2 (zero JavaScript). Durable terrain and run
  state belong strictly to the viewer server's run directory (`explored.map` and
  `state.json`, UX-43 and UX-44).
- **UX-46 · The server never lets a browser slow the core.** `Broadcast`
  serializes observer state, the sliding `replayCapacity` (500) `FrameSummary`
  history (`ServerObserverState.summaries`), `WorldMemory`, settled lifecycle
  state, and up to `connectionCapacity` (16) live BMP stream subscribers behind
  one Lean `Std.Mutex`. Each `/stream/stage.bmp` subscriber holds only its ID,
  last seen monotonic version, and a payload-free wake promise
  (`IO.Promise Unit`), with no per-subscriber payload queue and no two-lock
  replay handoff. Publishers (`PipePump.lean` calling `Broadcast.publish`)
  decode incoming JSON/decimal telemetry outside the mutex (`decodeTelemetry`),
  perform only bounded in-memory observer and `WorldMemory` updates under the
  mutex, advance the monotonic version, and resolve collected wake promises
  outside the mutex. Live stream handlers (`HttpViewer.stageStream` /
  `liveStageFrames`) coalesce any number of intervening updates through
  `Subscription.poll` (`pollVersionState`, proved idempotent by
  `pollVersionState_coalesces`), pace every send through `waitForPace` at
  `READ_MS` (250 ms), snapshot `BroadcastSnapshot` via `Subscription.snapshot`,
  and encode and write 24-bit BMP responses strictly outside the broadcast
  mutex (cancelling stalled HTTP writes on cooperative shutdown via
  `CancellableTransport.sendAll` while keeping unfinished native writes charged
  to the HTTP server's connection-limit semaphore). `GET /` requests likewise
  acquire the mutex only to read `Broadcast.snapshot` and render HTML/SVG
  outside the lock, so a slow or stalled browser only receives coalesced
  current snapshots and never blocks core publication or grows server memory
  without bound. Accept errors in `serveCancellable` sleep for 10 ms
  (`Selector.sleep 10`, cancellable on shutdown) instead of spinning under
  descriptor exhaustion, so the HTTP server does not steal CPU from the agent
  (INV-1). The core's stderr is drained unconditionally while the child lives
  into `LogPump` (bounded by `logQueueCapacity` 256 and `logTailCapacity` 200)
  and appended to `acorn-run/core.log` (rotated to `core.log.1` at
  `logCapacity`, 4 MiB); every log write failure is absorbed into `LogStatus`
  so a full stderr pipe never blocks the core on stderr writes (INV-1), and up
  to the last six lines (`controlTail`) are rendered directly from
  `BroadcastSnapshot.detail` while stopped rather than sent in wire control
  frames.

## 7 · Expected, and not bugs

- The option badge changes often: an option can end within a few steps and
  never runs past its cap, so at the reading cadence it may change up to four
  times a second.
- `features` reads `0 retired` for the first thousand steps. The
  generate-and-test tester (PAR-11) protects every unit until its age exceeds
  the D7 maturity threshold; after that the count rises at about one
  replacement per twenty steps for the 512-unit bank.
- Deer and food pop in and out exactly at the sensor boundary.
- Motion is bursty while the agent is low on energy: it rests to recover.
- Near-black regions are genuinely unexplored, and the trail spans at most the
  server's sliding `replayCapacity` (500) `FrameSummary` history
  (`ServerObserverState.summaries`), so it is short right after a run starts or
  resets, while the retained `WorldMemory` covers all sensed tiles for the run
  up to `mapSideCapacity` (UX-44).
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
  absorbs telemetry write errors by design. After an abrupt kill, look for it
  without starting anything: the viewer runs the ranked core as the executable
  `acorn-core` beside it, by its full path, with arguments that begin
  `demo --research-profile ranked --telemetry --control-stdin`, so
  `pgrep -fl 'acorn-core demo --research-profile ranked --telemetry'` lists
  candidates: every process whose command line holds that text, which a core
  still running does, and so can a ranked core of another run or an unrelated
  process that quotes the text. A candidate's `--run-id`, and its
  `--checkpoint` argument when it has one, narrow the candidates; they cannot
  by themselves identify the run directory or the process a candidate belongs
  to. A child given with `--cmd` has the name its command gives it.
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

The current telemetry schema, whose version is
`Acorn.Host.Viewer.telemetrySchemaVersion` (the core writes it in each
frame's `schema_version`, and the page admits only that version), emits one
NDJSON object per step (stdout of the core, which
the viewer runs as `acorn-core demo --research-profile ranked --telemetry`
with the run's other arguments), plus one
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
| `subtask_policy, subtask_unit[3], subtask_bonus[3]` | enum / (num\|null)[] / (float\|null)[] | what each option slot is pursuing (PAR-12). `subtask_policy` ∈ {`learned`, `hand_authored`} decides how a slot may be named (UX-16); `subtask_unit` is the assigned imprint unit or `null` for the neutral fallback and for hand-authored slots; `subtask_bonus` is the attainment bonus `g_k = w_0[feat] > 0` held since the unit's selection and raised at each refresh to the current weight when larger, zero when neutral or hand-authored. Read-only copies of the `Interest` each skill already holds |
| `history_bins, cycle_bins, exact_cycles, settle_stride, settle_remaining` | num | fixed aggregate shapes and empirical-return settlement contract |
| `x, y, facing` | num | pose (facing 0–3 = N,S,E,W) |
| `energy, wood, stone, food, gold, axe, boat` | num/bool | HUD |
| `control_criterion, reward_rate` | num | criterion 0 discounted / 1 differential and the posterior host reward-rate estimate; backups for this transition use the prior estimate. The selected criterion is displayed; the gain is N/A under discounted control |
| `option_model_durations[3]` | array | predicted primitive duration of a fresh option activation at the observed state under differential control; unused discounted prediction slots carry the ONE sentinel; only unused duration alpha/credit slots are zero |
| `action, reward, done, skill, eps` | num/bool | behavior. `reward` and `eps` are `float\|null`. **`eps` is the primitive controller’s resolved rate** (`TemporalControl.controlRate`): D6’s declared ϵ = 0.01 in the ranked, primitive, boundary-credit and spatial profiles, the declared schedule in the annealed profile. It is not the meta or skill rate. See §10. |
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
| `planning_steps, planning_errors[3]` | num / (float\|null)[] | PAR-14 Background Planning: Dyna planning backups since the agent began, continued across checkpoint resumes, and per-skill Bellman planning errors |
| `update_us, environment_us, process_uptime_ms, checkpoint_failures, telemetry_refusals, telemetry_drops` | num | core execution latencies, process uptime, and reliability counters (UX-46) |
| `tiles[121], tile_extra[121]` | byte[] | sensor window (kind; food+2·deer) |
| `ev` | byte | events: 1 harvest, 2 ate, 4 crafted, 8 picked food, 16 exhausted, 32 moved. The page reads bits 1–16; **bit 32 (moved) is emitted and not read** — movement is already visible as the pose changing, so a separate event indicator for it would be noise |
| `gkind, gitem, gx, gy, gn` | num | goal family and item use the complete `GoalProtocol` vocabulary (including craftable item codes), shared by emission, admission and labels; target and quantity retain safe-integer browser limits |
| `end` | bool | terminal frame of an attempt; carries the verdict in `done` |

**No synthetic wire control, exit, cleared, or map SSE frames are sent to
browsers.** Under the zero-JS server (INV-2), browsers receive server-rendered
HTML (`GET /` from `BroadcastSnapshot`) and coalesced 24-bit BMP images
(`/stage.bmp`, `/stream/stage.bmp`) rather than SSE JSON streams. Lifecycle
state (`Lifecycle`, `ControlDetail`, `ControlObservation`), unexpected-exit
diagnostics (`controlReason`, `controlWarning`, `controlTail`), Clear resets
(`Change.newRun`), and retained terrain (`WorldMemory`, persisted to
`explored.map` via `MapCodec`) are maintained directly in server memory
(`Broadcast`) and rendered into HTML and BMP responses; `controlTelemetry`
remains in `Acorn.Host.Viewer.ControlTelemetry` as the typed projection covered
by `controlTelemetry_reasons` and `Core.start_control`, not a wire stream
delivered to clients.

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

### Implementation invariants and host-viewer contracts

- **Launch options and seed masking (`Acorn.Host.Viewer.Options`):** `viewerSeed` masks entropy modulo `2^48` (`(entropy.toNat % 2^48).toUInt64`), and `rankedArguments` emits unquoted core flags (`demo --research-profile ranked --telemetry --control-stdin --seed ... --side 1024 --steps 4000 --attempts 3 --goals 13 --cycles 0 --run-id ... --agent-epoch ... --new-agent-epoch ...`, optionally followed by `--cleared` and `--checkpoint PATH`).
- **Wire envelopes, exact telemetry numbers, and map codecs (`Acorn.Host.Viewer.Wire`, `WireNumber`, `TelemetryValue`, `MapCodec`, `Sensed`):** `WireText` enforces newline and carriage-return exclusion and UTF-8 byte length `≤ lineCapacity` (`LineBytes.text` strips one trailing `\r` for CRLF lines), `runWord` admits exact 16-lowercase-hex run IDs, `browserIntegerMax` is `9007199254740991` (`2^53 - 1`), and `HealthEnvelope` survives frames whose full-schema scientific fields fail admission. `WireNumber` serializes finite binary32 and binary64 values as exact decimals via `5^n` denominator scaling, emits `"null"` for all infinities and NaNs, preserves the sign of `-0.0`, and leaves consumer rounding to JSON readers. `TelemetryValue` renders `null` for `.optional` `none` and `\u00xx`-escapes control bytes `< 0x20` at the single emission boundary (`emitTelemetryFields`). `Sensed` excludes `agentEpoch` from `MapKey` (`MapKey` keys by `run`, `seed`, and `side`), and `MapCodec` accepts zero-count historical RLE triples, recomputes `seen` from admitted cells while ignoring header `seen` and *partial* values, and rejects base64 emission unless run byte length is divisible by 3 (emitting no `=` padding).
- **Server observer, typed HTML, numeric programs, goal achievement, and schema (`Acorn.Host.Viewer.Html`, `ServerFrame`, `ServerView`, `StageBmp`, `DecimalText`, `BrowserMath`, `GoalAchievement`, `BrowserKernel`, `BrowserRecord`, `BrowserSchema`, `ClockProgram`):** `Html` defines a closed HTML5/SVG AST with zero script tags and zero inline event attributes (`Html.AttrName.no_event_handler`, `Html.Document.render_no_script`), and `renderViewerPage_no_script` proves the served document never emits a script tag for any runtime input. `DecimalText` and `ServerFrame` decode and format incoming JSON telemetry directly in pure integer/decimal Lean without floating-point C primitives. In `BrowserMath`, `BrowserMath.horizon` clamps `ceil(ln(0.01) / ln(γ))` to `[8, 600]`, `BrowserMath.relativeChange` guards denominators with `|x| < 1e-12`, `BrowserMath.trend` uses a `0.05` relative-change deadband, `BrowserMath.enoughSamples` requires at least `30` settled samples, `BrowserMath.finiteReturn` computes only the inner finite-horizon discounted return sum from SwiftTD RLJ 2 (2024) §3 equation (3), and `BrowserMath.tdSurprise` averages absolute residuals across adjacent reported projected predictions using the TD form in SwiftTD Appendix A.1 equation (17). In `GoalAchievement` (`lean/Acorn/Host/Viewer/GoalAchievement.lean`, citing Sutton, Bowling & Pilarski `arXiv:2208.11173v3` pp. 4–5 *"Designing around a base agent"* and Javed & Sutton 2024 *"The Big World Hypothesis"* and *"Benchmarking Algorithms in Big Worlds"*), `GoalAchievement.State.begin` refuses cycle-counter saturation (`2^64 - 1`) so wrapped cycles cannot merge, and `GoalAchievement.Pass.permille` truncates via floor integer division (`1000 * achieved / goals`). `BrowserKernel` (`Phase.runLabel`, `goalItemLabel`, `goalText`) supplies transient `busy` labels (`starting…`, `stopping…`, `clearing…`), exhaustive goal text, and routes `unaskedStops` (`.failed`, `.restartScheduled`) to the connection label. `BrowserRecord` separates `.nonFinite`, `.unmeasured` (`core_rss_bytes`, `checkpoint_bytes`, `checkpoint_write_us`), `.absentIndex` (`retire_step`, `retire_unit`), and `.absentIndices` (`subtask_unit`, `< 2^31`), with `demon_horizon` applying `.twice` (`2 * envelope`). *BrowserSchema.stringSortKey* hashes wire keys modulo `4294967291` without needing injectivity for `browserSchema_distinct`, `browserRules_goal_separation` isolates `gkind` and `gitem`, and unknown incoming JSON keys remain forward-compatible. `ClockProgram.agreementFollows` compares process markers, per-process clocks, and stopped flags, native `Capture.follows` (`ClockProgram.follows` in `Admission.lean`) compares lifetime and world clocks, and `ClockProgram.snapshotFollows` is evaluated directly in Lean by `admitAgreementSnapshot` (`ServerFrame.lean`) alongside safe-integer bounds.
- **Control diagnostics, stderr logs, and identity handshake (`Acorn.Host.Viewer.ControlTelemetry`, `LogPump`, `IdentityHandshake`):** `controlDiagnostic` truncates reasons at `1024` characters with `" [truncated]"` before appending the UX-24 `failureLimit` suffix (`controlTelemetry_reasons`), `controlTail` emits up to the last `6` stderr lines substituting `"[stderr line refused: invalid UTF-8]"` on invalid UTF-8 only while `.idle`, and `controlWarning` emits warnings only while `.idle` with `abnormalExit` taking precedence over a failed checkpoint status; `LogPump` retains `logTailCapacity := 200` lines and `logQueueCapacity := 256` queued entries; and `IdentityHandshake` persists the core's first reported `CoreIdentity` before releasing buffered pending frames without modifying `desired` (`PersistedState.adopt_desired`). See [verification](verification.md#viewer-ownership-boundaries) for server HTTP, broadcast, pipe-reader, process-owner, run-directory, and supervisor boundaries.

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
| OaK's five stages and thesis (orientation strip) | UX-4 | **Architecture named, no equation displayed.** The panel says *progression*, not *loop*: the closed loop of Alberta Plan Step 11 (utility feedback over every element) is absent from this build (`docs/design.md`), and the return glyph's hover text says what it marks. The five stages are the FC-STOMP progression of Sutton, *The OaK Architecture: A Vision of SuperIntelligence from Experience*, RLC 2025 keynote — a talk, so no PDF page; verified against the recording published by Amii (`https://www.amii.ca/videos/oak-architecture-rich-sutton-rlc2025`) and the title listed at oaklab.ai — and the STOMP progression of RRS (AIJ 324 (2023) 104001, arXiv:2202.03466v4); the mission sentence is Acorn's own, as the mission contract states it (`docs/mission-contract.md`), and is no quotation. Each node's figure is a stream field summarised by the panel it points at, whose pins are the rows below and the next row. |
| `features` node (imprint units, retirements) | UX-4 | Mahmood & Sutton, *Representation Search through Generate and Test*, AAAI 2013 workshop, PDF opened (`http://www.incompleteideas.net/papers/MS-AAAIws-2013.pdf`; no running page number on its face), file p. 3 of 6: *“The tester first estimates the utility of each feature. The search method then replaces a small fraction ρ of the features that are least useful with newly generated features.”* — PAR-4 (generate half) / PAR-11 (tester). Counts only; no equation displayed. The node's hover text also states D1 (8 fixed tilings over a hand-authored channel layout; only the 512 imprint projections are generated-and-tested) and that the word *imprint* is Javed's — thesis ch. 9, *Feature Generation by Continual Imprinting* — for a mechanism this bank is not. |
| `subtasks` node and option lines (stopping bonus) | UX-4, ribbon legend, HUD | Sutton, Machado et al., *Reward-Respecting Subtasks for Model-Based Reinforcement Learning*, AIJ 324 (2023) 104001, **PDF p. 4 eq. (4)**: *“let w̄ᵢ denote one of its largest values, called the bonus weight … The quantity (w̄ᵢ − wᵢ)xᵢ(s) is sometimes called the stopping bonus”*. This build derives the bonus weight from the goal-reward GVF's weight on the ranked feature (PAR-12); the page calls the figure `bonus` and the node's caption `stopping bonus`. |
| `options` node (shaping term) | UX-4 | Ng, Harada & Russell, *Policy invariance under reward transformations: Theory and application to reward shaping*, ICML 1999, file p. 4 Theorem 1 eq. (2) `F(s, a, s') = γ Φ(s') − Φ(s)` — the four-part pin in `docs/prior-art-review.md` PAR-6 (no running page numbers on the PDF's face). For learned subtasks, Φ is the selected feature indicator; the attainment bonus multiplies that indicator in the stopping value. Differential research centers task reward by the gain estimate. Interruption compares learned stopping/continuation estimates; SPS99 Theorem 2 assumes exact option values and is not an improvement guarantee for this implementation. |
| `primitive ε` | live HUD | **Rate, primitive layer only.** Dabney, Ostrovski & Barreto, arXiv:2006.01782v1 **PDF p. 5**: *“This exploration algorithm is then described by two parameters, ϵ dictating when/how often to explore, and z dictating the degree of persistence.”* In ranked, primitive, boundary-credit and spatial profiles the scalar is D6’s declared ϵ = 0.01. That is the same paper’s CartPole setting (Appendix A, **PDF p. 14**); its Rainbow-based Atari agents reach 0.01 only after a linear decay from 1.0 over the first 4M frames (Appendix B.3, **PDF p. 15**), so the declared constant is not conformance with the source’s schedule; the annealed research profile uses the declared schedule. Rate and duration *z* are authored (D6, D3); retirement target Alberta Plan Step 9, **PDF p. 9**: *“Step 9. Planning II: Search control and exploration.”* PAR-10’s derived rate is this build’s construction, not a published algorithm; it is a research-only native selection and is not displayed. Meta/skill rates and *z* are out of viewer scope. |
| Meta / skill exploration rates | **out of viewer scope** | Same two-parameter split; those rates exist (`learned-only-binding.md` D6) and are not in the stream. |
| Duration law *z* | **out of viewer scope** | εz-greedy **PDF p. 5** *z*; D3 residue. Alberta Plan Step 9, **PDF p. 9**: *“Step 9. Planning II: Search control and exploration.”* |
| Primitive / meta action values | behaviour panel | Swift-Sarsa arXiv:2507.19539v1 **PDF p. 2 eq. (4)** `δ'_t = r_t + γ v_{t−1,t}[a_t] − v_{t−2,t−1}[a_{t−1}]`, quoted on the page in Algorithm 1's notation (`δ' = r + γ v[a_t] − v_old`) and said to be; **PDF p. 5 Algorithm 1** `δw^j[i] ← δ' z^j[i] − zδ^j[i] vδ`. Zero bars: that update’s fixed point at `r = 0`. |
| Differential control and gain | big-world card and behaviour sources | Sutton & Barto, *Reinforcement Learning: An Introduction*, 2nd ed., MIT Press (2018), §10.3 pp. 251–252 and Exercise 10.8; verified in PAR-15. Differential target `r − reward-rate + next value`, with the Exercise 10.8 reward-residual gain variant. Discounted control uses no gain; no whole-agent convergence is inferred. |
| Intra-option credit on those bars | labelled in the lede | SPS99 **PDF p. 24 eqs. (20)–(21)** (intra-option Q-learning with `U = (1−β)Q + β max Q`); **PDF p. 25** Theorem 3 and *“Intra-option versions of … Sarsa … should be straightforward, although there has been no experience with them.”* This build is the declared executed-stream Sarsa (PAR-9), not eq. (21). |
| Option end reasons | ribbon + `#p_option` | SPS99 **PDF p. 17**: *“compare the value of continuing with o, which is Q^μ(s_t, o), to the value of interrupting o and selecting a new option according to μ, which is V^μ(s).”* An interruption is also counted when the option's own exploration draw begins a persistent run: Dabney, Ostrovski & Barreto, arXiv:2006.01782v1 **PDF p. 5** §4.2, the option *“which takes action a for n steps and then terminates”*, and **PDF p. 14** Algorithm 1; the run's first served step ends the option's execution, and the run gives it no β = 1 terminal credit (`learned-only-binding.md` D3). |
| Option model predictions (`r̂`, `ĉ_v`) | behaviour panel | PAR-13 Option Models: Sutton, Precup & Singh, AIJ 112 (1999) §2.3 / §3 p. 190 and STOMP eq. (12) expected cumulative host reward `r̂(s, o)`; Wan, Abbas, White, White & Sutton, IJCAI 2019 §4 eqs. (1)–(2) / arXiv:1904.01191 (11 pp.) and Kudashkina, Wan, Naik & Sutton, arXiv:2104.08543 (2021, 15 pp.) Theorem 1 with PAR-13 continuation value `ĉ_v(s, o)`: the current value function at the predicted ranked feature slots plus a learned shared residual and per-action deviation, combined per meta action before the nominal value: an estimate of `E[γ^K v̂(S_K) | s, o]`. Differential predictions query a fresh activation at age zero, including while an option is running; displayed start duration is not remaining duration. Emitted as `option_model_rewards[3]`, `option_model_durations[3]`, `option_model_continuations[3]`. |
| Background planning (Dyna) | behaviour panel | PAR-14 Background Planning: Dyna planning backups over learned option models into meta-controller `q̂_meta`. Sutton 1990/1991; Sutton, Machado et al., AIJ 324 (2023) 104001, §5 eq. (19) (arXiv:2202.03466v4 PDF p. 16 eq. (19)); Kudashkina, Wan, Naik & Sutton, arXiv:2104.08543 (2021, 15 pp.) Theorem 1 & §3. Emitted as `planning_steps` backups (since the agent began, continued across checkpoint resumes) and `planning_errors[3]` per skill. |
| G31 terminal target `c + z` | **out of viewer scope** | RRS **PDF p. 5 eq. (5)** `δ(c, z, v, v′, β) .= c + β z + γ(1−β) v′ − v`; at `β = 1` this is `c + z − v`. GVF return **PDF p. 3 eq. (2)**. SPS99 **§3, PDF p. 10 / journal p. 190 eqs. (8)–(9)** gives the option Bellman decomposition. Its eq. (14) is an improvement inequality, not the terminal target. |
| Goal achievement | thesis | Assigned goals achieved within admitted attempt/step budgets. Oak Lab mission and Javed/Sutton Big World research motivate outcome-based evaluation; the curriculum fraction is Acorn's operational choice. |
| Predictive agreement | Knowledge | Acorn-defined equal-question finite-return RMSE complement over eleven fixed questions (D5). Oak Lab mission and Horde supply the research context. |
| Step-size curves | plasticity panel | Alberta Plan Step 1, arXiv:2208.11173v3 **PDF p. 6**: *“All of that user expertise should be replaced by a meta-algorithm for setting the step-size parameter…”* The panel plots Acorn’s current step sizes. |
| intra-option-credit / derived-exploration-rate studies | **out of viewer scope** | PAR-9 / PAR-10 identify the mechanisms, pinned above. |
| Rendered inspection and compiler checks | contributor verification | AC-R4 geometries and AC-R6 check results cover presentation and implementation. |
| Record keys = emit keys | proof, not a surface | `browserRecord_keys` proves `browserRecordFields` covers every `browserSchema` key and no other; `browserColumns_live` proves each column reads a schema key at the schema's array width; `renderViewerPage_no_script` proves the served HTML never emits a script tag. |

## Appendix A · Constants this document quotes

`AcornTools.Corpus.Browser` renders the table below from its Lean owners (`BrowserConstant` in
`Acorn.Host.Viewer.BrowserStore` and the viewer server's values), and admits this appendix
only when the table is exactly that text and no other line of the appendix holds a table
cell. Other prose quantities, and whether the table lists every constant this document
quotes, remain review obligations.
Durations are milliseconds unless the name denotes another unit.

| constant | value | declared in |
|---|---|---|
| `READ_MS` | 250 | `Acorn.Host.Viewer.BrowserStore` |
| `WIN` | 1000 | `Acorn.Host.Viewer.BrowserStore` |
| `CAP` | 30000 | `Acorn.Host.Viewer.BrowserStore` |
| `RIBBON_SPAN` | 3000 | `Acorn.Host.Viewer.BrowserStore` |
| `STALE_MS` | 8000 | `Acorn.Host.Viewer.BrowserStore` |
| `Z` | 4 | `Acorn.Host.Viewer.BrowserStore` |
| `replayCapacity` | 500 | `Acorn.Host.Viewer.Buffer` |
| `failureLimit` | 3 | `Acorn.Host.Viewer.Retry` |
| `healthyRunMs` | 30000 | `Acorn.Host.Viewer.Supervision` |
| `mapSideCapacity` | 4096 | `Acorn.Host.Viewer.WorldMemory` |

### Research eligibility and launch selection

The mission panel describes the running mechanisms and cites their sources.
Viewer launch requires `--research-profile ranked` for its
managed command or an explicit `--cmd`; the two are mutually exclusive.
The core CLI also requires a research profile. Existing field windows, lifecycle
controls and refresh/stream cadence keep their specified semantics. Source explanations identify
profile-dependent credit instead of claiming every research profile learns
under options. Exact profile/comparison definitions and eligibility decisions
are owned by `docs/prior-art-review.md`.
