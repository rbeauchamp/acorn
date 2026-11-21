# Architectural intent and operational lifecycle

This document captures the foundational architectural commitments for scaling Acorn to hundreds or thousands of concurrent contributors and AI-agent swarms while preserving correct-by-construction verification and enabling continuous, fault-tolerant, always-on agent operation.

**Status and authority.** On 2026-11-21, in an exploratory architectural session, the owner of Acorn confirmed four foundational directions: (1) Acorn's architecture must scale cleanly to 100–1,000+ concurrent human and AI-agent contributors without Frankenstein code accumulation or central merge bottlenecks; (2) extensions must follow a standard, formally verified plugin protocol so additions and modifications are correct by construction; (3) the scientific mission contracts ([mission contract](mission-contract.md)) remain strictly separated over static verified releases while a second operational lifecycle regime governs continuous always-on operation, fault tolerance, and verified live state migration; and (4) the operational live-upgrade protocol starts with externally pushed verified releases and is architected from day one for eventual autonomous recursive self-improvement (RSI). The engineering design derived from this intent lives separately in [the architectural foundation](architecture-foundation.md). The plain-word Regime-2 operational lifecycle restatement below was explicitly confirmed by the owner on 2026-11-21 (at commit f93dd24) as the authoritative basis for Phase 3.1 `lean-intent` formalization.

**How to read this document.** Commitments stated here govern what any acceptable architecture and implementation must satisfy; derived engineering mechanisms (such as specific Lake package splits, compiler attributes, or IPC transports) belong in [the architectural foundation](architecture-foundation.md) and may evolve while these commitments hold. A name in inline code refers to an existing Lean declaration or maintained repository path.

## Context and purpose

Acorn's mission is to discover and implement algorithms that enable agents to achieve goals in big worlds ([README](../README.md#purpose-and-worlds)). Reaching that mission draws on two long-horizon strategies that today's single monolithic codebase struggles to support together:

1. **Community agent-swarm scale:** Pointing hundreds or thousands of external human and AI-agent swarms at Acorn's open problems requires modular isolation so breakthroughs compound rather than creating central merge storms, rebuilding the entire verification cone inside a single 360-second deadline, or accreting dead profile flags and ad hoc patches.
2. **Always-on living operation:** Acorn's long-term target is an always-on agent that runs continuously without stopping, pausing, or resetting its learned mind, withstanding component faults and receiving live verified upgrades (and eventually self-proposed verified upgrades) much as fault-tolerant telecommunications systems upgrade in service.

## Foundational commitments

### 1. Swarm-scale modularity without Frankenstein accumulation

Acorn must support 100–1,000+ concurrent human and AI-agent contributors authoring components, proofs, and competing agent architectures against shared contracts without serializing on central registry files, overwhelming one global verification timeout, or accumulating unmaintained code branches inside the released agent.

- **Requires:** Shared world interfaces, mission contracts, and verification harnesses are pinned behind versioned boundaries; candidate contributions build and pass verification in isolation; and the released baseline stays a single coherent agent updated strictly by replacing and removing superseded mechanisms rather than piling on feature flags or compatibility shims.
- **Allows:** Both surgical component upgrades inside a versioned baseline (Track A) and wholly independent `Kernel.Agent` architectures competing against frozen rung contracts (Track B), with winning discoveries consolidated into reusable verified primitives before baseline promotion.
- **Rules out:** Requiring every contributor to edit central hand-maintained lists (`lean/Acorn/Decisions.lean`, `lean/AcornVerif/Landings.lean`, closed global cost enums, or central C-route regex tables), retaining deprecated experimental algorithms behind runtime flags inside the released baseline, or forcing all novel algorithms through one fixed internal OaK slot diagram.

### 2. One standard, formally verified plugin protocol

Every extension or modification to the agent — whether a world adapter, a coarse internal subsystem inside the baseline, a sensor-word state mechanism, a whole competing agent, or a live release transition — must satisfy one machine-checked protocol before it can execute as part of an admitted Acorn system.

- **Requires:** Every stateful component or agent supplies explicit static memory and per-step work bounds (`Costed`), exact checkpoint/wire round-trip serialization (`Format.Exact`), contract-owned learned-state accounting (`KeepsOnly`), declared provenance and `Departure` isolation, and Assume-Guarantee composition contracts checked by Lean's kernel, Regula, boundary audits, and `lean-intent` without unverified runtime hooks or unsafe escapes.
- **Allows:** Static compile-time specialization over opaque module boundaries for high-frequency inner learning loops alongside coarse-grained algebraic plugin boundaries at mathematically genuine system seams.
- **Rules out:** Untyped runtime middleware waterfalls, unverified dynamic plugin loading, candidate-supplied comparators (`declaresNothing` / `nothing_stops`) or self-reported resource bounds replacing machine-checked contracts, or ad hoc extensions bypassing boundary and provenance checks.

### 3. Two-regime separation and always-on operational lifecycle (Regime 2 owner-confirmed 2026-11-21)

Scientific guarantees about continual learning from a single stream of experience remain strictly decoupled from the operational lifecycle that keeps a deployed agent running indefinitely across live upgrades and faults.

- **Regime 1 (Scientific Mission Contract — [mission contract](mission-contract.md)):** Every mission theorem and continual-learning invariant (`Kernel.World`, `Kernel.Agent`, Contracts 1–4, `OneStream`, `Mission`) quantifies strictly over a **single immutable verified release** with zero external memory writes, zero mid-stream upgrades, zero self-resets, and strict temporal uniformity. To support lifelong operation across upgrades, Regime 1 strengthens plasticity so invariants and relearning guarantees hold from every reachable valid state rather than only from cold initialization.
- **Regime 2 (Operational Lifecycle and Live-Upgrade Contract — owner-confirmed 2026-11-21):**
  1. *Fault isolation and uninterrupted stream continuity:* The world stream, real-time deadline reflex (`Pace.outcome`), and process supervision stay outside the replaceable agent worker in an isolated minimal supervisor fault domain; worker crashes, out-of-memory faults, or deadline misses never terminate the world loop or silently halt the organism.
  2. *Quiescent-boundary cutover:* Live transitions from an active verified release to a successor verified release occur strictly at quiescent step boundaries (such as `Stage.ready`) after offline verification and shadow warm-up, with zero normal-execution overhead and zero duplicated, dropped, or half-learned percepts.
  3. *Graded anti-reset state migration:* Every live upgrade carries a verified state-migration morphism with bounded migration work and memory, invariant preservation from every valid prior state, world-agnostic zero-injection guarantees, and an explicit knowledge-preservation grade: Grade 1 (exact stream bisimulation), Grade 2 (exact bit-for-bit preservation of every surviving contract-declared learned parameter family plus neutral entry for any newly added parameters, prohibiting staircase wipes and pretrained-weight smuggling), or Grade 3 (representation/paradigm shifts explicitly authorized as an epoch transition).
  4. *Canary probation and automatic rollback:* Every cutover retains a verified rollback path and last-known-good state across a bounded probation window under a finite upgrade budget; any fault or violation rolls back atomically instead of halting.
  5. *Compositional Bridge Theorem and uncontaminated science:* Because every admitted live transition preserves reachable invariants into a successor verified under Regime 1, an unbounded lifetime of verified upgrades preserves safety and continual-learning invariants inductively, while empirical scientific claims strictly separate static Regime-1 runs from runs containing live upgrades.
- **Requires:** Any system claiming always-on live upgrade support implements external supervisor fault isolation, quiescent verified migration, anti-reset grading, and canary rollback, and never attributes mid-stream upgrade interventions to single-stream autonomous learning.
- **Allows:** Fast sub-cycle direct state migration when untouched learned slices pass unchanged and off-real-time pre-copy catch-up over executed `(percept, action)` transitions (or world-declared safe-hold windows) for large schema transitions.
- **Rules out:** Silently dropping prior schema generations at cold start (`previous_generation_unloaded`), halting permanently on upgrade crash loops, mutating live shared-memory closures mid-step without invariant/anti-reset proofs, or sneaking phase splits or experience replay through migration functions.

### 4. Author-agnostic upgrade boundary prepared for RSI

Both externally pushed verified releases (Phase 3) and future autonomous recursive self-improvement proposals generated by the agent itself (Phase 4) must traverse the exact same immutable outer trust and verification boundary.

- **Requires:** The contract kernel, reward/world stream, verification checker (Lean kernel, Regula, `lean-intent`, boundary/frame audits), process supervisor, finite upgrade budget, rollback fallback, and unconditional external stop/corrigibility controls stay strictly outside the agent's writable domain; upgrades pass object-level deductive verification over frozen state snapshots plus separate non-monotonic empirical canary gating before promotion.
- **Allows:** An isolated offline suggester (whether human/community swarms today or an internal RSI component later) to propose and prove replacements for the entire `Kernel.Agent`, its internal wiring/plugin decomposition, its state migrator, and its own offline search heuristics.
- **Rules out:** Allowing any running agent or RSI module to modify reward channels, world interfaces, mission specifications, the proof verifier, or its own upgrade/corrigibility guardrails, or treating probabilistic self-improvement forecasts as deductive proof.

## Boundary between owner intent and derived design

- **Owned by the owner:** The four foundational commitments above, any changes to [the mission contract](mission-contract.md) or the owner-confirmed Regime-2 operational lifecycle contract, admission of new `Departure` entries, Grade-3 knowledge-loss epoch transitions, and Epochal Baseline promotions.
- **Delegated engineering design (decided on the owner's behalf, documented in [the architectural foundation](architecture-foundation.md)):** Specific Lake package decompositions (`acorn-contracts-exec`, `acorn-contracts-verif`, `acorn-worlds`, `acorn-primitives`, `acorn-baseline`), internal coarse seam boundaries, compiler attribute recipes, triage funnel stages, and build/cache mechanics — all subject to the commitments above and revisable by the owner.

Open: Empirical smoke verification of Lean v4.35.0 module-system replay under Regula v0.13.0 (Phase 0.1) and Phase 3.1 formalization of the owner-confirmed Commitment 3 Regime-2 contract in `lean-intent` with blind cross-model formalization comparison.

Sources: Owner direction and session confirmations of 2026-11-21 (100–1,000+ swarm modularity, uniform verified plugin protocol, two-regime separation 2a, external live upgrades advancing to RSI 1c, foundation-first prioritization with surgical pause, public-safe hygiene, and explicit confirmation of Commitment 3's Regime-2 operational lifecycle restatement on 2026-11-21); [the mission contract](mission-contract.md); [the learned-state frame](learned-state-frame.md); [the roadmap](roadmap.md).
