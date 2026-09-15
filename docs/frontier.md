# Research frontier and limitations

These are the main open questions in Acorn. The repository supplies executable
mechanisms and proofs of specific properties, but does not establish that their
combination learns effectively. No empirical performance result accompanies
this source release.

Start with [the learning loop](design.md#the-learning-loop) for terminology.
The F labels identify research questions, D labels identify authored departures,
and PAR labels identify mechanism contracts.

## F1 · Option-model quality

**Do the learned models predict useful consequences of executing an option?**

Scalar targets and bounded state do not establish accurate models under changing
policies and representations. Shared units, target alignment and age semantics
must be preserved in any extension.

*Refutation attempt.* Challenge whether the executed target denotes the claimed
quantity; then assess a prospective, isolated quality/benefit comparison.

## F2 · Planning benefit

**Do model-based updates improve decisions enough to justify their cost?**

Bounded model backups do not establish improved decisions. Model error and
planning cost require explicit tradeoffs and a coherent comparison boundary.

*Refutation attempt.* Check target/backup compatibility before attributing a
measured effect to planning.

## F3 · Representation and retirement

**Can the agent replace features safely, autonomously and usefully?**

Conditional safe retirement does not establish autonomous reachability or useful
turnover. Only imprint features are retired; input channels and tile features
remain authored. General learned agent state is absent.

*Refutation attempt.* Trace every admission/write boundary and characterize
reachability analytically before measuring turnover.

## F4 · Continuing control and exploration

**Which control and exploration mechanisms help over a continuing stream?**

Differential control is selectable with `--criterion average-reward` but is
not approved for default use. Exploration duration remains authored
([D3](learned-only-binding.md#d3--exploration-duration--step-9)). General GVFs,
the complete OaK feedback loop and learned prediction questions are not supplied
by this implementation.

*Refutation attempt.* Check units, gain/return identities, support and composition
hypotheses; state unresolved benefit without inferring it from local correctness.

See [design](design.md), [departures](learned-only-binding.md) and
[admission/promotion](prior-art-review.md). Proposals should first identify the
claim and its strongest available mathematical argument. Empirical work needs
the scoped protocol described in [Contributing](../CONTRIBUTING.md#scientific-evidence).

## Research status and limitations

No configuration is recommended as a qualified default, and no whole-agent
convergence or useful-learning guarantee is made. Explicitly choosing a profile
allows research execution; it is not an endorsement of its effectiveness.
The differential integration's status is **demoted**: it remains ineligible for
default use. Discounted control also lacks default qualification. A source
release does not reverse these decisions or establish an empirical benefit.

| Property | Executed/checked boundary | Remaining limit |
|---|---|---|
| State legality | Indexed value domains and checked construction/restoration | Hypotheses and machine domains belong to each theorem. |
| Learned-only separation | Declared provenance plus source/compiled quarantine | A declaration does not prove its scientific truth. |
| Persistence | Admitted format, dimensions, criterion and identity; refusing writes on invalid restore | No complete host-state resume or unconditional filesystem atomicity. |
| Viewer | One-way telemetry and lifecycle-only stop | Loopback research use; not a hardened hosted service. |
| Resources | Source/IR-linked structural contracts and bounded stored updates | No platform-independent physical latency or lifetime-memory theorem. |
| Learning quality | Explicit research selection and promotion rules | No qualified default; benefit requires prospective evidence. |
| C-AC5 | Derived arm `829aef890c81afaf`, checksum `b1a076b6ac5884f0`; annealed arm `d41d9d77b74b9858`, checksum `4b15707c76a9191a`; differential arm `bb1d5b590fad9933`, checksum `47a82981b9a9ee2d` | These retained pairs detect mutation and do not certify correctness or efficacy. |

See [verification](verification.md), [performance priorities](performance-engineering.md) and
[prior-art admission/promotion](prior-art-review.md). Signatures establish source
identity under the key's trust assumptions, not scientific validity.
