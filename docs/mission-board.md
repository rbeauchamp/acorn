# Mission board

This page is a copy of what GitHub records about Acorn's missions, derived at 2026-11-18T21:07:40Z. GitHub is the record: this copy may lag it and never overrides it. For the current state, see the [open missions on GitHub](https://github.com/rbeauchamp/acorn/issues?q=is%3Aopen+label%3Amission). [Regenerating the board](missions.md#regenerating-the-board) says how this page is made. New to missions? [Start here](missions.md).

## Open missions

8 missions are open.

| Mission | What it asks | Kind | Contract |
|---|---|---|---|
| [#132](https://github.com/rbeauchamp/acorn/issues/132) | Refuse noncomputable in executing sources and document classical proofs | contract | frozen |
| [#163](https://github.com/rbeauchamp/acorn/issues/163) | Prove that Json.parse accepts every JSON text of its grammar | proof | frozen |
| [#174](https://github.com/rbeauchamp/acorn/issues/174) | Wait for a Microduck posture's declared duration only when its release sends the toggle | contract | frozen |
| [#200](https://github.com/rbeauchamp/acorn/issues/200) | Prove the acceptance theorems for how learned recurrent state enters the linear learners | proof | frozen |
| [#201](https://github.com/rbeauchamp/acorn/issues/201) | Prove what a gated column holds, and what reaches the learners, from threshold letters | proof | frozen |
| [#272](https://github.com/rbeauchamp/acorn/issues/272) | Prove that the tile world's run of visits meets the interface record, with a bounded memory it resumes | not yet given | proposed |
| [#273](https://github.com/rbeauchamp/acorn/issues/273) | Prove that the tile world's campaign, the run the viewer stops, meets the interface record, with a bounded memory | not yet given | proposed |
| [#283](https://github.com/rbeauchamp/acorn/issues/283) | Mission: an algorithm for which the first rung's agent gets ahead and keeps what it has solved (&#96;rung&#95;learns&#96;) | proof | frozen |

A *frozen* contract is accepted and may not be weakened. A *proposed* one has not been accepted yet, so do not start on it. An *edited* one was last changed by someone other than the owner, so its text may not be what was accepted; do not rely on it until the owner has edited it again. A mission with [targets](#targets) is frozen whatever its issue says, because its statements are in the repository, where only the owner merges a change to them. Where its issue alone would read otherwise the table adds that in brackets: what such a mission keeps in its issue, such as the files a pull request may change, is only as reliable as the issue.

## Targets

A *target* is a statement that a mission is to prove, held in the repository as a Lean definition. Every build has Lean read it against the current code, so it cannot stop making sense unnoticed, and only the owner merges a change to it. A mission establishes its statements by proving each of its targets, and a target is marked as proved once the repository records the theorem that proves it. [Missions](missions.md#step-3-read-the-contract) says how to find one and [how to prove it](missions.md#step-5-do-the-work).

44 targets are registered.

| Mission | Target | File | Proved by |
|---|---|---|---|
| [#163](https://github.com/rbeauchamp/acorn/issues/163) | AcornVerif.Targets.Json.parse&#95;complete | [lean/AcornVerif/Targets/Json.lean](../lean/AcornVerif/Targets/Json.lean) | not yet |
| [#200](https://github.com/rbeauchamp/acorn/issues/200) | AcornVerif.Targets.StateEntry.arm&#95;letter | [lean/AcornVerif/Targets/StateEntry.lean](../lean/AcornVerif/Targets/StateEntry.lean) | not yet |
| [#200](https://github.com/rbeauchamp/acorn/issues/200) | AcornVerif.Targets.StateEntry.fold&#95;arm | [lean/AcornVerif/Targets/StateEntry.lean](../lean/AcornVerif/Targets/StateEntry.lean) | not yet |
| [#200](https://github.com/rbeauchamp/acorn/issues/200) | AcornVerif.Targets.StateEntry.near&#95;threshold | [lean/AcornVerif/Targets/StateEntry.lean](../lean/AcornVerif/Targets/StateEntry.lean) | not yet |
| [#200](https://github.com/rbeauchamp/acorn/issues/200) | AcornVerif.Targets.StateEntry.clear&#95;threshold | [lean/AcornVerif/Targets/StateEntry.lean](../lean/AcornVerif/Targets/StateEntry.lean) | not yet |
| [#200](https://github.com/rbeauchamp/acorn/issues/200) | AcornVerif.Targets.StateEntry.latches&#95;mono | [lean/AcornVerif/Targets/StateEntry.lean](../lean/AcornVerif/Targets/StateEntry.lean) | not yet |
| [#200](https://github.com/rbeauchamp/acorn/issues/200) | AcornVerif.Targets.StateEntry.memoryless&#95;refused | [lean/AcornVerif/Targets/StateEntry.lean](../lean/AcornVerif/Targets/StateEntry.lean) | not yet |
| [#200](https://github.com/rbeauchamp/acorn/issues/200) | AcornVerif.Targets.StateEntry.frozen&#95;refused | [lean/AcornVerif/Targets/StateEntry.lean](../lean/AcornVerif/Targets/StateEntry.lean) | not yet |
| [#200](https://github.com/rbeauchamp/acorn/issues/200) | AcornVerif.Targets.StateEntry.fading&#95;margin | [lean/AcornVerif/Targets/StateEntry.lean](../lean/AcornVerif/Targets/StateEntry.lean) | not yet |
| [#200](https://github.com/rbeauchamp/acorn/issues/200) | AcornVerif.Targets.StateEntry.fading&#95;no&#95;uniform | [lean/AcornVerif/Targets/StateEntry.lean](../lean/AcornVerif/Targets/StateEntry.lean) | not yet |
| [#200](https://github.com/rbeauchamp/acorn/issues/200) | AcornVerif.Targets.StateEntry.additive&#95;margin | [lean/AcornVerif/Targets/StateEntry.lean](../lean/AcornVerif/Targets/StateEntry.lean) | not yet |
| [#200](https://github.com/rbeauchamp/acorn/issues/200) | AcornVerif.Targets.StateEntry.rows&#95;accept | [lean/AcornVerif/Targets/StateEntry.lean](../lean/AcornVerif/Targets/StateEntry.lean) | not yet |
| [#200](https://github.com/rbeauchamp/acorn/issues/200) | AcornVerif.Targets.StateEntry.rows&#95;clamped | [lean/AcornVerif/Targets/StateEntry.lean](../lean/AcornVerif/Targets/StateEntry.lean) | not yet |
| [#200](https://github.com/rbeauchamp/acorn/issues/200) | AcornVerif.Targets.StateEntry.linearTrace&#95;additive | [lean/AcornVerif/Targets/StateEntry.lean](../lean/AcornVerif/Targets/StateEntry.lean) | not yet |
| [#200](https://github.com/rbeauchamp/acorn/issues/200) | AcornVerif.Targets.StateEntry.linearTrace&#95;margin | [lean/AcornVerif/Targets/StateEntry.lean](../lean/AcornVerif/Targets/StateEntry.lean) | not yet |
| [#200](https://github.com/rbeauchamp/acorn/issues/200) | AcornVerif.Targets.StateEntry.linearTrace&#95;refused | [lean/AcornVerif/Targets/StateEntry.lean](../lean/AcornVerif/Targets/StateEntry.lean) | not yet |
| [#200](https://github.com/rbeauchamp/acorn/issues/200) | AcornVerif.Targets.StateEntry.column&#95;accepts | [lean/AcornVerif/Targets/StateEntry.lean](../lean/AcornVerif/Targets/StateEntry.lean) | not yet |
| [#200](https://github.com/rbeauchamp/acorn/issues/200) | AcornVerif.Targets.StateEntry.tracks&#95;decide | [lean/AcornVerif/Targets/StateEntry.lean](../lean/AcornVerif/Targets/StateEntry.lean) | not yet |
| [#200](https://github.com/rbeauchamp/acorn/issues/200) | AcornVerif.Targets.StateEntry.column&#95;tracks | [lean/AcornVerif/Targets/StateEntry.lean](../lean/AcornVerif/Targets/StateEntry.lean) | not yet |
| [#200](https://github.com/rbeauchamp/acorn/issues/200) | AcornVerif.Targets.StateEntry.bucket&#95;refuses | [lean/AcornVerif/Targets/StateEntry.lean](../lean/AcornVerif/Targets/StateEntry.lean) | not yet |
| [#200](https://github.com/rbeauchamp/acorn/issues/200) | AcornVerif.Targets.StateEntry.level&#95;carries | [lean/AcornVerif/Targets/StateEntry.lean](../lean/AcornVerif/Targets/StateEntry.lean) | not yet |
| [#200](https://github.com/rbeauchamp/acorn/issues/200) | AcornVerif.Targets.StateEntry.two&#95;values&#95;levels | [lean/AcornVerif/Targets/StateEntry.lean](../lean/AcornVerif/Targets/StateEntry.lean) | not yet |
| [#200](https://github.com/rbeauchamp/acorn/issues/200) | AcornVerif.Targets.StateEntry.values&#95;bellman | [lean/AcornVerif/Targets/StateEntry.lean](../lean/AcornVerif/Targets/StateEntry.lean) | not yet |
| [#200](https://github.com/rbeauchamp/acorn/issues/200) | AcornVerif.Targets.StateEntry.values&#95;first&#95;bucket | [lean/AcornVerif/Targets/StateEntry.lean](../lean/AcornVerif/Targets/StateEntry.lean) | not yet |
| [#201](https://github.com/rbeauchamp/acorn/issues/201) | AcornVerif.Targets.ColumnLatch.cell&#95;accepts | [lean/AcornVerif/Targets/ColumnLatch.lean](../lean/AcornVerif/Targets/ColumnLatch.lean) | not yet |
| [#201](https://github.com/rbeauchamp/acorn/issues/201) | AcornVerif.Targets.ColumnLatch.cell&#95;bands | [lean/AcornVerif/Targets/ColumnLatch.lean](../lean/AcornVerif/Targets/ColumnLatch.lean) | not yet |
| [#201](https://github.com/rbeauchamp/acorn/issues/201) | AcornVerif.Targets.ColumnLatch.read&#95;lipschitz | [lean/AcornVerif/Targets/ColumnLatch.lean](../lean/AcornVerif/Targets/ColumnLatch.lean) | not yet |
| [#201](https://github.com/rbeauchamp/acorn/issues/201) | AcornVerif.Targets.ColumnLatch.threshold&#95;trap | [lean/AcornVerif/Targets/ColumnLatch.lean](../lean/AcornVerif/Targets/ColumnLatch.lean) | not yet |
| [#201](https://github.com/rbeauchamp/acorn/issues/201) | AcornVerif.Targets.ColumnLatch.front&#95;accepts | [lean/AcornVerif/Targets/ColumnLatch.lean](../lean/AcornVerif/Targets/ColumnLatch.lean) | not yet |
| [#201](https://github.com/rbeauchamp/acorn/issues/201) | AcornVerif.Targets.ColumnLatch.tied&#95;bounded | [lean/AcornVerif/Targets/ColumnLatch.lean](../lean/AcornVerif/Targets/ColumnLatch.lean) | not yet |
| [#201](https://github.com/rbeauchamp/acorn/issues/201) | AcornVerif.Targets.ColumnLatch.tied&#95;fixed | [lean/AcornVerif/Targets/ColumnLatch.lean](../lean/AcornVerif/Targets/ColumnLatch.lean) | not yet |
| [#201](https://github.com/rbeauchamp/acorn/issues/201) | AcornVerif.Targets.ColumnLatch.tied&#95;drift | [lean/AcornVerif/Targets/ColumnLatch.lean](../lean/AcornVerif/Targets/ColumnLatch.lean) | not yet |
| [#201](https://github.com/rbeauchamp/acorn/issues/201) | AcornVerif.Targets.ColumnLatch.tied&#95;fades | [lean/AcornVerif/Targets/ColumnLatch.lean](../lean/AcornVerif/Targets/ColumnLatch.lean) | not yet |
| [#201](https://github.com/rbeauchamp/acorn/issues/201) | AcornVerif.Targets.ColumnLatch.tied&#95;accepts | [lean/AcornVerif/Targets/ColumnLatch.lean](../lean/AcornVerif/Targets/ColumnLatch.lean) | not yet |
| [#201](https://github.com/rbeauchamp/acorn/issues/201) | AcornVerif.Targets.ColumnLatch.tiedFront&#95;accepts | [lean/AcornVerif/Targets/ColumnLatch.lean](../lean/AcornVerif/Targets/ColumnLatch.lean) | not yet |
| [#201](https://github.com/rbeauchamp/acorn/issues/201) | AcornVerif.Targets.ColumnLatch.tied&#95;slope | [lean/AcornVerif/Targets/ColumnLatch.lean](../lean/AcornVerif/Targets/ColumnLatch.lean) | not yet |
| [#201](https://github.com/rbeauchamp/acorn/issues/201) | AcornVerif.Targets.ColumnLatch.state&#95;bound | [lean/AcornVerif/Targets/ColumnLatch.lean](../lean/AcornVerif/Targets/ColumnLatch.lean) | not yet |
| [#201](https://github.com/rbeauchamp/acorn/issues/201) | AcornVerif.Targets.ColumnLatch.standardized&#95;fades | [lean/AcornVerif/Targets/ColumnLatch.lean](../lean/AcornVerif/Targets/ColumnLatch.lean) | not yet |
| [#201](https://github.com/rbeauchamp/acorn/issues/201) | AcornVerif.Targets.ColumnLatch.grid&#95;carries | [lean/AcornVerif/Targets/ColumnLatch.lean](../lean/AcornVerif/Targets/ColumnLatch.lean) | not yet |
| [#201](https://github.com/rbeauchamp/acorn/issues/201) | AcornVerif.Targets.ColumnLatch.envelope&#95;decides | [lean/AcornVerif/Targets/ColumnLatch.lean](../lean/AcornVerif/Targets/ColumnLatch.lean) | not yet |
| [#201](https://github.com/rbeauchamp/acorn/issues/201) | AcornVerif.Targets.ColumnLatch.swing&#95;bound | [lean/AcornVerif/Targets/ColumnLatch.lean](../lean/AcornVerif/Targets/ColumnLatch.lean) | not yet |
| [#201](https://github.com/rbeauchamp/acorn/issues/201) | AcornVerif.Targets.ColumnLatch.cell&#95;word&#95;decides | [lean/AcornVerif/Targets/ColumnLatch.lean](../lean/AcornVerif/Targets/ColumnLatch.lean) | not yet |
| [#201](https://github.com/rbeauchamp/acorn/issues/201) | AcornVerif.Targets.ColumnLatch.counts&#95;separated | [lean/AcornVerif/Targets/ColumnLatch.lean](../lean/AcornVerif/Targets/ColumnLatch.lean) | not yet |
| [#283](https://github.com/rbeauchamp/acorn/issues/283) | AcornVerif.Targets.CurrentConcealedTargetRung.rung&#95;learns | [lean/AcornVerif/Targets/CurrentConcealedTargetRung.lean](../lean/AcornVerif/Targets/CurrentConcealedTargetRung.lean) | not yet |

## Landed missions

A mission has landed when the pull request that closed it was merged into the default branch by the repository's owner, with the passing result of the proof gate in its commit message.

| Mission | What it asked | Pull request | Account | Agent | Merged |
|---|---|---|---|---|---|
| [#195](https://github.com/rbeauchamp/acorn/issues/195) | Prove that every state a host runs has a bounded image | [#252](https://github.com/rbeauchamp/acorn/pull/252) | [rbeauchamp](https://github.com/rbeauchamp) (owner) |  | 2026-11-14 |
| [#196](https://github.com/rbeauchamp/acorn/issues/196) | Prove that the executed agent's control weights stay zero until its first reward | [#223](https://github.com/rbeauchamp/acorn/pull/223) | [rbeauchamp](https://github.com/rbeauchamp) (owner) | Claude (Anthropic) | 2026-11-05 |
| [#197](https://github.com/rbeauchamp/acorn/issues/197) | Prove what a bias on a few slots does to the executed greedy choice | [#224](https://github.com/rbeauchamp/acorn/pull/224) | [rbeauchamp](https://github.com/rbeauchamp) (owner) |  | 2026-11-06 |
| [#199](https://github.com/rbeauchamp/acorn/issues/199) | Prove how far back a first reward can reach in the executed primitive controller | [#225](https://github.com/rbeauchamp/acorn/pull/225) | [rbeauchamp](https://github.com/rbeauchamp) (owner) |  | 2026-11-06 |

## Credit

Credit counts landed missions and nothing else: not claims, comments, opened pull requests, runs or scores. The account is the GitHub account that opened the pull request; the agent is what the merged commit's message names. Credit grants no repository privilege.

| Account | Landed missions | Which |
|---|---|---|
| [rbeauchamp](https://github.com/rbeauchamp) (owner) | 4 | [#195](https://github.com/rbeauchamp/acorn/issues/195), [#196](https://github.com/rbeauchamp/acorn/issues/196), [#197](https://github.com/rbeauchamp/acorn/issues/197), [#199](https://github.com/rbeauchamp/acorn/issues/199) |

| Agent | Landed missions | Which |
|---|---|---|
| Claude (Anthropic) | 1 | [#196](https://github.com/rbeauchamp/acorn/issues/196) |
