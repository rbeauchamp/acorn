/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

/-!
# The work of an executed computation

A definition whose work Acorn bounds returns a `Costed` value: its result together with the
work of computing it. The work is a type former and a proof about a cost model, which the
compiler erases, so a definition that returns `Costed α` compiles to the code of its result
alone, and reading `val` compiles to nothing (a trust assumption, below). The definition that
runs is the definition whose work the bounds count, and a definition with the plain result type
is the `val` of its costed definition.

**Sites.** A *site* (`Site`) is a kind of constant stretch of executed code, and its docstring names
the operations its charge marks. The intended reading of what a charge counts is its *segment*,
defined here once. No checked statement contains this reading:

- the *trace* is the word operations the compiled code runs during one call of a bounded part, as
  one flat sequence. The bounded parts are the first part, from the step's entry until
  `Agent.choose` returns, including the `Chosen` record built after selection's last charge, and the
  second part, from the entry of `Chosen.learn` until it returns. The world receives the action
  after the second part under `learn-then-act`, and between the two parts under `plan-after-act` and
  `act-then-learn`. For the bound of a costed definition the trace is the word operations of one
  call of that definition, from its entry to its return. An operation inside a callee is itself an
  operation of the trace, at its own position;
- the *charge points* are an `op` at the value it charges, a `charge` before the computation it
  wraps, a loop's visits at fixed points of each pass, whether a loop combinator, a scan or a charge
  of its row's work or control charges them (each element's visit before that element's step,
  which is its callback in a pass that runs one, and the pass's end visit after its last element),
  `prepend`'s read at the vector it builds, after the operations that build that vector and before
  the pass over the vector it puts the element before, and a costed recursion's charges where the
  recursion makes them;
- each operation belongs to the segment of the first charge point at or after it, and the operations
  after the trace's last charge point belong to that last one, so the segments partition the trace.

The segment of an operation is decided by its position alone, so a site's segment can include
operations its docstring does not name, and a site's named operations can lie in another charge's
segment: after the site's own point, or before a charge stacked ahead of it. Under this reading a
cost model `words` in word operations gives each site the largest number of word operations of a
segment at a charge point of that site, so `κ site` must cover the largest segment of that site.
`SiteBounds words κ` (`AcornVerif.Resource.Twin.SiteBounds`) states only `words site ≤ κ site` for
every site, a relation between two cost models, and a bound in word operations bounds the
accounting charged at `words` under it; it is not a bound of executed work. That `words` counts the
segments of the executed code, so that such a bound bounds the executed work, is a correspondence a
later increment of requirement R8 (rbeauchamp/acorn#90) owes. A `visit` segment of the SwiftTD loops
(`learnFirstLoopGoCosted`, `learnSecondLoopGoCosted`, `planWeightsGoCosted`) can include the work of
a whole element and, in the first loop, a prune, and the first visits of the second and planning
loops can include operations their opens name, so `κ visit` must cover the largest visit segment.

Every segment of the first part, and every segment of each costed definition's own call read over
that call's trace, is bounded by a constant of the code in the operations counted. The copy of an
array into a larger buffer when a push outgrows its capacity, whose length depends on the state, is,
like allocation, outside the count (**What is not counted**). Every loop of these whose trip count
depends on the configuration or the state runs in a loop combinator or a costed recursion, which has
a charge point on each iteration, so no segment contains one. A costed recursion charges each level
before its recursive call, and charges again on the return where the level works after the call
returns, so neither its descent nor its return falls in one segment. A library loop whose recursion
has a depth that depends on the configuration or the state and works on the return counts that
return as a pass of its row (`Library.fillVacant`). The cost discipline below requires this of
costed definitions; of the twins it is a property of their charge placement, checked by reading,
which the one-time compiled-call inventory of one build did not compare. The loops left inside a
segment have trip counts bounded by constants of the code: the three options and their slots, the
four meta actions, the 32 samples of a projection, including the return of their sum's recursion
(`Library.sum`, one pass), the at most 15 doublings of the ranked width's search
(`rankExponentFrom`) and the at most 33 steps of `Portable.pow`. A cost model (`Costs`) assigns each
site a cost, and every work bound holds for every cost model. No theorem derives the cost of a site
in word operations; the scalar operations that the native resource audit bounds are the operations
with an extracted cost.

The second part runs stretches outside the costed definitions. In the second part's trace the
operations of those stretches belong to the segment of the next costed charge point, or of the
part's last one, so the second part's segments are not yet bounded by constants of the code and its
bound is an open obligation of R8. `DemonRecords.observe` is one such stretch: a loop over the
channels of the demons' lifetime records, whose trip count depends on the configuration, with no
charge point. That is why the claim above that every segment is bounded by a constant of the code
is limited to the first part and to each costed definition's own call.

**Counting.** `op site value` is a stretch at the site's cost, `charge` puts a stretch before a
computation, and `bind` sequences two computations and adds their work; `Pure` and `Bind` are the
only instances, so `do` blocks sequence costed computations and nothing maps an uncosted callback.
Each loop combinator has as its value the library loop applied to its callbacks' values, and as its
work each callback's work once and the control of its row of the table (`Library`,
`Library.control`): each of the row's passes, a `visit` for each element and one for the pass's end.
A loop's bound is therefore `Library.work`: its trip count times a bound of one callback, and its
row's control. Every function a combinator takes is costed: the steps of `foldl` and `foldlArray`,
the operations of `map`, `mapVector`, `mapFinIdx`, `ofFn`, `filterMap` and `flatMap`, the tests of
`findIdx?` and `filter`, the continuation of `bind` and the arms of `ite` and `dite`; `flatMap` also
charges the elements of each result to its row `flatMapResult`. `attach` pairs a computation's
result with its equation, for a proof that names the result, and its work is that computation's
work. A *scan* (`toList`, `arrayToList`, `drop`, `finRange`, `length`, `range`, `zipIdx`, `append`,
`prepend`, `reverse`, `sum`, `mem`, `vectorEq`) is a library loop that takes no function: its value
is the library function of the collection it names, and its work is the control of its row over the
elements it visits, the whole collection or, for `drop`, the elements it drops, for `append`, its
first list and, for `prepend`, the vector it puts the element before; `sum` charges each visit the
addition of its term (`sumTerm`) and `mem` and `vectorEq` one comparison (`compare`) as well, and
`prepend` charges the read of its element into a new vector (`read`) once. A recursion of Acorn's
own is a costed recursion whose every recursive call is under a charge and whose end is charged a
visit.

**Bounds.** `x.Within κ bound` states that under the cost model `κ` the work of `x` is at most
`bound`. Every `Costed` value is built here, and its work is one number under each cost model
(`single`), so a bound is never vacuous (`within_iff`).

**What is trusted.** That the counted work covers each operation of the compiled code rests on the
cost discipline of the costed definitions: the learner's (`NumericState.linearPredictionCosted`,
`predictCosted`, `clearTransientCosted`, `releaseEligibleCosted`, `learnFirstLoopGoCosted`,
`learnFirstLoopCosted`, `learnSecondLoopGoCosted`, `learnSecondLoopCosted`, `stepCosted`,
`beginTrajectoryCosted`, `terminalStepCosted`, `planWeightsGoCosted`, `planStepCosted`,
`retireIndexCosted` and `normalizedStepSizeSumCosted` and `SwiftTd.Entry.applyCosted` in
`Acorn.SwiftTd`, `TransientState.zeroCosted` in `Acorn.State`, and the ordered sums
`Binary32.sumFromCosted` and `sumMapCosted` in `Acorn.Arithmetic`), a learner record's entry,
retirement and credit (`Managed.applyCosted` and `Managed.retireCosted` in `Acorn.FeatureConsumers`,
`Managed.creditCosted` in `Acorn.Sarsa`), the controllers' predictions, clear, release, snapshot and
derived rate (`Controller.predictAllCosted`, `clearCosted` and `releaseCosted` in `Acorn.Sarsa`,
`Controller.snapshotCosted` and `exploreRateCosted` in `Acorn.Policy`), the controllers' updates and
their helper (`Controller.creditStepCosted`, `valuesStepCosted`, `stopStepCosted` and
`terminalCosted` in `Acorn.Sarsa`, `Controller.retireCosted` and the helper `detachedUpdateCosted`
in `Acorn.FeatureConsumers`, `Controller.planCosted` in `Acorn.Planning`,
`Controller.policyStepCosted` in `Acorn.Policy`, `Controller.persistentStepCosted` in
`Acorn.Exploration`, `Controller.startStepCosted`, `stepCosted`, `smdpStepCosted` and
`closeStepCosted` in `Acorn.Sarsa`, and `Controller.backupStepCosted`, `backupErrorCosted` and
`PolicySnapshot.massCosted` in `Acorn.Policy`), the frozen policy's (`PolicySnapshot.bestCosted`,
`candidatesCosted`, `reservoirCosted`, `greedyCosted`, `probabilitiesCosted`, `drawCosted`,
`expectedCosted` and `consistentCosted` in `Acorn.Policy`), its exploration's
(`PolicySnapshot.drawPersistentCosted` and `servedProbabilitiesCosted` in `Acorn.Exploration`) and
the encoding of a frame's (`projectionValueCosted`, `Bank.activationsCosted`, `tiledFeaturesCosted`,
`imprintFeaturesCosted`, `rawEncodeWithCosted`, `UniqueBuilder.emptyCosted`,
`UniqueBuilder.finishCosted`, `uniqueCosted` and `encodeWithCosted` in `Acorn.Features`,
`EncodingFrame.computeCosted` in `Acorn.FeatureHistory`, `PredictionCache.wordsCosted` and
`FeatureRuntime.encodeCurrentCosted` in `Acorn.FeatureReferences`, `feedbackWordsCosted` in
`Acorn.Handcrafted.Signals`, `Agent.wordsCosted` and `Agent.frameCosted` in
`Acorn.Handcrafted.Agent`) and the option models' input, ranked features and prediction
(`insertCosted` in `Acorn.Features`, `modelInputCosted` in `Acorn.FeatureModelInput`,
`RankedFeatures.activeCosted`, `inputCosted`, `indicatorCosted` and `occupiedCosted` in
`Acorn.RankedFeatures`, `comparisonValueCosted` in `Acorn.Options`,
`ValueFunction.rankedValuesCosted`, `Transition.expectedAtCosted`, `outcomeValuesCosted`,
`lookaheadCosted` and `Model.predictCosted` in `Acorn.Models`) and updates
(`Transition.outcomeCosted`, `updateRowsCosted`, `beginCosted`, `stepCosted`, `terminalCosted`,
`stopCosted` and `restartCosted`, `Managed.stopTrajectoryCosted` and `restartTrajectoryCosted`, and
`Model.beginCosted`, `stepCosted`, `terminalCosted`, `stopCosted` and `restartCosted` in
`Acorn.Models`), the prediction demons' bank step (`DemonBank.stepCosted` in `Acorn.Demon`), and
every option's off-policy questions (`setFlagsCosted`, `wideSumCosted`, `addAllCosted`,
`subAllCosted`, `Preceding.advanceCosted`, `GradientLearner.scalarsCosted`, `incrementsCosted` and
`stepCosted`, `Question.stepCosted`, `GradientBank.stepCosted` and `OptionQuestions.followCosted` in
`Acorn.OffPolicy`, and `askQuestionsCosted` in `Acorn.Handcrafted.TemporalControl`), and an option's
rate, start, termination decision, step, credit, frozen policy and termination
(`ConsumerRate.resolveCosted`, `Skill.beginOptionCosted`, `decideOptionCosted`, `optionStepCosted`,
`optionCreditCosted`, `frozenPolicyCosted` and `terminateOptionCosted` in `Acorn.Options`), and an
option's start, step, credit of a drawn decision, end, the stop and settling of its stored
trajectory, a start whose first action is drawn and its off-policy following, with its model
(`Skill.beginTemporalCosted`, `stepTemporalCosted`, `creditTemporalCosted`, `endTemporalCosted`,
`stopFollowingCosted`, `settleFollowingCosted`, `settleTemporalCosted`, `startTemporalCosted`,
`startFollowingCosted` and `followTemporalCosted` in `Acorn.Temporal`).
A combinator counts the work of every function it takes, but not the computation of a value it
takes. The values a costed definition passes in, which are all its uncosted entry points, are:

- the value parameters of the combinators: the value of `pure`; the site and value of `op`; the site
  of `charge`; the count and element of `replicate`; the initial accumulator and the collection of
  `foldl` and `foldlArray`; the collection of `map`, `filter`, `filterMap`, `flatMap`, `length`,
  `reverse` and `sum`; the collection and start of `zipIdx`; the two lists of `append`; the element
  and the vector of `prepend`; the element and the list of `mem`; the two vectors of `vectorEq`;
  the vector of `mapVector`, `mapFinIdx` and `toList`; the array of `findIdx?` and `arrayToList`;
  the count and the list of `drop`; the count of `range`, `finRange` and `ofFn`; the condition of
  `ite` and of `dite` (`bind` and `attach` take none);
- the terms a costed definition evaluates in its own body between combinators: its `let`
  values, its branch conditions and the scrutinees of its matches.

The private constructor's work field is set only by the combinators here.

Each must be computed by a stretch that calls no costed definition and runs no loop except those
that **Sites** lists as left inside a segment, whose trip counts are bounded by constants of the
code (the at most 33 steps of `Portable.pow` among them). Every other loop must run only in a loop
combinator or a costed definition, each path to a recursive call must pass a charge, and a level
that works after its recursive call returns must charge there. The combinators cannot enforce it:
`pure` accepts any value, so `Costed.pure (state.step config features reward)` has work zero
although its value runs the learner. Lean's logic gives a pure term no operational meaning, so no
theorem states the discipline; it is a syntactic property, checked by reading until the cost-closed
rule that rbeauchamp/regula#333 proposes checks it. That a library loop makes the passes
`Library.passes` states is read once from the library's runtime implementation, which each row of
`Library` cites. That the compiler erases the work, since `work` is a type former and `single` a
proof, and leaves the code of the value as written is a trust assumption on the compiler's erasure.
A comparison of the generated C of the costed learner with that of the same definitions written
without work found them equal up to renaming. A comparison of the generated C of the costed policy
and exploration definitions and their callers with that of the same definitions written without work
found them equal up to the renaming of the definitions and their local variables and, in four
callers (`TemporalControl.choosePrimitive`, `TemporalControl.serve`, `TemporalControl.serveDraw`,
`Skill.followTemporal`), the order of the parallel moves into a join point. The same holds of the
costed definitions of a learner's record, the controllers' parts and updates listed above and the
normalized step-size sum and their callers, where `TemporalControl.serveDraw` again differs only in
that order, and of the costed definitions of the encoding of a frame and their callers, where
`NumericState.resumable` and `Checkpoint.presence`, which fold `UniqueBuilder.add` as `unique` does,
call a specialization of that fold of their own with the body of the one they shared with `unique`,
and of the costed definitions of an option model's input, ranked features, prediction and updates
and of the controllers' remaining updates, the prediction demons' bank step, every option's
off-policy questions, an option's operations without and with its model and its off-policy
following, and their callers, where `Skill.followTemporal` reaches the model's restart, a costed
operation, through nested tests of consistency and liveness, and the code without work passed
the restart's arguments to a join point that tested consistency again, with the same calls in
the same order.
Each is an observation of one build, which no gate repeats. A bound in word operations bounds the
accounting under `SiteBounds`; no checked statement says that a segment of the executed code does
at most its site's cost in word operations.

**What is not counted:** allocation and release of objects, reference counting, the copy of an
array that is shared when it is written (issue 84 of the repository), the copy of an array into a
larger buffer when a push outgrows its capacity, the one-time initialization of a closed term, a
value with no free variable that the compiled code builds once for the process and then reads,
cache behaviour and time.
No unit here is a second, a byte or an instruction of a particular processor.
-/

namespace Acorn

/-- The constant stretches of the agent's step. Each constructor names the operations its
charge marks; a charge counts its segment (the module's **Sites**). -/
inductive Site where
  /-- The control of one visit of a loop: its test, its advance and its branch. -/
  | visit
  /-- One addition of an ordered sum with the read of its term: a binary32 addition, the binary64
  addition of a widened stored word, or the integer addition of a projection's term. -/
  | sumTerm
  /-- The read of one stored element into a list or vector being built, or as the first
  accumulator of a fold. -/
  | read
  /-- The first SwiftTD loop's entry: the worklist is taken and the eligible list emptied. -/
  | firstOpen
  /-- One element of the first SwiftTD loop, with the read of its index and the prune test. -/
  | firstElement
  /-- A pruned first-loop index: its nine registers cleared and its entry swap-removed. -/
  | prune
  /-- The first SwiftTD loop's exit: the pruned worklist stored as the eligible list. -/
  | firstClose
  /-- The second SwiftTD loop's entry: the overshoot test, the scale and the complement. -/
  | secondOpen
  /-- One element of the second SwiftTD loop. -/
  | secondElement
  /-- The TD error of a SwiftTD step and the store of its prediction and accumulator. -/
  | stepClose
  /-- A fresh transient record apart from its zero register vectors. -/
  | zeroTransient
  /-- The store of a new trajectory's anchor prediction and accumulator. -/
  | beginClose
  /-- The terminal TD error and the result of a terminal step. -/
  | terminalClose
  /-- A planning step's error, its finiteness test and its scale. -/
  | planOpen
  /-- One planning weight write. -/
  | planElement
  /-- The nine registers of one eligible index cleared. -/
  | clearRegisters
  /-- The eligible list emptied after a release. -/
  | releaseClose
  /-- A retired index's registers cleared, its weight zeroed and its step size re-anchored. -/
  | retire
  /-- A managed learner's record after one entry: its next phase and the record itself. -/
  | managedEntry
  /-- A row credit's test of a pending restart. -/
  | creditRestart
  /-- The error or target a learner entry reads that its caller forms: a terminal credit's
  error and trace decay, a stopped trajectory's error, a closed span's error, a tree-backup
  error, a ranked row's discounted target or a deviation learner's target. -/
  | learnerError
  /-- A shared-error update's store of the rows, the taken row and the lags. -/
  | creditClose
  /-- The on-policy error of a shared-error update. -/
  | valuesOpen
  /-- A controller record stored after its rows are updated. -/
  | controllerClose
  /-- The store of a planned row and the planning error. -/
  | planClose
  /-- One comparison of two values with the selection of one of them. -/
  | compare
  /-- One near-maximum test of an action's value against the tie threshold. -/
  | candidate
  /-- A policy's tie threshold: its maximum less the tie window. -/
  | tieThreshold
  /-- One reservoir step: a bounded draw and the selection of the pick. -/
  | reservoirDraw
  /-- One action's nominal mass. -/
  | probability
  /-- The exploration mass, the greedy mass and the tie threshold of a policy. -/
  | probabilitiesOpen
  /-- One uniform draw of an action. -/
  | uniform
  /-- The branch draw of a policy draw and the store of its decision. -/
  | drawClose
  /-- A persistent draw's branch, duration and action draws and the store of its decision. -/
  | explorationBegin
  /-- A duration's powers: the two discount powers of a frozen-decision or duration credit and
  the discount power of a closed span. -/
  | policyOpen
  /-- The store of a frozen policy snapshot. -/
  | snapshot
  /-- One learner's contribution to a derived exploration rate. -/
  | rateTerm
  /-- The projection of an exploration rate: a derived rate, with its fresh-feature fallback,
  or an annealed rate. -/
  | rateClose
  /-- A normalized step-size sum's emptiness test, its endpoints and its result. -/
  | normalizedOpen
  /-- One normalized log step size. -/
  | normalizedTerm
  /-- One term of a policy mean: the widened value added to the totals and the tie test. -/
  | expectedTerm
  /-- A policy mean's two weighted parts, its narrowing and its saturation. -/
  | expectedClose
  /-- One feedback word: a prediction's bucket at its horizon and its channel. -/
  | feedbackWord
  /-- One sample's term of a generated unit's projection. -/
  | sampleTerm
  /-- A generated unit's output from its projection. -/
  | activation
  /-- One word hashed into a feature slot: a sensor word for one tiling, a unit or a model
  age. -/
  | hashFeature
  /-- One unit's output tested and its feature slot computed. -/
  | imprint
  /-- One raw feature's admission into the unique encoding. -/
  | uniqueAdd
  /-- The membership test and append of one absent index to an active set. -/
  | insert
  /-- One ranked position looked up for a feature slot. -/
  | position
  /-- One element written into a vector. -/
  | write
  /-- One product of a ranked value: a weight read times an expected value. -/
  | productTerm
  /-- One prediction admitted as an expected feature value. -/
  | project
  /-- One meta action's value of a predicted outcome. -/
  | outcomeValue
  /-- The record of an option model's prediction. -/
  | prediction
  /-- One meta action's discounted deviation of an outcome, with the outcome's residual. -/
  | deviation
  /-- The record of an option model after its learners are updated. -/
  | modelClose
  /-- A demon's learner record and its projected prediction, each put before the rest of its
  bank's, and its absolute error. -/
  | demonOutput
  /-- The record of a demon bank's outputs: its learners, predictions, errors and cumulants. -/
  | demonClose
  /-- A membership flag of a feature slot read for a filter's test. -/
  | flagTest
  /-- A preceding set's advance: its emptiness and armed tests, a classified transition's step
  size, counts and record, and the stored set's record. -/
  | preceding
  /-- The two inner products of a GTD2-MP step's extragradient midpoint, from its four sums. -/
  | innerProducts
  /-- The four increments of a GTD2-MP step, each narrowed once. -/
  | increments
  /-- One weight of a GTD2-MP step read, moved by its increment through the weight projection and
  written. -/
  | gradientWrite
  /-- A question's silence test and its record. -/
  | question
  /-- A question put before the rest of its bank's. -/
  | questionBank
  /-- An option's questions' record after their preceding set's advance. -/
  | follow
  /-- An option's armed test and its record after its questions take the frame. -/
  | ask
  /-- An assignment's feature slot computed before its membership test. -/
  | assignmentPotential
  /-- A declared potential read from the frame's declared values. -/
  | declaredPotential
  /-- An option's termination tests: goal, duration and the stopping comparison. -/
  | decide
  /-- A started invocation's activation and continuation records. -/
  | beginOption
  /-- An option step's or a drawn decision's credit's learning test, shaped cumulant and skill
  record, and a step's activation advance and records. -/
  | optionStep
  /-- An option's terminal cumulant and stopping value. -/
  | terminateOption
  /-- A stopped trajectory's stopping error and the skill record. -/
  | stopFollowing
  /-- A settled trajectory's shaped cumulant and the skill record. -/
  | settleFollowing
  /-- A followed trajectory's start: its restart test, link and the skill record. -/
  | startFollowing
  /-- A followed frame's restart test, age advance, link and the skill record. -/
  | followStep
  /-- A planning look-ahead's backed-up target and its result record. -/
  | lookAhead
  /-- A backup's store of its prediction cache and planning error. -/
  | backupClose
  /-- A planning boundary's work count, its search-control advance and its result. -/
  | planBoundary
  /-- A fresh learner's rails and record, or a fresh question's projected zero weight, apart
  from their vectors. -/
  | initialState
  /-- One unit's Demon-0 weight tested for a ranking candidate, with its feature slot computed. -/
  | rankCandidate
  /-- The ranked width's search, of at most 15 doublings. -/
  | rankWidth
  /-- One slot's objective installed, with the slot's cache and closing owner. -/
  | install
  /-- The slot-stable objective table: the kept objectives, the entrants and the open slots,
  over the three slots and the at most three ranked candidates. -/
  | assignmentTable
  /-- A rate schedule's advance and a credit gap's discounted reward. -/
  | prepare
  /-- A served step's run, interruption and decision record. -/
  | serve
  /-- A primitive draw's occupancy and decision record. -/
  | choosePrimitive
  /-- A free dispatch's records around the refresh. -/
  | refreshFree
  /-- A free boundary's planning state and its write-back. -/
  | planFree
  /-- A meta draw's generator write. -/
  | drawMeta
  /-- An ending option's slot and event record. -/
  | closeOption
  /-- The owed meta span and its write-back. -/
  | learnMeta
  /-- A dispatch's meta action mapped to an option, its value function and records. -/
  | dispatchMeta
  /-- A stepped option's occupancy and decision record. -/
  | stepOption
  /-- A free boundary's closing record and event. -/
  | atBoundary
  /-- Selection's branch tests and phase write. -/
  | select
  /-- The agent's clock advance and the chosen value's record. -/
  | choose

/-- A cost model: the cost of each site, counted once for the segment of each charge of the
site. -/
abbrev Costs := Site → Nat

/-- The library loops that costed code and the twins of `AcornVerif.Resource.Work` run. Each
is charged the passes of its runtime implementation over the collection it is charged for: the
compiler replacement that runs (a `csimp` theorem or an implementation attribute) and the loops
of that definition. `Library.passes` states each count once. -/
inductive Library where
  /-- `List.foldl`: one structural loop. -/
  | foldl
  /-- `Array.foldl`, implemented by `Array.foldlMUnsafe`: one loop. -/
  | foldlArray
  /-- `List.map`, replaced by `List.mapTR` (`List.map_eq_mapTR`): a loop, then `List.reverse`. -/
  | map
  /-- `Vector.replicate`, `Array.replicate`, implemented by the runtime's `lean_mk_array`: one
  loop. -/
  | replicate
  /-- `Array.findIdx?`: the loop `Array.findIdx?.loop`. -/
  | findIdx
  /-- `Vector.map`, `Array.map` by `Array.mapM`, implemented by `Array.mapMUnsafe`: one loop. -/
  | vectorMap
  /-- `Vector.ofFn`, `Array.ofFn` by its loop `Array.ofFn.go`: one loop. -/
  | ofFn
  /-- `Vector.mapFinIdx`, `Array.mapFinIdx`, implemented by `Array.mapFinIdxMUnsafe`: one loop. -/
  | mapFinIdx
  /-- `List.filter`, replaced by `List.filterTR` (`List.filter_eq_filterTR`): a loop, then
  `List.reverse`. -/
  | filter
  /-- `List.filterMap`, replaced by `List.filterMapTR` (`List.filterMap_eq_filterMapTR`): a loop,
  then `Array.toList` of the kept elements, at most one for each element. -/
  | filterMap
  /-- `List.flatMap`, replaced by `List.flatMapTR` (`List.flatMap_eq_flatMapTR`): a loop over the
  list, then `Array.toList` of the results, whose end is charged as a second pass over the list
  and whose elements are counted by `flatMapResult`. -/
  | flatMap
  /-- The elements of one result of `List.flatMapTR`: `Array.appendList` pushes each one
  (`List.foldl`), and the final `Array.toList` reads each one. -/
  | flatMapResult
  /-- `List.length`, replaced by `List.lengthTR` (`List.length_eq_lengthTR`): one loop. -/
  | length
  /-- `List.contains` and the membership test of a list, `List.elem`: one loop. -/
  | contains
  /-- `List.range`, the loop `List.range.loop`: one loop. -/
  | range
  /-- `List.finRange`, `List.ofFn` by `Fin.foldr`: one loop. -/
  | finRange
  /-- `List.toArray`, implemented by `List.toArrayImpl`: `List.length`, then `List.toArrayAux`. -/
  | toArray
  /-- `Array.toList` and `Vector.toList`, implemented by `Array.toListImpl`, an `Array.foldr`: one
  loop. -/
  | toList
  /-- `List.reverse`, `List.reverseAux`: one loop. -/
  | reverse
  /-- The equality of two vectors, the equality of their arrays, replaced by
  `Array.instDecidableEqImpl` (`Array.instDecidableEq_csimp`), an `Array.isEqv`: one loop. -/
  | vectorEq
  /-- `++` on lists, replaced by `List.appendTR` (`List.append_eq_appendTR`): `List.reverse` of
  the first list, then `List.reverseAux` over it. -/
  | append
  /-- `++` on vectors, `Array.append`: an `Array.foldl` over the second array that pushes each of
  its elements, implemented by `Array.foldlMUnsafe`: one loop. -/
  | vectorAppend
  /-- `List.drop` (`Init.Data.List.Basic`), which no `csimp` replaces: a structural recursion
  over the elements it drops, one loop. -/
  | drop
  /-- `List.dropLast`, replaced by `List.dropLastTR` (`List.dropLast_eq_dropLastTR`):
  `List.toArray` (two), `Array.pop`, then `Array.toList` (one). -/
  | dropLast
  /-- `List.zipIdx`, replaced by `List.zipIdxTR` (`List.zipIdx_eq_zipIdxTR`): `List.toArray`
  (two), then `Array.foldr` (one). -/
  | zipIdx
  /-- `List.sum` of integers, a `List.foldr`. The specialization that runs is the toolchain's
  `List.foldr` at `Lean.Omega.IntList.sum` (`Init.Omega.IntList`), whose compiled code is the
  structural recursion, not `List.foldrTR`: one loop. -/
  | sum
  /-- Acorn's `fillVacant`, a structural recursion over the held positions that puts each
  position's slot before the rest after its recursive call returns: two passes, its descent and
  then its return. -/
  | fillVacant

/-- The passes of a library loop's runtime implementation over the collection it is charged
for. -/
def Library.passes : Library → Nat
  | .foldl => 1
  | .foldlArray => 1
  | .map => 2
  | .replicate => 1
  | .findIdx => 1
  | .vectorMap => 1
  | .ofFn => 1
  | .mapFinIdx => 1
  | .filter => 2
  | .filterMap => 2
  | .flatMap => 2
  | .flatMapResult => 2
  | .length => 1
  | .contains => 1
  | .range => 1
  | .finRange => 1
  | .toArray => 2
  | .toList => 1
  | .reverse => 1
  | .vectorEq => 1
  | .append => 2
  | .vectorAppend => 1
  | .drop => 1
  | .dropLast => 3
  | .zipIdx => 3
  | .sum => 1
  | .fillVacant => 2

/-- The loop control of the library loop `row` over `count` elements: each of its passes visits
each element once and ends with one visit. -/
abbrev Library.control (row : Library) (visit count : Nat) : Nat :=
  row.passes * (count * visit + visit)

/-- The work of the library loop `row` over `count` elements whose callback is within `bound` at
each element: the callback once for each element, and the loop's control. -/
abbrev Library.work (row : Library) (visit count bound : Nat) : Nat :=
  count * bound + row.control visit count

/-- A loop over more elements has more control. -/
theorem Library.control_mono (row : Library) {visit count limit : Nat} (fits : count ≤ limit) :
    row.control visit count ≤ row.control visit limit :=
  Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_right visit fits) visit)

/-- A loop over more elements, each with a larger callback bound, does more work. -/
theorem Library.work_mono (row : Library) {visit count limit bound most : Nat}
    (fits : count ≤ limit) (within : bound ≤ most) :
    row.work visit count bound ≤ row.work visit limit most :=
  Nat.add_le_add (Nat.mul_le_mul fits within) (row.control_mono fits)

/-- A result together with the work of computing it. The constructor is private, so every
`Costed` value is built by the combinators below. -/
structure Costed (α : Type) where
  private mk ::
  /-- The result. -/
  val : α
  /-- `work κ n`: under the cost model `κ`, computing the result does `n` work. A type former,
  so the compiler erases it. -/
  work : Costs → Nat → Prop
  /-- Under each cost model the work is one number. -/
  single : ∀ κ, ∃ n, work κ n ∧ ∀ m, work κ m → m = n

namespace Costed

variable {α β : Type}

/-- Under the cost model `κ`, the work of `x` is at most `bound`. -/
def Within (x : Costed α) (κ : Costs) (bound : Nat) : Prop :=
  ∀ n, x.work κ n → n ≤ bound

/-- A bound holds exactly when the one work number is at most it. -/
theorem within_iff (x : Costed α) (κ : Costs) (bound : Nat) :
    x.Within κ bound ↔ ∃ n, x.work κ n ∧ n ≤ bound := by
  obtain ⟨n, holds, unique⟩ := x.single κ
  constructor
  · intro within
    exact ⟨n, holds, within n holds⟩
  · intro ⟨m, held, fits⟩ k work
    rw [unique k work, ← unique m held]
    exact fits

/-- A larger bound holds too. -/
theorem Within.mono {x : Costed α} {κ : Costs} {a b : Nat} (within : x.Within κ a)
    (fits : a ≤ b) : x.Within κ b :=
  fun n work => Nat.le_trans (within n work) fits

/-- A branch is bounded by a bound of each of its arms. -/
theorem within_ite {condition : Prop} [Decidable condition] {yes no : Costed α} {κ : Costs}
    {bound : Nat} (yesFits : yes.Within κ bound) (noFits : no.Within κ bound) :
    (if condition then yes else no).Within κ bound := by
  split
  · exact yesFits
  · exact noFits

/-- A value read without an operation of its own. -/
@[inline] def pure (value : α) : Costed α :=
  ⟨value, fun _ n => n = 0, fun _ => ⟨0, rfl, fun _ same => same⟩⟩

/-- A stretch of constant work at a site. -/
@[inline] def op (site : Site) (value : α) : Costed α :=
  ⟨value, fun κ n => n = κ site, fun κ => ⟨κ site, rfl, fun _ same => same⟩⟩

/-- A stretch at a site before a computation. -/
@[inline] def charge (site : Site) (rest : Costed α) : Costed α :=
  ⟨rest.val, fun κ n => ∃ later, rest.work κ later ∧ n = κ site + later, fun κ => by
    obtain ⟨later, held, unique⟩ := rest.single κ
    exact ⟨κ site + later, ⟨later, held, rfl⟩, fun m ⟨other, work, same⟩ => by
      rw [same, unique other work]⟩⟩

/-- Sequential composition: the continuation reads the first result, and the work of the two
parts adds. -/
@[inline] def bind (first : Costed α) (next : α → Costed β) : Costed β :=
  ⟨(next first.val).val,
    fun κ n => ∃ here later, first.work κ here ∧ (next first.val).work κ later ∧
      n = here + later, fun κ => by
    obtain ⟨here, firstHeld, firstUnique⟩ := first.single κ
    obtain ⟨later, nextHeld, nextUnique⟩ := (next first.val).single κ
    exact ⟨here + later, ⟨here, later, firstHeld, nextHeld, rfl⟩,
      fun m ⟨a, b, firstWork, nextWork, same⟩ => by
        rw [same, firstUnique a firstWork, nextUnique b nextWork]⟩⟩

/-- A branch: the value of the arm the condition selects, with that arm's work. Each arm is a
thunk, so only the selected arm is computed. -/
@[inline] def ite (condition : Prop) [Decidable condition] (yes no : Unit → Costed α) : Costed α :=
  ⟨if condition then (yes ()).val else (no ()).val,
    fun κ n => if condition then (yes ()).work κ n else (no ()).work κ n, fun κ => by
      by_cases holds : condition
      · simp only [holds, ↓reduceIte]
        exact (yes ()).single κ
      · simp only [holds, ↓reduceIte]
        exact (no ()).single κ⟩

/-- The `pure` of `do` blocks. There is no `Functor` or `Monad` instance, whose derived `map`
and `seq` would apply a callback that is not costed. -/
instance : Pure Costed := ⟨Costed.pure⟩

/-- The sequencing of `do` blocks. -/
instance : Bind Costed := ⟨Costed.bind⟩

theorem pure_val (value : α) : (pure value).val = value := rfl

theorem op_val (site : Site) (value : α) : (op site value).val = value := rfl

theorem charge_val (site : Site) (rest : Costed α) : (charge site rest).val = rest.val := rfl

theorem bind_val (first : Costed α) (next : α → Costed β) :
    (first >>= next).val = (next first.val).val := rfl

theorem pure_eq (value : α) : (Pure.pure value : Costed α) = Costed.pure value := rfl

theorem bind_eq (first : Costed α) (next : α → Costed β) :
    first >>= next = Costed.bind first next := rfl

theorem pure_within (value : α) (κ : Costs) : (pure value).Within κ 0 :=
  fun _ same => Nat.le_of_eq same

theorem op_within (site : Site) (value : α) (κ : Costs) : (op site value).Within κ (κ site) :=
  fun _ same => Nat.le_of_eq same

theorem charge_within {site : Site} {rest : Costed α} {κ : Costs} {bound : Nat}
    (fits : rest.Within κ bound) : (charge site rest).Within κ (κ site + bound) :=
  fun _ ⟨later, work, same⟩ => by
    rw [same]
    exact Nat.add_le_add_left (fits later work) _

/-- A sequence is bounded by a bound of its first part and a bound of its continuation at the
first result. -/
theorem bind_within {first : Costed α} {next : α → Costed β} {κ : Costs} {a b : Nat}
    (firstFits : first.Within κ a) (nextFits : (next first.val).Within κ b) :
    (first >>= next).Within κ (a + b) :=
  fun _ ⟨here, later, firstWork, nextWork, same⟩ => by
    rw [same]
    exact Nat.add_le_add (firstFits here firstWork) (nextFits later nextWork)

/-- A branch's value is the value of the arm its condition selects. -/
theorem ite_val (condition : Prop) [Decidable condition] (yes no : Unit → Costed α) :
    (ite condition yes no).val = if condition then (yes ()).val else (no ()).val := rfl

/-- A branch is bounded by a bound of each arm under its condition. -/
theorem ite_within {condition : Prop} [Decidable condition] {yes no : Unit → Costed α}
    {κ : Costs} {bound : Nat} (yesFits : condition → (yes ()).Within κ bound)
    (noFits : ¬condition → (no ()).Within κ bound) : (ite condition yes no).Within κ bound := by
  intro n work
  change (if condition then (yes ()).work κ n else (no ()).work κ n) at work
  by_cases holds : condition
  · simp only [holds, ↓reduceIte] at work
    exact yesFits holds n work
  · simp only [holds, ↓reduceIte] at work
    exact noFits holds n work

/-- A dependent branch: the value of the arm the condition selects, each arm reading the
condition's proof, with that arm's work. -/
@[inline] def dite (condition : Prop) [Decidable condition] (yes : condition → Costed α)
    (no : ¬condition → Costed α) : Costed α :=
  ⟨if holds : condition then (yes holds).val else (no holds).val,
    fun κ n => if holds : condition then (yes holds).work κ n else (no holds).work κ n,
    fun κ => by
      by_cases holds : condition
      · simp only [holds, ↓reduceDIte]
        exact (yes holds).single κ
      · simp only [holds, ↓reduceDIte]
        exact (no holds).single κ⟩

/-- A dependent branch's value is the value of the arm its condition selects. -/
theorem dite_val (condition : Prop) [Decidable condition] (yes : condition → Costed α)
    (no : ¬condition → Costed α) :
    (dite condition yes no).val = if holds : condition then (yes holds).val else (no holds).val :=
  rfl

/-- A dependent branch is bounded by a bound of each arm under its condition. -/
theorem dite_within {condition : Prop} [Decidable condition] {yes : condition → Costed α}
    {no : ¬condition → Costed α} {κ : Costs} {bound : Nat}
    (yesFits : ∀ holds, (yes holds).Within κ bound)
    (noFits : ∀ holds, (no holds).Within κ bound) :
    (dite condition yes no).Within κ bound := by
  intro n work
  change (if holds : condition then (yes holds).work κ n else (no holds).work κ n) at work
  by_cases holds : condition
  · simp only [holds, ↓reduceDIte] at work
    exact yesFits holds n work
  · simp only [holds, ↓reduceDIte] at work
    exact noFits holds n work

/-- A sequence is bounded by a bound of its first part and a bound of its continuation at each
result. -/
theorem bind_within_all {first : Costed α} {next : α → Costed β} {κ : Costs} {a b : Nat}
    (firstFits : first.Within κ a) (nextFits : ∀ value, (next value).Within κ b) :
    (first >>= next).Within κ (a + b) :=
  bind_within firstFits (nextFits first.val)

/-! ## Loops -/

/-- The work of the steps of a left fold: each step's work at the accumulator the fold reaches
there. The loop's control is charged from its row of `Library`. -/
def foldlSteps (step : β → α → Costed β) : β → List α → Costs → Nat → Prop
  | _, [], _, n => n = 0
  | acc, item :: rest, κ, n => ∃ here later, (step acc item).work κ here ∧
      foldlSteps step (step acc item).val rest κ later ∧ n = here + later

theorem foldlSteps_single (step : β → α → Costed β) (κ : Costs) (items : List α) :
    ∀ acc : β, ∃ n, foldlSteps step acc items κ n ∧ ∀ m, foldlSteps step acc items κ m → m = n := by
  induction items with
  | nil => exact fun _ => ⟨0, rfl, fun _ same => same⟩
  | cons item rest ih =>
    intro acc
    obtain ⟨here, stepHeld, stepUnique⟩ := (step acc item).single κ
    obtain ⟨later, restHeld, restUnique⟩ := ih (step acc item).val
    refine ⟨here + later, ⟨here, later, stepHeld, restHeld, rfl⟩, fun m work => ?_⟩
    obtain ⟨a, b, stepWork, restWork, same⟩ := work
    rw [same, stepUnique a stepWork, restUnique b restWork]

/-- The steps of a fold whose every step is within `bound` are within the trip count times that
bound. The bound holds at every accumulator, so no reasoning about the values the fold computes
is needed. -/
theorem foldlSteps_within (step : β → α → Costed β) (κ : Costs) (bound : Nat)
    (items : List α) (each : ∀ acc, ∀ item ∈ items, (step acc item).Within κ bound) :
    ∀ acc n, foldlSteps step acc items κ n → n ≤ items.length * bound := by
  induction items with
  | nil =>
    intro _ n work
    have same : n = 0 := work
    omega
  | cons item rest ih =>
    intro acc n work
    obtain ⟨here, later, stepWork, restWork, same⟩ := work
    have headFits := each acc item (List.mem_cons_self ..) here stepWork
    have restFits := ih (fun acc item member => each acc item (List.mem_cons_of_mem _ member))
      _ later restWork
    rw [same, List.length_cons, Nat.succ_mul]
    omega

/-- A left fold over a list (`Library.foldl`). Its value is the library fold of the steps'
values; its work is its steps' work and the control of its row. -/
@[inline] def foldl (step : β → α → Costed β) (init : β) (items : List α) : Costed β :=
  ⟨items.foldl (fun acc item => (step acc item).val) init,
    fun κ n => ∃ steps, foldlSteps step init items κ steps ∧
      n = steps + Library.foldl.control (κ .visit) items.length,
    fun κ => by
      obtain ⟨steps, held, unique⟩ := foldlSteps_single step κ items init
      exact ⟨_, ⟨steps, held, rfl⟩, fun m ⟨other, work, same⟩ => by
        rw [same, unique other work]⟩⟩

theorem foldl_val (step : β → α → Costed β) (init : β) (items : List α) :
    (foldl step init items).val = items.foldl (fun acc item => (step acc item).val) init := rfl

/-- A fold whose every step is within `bound` is within its row's work at that bound. -/
theorem foldl_within {step : β → α → Costed β} {init : β} {items : List α} {κ : Costs}
    {bound : Nat} (each : ∀ acc, ∀ item ∈ items, (step acc item).Within κ bound) :
    (foldl step init items).Within κ (Library.foldl.work (κ .visit) items.length bound) :=
  fun _ ⟨steps, work, same⟩ => by
    rw [same]
    exact Nat.add_le_add_right (foldlSteps_within step κ bound items each init steps work) _

/-- A left fold over an array (`Library.foldlArray`), visiting its elements in order. -/
@[inline] def foldlArray (step : β → α → Costed β) (init : β) (items : Array α) : Costed β :=
  ⟨items.foldl (fun acc item => (step acc item).val) init,
    fun κ n => ∃ steps, foldlSteps step init items.toList κ steps ∧
      n = steps + Library.foldlArray.control (κ .visit) items.size,
    fun κ => by
      obtain ⟨steps, held, unique⟩ := foldlSteps_single step κ items.toList init
      exact ⟨_, ⟨steps, held, rfl⟩, fun m ⟨other, work, same⟩ => by
        rw [same, unique other work]⟩⟩

theorem foldlArray_val (step : β → α → Costed β) (init : β) (items : Array α) :
    (foldlArray step init items).val = items.foldl (fun acc item => (step acc item).val) init :=
  rfl

theorem foldlArray_within {step : β → α → Costed β} {init : β} {items : Array α} {κ : Costs}
    {bound : Nat} (each : ∀ acc, ∀ item ∈ items.toList, (step acc item).Within κ bound) :
    (foldlArray step init items).Within κ (Library.foldlArray.work (κ .visit) items.size bound) :=
  fun _ ⟨steps, work, same⟩ => by
    rw [same]
    have counted := foldlSteps_within step κ bound items.toList each init steps work
    rw [Array.length_toList] at counted
    exact Nat.add_le_add_right counted _

/-- The work of the operations of a mapping loop: each operation's work. The loop's control is
charged from its row of `Library`. -/
def mapSteps (operation : α → Costed β) : List α → Costs → Nat → Prop
  | [], _, n => n = 0
  | item :: rest, κ, n => ∃ here later, (operation item).work κ here ∧
      mapSteps operation rest κ later ∧ n = here + later

theorem mapSteps_single (operation : α → Costed β) (κ : Costs) (items : List α) :
    ∃ n, mapSteps operation items κ n ∧ ∀ m, mapSteps operation items κ m → m = n := by
  induction items with
  | nil => exact ⟨0, rfl, fun _ same => same⟩
  | cons item rest ih =>
    obtain ⟨here, opHeld, opUnique⟩ := (operation item).single κ
    obtain ⟨later, restHeld, restUnique⟩ := ih
    refine ⟨here + later, ⟨here, later, opHeld, restHeld, rfl⟩, fun m work => ?_⟩
    obtain ⟨a, b, opWork, restWork, same⟩ := work
    rw [same, opUnique a opWork, restUnique b restWork]

/-- The operations of a mapping loop, each within `bound`, are within the trip count times that
bound. -/
theorem mapSteps_within {operation : α → Costed β} {κ : Costs} {bound : Nat} :
    ∀ items : List α, (∀ item ∈ items, (operation item).Within κ bound) →
      ∀ n, mapSteps operation items κ n → n ≤ items.length * bound := by
  intro items
  induction items with
  | nil =>
    intro _ n work
    have same : n = 0 := work
    omega
  | cons item rest ih =>
    intro each n work
    obtain ⟨here, later, opWork, restWork, same⟩ := work
    have headFits := each item (List.mem_cons_self ..) here opWork
    have restFits := ih (fun item member => each item (List.mem_cons_of_mem _ member)) later
      restWork
    rw [same, List.length_cons, Nat.succ_mul]
    omega

/-- A map over a list (`Library.map`): its operations' work and the control of its row, the loop
of `List.mapTR` and the reversal of its result. -/
@[inline] def map (operation : α → Costed β) (items : List α) : Costed (List β) :=
  ⟨items.map fun item => (operation item).val,
    fun κ n => ∃ steps, mapSteps operation items κ steps ∧
      n = steps + Library.map.control (κ .visit) items.length,
    fun κ => by
      obtain ⟨steps, held, unique⟩ := mapSteps_single operation κ items
      exact ⟨_, ⟨steps, held, rfl⟩, fun m ⟨other, work, same⟩ => by
        rw [same, unique other work]⟩⟩

theorem map_val (operation : α → Costed β) (items : List α) :
    (map operation items).val = items.map fun item => (operation item).val := rfl

theorem map_within {operation : α → Costed β} {items : List α} {κ : Costs} {bound : Nat}
    (each : ∀ item ∈ items, (operation item).Within κ bound) :
    (map operation items).Within κ (Library.map.work (κ .visit) items.length bound) :=
  fun _ ⟨steps, work, same⟩ => by
    rw [same]
    exact Nat.add_le_add_right (mapSteps_within items each steps work) _

/-- A vector of one repeated element (`Library.replicate`): the control of its row. -/
@[inline] def replicate (count : Nat) (value : α) : Costed (Vector α count) :=
  ⟨Vector.replicate count value, fun κ n => n = Library.replicate.control (κ .visit) count,
    fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem replicate_val (count : Nat) (value : α) :
    (replicate count value).val = Vector.replicate count value := rfl

theorem replicate_within (count : Nat) (value : α) (κ : Costs) :
    (replicate count value).Within κ (Library.replicate.control (κ .visit) count) :=
  fun _ same => Nat.le_of_eq same

/-- The index of the first element of `items` whose costed test holds, by the library search
`Array.findIdx?` (`Library.findIdx`), with the equation that names it: the work of each
element's test, whether the search stops early or not, and the control of its row. -/
@[inline] def findIdx? (items : Array α) (test : α → Costed Bool) :
    Costed {found : Option Nat // items.findIdx? (fun item => (test item).val) = found} :=
  ⟨⟨items.findIdx? fun item => (test item).val, rfl⟩,
    fun κ n => ∃ steps, mapSteps test items.toList κ steps ∧
      n = steps + Library.findIdx.control (κ .visit) items.size,
    fun κ => by
      obtain ⟨steps, held, unique⟩ := mapSteps_single test κ items.toList
      exact ⟨_, ⟨steps, held, rfl⟩, fun m ⟨other, work, same⟩ => by
        rw [same, unique other work]⟩⟩

theorem findIdx?_val (items : Array α) (test : α → Costed Bool) :
    (findIdx? items test).val.val = items.findIdx? fun item => (test item).val := rfl

/-- A search whose every test is within `bound` is within its row's work at that bound. -/
theorem findIdx?_within {items : Array α} {test : α → Costed Bool} {κ : Costs} {bound : Nat}
    (each : ∀ item ∈ items.toList, (test item).Within κ bound) :
    (findIdx? items test).Within κ (Library.findIdx.work (κ .visit) items.size bound) :=
  fun _ ⟨steps, work, same⟩ => by
    rw [same]
    have counted := mapSteps_within items.toList each steps work
    rw [Array.length_toList] at counted
    exact Nat.add_le_add_right counted _

/-- The elements of `items` whose costed test holds, in order, by the library function
`List.filter` (`Library.filter`): the work of each element's test and the control of its row. -/
@[inline] def filter (test : α → Costed Bool) (items : List α) : Costed (List α) :=
  ⟨items.filter fun item => (test item).val,
    fun κ n => ∃ steps, mapSteps test items κ steps ∧
      n = steps + Library.filter.control (κ .visit) items.length,
    fun κ => by
      obtain ⟨steps, held, unique⟩ := mapSteps_single test κ items
      exact ⟨_, ⟨steps, held, rfl⟩, fun m ⟨other, work, same⟩ => by
        rw [same, unique other work]⟩⟩

theorem filter_val (test : α → Costed Bool) (items : List α) :
    (filter test items).val = items.filter fun item => (test item).val := rfl

/-- A filter whose every test is within `bound` is within its row's work at that bound. -/
theorem filter_within {test : α → Costed Bool} {items : List α} {κ : Costs} {bound : Nat}
    (each : ∀ item ∈ items, (test item).Within κ bound) :
    (filter test items).Within κ (Library.filter.work (κ .visit) items.length bound) :=
  fun _ ⟨steps, work, same⟩ => by
    rw [same]
    exact Nat.add_le_add_right (mapSteps_within items each steps work) _

/-- The results of a costed operation on the elements of `items` that it keeps, in order, by the
library function `List.filterMap` (`Library.filterMap`): the work of each element's operation and
the control of its row. -/
@[inline] def filterMap (operation : α → Costed (Option β)) (items : List α) :
    Costed (List β) :=
  ⟨items.filterMap fun item => (operation item).val,
    fun κ n => ∃ steps, mapSteps operation items κ steps ∧
      n = steps + Library.filterMap.control (κ .visit) items.length,
    fun κ => by
      obtain ⟨steps, held, unique⟩ := mapSteps_single operation κ items
      exact ⟨_, ⟨steps, held, rfl⟩, fun m ⟨other, work, same⟩ => by
        rw [same, unique other work]⟩⟩

theorem filterMap_val (operation : α → Costed (Option β)) (items : List α) :
    (filterMap operation items).val = items.filterMap fun item => (operation item).val := rfl

/-- A filtering map whose every operation is within `bound` is within its row's work at that
bound. -/
theorem filterMap_within {operation : α → Costed (Option β)} {items : List α} {κ : Costs}
    {bound : Nat} (each : ∀ item ∈ items, (operation item).Within κ bound) :
    (filterMap operation items).Within κ (Library.filterMap.work (κ .visit) items.length bound) :=
  fun _ ⟨steps, work, same⟩ => by
    rw [same]
    exact Nat.add_le_add_right (mapSteps_within items each steps work) _

/-- The work of the operations of a flattening loop: each operation's work and the control of
the row `flatMapResult` over the elements of its result. -/
def flatMapSteps (operation : α → Costed (List β)) : List α → Costs → Nat → Prop
  | [], _, n => n = 0
  | item :: rest, κ, n => ∃ here later, (operation item).work κ here ∧
      flatMapSteps operation rest κ later ∧
      n = here + Library.flatMapResult.control (κ .visit) (operation item).val.length + later

theorem flatMapSteps_single (operation : α → Costed (List β)) (κ : Costs) (items : List α) :
    ∃ n, flatMapSteps operation items κ n ∧
      ∀ m, flatMapSteps operation items κ m → m = n := by
  induction items with
  | nil => exact ⟨0, rfl, fun _ same => same⟩
  | cons item rest ih =>
    obtain ⟨here, opHeld, opUnique⟩ := (operation item).single κ
    obtain ⟨later, restHeld, restUnique⟩ := ih
    refine ⟨_, ⟨here, later, opHeld, restHeld, rfl⟩, fun m work => ?_⟩
    obtain ⟨a, b, opWork, restWork, same⟩ := work
    rw [same, opUnique a opWork, restUnique b restWork]

/-- The operations of a flattening loop, each within `bound` with a result of at most `size`
elements, are within the trip count times that bound and that result's control. -/
theorem flatMapSteps_within {operation : α → Costed (List β)} {κ : Costs} {bound size : Nat} :
    ∀ items : List α, (∀ item ∈ items, (operation item).Within κ bound) →
      (∀ item ∈ items, (operation item).val.length ≤ size) →
      ∀ n, flatMapSteps operation items κ n →
        n ≤ items.length * (bound + Library.flatMapResult.control (κ .visit) size) := by
  intro items
  induction items with
  | nil =>
    intro _ _ n work
    have same : n = 0 := work
    omega
  | cons item rest ih =>
    intro each sizes n work
    obtain ⟨here, later, opWork, restWork, same⟩ := work
    have headFits := each item (List.mem_cons_self ..) here opWork
    have headSize := Library.control_mono .flatMapResult (visit := κ .visit)
      (sizes item (List.mem_cons_self ..))
    have restFits := ih (fun item member => each item (List.mem_cons_of_mem _ member))
      (fun item member => sizes item (List.mem_cons_of_mem _ member)) later restWork
    rw [same, List.length_cons, Nat.succ_mul]
    omega

/-- The concatenation of the results of a costed operation on each element of `items`, by the
library function `List.flatMap` (`Library.flatMap`): the work of each element's operation, the
control of the row `flatMapResult` over the elements of each result, and the control of its
row. -/
@[inline] def flatMap (operation : α → Costed (List β)) (items : List α) : Costed (List β) :=
  ⟨items.flatMap fun item => (operation item).val,
    fun κ n => ∃ steps, flatMapSteps operation items κ steps ∧
      n = steps + Library.flatMap.control (κ .visit) items.length,
    fun κ => by
      obtain ⟨steps, held, unique⟩ := flatMapSteps_single operation κ items
      exact ⟨_, ⟨steps, held, rfl⟩, fun m ⟨other, work, same⟩ => by
        rw [same, unique other work]⟩⟩

theorem flatMap_val (operation : α → Costed (List β)) (items : List α) :
    (flatMap operation items).val = items.flatMap fun item => (operation item).val := rfl

/-- A flattening loop whose every operation is within `bound` with a result of at most `size`
elements is within its row's work at that bound and that result's control. -/
theorem flatMap_within {operation : α → Costed (List β)} {items : List α} {κ : Costs}
    {bound size : Nat} (each : ∀ item ∈ items, (operation item).Within κ bound)
    (sizes : ∀ item ∈ items, (operation item).val.length ≤ size) :
    (flatMap operation items).Within κ (Library.flatMap.work (κ .visit) items.length
      (bound + Library.flatMapResult.control (κ .visit) size)) :=
  fun _ ⟨steps, work, same⟩ => by
    rw [same]
    exact Nat.add_le_add_right (flatMapSteps_within items each sizes steps work) _

/-- A map over a vector (`Library.vectorMap`): its operations' work and the control of its row. -/
@[inline] def mapVector {count : Nat} (operation : α → Costed β) (items : Vector α count) :
    Costed (Vector β count) :=
  ⟨items.map fun item => (operation item).val,
    fun κ n => ∃ steps, mapSteps operation items.toList κ steps ∧
      n = steps + Library.vectorMap.control (κ .visit) count,
    fun κ => by
      obtain ⟨steps, held, unique⟩ := mapSteps_single operation κ items.toList
      exact ⟨_, ⟨steps, held, rfl⟩, fun m ⟨other, work, same⟩ => by
        rw [same, unique other work]⟩⟩

theorem mapVector_val {count : Nat} (operation : α → Costed β) (items : Vector α count) :
    (mapVector operation items).val = items.map fun item => (operation item).val := rfl

/-- A map over a vector whose every operation is within `bound` is within its row's work at that
bound. -/
theorem mapVector_within {count : Nat} {operation : α → Costed β} {items : Vector α count}
    {κ : Costs} {bound : Nat} (each : ∀ item ∈ items.toList, (operation item).Within κ bound) :
    (mapVector operation items).Within κ (Library.vectorMap.work (κ .visit) count bound) :=
  fun _ ⟨steps, work, same⟩ => by
    rw [same]
    have counted := mapSteps_within items.toList each steps work
    rw [Vector.length_toList] at counted
    exact Nat.add_le_add_right counted _

/-- A map over a vector with each element's index (`Library.mapFinIdx`): its operations' work and
the control of its row. -/
@[inline] def mapFinIdx {count : Nat} (items : Vector α count)
    (operation : (index : Nat) → α → index < count → Costed β) : Costed (Vector β count) :=
  ⟨items.mapFinIdx fun index item bound => (operation index item bound).val,
    fun κ n => ∃ steps, mapSteps (fun index : Fin count =>
        operation index.val (items.get index) index.isLt) (List.finRange count) κ steps ∧
      n = steps + Library.mapFinIdx.control (κ .visit) count,
    fun κ => by
      obtain ⟨steps, held, unique⟩ := mapSteps_single (fun index : Fin count =>
        operation index.val (items.get index) index.isLt) κ (List.finRange count)
      exact ⟨_, ⟨steps, held, rfl⟩, fun m ⟨other, work, same⟩ => by
        rw [same, unique other work]⟩⟩

theorem mapFinIdx_val {count : Nat} (items : Vector α count)
    (operation : (index : Nat) → α → index < count → Costed β) :
    (mapFinIdx items operation).val =
      items.mapFinIdx fun index item bound => (operation index item bound).val := rfl

/-- An indexed map whose every operation is within `bound` is within its row's work at that
bound. -/
theorem mapFinIdx_within {count : Nat} {items : Vector α count}
    {operation : (index : Nat) → α → index < count → Costed β} {κ : Costs} {bound : Nat}
    (each : ∀ index : Fin count, (operation index.val (items.get index) index.isLt).Within κ bound) :
    (mapFinIdx items operation).Within κ (Library.mapFinIdx.work (κ .visit) count bound) :=
  fun _ ⟨steps, work, same⟩ => by
    rw [same]
    have counted := mapSteps_within (List.finRange count) (fun index _ => each index) steps work
    rw [List.length_finRange] at counted
    exact Nat.add_le_add_right counted _

/-- A vector built from a costed operation at each index, by `Vector.ofFn` (`Library.ofFn`): the
operations' work and the control of its row. -/
@[inline] def ofFn {count : Nat} (operation : Fin count → Costed β) : Costed (Vector β count) :=
  ⟨Vector.ofFn fun index => (operation index).val,
    fun κ n => ∃ steps, mapSteps operation (List.finRange count) κ steps ∧
      n = steps + Library.ofFn.control (κ .visit) count,
    fun κ => by
      obtain ⟨steps, held, unique⟩ := mapSteps_single operation κ (List.finRange count)
      exact ⟨_, ⟨steps, held, rfl⟩, fun m ⟨other, work, same⟩ => by
        rw [same, unique other work]⟩⟩

theorem ofFn_val {count : Nat} (operation : Fin count → Costed β) :
    (ofFn operation).val = Vector.ofFn fun index => (operation index).val := rfl

/-- A built vector whose every operation is within `bound` is within its row's work at that
bound. -/
theorem ofFn_within {count : Nat} {operation : Fin count → Costed β} {κ : Costs} {bound : Nat}
    (each : ∀ index, (operation index).Within κ bound) :
    (ofFn operation).Within κ (Library.ofFn.work (κ .visit) count bound) :=
  fun _ ⟨steps, work, same⟩ => by
    rw [same]
    have counted := mapSteps_within (List.finRange count) (fun index _ => each index) steps work
    rw [List.length_finRange] at counted
    exact Nat.add_le_add_right counted _

/-- A computation's result together with its equation, for a caller whose proof names the
result: the computation's work and no more. -/
@[inline] def attach (x : Costed α) : Costed {value : α // value = x.val} :=
  ⟨⟨x.val, rfl⟩, x.work, x.single⟩

theorem attach_val (x : Costed α) : (attach x).val.val = x.val := rfl

theorem attach_within {x : Costed α} {κ : Costs} {bound : Nat} (fits : x.Within κ bound) :
    (attach x).Within κ bound := fits

/-! ## Scans -/

/-- The elements of a vector as a list, by `Vector.toList` (`Library.toList`): the control of its
row. -/
@[inline] def toList {count : Nat} (items : Vector α count) : Costed (List α) :=
  ⟨items.toList, fun κ n => n = Library.toList.control (κ .visit) count,
    fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem toList_val {count : Nat} (items : Vector α count) : (toList items).val = items.toList :=
  rfl

theorem toList_within {count : Nat} (items : Vector α count) (κ : Costs) :
    (toList items).Within κ (Library.toList.control (κ .visit) count) :=
  fun _ same => Nat.le_of_eq same

/-- The elements of an array as a list, by `Array.toList` (`Library.toList`): the control of its
row. -/
@[inline] def arrayToList (items : Array α) : Costed (List α) :=
  ⟨items.toList, fun κ n => n = Library.toList.control (κ .visit) items.size,
    fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem arrayToList_val (items : Array α) : (arrayToList items).val = items.toList := rfl

theorem arrayToList_within (items : Array α) (κ : Costs) :
    (arrayToList items).Within κ (Library.toList.control (κ .visit) items.size) :=
  fun _ same => Nat.le_of_eq same

/-- A list without its first `count` elements, by `List.drop` (`Library.drop`): the control of
its row over the elements it drops. -/
@[inline] def drop (count : Nat) (items : List α) : Costed (List α) :=
  ⟨items.drop count, fun κ n => n = Library.drop.control (κ .visit) (min count items.length),
    fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem drop_val (count : Nat) (items : List α) : (drop count items).val = items.drop count :=
  rfl

/-- A drop is within its row's control over the count it drops. -/
theorem drop_within (count : Nat) (items : List α) (κ : Costs) :
    (drop count items).Within κ (Library.drop.control (κ .visit) count) :=
  fun _ same => by
    rw [same]
    exact Library.control_mono _ (Nat.min_le_left _ _)

/-- The indices below `count` in order, by `List.finRange` (`Library.finRange`): the control of
its row. -/
@[inline] def finRange (count : Nat) : Costed (List (Fin count)) :=
  ⟨List.finRange count, fun κ n => n = Library.finRange.control (κ .visit) count,
    fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem finRange_val (count : Nat) : (finRange count).val = List.finRange count := rfl

theorem finRange_within (count : Nat) (κ : Costs) :
    (finRange count).Within κ (Library.finRange.control (κ .visit) count) :=
  fun _ same => Nat.le_of_eq same

/-- The length of a list, by `List.length` (`Library.length`): the control of its row. -/
@[inline] def length (items : List α) : Costed Nat :=
  ⟨items.length, fun κ n => n = Library.length.control (κ .visit) items.length,
    fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem length_val (items : List α) : (length items).val = items.length := rfl

theorem length_within (items : List α) (κ : Costs) :
    (length items).Within κ (Library.length.control (κ .visit) items.length) :=
  fun _ same => Nat.le_of_eq same

/-- Whether `item` is an element of `items`, by the membership test of a list
(`Library.contains`): the control of its row, each visit charged one comparison (`compare`) as
well. -/
@[inline] def mem [DecidableEq α] (item : α) (items : List α) : Costed Bool :=
  ⟨decide (item ∈ items), fun κ n => n = Library.contains.control (κ .visit + κ .compare)
    items.length, fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem mem_val [DecidableEq α] (item : α) (items : List α) :
    (mem item items).val = decide (item ∈ items) := rfl

theorem mem_within [DecidableEq α] (item : α) (items : List α) (κ : Costs) :
    (mem item items).Within κ (Library.contains.control (κ .visit + κ .compare) items.length) :=
  fun _ same => Nat.le_of_eq same

/-- Whether two vectors are equal, by the equality of their arrays (`Library.vectorEq`): the
control of its row, each visit charged one comparison (`compare`) as well. -/
@[inline] def vectorEq [DecidableEq α] {count : Nat} (first second : Vector α count) :
    Costed Bool :=
  ⟨decide (first = second), fun κ n => n = Library.vectorEq.control (κ .visit + κ .compare) count,
    fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem vectorEq_val [DecidableEq α] {count : Nat} (first second : Vector α count) :
    (vectorEq first second).val = decide (first = second) := rfl

theorem vectorEq_within [DecidableEq α] {count : Nat} (first second : Vector α count) (κ : Costs) :
    (vectorEq first second).Within κ (Library.vectorEq.control (κ .visit + κ .compare) count) :=
  fun _ same => Nat.le_of_eq same

/-- The numbers below `count` in order, by `List.range` (`Library.range`): the control of its
row. -/
@[inline] def range (count : Nat) : Costed (List Nat) :=
  ⟨List.range count, fun κ n => n = Library.range.control (κ .visit) count,
    fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem range_val (count : Nat) : (range count).val = List.range count := rfl

theorem range_within (count : Nat) (κ : Costs) :
    (range count).Within κ (Library.range.control (κ .visit) count) :=
  fun _ same => Nat.le_of_eq same

/-- The elements of a list each with its position from `start`, by `List.zipIdx`
(`Library.zipIdx`): the control of its row. -/
@[inline] def zipIdx (items : List α) (start : Nat := 0) : Costed (List (α × Nat)) :=
  ⟨items.zipIdx start, fun κ n => n = Library.zipIdx.control (κ .visit) items.length,
    fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem zipIdx_val (items : List α) (start : Nat) :
    (zipIdx items start).val = items.zipIdx start := rfl

theorem zipIdx_within (items : List α) (start : Nat) (κ : Costs) :
    (zipIdx items start).Within κ (Library.zipIdx.control (κ .visit) items.length) :=
  fun _ same => Nat.le_of_eq same

/-- Two lists joined, by `++` (`Library.append`): the control of its row over the first list,
the only one it walks. -/
@[inline] def append (first second : List α) : Costed (List α) :=
  ⟨first ++ second, fun κ n => n = Library.append.control (κ .visit) first.length,
    fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem append_val (first second : List α) : (append first second).val = first ++ second := rfl

theorem append_within (first second : List α) (κ : Costs) :
    (append first second).Within κ (Library.append.control (κ .visit) first.length) :=
  fun _ same => Nat.le_of_eq same

/-- A vector with `head` put before `tail`, by `#v[head] ++ tail` (`Library.vectorAppend`): the
read of `head` into a new vector (`read`), charged at that vector after the operations that build
it and before the pass over `tail`, then the control of its row over `tail`, the only one it
walks. -/
@[inline] def prepend {count : Nat} (head : α) (tail : Vector α count) :
    Costed (Vector α (count + 1)) :=
  ⟨(#v[head] ++ tail).cast (Nat.add_comm 1 count),
    fun κ n => n = κ .read + Library.vectorAppend.control (κ .visit) count,
    fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem prepend_val {count : Nat} (head : α) (tail : Vector α count) :
    (prepend head tail).val = (#v[head] ++ tail).cast (Nat.add_comm 1 count) := rfl

theorem prepend_within {count : Nat} (head : α) (tail : Vector α count) (κ : Costs) :
    (prepend head tail).Within κ (κ .read + Library.vectorAppend.control (κ .visit) count) :=
  fun _ same => Nat.le_of_eq same

/-- A list in reverse order, by `List.reverse` (`Library.reverse`): the control of its row. -/
@[inline] def reverse (items : List α) : Costed (List α) :=
  ⟨items.reverse, fun κ n => n = Library.reverse.control (κ .visit) items.length,
    fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem reverse_val (items : List α) : (reverse items).val = items.reverse := rfl

theorem reverse_within (items : List α) (κ : Costs) :
    (reverse items).Within κ (Library.reverse.control (κ .visit) items.length) :=
  fun _ same => Nat.le_of_eq same

/-- The sum of a list of integers, by `List.sum` (`Library.sum`): the control of its row, each
visit charged the addition of its term (`sumTerm`) as well. -/
@[inline] def sum (items : List Int) : Costed Int :=
  ⟨items.sum, fun κ n => n = Library.sum.control (κ .visit + κ .sumTerm) items.length,
    fun _ => ⟨_, rfl, fun _ same => same⟩⟩

theorem sum_val (items : List Int) : (sum items).val = items.sum := rfl

theorem sum_within (items : List Int) (κ : Costs) :
    (sum items).Within κ (Library.sum.control (κ .visit + κ .sumTerm) items.length) :=
  fun _ same => Nat.le_of_eq same

end Costed

end Acorn
