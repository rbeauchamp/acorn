/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Init

/-!
# The constant stretches of the agent's step

A **site** is a stretch of an executed definition whose work is a constant of the compiled
code, together with every such definition it calls. It contains no loop, or only loops whose
trip count is a constant of the code and whose bodies are such stretches: the three options,
the four meta actions, the 32 samples of a projection, the at most 15 doublings of the
ranked width's search and the at most 33 steps of `Portable.pow`. A twin charges a site each
time the executed definition runs its stretch; every loop whose trip count is not a
constant of the code is a combinator of `AcornVerif.Resource.Work` instead. A site's cost
includes evaluating the ranked width where its stretch evaluates it, and a twin that reads
the width before a loop charges `rankWidth`.

A cost model assigns each site a cost, and every work bound holds for every cost model. No
theorem here derives the cost of a site in word operations; the scalar operations that the
native resource audit bounds are the operations with an extracted cost.
-/

namespace AcornVerif.Resource

/-- The constant stretches the twins charge. -/
inductive Site where
  /-- The control of one visit of a loop: its test, its advance and its branch. -/
  | visit
  /-- One binary32 addition of an ordered sum, with the read of its term. -/
  | sumTerm
  /-- The read of one stored element into a list or vector being built. -/
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
  /-- A fresh transient record apart from its nine register vectors. -/
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
  /-- The two discount powers of a frozen-decision credit. -/
  | policyOpen
  /-- The store of a frozen policy snapshot. -/
  | snapshot
  /-- One learner's contribution to a derived exploration rate. -/
  | rateTerm
  /-- The projection of a derived exploration rate, with the fresh-feature fallback. -/
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
  /-- One sensor word hashed into a feature slot for one tiling. -/
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
  /-- An assignment's feature slot computed before its membership test. -/
  | assignmentPotential
  /-- A declared potential read from the frame's declared values. -/
  | declaredPotential
  /-- An option's termination tests: goal, duration and the stopping comparison. -/
  | decide
  /-- A started invocation's activation and continuation records. -/
  | beginOption
  /-- An option step's shaped cumulant, its activation advance and its records. -/
  | optionStep
  /-- An option's terminal cumulant and stopping value. -/
  | terminateOption
  /-- A stopped trajectory's stopping error and the skill record. -/
  | stopFollowing
  /-- A settled trajectory's shaped cumulant, its tree-backup error and the skill record. -/
  | settleFollowing
  /-- A planning look-ahead's backed-up target and its result record. -/
  | lookAhead
  /-- A backup's store of its prediction cache and planning error. -/
  | backupClose
  /-- A planning boundary's work count, its search-control advance and its result. -/
  | planBoundary
  /-- A fresh learner's rails and record, apart from its vectors. -/
  | initialState
  /-- One unit's Demon-0 weight tested for a ranking candidate. -/
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
  /-- Selection's branch tests, phase write and the stopping estimate. -/
  | select
  /-- The agent's clock advance and the chosen value's record. -/
  | choose
  deriving DecidableEq, Repr

/-- A cost for each site. -/
abbrev Costs := Site → Nat

end AcornVerif.Resource
