/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentBackupBounds
import AcornVerif.CurrentConstants
import AcornVerif.CurrentRetirement
import AcornVerif.CurrentRetirementRounding
import AcornVerif.Axioms
import Acorn
import AcornVerif.CurrentRng
import AcornVerif.CurrentFloat
import AcornVerif.CurrentPower
import AcornVerif.CurrentExponential
import AcornVerif.CurrentArithmetic
import AcornVerif.CurrentOrder
import AcornVerif.CurrentOperations
import AcornVerif.CurrentDivision
import AcornVerif.CurrentIntervals
import AcornVerif.CurrentReduction
import AcornVerif.CurrentSeries
import AcornVerif.CurrentPortable
import AcornVerif.CurrentLogarithm
import AcornVerif.CurrentPrediction
import AcornVerif.CurrentState
import AcornVerif.CurrentLearnerArithmetic
import AcornVerif.CurrentLearner
import AcornVerif.CurrentFloor
import AcornVerif.CurrentWorld
import AcornVerif.CurrentRunner
import AcornVerif.CurrentFeatureConsumers
import AcornVerif.CurrentControl
import AcornVerif.CurrentAgent
import AcornVerif.CurrentCheckpoint
import AcornVerif.CurrentModels
import AcornVerif.Checkpoint
import AcornVerif.AverageReward
import AcornVerif.ModelConstants
import AcornVerif.Projection
import AcornVerif.StepSize
import AcornVerif.MetaGradient
import AcornVerif.Options
import AcornVerif.Energy
import AcornVerif.Exploration
import AcornVerif.Traces
import AcornVerif.Retirement
import AcornVerif.BigWorld
import AcornVerif.Rng
import AcornVerif.WorldGoals

/-!
# Executable contracts and mathematical analysis

Current* modules verify the imported Lean execution owners. Other modules retain
mathematical identities and conditional algorithm contracts supporting the
current mechanisms. Each theorem states its domain and hypotheses; mathematical
identities establish execution properties only through their checked linkage.

Every maintained theorem enters the compiler-owned axiom inventory. The only
admitted axiom dependencies are propext, Classical.choice and Quot.sound. Native
compiler/runtime, reviewed tooling and OS boundaries remain explicit. No theorem
count, source digest or successful build establishes useful learning.
-/
