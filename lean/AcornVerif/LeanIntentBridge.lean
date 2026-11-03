/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import LeanIntent.Confirmation
import LeanIntent.Degenerate
import LeanIntent.Implementation
import LeanIntent.Refinement
import LeanIntent.Statement

/-!
# Bridge to lean-intent

lean-intent (https://github.com/rbeauchamp/lean-intent, commit `9502fbe`) states what an owner
wants from one deliverable as an intent record, `LeanIntent.IntentRecord`: named properties of a
subject under named domain hypotheses, written before the subject's implementation is read. It
computes the record's adequacy obligations O1 to O5 with theorems fixing what each states, checks
the record against the degenerate subjects of its type, keeps the answers to the record's
consequences across revisions, and links an implementation to its record by refinement. A project
declares each record as a deliverable (`LeanIntent.Deliverable`), with its explanation and the
answers it keeps, and the owners' log those answers are read against (`LeanIntent.OwnersLog`); it
declares the implementation of each implemented deliverable (`LeanIntent.Implementation`), and
lean-intent's two checks, which Acorn's merge gate runs, read both from the build.

This module is the only importer of lean-intent among the modules of the proof library. The intent
records under `AcornVerif.Intent` reach lean-intent's declarations through it, so the provisioned
target `leanIntentBridge` builds exactly the lean-intent modules the proof library uses; no
executing module imports lean-intent. The gate's checker, the tool module `AcornTools.Intent`,
imports lean-intent's two readers itself.
-/
