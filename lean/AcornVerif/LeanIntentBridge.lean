/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import LeanIntent.Degenerate
import LeanIntent.Refinement
import LeanIntent.Statement

/-!
# Bridge to lean-intent

lean-intent (https://github.com/rbeauchamp/lean-intent, commit `30fe70d`) states what an owner
wants from one deliverable as an intent record, `LeanIntent.IntentRecord`: named properties of a
subject under named domain hypotheses, written before the subject's implementation is read. It
computes the record's adequacy obligations O1 to O5 with theorems fixing what each states, checks
the record against the degenerate subjects of its type, keeps the owner's answers to the record's
consequences across revisions, and links an implementation to its record by refinement.

This module is the only importer of lean-intent. The intent records under `AcornVerif.Intent`
reach lean-intent's declarations through it, so the provisioned target `leanIntentBridge` builds
exactly the lean-intent modules the proof library uses; no executing module imports lean-intent.
-/
