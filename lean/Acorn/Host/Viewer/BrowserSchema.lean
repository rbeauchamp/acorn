import Acorn.Host.Viewer.CoreTelemetry
import Acorn.Host.Viewer.ControlTelemetry

namespace Acorn.Host.Viewer
open Features Handcrafted

def browserSchema : List (String × TelemetryShape) :=
  [("schema_version", TelemetryShape.natural), ("source_sha256", TelemetryShape.text),
  ("build_sha256", TelemetryShape.text), ("audit_digest", TelemetryShape.text), ("run_id", TelemetryShape.text),
  ("agent_epoch", TelemetryShape.natural), ("origin", TelemetryShape.text), ("timestamp_ms", TelemetryShape.natural),
  ("update_us", TelemetryShape.natural), ("environment_us", TelemetryShape.natural),
  ("process_uptime_ms", TelemetryShape.natural),
  ("process_started_ms", TelemetryShape.natural), ("core_rss_bytes", TelemetryShape.natural.optional),
  ("checkpoint_bytes", TelemetryShape.natural.optional), ("checkpoint_write_us", TelemetryShape.natural.optional),
  ("checkpoint_failures", TelemetryShape.natural), ("telemetry_refusals", TelemetryShape.natural),
  ("telemetry_drops", TelemetryShape.natural), ("goal_count", TelemetryShape.natural),
  ("attempt_cap", TelemetryShape.natural), ("step_cap", TelemetryShape.natural), ("cycle_cap", TelemetryShape.natural),
  ("goal_progress_invalid", TelemetryShape.flag),
  ("goal_progress_cycle", TelemetryShape.natural),
  ("goal_progress_resolved", TelemetryShape.natural),
  ("goal_progress_attempt", TelemetryShape.natural),
  ("goal_progress_achieved", TelemetryShape.natural),
  ("goal_progress_completed_cycle", TelemetryShape.natural.optional),
  ("goal_progress_completed_achieved", TelemetryShape.natural.optional),
  ("goal_progress_score", TelemetryShape.natural.optional),
  ("curriculum_names", .sequence .text),
  ("curriculum_failed_attempts", .sequence .natural),
  ("curriculum_success_steps", .sequence (.optional .natural)),
  ("world_step", TelemetryShape.natural), ("seed", TelemetryShape.natural), ("side", TelemetryShape.natural),
  ("day_length", TelemetryShape.natural), ("regrow", TelemetryShape.natural), ("food_interval", TelemetryShape.natural),
  ("food_cap", TelemetryShape.natural), ("deer_cap", TelemetryShape.natural), ("x", TelemetryShape.integer),
  ("y", TelemetryShape.integer), ("facing", TelemetryShape.natural), ("energy", TelemetryShape.natural),
  ("wood", TelemetryShape.natural), ("stone", TelemetryShape.natural), ("food", TelemetryShape.natural),
  ("gold", TelemetryShape.natural), ("axe", TelemetryShape.flag), ("boat", TelemetryShape.flag),
  ("action", TelemetryShape.natural), ("reward", TelemetryShape.binary32), ("done", TelemetryShape.flag),
  ("ev", TelemetryShape.natural), ("goal", TelemetryShape.natural), ("attempt", TelemetryShape.natural),
  ("tier", TelemetryShape.natural), ("cycle", TelemetryShape.natural), ("gkind", TelemetryShape.goalKind),
  ("gitem", TelemetryShape.goalItem), ("gx", TelemetryShape.integer), ("gy", TelemetryShape.integer),
  ("gn", TelemetryShape.natural), ("tiles", TelemetryShape.array 121 TelemetryShape.natural),
  ("tile_extra", TelemetryShape.array 121 TelemetryShape.natural), ("end", TelemetryShape.flag),
  ("lifetime_step", TelemetryShape.natural), ("reward_rate", TelemetryShape.binary32), ("eps", TelemetryShape.binary32),
  ("mean_alpha", TelemetryShape.binary32), ("a_ctl", TelemetryShape.binary32), ("a_dem", TelemetryShape.binary32),
  ("alpha_control_all", TelemetryShape.array 9 TelemetryShape.binary32),
  ("alpha_meta_all", TelemetryShape.array 4 TelemetryShape.binary32),
  ("alpha_option_all", TelemetryShape.array 27 TelemetryShape.binary32),
  ("alpha_demon_all", TelemetryShape.array 11 TelemetryShape.binary32),
  ("alpha_models", TelemetryShape.array 9 TelemetryShape.binary32),
  ("credit_control", TelemetryShape.array 9 TelemetryShape.natural),
  ("credit_meta", TelemetryShape.array 4 TelemetryShape.natural),
  ("credit_options", TelemetryShape.array 27 TelemetryShape.natural),
  ("credit_demons", TelemetryShape.array 11 TelemetryShape.natural),
  ("credit_models", TelemetryShape.array 9 TelemetryShape.natural),
  ("option_model_rewards", TelemetryShape.array 3 TelemetryShape.binary32),
  ("option_model_continuations", TelemetryShape.array 3 TelemetryShape.binary32),
  ("option_model_durations", TelemetryShape.array 3 TelemetryShape.binary32),
  ("planning_errors", TelemetryShape.array 3 TelemetryShape.binary32), ("planning_steps", TelemetryShape.natural),
  ("decision_source", TelemetryShape.text), ("skill", TelemetryShape.natural), ("explored", TelemetryShape.flag),
  ("control", TelemetryShape.array 9 TelemetryShape.binary32), ("meta", TelemetryShape.array 4 TelemetryShape.binary32),
  ("action_probabilities", TelemetryShape.array 9 TelemetryShape.binary32),
  ("meta_probabilities", TelemetryShape.array 4 TelemetryShape.binary32), ("meta_action", TelemetryShape.natural),
  ("option_start", TelemetryShape.natural), ("option_end_skill", TelemetryShape.natural),
  ("option_end_duration", TelemetryShape.natural), ("option_end_reason", TelemetryShape.natural),
  ("option_elapsed", TelemetryShape.natural), ("lifetime_reward_sum", TelemetryShape.binary64),
  ("lifetime_reward_count", TelemetryShape.natural),
  ("lifetime_reward_family_sum", TelemetryShape.array 4 TelemetryShape.binary64),
  ("lifetime_reward_family_count", TelemetryShape.array 4 TelemetryShape.natural),
  ("lifetime_reward_history_sum", TelemetryShape.array 64 TelemetryShape.binary64),
  ("lifetime_reward_history_count", TelemetryShape.array 64 TelemetryShape.natural),
  ("lifetime_error_history_sum", TelemetryShape.array 64 TelemetryShape.binary64),
  ("lifetime_error_history_count", TelemetryShape.array 64 TelemetryShape.natural),
  ("lifetime_error_sum", TelemetryShape.array 11 TelemetryShape.binary64),
  ("lifetime_error_count", TelemetryShape.array 11 TelemetryShape.natural),
  ("settled_return", TelemetryShape.array 11 TelemetryShape.binary32),
  ("settled_error", TelemetryShape.array 11 TelemetryShape.binary32),
  ("lifetime_option_started", TelemetryShape.array 3 TelemetryShape.natural),
  ("lifetime_option_completed", TelemetryShape.array 3 TelemetryShape.natural),
  ("lifetime_option_duration", TelemetryShape.array 3 TelemetryShape.natural),
  ("lifetime_option_end_reasons", TelemetryShape.array 9 TelemetryShape.natural),
  ("lifetime_goal_attempts", TelemetryShape.array 4 TelemetryShape.natural),
  ("lifetime_goal_successes", TelemetryShape.array 4 TelemetryShape.natural),
  ("lifetime_goal_steps", TelemetryShape.array 4 TelemetryShape.natural),
  ("lifetime_cycle_attempts", TelemetryShape.array 64 TelemetryShape.natural),
  ("lifetime_cycle_successes", TelemetryShape.array 64 TelemetryShape.natural),
  ("lifetime_cycle_steps", TelemetryShape.array 64 TelemetryShape.natural),
  ("agreement_version", TelemetryShape.natural),
  ("agreement_scale", TelemetryShape.natural),
  ("agreement_started", TelemetryShape.natural.optional),
  ("agreement_stopped", TelemetryShape.flag),
  ("agreement_score", TelemetryShape.natural.optional),
  ("agreement_text", TelemetryShape.text.optional),
  ("agreement_error", TelemetryShape.natural.optional),
  ("agreement_channel_score", .array demonLayout.length (TelemetryShape.natural.optional)),
  ("agreement_channel_text", .array demonLayout.length (TelemetryShape.text.optional)),
  ("agreement_channel_error", .array demonLayout.length (TelemetryShape.natural.optional)),
  ("agreement_count", .array demonLayout.length (TelemetryShape.text)),
  ("agreement_pending", .array demonLayout.length (TelemetryShape.natural)),
  ("agreement_censored", .array demonLayout.length (TelemetryShape.text)),
  ("agreement_status", .array demonLayout.length (TelemetryShape.text)),
  ("agreement_horizon", .array demonLayout.length (TelemetryShape.natural)),
  ("agreement_start_first", .array demonLayout.length (TelemetryShape.natural.optional)),
  ("agreement_start_last", .array demonLayout.length (TelemetryShape.natural.optional)),
  ("agreement_settlement_first", .array demonLayout.length (TelemetryShape.natural.optional)),
  ("agreement_settlement_last", .array demonLayout.length (TelemetryShape.natural.optional)),
  ("agreement_tail", .array demonLayout.length (TelemetryShape.natural.optional)),
  ("agreement_rounding", .array demonLayout.length (TelemetryShape.natural.optional)),
  ("agreement_history_clock", .array FeatureConstants.historyBins (TelemetryShape.natural.optional)),
  ("agreement_history_score", .array FeatureConstants.historyBins (TelemetryShape.natural.optional)),
  ("checkpoint_format", TelemetryShape.natural), ("control_criterion", TelemetryShape.natural),
  ("weight_space", TelemetryShape.natural), ("primitive_count", TelemetryShape.natural),
  ("meta_count", TelemetryShape.natural), ("skill_count", TelemetryShape.natural),
  ("option_end_count", TelemetryShape.natural), ("demon_count", TelemetryShape.natural),
  ("learner_count", TelemetryShape.natural), ("history_bins", TelemetryShape.natural),
  ("cycle_bins", TelemetryShape.natural), ("exact_cycles", TelemetryShape.natural),
  ("settle_stride", TelemetryShape.natural), ("settle_remaining", TelemetryShape.binary32),
  ("n_tilings", TelemetryShape.natural), ("imprint_units", TelemetryShape.natural),
  ("retire_step", TelemetryShape.natural.optional), ("retire_unit", TelemetryShape.natural.optional),
  ("retire_count", TelemetryShape.natural), ("subtask_policy", TelemetryShape.text),
  ("subtask_unit", TelemetryShape.array 3 TelemetryShape.natural.optional),
  ("subtask_bonus", TelemetryShape.array 3 TelemetryShape.binary32),
  ("action_names", TelemetryShape.array 9 TelemetryShape.text),
  ("meta_names", TelemetryShape.array 4 TelemetryShape.text),
  ("skill_names", TelemetryShape.array 3 TelemetryShape.text),
  ("goal_family_names", TelemetryShape.array 4 TelemetryShape.text),
  ("demons", TelemetryShape.array 11 TelemetryShape.binary32),
  ("cums", TelemetryShape.array 11 TelemetryShape.binary32),
  ("demon_names", TelemetryShape.array 11 TelemetryShape.text),
  ("demon_target_policy", TelemetryShape.array 11 TelemetryShape.text),
  ("demon_gamma", TelemetryShape.array 11 TelemetryShape.binary32),
  ("demon_horizon", TelemetryShape.array 11 TelemetryShape.binary32)]

def stringSortKey (s : String) : Nat :=
  s.toByteArray.data.toList.foldl (fun acc b => (acc * 131 + b.toNat + 1) % 4294967291) 0

private inductive NatTree where
  | leaf
  | node (val : Nat) (left right : NatTree)

private def NatTree.contains (x : Nat) : NatTree → Bool
  | .leaf => false
  | .node v l r =>
    if x < v then l.contains x else if v < x then r.contains x else true

private def NatTree.insertFresh (x : Nat) : NatTree → Option NatTree
  | .leaf => some (.node x .leaf .leaf)
  | .node v l r =>
    if x < v then (l.insertFresh x).map fun l' => .node v l' r
    else if v < x then (r.insertFresh x).map fun r' => .node v l r'
    else none

private theorem NatTree.insertFresh_spec : ∀ {t t' : NatTree} {x : Nat},
    t.insertFresh x = some t' →
    t.contains x = false ∧ t'.contains x = true ∧
      ∀ y, t.contains y = true → t'.contains y = true
  | .leaf, t', x, h => by
    simp only [NatTree.insertFresh, Option.some.injEq] at h
    subst h
    refine ⟨rfl, ?_, fun _ hy => by simp [NatTree.contains] at hy⟩
    simp [NatTree.contains, Nat.lt_irrefl]
  | .node v l r, t', x, h => by
    simp only [NatTree.insertFresh] at h
    by_cases hlt : x < v
    · simp only [hlt, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨l', hl', rfl⟩ := h
      obtain ⟨habs, hpres, hmono⟩ := NatTree.insertFresh_spec hl'
      refine ⟨by simp [NatTree.contains, hlt, habs], by simp [NatTree.contains, hlt, hpres], ?_⟩
      intro y hy
      simp only [NatTree.contains] at hy ⊢
      split at hy
      · rename_i hyl; simp only [hyl, ↓reduceIte]; exact hmono y hy
      · rename_i hyl; simp only [hyl, ↓reduceIte]; exact hy
    · by_cases hgt : v < x
      · simp only [hlt, hgt, ↓reduceIte, Option.map_eq_some_iff] at h
        obtain ⟨r', hr', rfl⟩ := h
        obtain ⟨habs, hpres, hmono⟩ := NatTree.insertFresh_spec hr'
        refine ⟨by simp [NatTree.contains, hlt, hgt, habs],
          by simp [NatTree.contains, hlt, hgt, hpres], ?_⟩
        intro y hy
        simp only [NatTree.contains] at hy ⊢
        split at hy
        · rename_i hyl; simp only [hyl, ↓reduceIte]; exact hy
        · rename_i hyl
          simp only [hyl, ↓reduceIte]
          split at hy
          · rename_i hyr; simp only [hyr, ↓reduceIte]; exact hmono y hy
          · rename_i hyr; simp only [hyr, ↓reduceIte]
      · simp [hlt, hgt] at h

def natListDistinct (xs : List Nat) : Bool :=
  go xs .leaf
where
  go : List Nat → NatTree → Bool
    | [], _ => true
    | x :: rest, t =>
      match t.insertFresh x with
      | none => false
      | some t' => go rest t'

private theorem natListDistinct_go_spec : ∀ {xs : List Nat} {t : NatTree},
    natListDistinct.go xs t = true →
    xs.Nodup ∧ ∀ z, t.contains z = true → z ∉ xs
  | [], _, _ => ⟨List.nodup_nil, fun _ _ h => by cases h⟩
  | x :: rest, t, h => by
    simp only [natListDistinct.go] at h
    cases hins : t.insertFresh x with
    | none => simp [hins] at h
    | some t' =>
      simp only [hins] at h
      obtain ⟨habs, hpres, hmono⟩ := NatTree.insertFresh_spec hins
      obtain ⟨hnd, hdisj⟩ := natListDistinct_go_spec h
      refine ⟨List.nodup_cons.mpr ⟨hdisj x hpres, hnd⟩, fun z hz hmem => ?_⟩
      rcases List.mem_cons.mp hmem with rfl | hrest
      · rw [habs] at hz; cases hz
      · exact hdisj z (hmono z hz) hrest

private theorem nodup_of_map {α β : Type} (f : α → β) : ∀ {xs : List α},
    (xs.map f).Nodup → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: rest, h => by
    rw [List.map_cons, List.nodup_cons] at h
    exact List.nodup_cons.mpr
      ⟨fun hmem => h.1 (List.mem_map.mpr ⟨x, hmem, rfl⟩), nodup_of_map f h.2⟩

theorem nodup_of_distinct_keys {α : Type} (key : α → Nat) (xs : List α)
    (distinct : natListDistinct (xs.map key) = true) :
    xs.Nodup :=
  nodup_of_map key (natListDistinct_go_spec distinct).1

theorem eq_of_mem_of_nodup_fst {α β : Type} : ∀ {l : List (α × β)} {k : α} {v₁ v₂ : β},
    (l.map Prod.fst).Nodup → (k, v₁) ∈ l → (k, v₂) ∈ l → v₁ = v₂
  | [], _, _, _, _, h₁, _ => by cases h₁
  | (_, _) :: rest, _, v₁, v₂, hnd, h₁, h₂ => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h₁ with e₁ | m₁ <;> rcases List.mem_cons.mp h₂ with e₂ | m₂
    · cases e₁; cases e₂; rfl
    · cases e₁
      exact absurd (List.mem_map.mpr ⟨(_, v₂), m₂, rfl⟩) hnd.1
    · cases e₂
      exact absurd (List.mem_map.mpr ⟨(_, v₁), m₁, rfl⟩) hnd.1
    · exact eq_of_mem_of_nodup_fst hnd.2 m₁ m₂

theorem browserSchema_distinct : (browserSchema.map Prod.fst).Nodup :=
  nodup_of_distinct_keys stringSortKey (browserSchema.map Prod.fst) (by decide +kernel)

set_option maxRecDepth 4096 in
theorem browserSchema_execution {config : Features.Config} {dimension : Dimension}
    (context : TelemetryContext) (frame : StepFrame (AgentObservation config dimension))
    (terminal : Bool) : telemetrySchema (coreTelemetry context frame terminal) = browserSchema := by
  rfl

inductive BrowserRule where
  | shape (value : TelemetryShape)
  | exact (value : Nat)
  | tags (values : List String)
  | hex (width : Nat)
  | belowField (field : String)
  | atMost (field : String)
  | lengthField (field : String)
  | each (rule : BrowserRule)
  | range (upper : Nat)
  | nullable (rule : BrowserRule)
  | list (maximum : Nat) (element : BrowserRule)
  | either (left right : BrowserRule)
  | positive
  | decimal (maximum : Nat)

def browserRules : List (String × BrowserRule) :=
  [("curriculum_names", .lengthField "goal_count"),
   ("curriculum_failed_attempts", .lengthField "goal_count"),
   ("curriculum_success_steps", .lengthField "goal_count"),
   ("curriculum_failed_attempts", .each (.atMost "attempt_cap")),
   ("curriculum_success_steps", .each (.atMost "step_cap"))] ++
  [("schema_version", .exact telemetrySchemaVersion),
   ("goal_progress_score", .nullable (.range 1001)),
   ("goal_progress_resolved", .atMost "goal_count"),
    ("goal_progress_attempt", .atMost "attempt_cap"),
   ("goal_progress_achieved", .atMost "goal_progress_resolved"),
   ("goal_progress_completed_achieved", .atMost "goal_count"),
   ("goal_progress_completed_cycle", .atMost "goal_progress_cycle"),
   ("agreement_version", .exact 1),
   ("agreement_scale", .exact Agreement.displayScale),
   ("agreement_score", .nullable (.range (Agreement.displayScale + 1))),
   ("agreement_error", .nullable (.range (Agreement.displayScale + 1))),
   ("agreement_channel_score", .each (.nullable (.range (Agreement.displayScale + 1)))),
   ("agreement_channel_error", .each (.nullable (.range (Agreement.displayScale + 1)))),
   ("agreement_pending", .each (.range (FeatureConstants.pendingSamples + 1))),
   ("agreement_count", .each (.decimal Agreement.countLimit)),
   ("agreement_censored", .each (.decimal Agreement.countLimit)),
   ("agreement_horizon", .each (.range (FeatureConstants.maxSettlement + 1))),
   ("agreement_tail", .each (.nullable (.range (Agreement.displayScale + 1)))),
   ("agreement_rounding", .each (.nullable (.range (Agreement.displayScale + 1)))),
   ("agreement_history_score", .each (.nullable (.range (Agreement.displayScale + 1)))),
   ("agreement_status", .each (.tags
     ["invalid", "saturated", "partially censored", "censored", "pending", "complete", "empty"])),
   ("primitive_count", .exact FeatureConstants.primitiveCount),
   ("meta_count", .exact FeatureConstants.metaActionCount),
   ("skill_count", .exact FeatureConstants.skillCount),
   ("demon_count", .exact FeatureConstants.demonCount),
   ("option_end_count", .exact 3),
   ("history_bins", .exact FeatureConstants.historyBins),
   ("cycle_bins", .exact FeatureConstants.cycleBins),
   ("exact_cycles", .exact FeatureConstants.exactCycles),
   ("learner_count", .exact telemetryLearnerCount),
   ("control_criterion", .range 2),
   ("action", .range FeatureConstants.primitiveCount), ("facing", .range 4),
   ("skill", .either (.range FeatureConstants.skillCount) (.exact 255)),
   ("option_start", .either (.range FeatureConstants.skillCount) (.exact 255)),
   ("option_end_skill", .either (.range FeatureConstants.skillCount) (.exact 255)),
   ("option_end_reason", .either (.range 3) (.exact 255)),
   ("meta_action", .either (.range FeatureConstants.metaActionCount) (.exact 255)),
   ("ev", .range 64), ("side", .positive),
   ("run_id", .hex 16), ("audit_digest", .hex 16),
   ("source_sha256", .hex 64), ("build_sha256", .hex 64),
   ("origin", .tags ["fresh", "resumed", "cleared"]),
   ("decision_source", .tags ["primitive", "exploration_start", "exploration_continuation", "option"]),
   ("subtask_policy", .tags ["learned", "hand_authored"]),
   ("subtask_unit", .each (.belowField "imprint_units")),
   ("subtask_unit", .each (.nullable (.range (2 ^ 31)))),
   ("retire_unit", .belowField "imprint_units"), ("retire_step", .atMost "lifetime_step"),
   ("tiles", .each (.range 8)), ("tile_extra", .each (.range 256))]

theorem browserRules_goal_separation :
    ∀ entry ∈ browserRules, entry.1 ≠ "gkind" ∧ entry.1 ≠ "gitem" := by
  decide

inductive BrowserRefusal where
  | schema
  | cardinality
  | missingField
  | malformed

def BrowserRefusal.tag : BrowserRefusal → String
  | .schema => "schema" | .cardinality => "cardinality"
  | .missingField => "missingField" | .malformed => "malformed"

def BrowserRefusal.all : List BrowserRefusal :=
  [.schema, .cardinality, .missingField, .malformed]

theorem BrowserRefusal.all_complete (refusal : BrowserRefusal) :
    refusal ∈ BrowserRefusal.all := by
  cases refusal <;> simp [BrowserRefusal.all]

def browserEnvelopeRules : List (String × BrowserRule) :=
  [("run_id", .hex 16), ("agent_epoch", .shape .natural),
   ("timestamp_ms", .shape .natural), ("lifetime_step", .shape .natural),
   ("world_step", .shape .natural)]

def browserControlRules : List (String × BrowserRule) :=
  [("runId", .hex 16), ("agentEpoch", .shape .natural),
   ("transition", .tags ["initialized", "start_requested", "stop_requested", "clear_requested",
     "core_started", "core_stopped", "restart_scheduled", "archiving", "cleared", "failed"]),
   ("transitionReason", .shape .text), ("reason", .shape .text),
   ("actual", .tags (Phase.representatives.map Phase.controlTag)),
   ("desired", .tags ["running", "stopped"]), ("seed", .shape .natural),
   ("checkpointRefused", .shape .flag), ("clearDisabled", .shape (.optional .text)),
   ("terminalWarning", .shape (.optional .text)),
   ("tail", .list 6 (.shape .text))]

def browserMapRules : List (String × BrowserRule) :=
  [("runId", .hex 16), ("side", .shape .natural), ("side", .positive), ("side", .range 4097),
   ("seed", .shape .natural), ("kinds", .shape .text), ("partial", .shape .flag)]

end Acorn.Host.Viewer
