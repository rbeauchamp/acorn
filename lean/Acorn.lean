/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.AgentAdmission
import Acorn.Host.AgentAudit
import Acorn.Host.Checkpoint.IO
import Acorn.Average
import Acorn.Handcrafted.PredictionControl
import Acorn.Handcrafted.TemporalControl
import Acorn.Shuffle
import Acorn.SwiftTd
import Acorn.FeatureModelInput
import Acorn.FeatureReferences
import Acorn.Handcrafted.FeatureProfile
import Acorn.Host.Ansi
import Acorn.Host.Baseline
import Acorn.Host.Endurance
import Acorn.Host.TemporalProfile

/-!
# Current Acorn executable foundations

Machine encodings, arithmetic, local approximations, indexed state admission
and seeded word streams are maintained here, together with the complete
current SwiftTD learner (`Acorn.SwiftTd`) and receiver-owned feature encoding,
ranking, refresh, retirement and restoration. The host modules supply the current
world, tasks, CLI admission and streaming runner with explicit full-agent callbacks.
Declared host/profile composition enters through the reviewed composition roots.
`Acorn.Constants` supplies the shared constant interface. Native application
entry points live in `NativeApp`.
-/
