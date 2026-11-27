import AcornVerif.CurrentConcealedTargetRung

namespace AcornVerif.Targets.CurrentConcealedTargetRung
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetRung

def rung_learns : Prop :=
  witnessConfig.raw =
      { seed := 1, side := ⟨64, by decide⟩, dayLength := 2048, regrow := 400, foodInterval := 48,
        foodCap := 0, deerCap := 0, baseScale := ⟨0x41000000⟩ } ∧
    witnessLive.world = Host.World.empty witnessConfig ∧
    witnessLive.world.body.position.position.x.val = 32 ∧
    witnessLive.world.body.position.position.y.val = 32 ∧
    witnessLive.carried = ⟨⟨false, false, none, false, none, false, 0⟩, ⟨0⟩⟩ ∧
    ∃ (planning : PlanningSelection)
      (counted : List (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode
        witnessLive 7).Index),
      rungConstruction planning =
          AgentConstruction.standard 1 ⟨.primitive, .discounted⟩ planning .learnThenAct ∧
        (rungConstruction planning).profile = ⟨.primitiveOnly, .perStep, .declared, .learned⟩ ∧
        (rungConstruction planning).criterion = .discounted ∧
        (rungConstruction planning).order = .learnThenAct ∧
        (rungConstruction planning).config.seed = 1 ∧
        counted.Nodup ∧
        Kernel.SeparatesBy
          (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive 7)
          (fun _ => completion witnessConfig (rungConstruction planning).profile.taskMode 7) 7
          98 counted 288 (executedAgent (rungConstruction planning).initial.agent) ∧
        Kernel.RetainsBut
          (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive 7)
          (fun _ => completion witnessConfig (rungConstruction planning).profile.taskMode 7) 7
          864 144 (executedAgent (rungConstruction planning).initial.agent)

end AcornVerif.Targets.CurrentConcealedTargetRung
