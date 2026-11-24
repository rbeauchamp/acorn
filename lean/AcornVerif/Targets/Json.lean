import Acorn.Json

namespace AcornVerif.Targets.Json
open Acorn Acorn.Json

def parse_complete : Prop :=
  ∀ text v, Grammar.Text text.toList v → Json.parse text = .ok v

end AcornVerif.Targets.Json
