import Acorn.Provenance
import Acorn.State

namespace Acorn.Features

inductive Cumulants : List Discount → Type where
  | nil : Cumulants []
  | cons {discount : Discount} {rest : List Discount} (origin : Option Departure)
      (value : Binary32) (tail : Cumulants rest) : Cumulants (discount :: rest)

end Acorn.Features
