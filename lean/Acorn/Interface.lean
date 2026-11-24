import Acorn.Options
import Acorn.SignalValues
import Acorn.Timing

namespace Acorn.Features

structure Interface where
  symbols : PatchShape
  signals : List Discount
  actions : Word.Count
  words : Nat
  feedback : UInt64
  timing : Timing

abbrev Interface.layout (interface : Interface) : List Discount := .g99 :: interface.signals

def Interface.reserved (interface : Interface) (channel : UInt64) : Bool :=
  (channel - interface.feedback).toNat < interface.layout.length

structure Frame (interface : Interface) where
  words : List SensorWord
  bounded : words.length ≤ interface.words
  clear : ∀ word ∈ words, interface.reserved word.channel = false
  symbols : Patch interface.symbols
  signals : Cumulants interface.signals
  potentials : Vector Potential Acorn.FeatureConstants.skillCount
  achieved : Bool

structure Percept (interface : Interface) where
  frame : Frame interface
  reward : Binary32

end Acorn.Features
