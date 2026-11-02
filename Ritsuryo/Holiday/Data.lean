module

meta import Ritsuryo.Basis

@[expose] public section

namespace Ritsuryo.Holiday

inductive EntryKind where
  | national
  | treatedAsNational
  | specialLaw
  | rest
  deriving DecidableEq, Repr, Inhabited

structure Entry where
  month : Nat
  day : Nat
  name : String
  kind : EntryKind
  deriving DecidableEq, Repr, Inhabited

end Ritsuryo.Holiday
