import Canonical.Main

axiom HashSet (X : Type) [BEq X] [Hashable X] : Type

axiom empty [BEq X] [Hashable X] : HashSet X

noncomputable def getEmpty : HashSet Nat := by
  canonical [empty]

#check Nat.decEq.match_1
#check Nat.decEq
