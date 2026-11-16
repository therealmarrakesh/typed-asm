import TypedAsm.Tactic.Match

/-!
# What the matcher finds

A label's context is written with parameters; these check that the matcher
finds them from a context reached, by arithmetic on the terms. In each,
variable 0 is the unknown and the others are whatever they are. The matcher
is no part of what is trusted, so these are checked by running it.
-/

namespace Tests.Match

open TypedAsm TypedAsm.Sym TypedAsm.Sym.Match

/-- The number unknown 0 is found to be, from a pattern and a number. -/
def solved (p c : Num) : Option Num := ((num ⟨[0], []⟩ {} p c).num.find? (·.1 == 0)).map (·.2)

/-- The value unknown 0 is found to be, from a pattern and a value. -/
def solvedV (p c : Val) : Option Val := ((val ⟨[], [0]⟩ {} p c).val.find? (·.1 == 0)).map (·.2)

-- eight of the unknown against eight of something and eight more: one more of it
#guard solved (.mul (.lit 8) (.var 0)) (.add (.mul (.lit 8) (.var 1)) (.lit 8))
    = some (.add (.var 1) (.lit 1))
-- however either side is written
#guard solved (.mul (.var 0) (.lit 8)) (.mul (.lit 8) (.add (.var 1) (.lit 1)))
    = some (.add (.var 1) (.lit 1))
-- past a header of sixteen bytes
#guard solved (.add (.lit 16) (.mul (.lit 8) (.var 0))) (.add (.mul (.lit 8) (.var 1)) (.lit 24))
    = some (.add (.var 1) (.lit 1))
-- with another term on both sides
#guard solved (.add (.var 0) (.var 2)) (.add (.add (.var 1) (.var 2)) (.lit 3))
    = some (.add (.var 1) (.lit 3))
-- a number written out
#guard solved (.mul (.lit 24) (.var 0)) (.lit 72) = some (.lit 3)
-- nothing where it does not come out even, or would take away what is not there
#guard solved (.mul (.lit 8) (.var 0)) (.add (.mul (.lit 8) (.var 1)) (.lit 4)) = none
#guard solved (.add (.var 0) (.lit 8)) (.lit 4) = none
#guard solved (.add (.var 0) (.var 2)) (.var 1) = none

-- a value: the unknown itself, and the unknown among the terms of a sum
#guard solvedV (.var 0) (.add (.var 1) (.lit 8)) = some (.add (.var 1) (.lit 8))
#guard solvedV (.add (.var 0) (.lit 8)) (.add (.var 1) (.lit 24))
    = some (.add (.var 1) (.lit 16))
#guard solvedV (.add (.var 0) (.var 2)) (.add (.var 2) (.var 1)) = some (.var 1)
#guard solvedV (.add (.var 0) (.var 2)) (.var 1) = none

end Tests.Match
