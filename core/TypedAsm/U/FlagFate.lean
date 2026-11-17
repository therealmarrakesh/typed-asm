import TypedAsm.U.Term

/-!
# What can be said of a flag after an operation

Of each flag, an operation leaves it as it was, or leaves it defined, or
leaves it defined if another was, or nothing can be said. Here are those
four, what each means, and which holds of a shift by a known count and of a
multiplication.
-/

namespace TypedAsm.U

open TypedAsm

/-- The four flags. -/
inductive Flag
  | cf | zf | sf | of
  deriving DecidableEq

def _root_.TypedAsm.Flags.get (f : Flags) : Flag → Option Bool
  | .cf => f.cf
  | .zf => f.zf
  | .sf => f.sf
  | .of => f.of

/-- What an instruction does to a flag. -/
inductive Fate
  /-- It is as it was. -/
  | keeps
  /-- It is defined. -/
  | defines
  /-- It is defined, if another flag was: the one the instruction reads. -/
  | definesIf (y : Flag)
  /-- Neither can be said. -/
  | lost
  deriving DecidableEq

/-- What a fate says of a flag before and after, given all the flags
before. -/
def Fate.Holds : Fate → Flags → Option Bool → Option Bool → Prop
  | .keeps, _, old, new => new = old
  | .defines, _, _, new => new.isSome = true
  | .definesIf y, all, _, new => (all.get y).isSome = true → new.isSome = true
  | .lost, _, _, _ => True

/-- A shift or a rotation by a count written out. -/
def shiftFate (op : ShiftOp) (n : Nat) (x : Flag) : Fate :=
  if n = 0 then .keeps else
  match op, x with
  | _, .of => if n = 1 then .defines else .lost
  | .rol, .cf | .ror, .cf => .defines
  | .rol, _ | .ror, _ => .keeps
  | _, _ => .defines

/-- A multiplication: carry and overflow say whether the product fit. -/
def mulFate : Flag → Fate
  | .cf | .of => .defines
  | _ => .lost

end TypedAsm.U
