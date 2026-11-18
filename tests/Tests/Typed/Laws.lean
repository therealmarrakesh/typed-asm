import Tests.Typed.Sized
import Fact

/-!
# The checker's tests: functions an author defines, and laws

A term may be what a function the program's author defines gives of
values. Where the values are numbers, Lean's kernel computes it; and where
a term the machine came to is not the term wanted, a law the author has
proved may show them one value. The factorial of `examples/Fact` is the
case: each is checked by the kernel as this file is compiled, what the
checker accepts and what it refuses.
-/

open TypedAsm TypedAsm.U

namespace Tests.Unified

/-! ## Computed where the values are numbers -/

-- the factorial of five is a number, once computed
example : (Fact.fac 5).evalApps Fact.fns = .lit 120 := by decide +kernel
-- of a value not written out, it is left as it is
example : (Fact.fac (.var 3)).evalApps Fact.fns = Fact.fac (.var 3) := by decide +kernel
-- and so what is built on it is computed too
example : (Val.add (Fact.fac 3) (.lit 1)).evalApps Fact.fns = .lit 7 := by decide +kernel

/-! ## The same value, by a law -/

/-- What is known: the value `var 0` is not nought. -/
def notNought : List (Val × TyS) := [(.var 0, .range 1 (-1))]

-- one less than it, its factorial, times it: the factorial of it
example : sameBy Fact.fns Fact.laws notNought
    (.bin (.imul .w64) (Fact.fac (.add (.var 0) (.lit (-1)))) (.var 0)) (Fact.fac (.var 0))
    = true := by decide +kernel
-- however one less is written
example : sameBy Fact.fns Fact.laws notNought
    (.bin (.imul .w64) (Fact.fac (.add (.lit (-1)) (.var 0))) (.var 0)) (Fact.fac (.var 0))
    = true := by decide +kernel
-- not where nothing says it is not nought
example : sameBy Fact.fns Fact.laws []
    (.bin (.imul .w64) (Fact.fac (.add (.var 0) (.lit (-1)))) (.var 0)) (Fact.fac (.var 0))
    = false := by decide +kernel
-- not times another value
example : sameBy Fact.fns Fact.laws notNought
    (.bin (.imul .w64) (Fact.fac (.add (.var 0) (.lit (-1)))) (.var 1)) (Fact.fac (.var 0))
    = false := by decide +kernel
-- and not with no law
example : sameBy Fact.fns [] notNought
    (.bin (.imul .w64) (Fact.fac (.add (.var 0) (.lit (-1)))) (.var 0)) (Fact.fac (.var 0))
    = false := by decide +kernel

/-! ## A function's result, for every argument -/

/-- The program of `examples/Fact`, with the laws given and the status it is
to end with. -/
def pgFac (laws : List LawS) (status : BitVec 32) : Prog :=
  { Fact.pg with laws := laws, pre := preExits (· == status) }

/-- The labels, the function returning this. -/
def facLabels (result : Val) : List U.Label :=
  [⟨Fact.entry, inProgram 11⟩,
   ⟨Asm.addr Fact.code Fact.base .fact,
     inFunction (known := smallArg) (room := (Val.was .rdi) <<< 4) (results := [(.rax, result)])⟩]

/-- The factorial of the argument the function was entered with. -/
def facOfArg : Val := Fact.fac (Val.was .rdi).lift

-- the function returns the factorial of its argument, for every argument,
-- and the program ends with the factorial of five
example : wholeOk Fact.code .start 11 (pgFac Fact.laws 120) (facLabels facOfArg) 80 = true := by
  decide +kernel
-- not with 121
example : wholeOk Fact.code .start 11 (pgFac Fact.laws 121) (facLabels facOfArg) 80 = false := by
  decide +kernel
-- without the laws, what the machine computes is not seen to be the factorial
example : wholeOk Fact.code .start 11 (pgFac [] 120) (facLabels facOfArg) 80 = false := by
  decide +kernel
-- and it is not one more than the factorial
example : wholeOk Fact.code .start 11 (pgFac Fact.laws 120)
    (facLabels (.add facOfArg (.lit 1))) 80 = false := by decide +kernel

end Tests.Unified
