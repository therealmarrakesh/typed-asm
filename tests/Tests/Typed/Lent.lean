import Tests.Typed.Laws
import LendProgram
import PairProgram

/-!
# The checker's tests: memory lent to a function, and memory handed back

A function is handed memory by being handed a region to hold. Its label
says what it takes and gives back, and what it hands its caller that the
caller did not have. The checker finds what is taken among what the caller
holds, a part of a region where that is what it is. The programs are those
of `examples/Lend` and `examples/Pair`: each is checked by the kernel as
this file is compiled, what the checker accepts and what it refuses.
-/

open TypedAsm TypedAsm.U

namespace Tests.Unified

/-! ## Part of a stack lent -/

/-- The program of `examples/Lend`, to end with status seven. -/
def pgLend : Prog :=
  { code := progCode (Asm.table Lend.base Lend.code), pre := preExits (· == 7) }

/-- The labels: `work` returning this, and `fill` taking so many bytes at
`rdi` and leaving these two values in the first sixteen. -/
def lendLabels (result : Val) (taken : Val) (first second : Val) : List U.Label :=
  [⟨Lend.entry, inProgram 4⟩,
   ⟨Asm.addr Lend.code Lend.base .work, inFunction (room := 24) (results := [(.rax, result)])⟩,
   ⟨Asm.addr Lend.code Lend.base .fill,
     inFunction (takes := [(.rdi, taken)]) (leaves := [(.rdi, [(0, first), (8, second)])])⟩]

-- sixteen bytes of `work`'s stack are `fill`'s for the call; what `fill`
-- leaves there is what `work` adds up
example : wholeOk Lend.code .start 4 pgLend (lendLabels 7 16 3 4) 80 = true := by decide +kernel
-- `work` does not return eight
example : wholeOk Lend.code .start 4 pgLend (lendLabels 8 16 3 4) 80 = false := by decide +kernel
-- `fill` does not leave five there
example : wholeOk Lend.code .start 4 pgLend (lendLabels 7 16 3 5) 80 = false := by decide +kernel
-- were `fill` to take twenty-four bytes, `work`'s return address would be
-- `fill`'s to write over: refused
example : wholeOk Lend.code .start 4 pgLend (lendLabels 7 24 3 4) 80 = false := by decide +kernel
-- and eight are not enough for what `fill` stores
example : wholeOk Lend.code .start 4 pgLend (lendLabels 7 8 3 4) 80 = false := by decide +kernel

/-! ## Two regions handed back -/

/-- The program of `examples/Pair`. -/
def pgPair : Prog := { code := progCode (Asm.table Pair.base Pair.code) }

/-- The labels: `two` handing its caller these. -/
def pairLabels (gives : List (Reg × Val)) : List U.Label :=
  [⟨Pair.entry, inProgram 2⟩,
   ⟨Asm.addr Pair.code Pair.base .two, inFunction (room := 8) (gives := gives)⟩]

-- a page at each of the two addresses returned
example : wholeOk Pair.code .start 2 pgPair (pairLabels [(.rax, 4096), (.rdx, 4096)]) 80
    = true := by decide +kernel
-- said to hand back only one, the caller has no second page to use: refused
example : wholeOk Pair.code .start 2 pgPair (pairLabels [(.rax, 4096)]) 80 = false := by
  decide +kernel
-- said to hand back two pages at the second address, it does not: refused
example : wholeOk Pair.code .start 2 pgPair (pairLabels [(.rax, 4096), (.rdx, 8192)]) 80
    = false := by decide +kernel

end Tests.Unified
