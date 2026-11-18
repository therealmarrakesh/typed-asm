import Tests.Typed.Made
import TypedAsm.U.Explain

/-!
# The checker's tests: why a program is refused

Where a check fails, what is said of it: which instruction, what it reads
or writes and where, what a register holds and which instruction left it
so, and what a label wants that is not so; into the code a call returns to
as well. Each is checked by the kernel as this file is compiled.
-/

open TypedAsm TypedAsm.U

namespace Tests.Unified

/-- Whether something said of a refusal is among what is said. -/
def saysDetail (fs : List Refusal) (d : String) : Bool := (fs.flatMap (·.detail)).contains d

-- of a program that checks, nothing is said
example : (explain (prog codeBelow) [lab 0 (Pbelow 4)] 10).length = 0 := by decide +kernel

-- a read at an index not shown to be within what is held: the instruction,
-- where, and that it is the label's first
example : (explain (prog codeBelow) [lab 0 (Pbelow 5)] 10).map (fun f => (f.addr, f.why))
    = [(0, "`mov rax, qword ptr [rsp+rcx*8]` reads memory that is not shown to be the program's")]
    := by decide +kernel
-- and what the machine could do
example : saysDetail (explain (prog codeBelow) [lab 0 (Pbelow 5)] 10)
    "on the machine: it could read memory the program does not have, and fault" = true := by
  decide +kernel

-- a function said to return eight that returns seven: what `rax` holds, the
-- instruction that left it so, and what was wanted; found in the code the
-- call returns to
example : saysDetail (explain pgLend (lendLabels 8 16 3 4) 80)
    "rax holds 7, left so by `add rax, qword ptr [rsp+8]` at 0x400097; wanted there: 8" = true
    := by decide +kernel

-- the factorial without its laws: what the machine computed, in the
-- program's terms, against what the label says it returns
example : saysDetail (explain (pgFac [] 120) (facLabels facOfArg) 80)
    ("rax holds (fn0(rdi at the label walked from 0x40008b - 1, 0)) * " ++
      "(rdi at the label walked from 0x40008b), left so by `imul rax, rdi` at 0x4000a5; " ++
      "wanted there: fn0(rdi at the label walked from 0x40008b, 0)") = true
    := by decide +kernel

-- a write of nine bytes where eight are known: each register of the call
example : saysDetail (explain (pgMade 9 [0x48]) [lab 0 Pw] 20)
    "rdx holds 9, left so by `mov edx, 9` at 0x13" = true := by decide +kernel

-- a function said to hand back one page that hands back two: what is held
-- that the return does not account for
example : (explain pgPair (pairLabels [(.rax, 4096)]) 80).any
    (fun f => f.detail.any fun d =>
      d.startsWith "more is held than is wanted, and what is wanted does not range over the rest")
    = true := by decide +kernel

end Tests.Unified
