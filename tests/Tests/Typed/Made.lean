import Tests.Typed.Lent

/-!
# The checker's tests: writing bytes the program made

A number a region held is said to hold is its eight bytes, the least
significant first. A `write` from such a region offers those bytes, and a
program can be proved to write them and nothing else. A byte stored into
such a number leaves it known, with that byte replaced. Each is checked by
the kernel as this file is compiled: what the checker accepts, and what it
refuses.
-/

open TypedAsm TypedAsm.U

namespace Tests.Unified

/-- `mov eax, 0x0a6948; push rax; write(1, rsp, n); exit(0)`: the number is
the three bytes of `Hi` and a new line, and five noughts. -/
def codeMade (n : BitVec 32) : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .mov .w32 (.rm_i (.reg .rax) 0x0a6948), 5), (5, .push .rax, 1),
   (6, .mov .w32 (.rm_i (.reg .rax) 1), 5), (11, .mov .w32 (.rm_i (.reg .rdi) 1), 5),
   (16, .mov .w64 (.rm_r (.reg .rsi) .rsp), 3), (19, .mov .w32 (.rm_i (.reg .rdx) n), 5),
   (24, .syscall, 2),
   (26, .mov .w32 (.rm_i (.reg .rax) 60), 5), (31, .mov .w32 (.rm_i (.reg .rdi) 0), 5),
   (36, .syscall, 2)]

/-- The program, to end with nought and to write, on descriptor one, only
these bytes. No block of the program says any bytes. -/
def pgMade (n : BitVec 32) (want : List (BitVec 8)) : Prog :=
  { code := codeMade n, pre := preOut [] (· == 0) (fun fd bs => fd == 1 && bs == want) }

-- the first three bytes of the number pushed are `H`, `i` and a new line
example : checkProgram (pgMade 3 [0x48, 0x69, 0x0a]) [lab 0 Pw] 20 0 = true := by decide +kernel
-- and not anything else
example : checkProgram (pgMade 3 [0x48, 0x69, 0x0b]) [lab 0 Pw] 20 0 = false := by decide +kernel
-- all eight of its bytes
example : checkProgram (pgMade 8 [0x48, 0x69, 0x0a, 0, 0, 0, 0, 0]) [lab 0 Pw] 20 0 = true := by
  decide +kernel
-- a ninth byte is not of the number: nothing is said of it, so nothing is
-- known of what would be written: refused
example : checkProgram (pgMade 9 [0x48, 0x69, 0x0a, 0, 0, 0, 0, 0, 0]) [lab 0 Pw] 20 0
    = false := by decide +kernel

/-- The bytes at a place, where a region is said to hold numbers there. -/
def twoCells : CtxS :=
  { Pw with held := [(.bvar 0 16, ⟨64, [(32, .lit 0x0807060504030201), (40, .lit 0x11)]⟩)] }

-- from the stack pointer, which is thirty-two in: the first number's bytes
example : heldBytes twoCells (.add (.bvar 0 16) (.lit 32)) 4 = some [1, 2, 3, 4] := by
  decide +kernel
-- across from one number into the next
example : heldBytes twoCells (.add (.bvar 0 16) (.lit 38)) 4 = some [7, 8, 0x11, 0] := by
  decide +kernel
-- where nothing is said to be held: no answer
example : heldBytes twoCells (.add (.bvar 0 16) (.lit 46)) 4 = none := by decide +kernel

/-! ## A byte stored into a number -/

/-- The number pushed; `mov ecx, 0x4a; mov [rsp + k], cl`, a `J` stored
into its `k`th byte; three bytes written; and the program ends. -/
def codeByte (k : BitVec 32) : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .mov .w32 (.rm_i (.reg .rax) 0x0a6948), 5), (5, .push .rax, 1),
   (6, .mov .w32 (.rm_i (.reg .rcx) 0x4a), 5), (11, .store8 (.sib (some .rsp) none k) .rcx, 4),
   (15, .mov .w32 (.rm_i (.reg .rax) 1), 5), (20, .mov .w32 (.rm_i (.reg .rdi) 1), 5),
   (25, .mov .w64 (.rm_r (.reg .rsi) .rsp), 3), (28, .mov .w32 (.rm_i (.reg .rdx) 3), 5),
   (33, .syscall, 2),
   (35, .mov .w32 (.rm_i (.reg .rax) 60), 5), (40, .mov .w32 (.rm_i (.reg .rdi) 0), 5),
   (45, .syscall, 2)]

def pgByte (k : BitVec 32) (want : List (BitVec 8)) : Prog :=
  { code := codeByte k, pre := preOut [] (· == 0) (fun fd bs => fd == 1 && bs == want) }

-- the first byte replaced: `J`, `i`, a new line
example : checkProgram (pgByte 0 [0x4a, 0x69, 0x0a]) [lab 0 Pw] 20 0 = true := by decide +kernel
-- no longer `H`
example : checkProgram (pgByte 0 [0x48, 0x69, 0x0a]) [lab 0 Pw] 20 0 = false := by decide +kernel
-- the third replaced
example : checkProgram (pgByte 2 [0x48, 0x69, 0x4a]) [lab 0 Pw] 20 0 = true := by decide +kernel
-- the sixth: the first three are as they were
example : checkProgram (pgByte 5 [0x48, 0x69, 0x0a]) [lab 0 Pw] 20 0 = true := by decide +kernel

end Tests.Unified
