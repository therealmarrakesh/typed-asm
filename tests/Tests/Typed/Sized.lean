import Tests.Typed.Whole
import FactProgram
import TypedAsm.U.Checked

/-!
# The checker's tests: memory as large as a value says

How many bytes a region held is, and how far into it a value lies, are
terms. A function may then need as much stack as its argument says, be
handed a region as large as a register says, and read back what it stored
at a place it worked out. Each is checked by the kernel as this file is
compiled: what the checker accepts, and what it refuses.
-/

open TypedAsm TypedAsm.U

namespace Tests.Unified

/-! ## A place worked out -/

/-- `mov [rsp + rcx*8], rax; mov rbx, [rsp + rcx*8]`, then on to a label. -/
def codeIdx : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .mov .w64 (.rm_r (.mem (.sib (some .rsp) (some (.rcx, .s8)) 0)) .rax), 4),
   (4, .mov .w64 (.r_m .rbx (.sib (some .rsp) (some (.rcx, .s8)) 0)), 4),
   (8, .mov .w32 (.rm_i (.reg .rax) 60), 5), (13, .syscall, 2)]

/-- As `Pbelow 4`, and `rbx` holding what `rax` holds. -/
def Psame : CtxS := { Pbelow 4 with regs := (Pbelow 4).regs.set .rbx (.bvar 0 0) }

-- what was stored at an index below a count of at most four is what is read
-- back from there
example : checkProgram (prog codeIdx) [lab 0 (Pbelow 4), lab 8 Psame] 10 0 = true := by
  decide +kernel
-- with the count at most five the store may fall outside what is held: refused
example : checkProgram (prog codeIdx) [lab 0 (Pbelow 5), lab 8 Psame] 10 0 = false := by
  decide +kernel
-- and it is that value, not another: refused
example : checkProgram (prog codeIdx)
    [lab 0 (Pbelow 4), lab 8 { Psame with regs := Psame.regs.set .rbx (.bvar 0 1) }] 10 0
    = false := by decide +kernel

/-! ## A region as large as a register says -/

/-- A function given, at `rdi`, a region of as many bytes as `rsi` says. -/
def Pfill : CtxS := inFunction (takes := [(.was .rdi, Val.was .rsi)])

/-- It asks the kernel to read into the region as many bytes as that, and
returns. -/
def codeFill : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .mov .w64 (.rm_r (.reg .rdx) .rsi), 3), (3, .mov .w64 (.rm_r (.reg .rsi) .rdi), 3),
   (6, .mov .w32 (.rm_i (.reg .rdi) 0), 5), (11, .mov .w32 (.rm_i (.reg .rax) 0), 5),
   (16, .syscall, 2), (18, .ret, 1)]

/-- The same, asking for one byte more than there is. -/
def codeFillMore : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .lea .w64 .rdx (.sib (some .rsi) none 1), 4), (4, .mov .w64 (.rm_r (.reg .rsi) .rdi), 3),
   (7, .mov .w32 (.rm_i (.reg .rdi) 0), 5), (12, .mov .w32 (.rm_i (.reg .rax) 0), 5),
   (17, .syscall, 2), (19, .ret, 1)]

-- typed for every caller: whatever the size, the call fills no more than is held
example : checkProgram (prog codeFill) [lab 0 Pfill] 10 0 = true := by decide +kernel
-- one byte more: refused
example : checkProgram (prog codeFillMore) [lab 0 Pfill] 10 0 = false := by decide +kernel

/-! ## A stack as deep as an argument says

The factorial of `examples/Fact`, which calls itself: each level pushes its
argument and a return address, so a call needs sixteen bytes of stack for
each unit of its argument. With a label saying so, the function is typed
once, for every argument and every caller. -/

/-- The program, and nothing asked of how it ends. -/
def pgFact : Prog := { code := progCode (Asm.table Fact.base Fact.code) }

/-- The labels: the start; and the function, knowing this of its argument
and wanting so much stack below its return address. -/
def factLabels (known : List (Val × TyS)) (room : Val) : List U.Label :=
  [⟨Fact.entry, inProgram 11⟩,
   ⟨Asm.addr Fact.code Fact.base .fact, inFunction (known := known) (room := room)⟩]

/-- The argument is small enough that sixteen times it is a number of bytes. -/
def smallArg : List (Val × TyS) := [(.was .rdi, .range 0 0xFFFFFFF)]

-- sixteen bytes for each unit of the argument: typed, for every argument
example : wholeOk Fact.code .start 11 pgFact (factLabels smallArg ((Val.was .rdi) <<< 4)) 80
    = true := by decide +kernel
-- eight for each: the call to itself would be handed less than it wants: refused
example : wholeOk Fact.code .start 11 pgFact (factLabels smallArg ((Val.was .rdi) <<< 3)) 80
    = false := by decide +kernel
-- eighty, whatever the argument: enough for five levels, not for the level
-- below, which wants eighty again: refused
example : wholeOk Fact.code .start 11 pgFact (factLabels smallArg 80) 80 = false := by
  decide +kernel
-- nothing known of the argument: sixteen times it may not be a number of
-- bytes at all: refused
example : wholeOk Fact.code .start 11 pgFact (factLabels [] ((Val.was .rdi) <<< 4)) 80
    = false := by decide +kernel

end Tests.Unified
