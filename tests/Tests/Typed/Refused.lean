import TypedAsm.U.Span
import TypedAsm.U.Loader
import TypedAsm.U.Exits
import TypedAsm.U.Writes
import TypedAsm.U.Pages
import TypedAsm.Linux
import TypedAsm.U.Loaded
import TypedAsm.U.Whole
import TypedAsm.U.Order
import TypedAsm.U.Know
import TypedAsm.U.Labels
import TypedAsm.U.Open
import Tests.Typed.Numbers

/-!
# The checker's tests: refused

What a program may not do, each on its own. Each is checked by the kernel as this file is compiled: what the
checker accepts, and what it refuses.
-/

open TypedAsm TypedAsm.U

namespace Tests.Unified

/-! ## More that is refused

What a program may not do, each on its own: with the stack, with control,
with the flags, and at a system call. -/

/-- A context with no stack at all. -/
def Pn : CtxS :=
  { regs := ⟨.bvar 0 0, .bvar 0 1, .bvar 0 2, .bvar 0 3, .bvar 0 4, .bvar 0 5, .bvar 0 6,
      .bvar 0 7, .bvar 0 8, .bvar 0 9, .bvar 0 10, .bvar 0 11, .bvar 0 12, .bvar 0 13,
      .bvar 0 14, .bvar 0 15⟩
    flags := .bvar 0 }

/-- Code that ends the program, at an address. -/
def exitAt (a : BitVec 64) : List (BitVec 64 × Instr × BitVec 64) :=
  [(a, .mov .w32 (.rm_i (.reg .rax) 60), 5), (a + 5, .syscall, 2)]

-- a push with no stack held: refused
example : checkProgram (prog ([(0, .push .rax, 1)] ++ exitAt 1)) [lab 0 Pn] 10 0 = false := by
  decide +kernel
-- a return where nothing says what is at the stack pointer: refused
example : checkProgram (prog [(0, .ret, 1)]) [lab 0 Pw] 10 0 = false := by decide +kernel
-- the stack pointer given a value nothing is known of, and then pushed through: refused
example : checkProgram
    (prog ([(0, .mov .w64 (.rm_r (.reg .rsp) .rax), 3), (3, .push .rbx, 1)] ++ exitAt 4))
    [lab 0 Pw] 10 0 = false := by decide +kernel
-- a jump on a flag nothing is known of: refused
example : checkProgram (prog ([(0, .jcc .o 0, 2)] ++ exitAt 2)) [lab 0 Pw] 10 0 = false := by
  decide +kernel
-- a move on a condition nothing is known of: refused
example : checkProgram (prog ([(0, .cmov .g .w32 .rax (.reg .rcx), 3)] ++ exitAt 3))
    [lab 0 Pw] 10 0 = false := by decide +kernel
-- a system call whose number is not known: refused
example : checkProgram (prog [(0, .syscall, 2)]) [lab 0 Pw] 10 0 = false := by decide +kernel
-- a call through a register nothing is known of: refused
example : checkProgram (prog ([(0, .call (.ind (.reg .rax)), 2)] ++ exitAt 2))
    [lab 0 Pw] 10 0 = false := by decide +kernel
-- an instruction that is not one: refused
example : checkProgram (prog [(0, .ud2, 2)]) [lab 0 Pw] 10 0 = false := by decide +kernel
-- a jump back to an address that is no label: the walk has no end. Refused
example : checkProgram (prog [(0, .nop, 1), (1, .nop, 1), (2, .jmp (.rel (-6)), 5)])
    [lab 0 Pw] 20 0 = false := by decide +kernel
-- a call the kernel is not modelled for (`mprotect`, 10): refused. The model
-- would answer that there is no such call, which is not what the kernel does
example : checkProgram (prog ([(0, .mov .w32 (.rm_i (.reg .rax) 10), 5), (5, .syscall, 2)] ++
    exitAt 7)) [lab 0 Pw] 10 0 = false := by decide +kernel
-- one it is modelled for that touches nothing of the program's (`getpid`, 39): typed
example : checkProgram (prog ([(0, .mov .w32 (.rm_i (.reg .rax) 39), 5), (5, .syscall, 2)] ++
    exitAt 7)) [lab 0 Pw] 10 0 = true := by decide +kernel
-- a `read` of as many bytes as a register nothing is known of says: refused
example : checkProgram
    (prog ([(0, .alu .xor .w32 (.rm_r (.reg .rax) .rax), 2),
      (2, .alu .xor .w32 (.rm_r (.reg .rdi) .rdi), 2),
      (4, .lea .w64 .rsi (.sib (some .rsp) none 0), 4), (8, .syscall, 2)] ++ exitAt 10))
    [lab 0 Pw] 10 0 = false := by decide +kernel

/-- The stack, and `rbx` a pointer to sixteen bytes that may be written, the
second eight of them a pointer. -/
def Pq : CtxS :=
  { Pw with known := [(.bvar 0 3, .ptr (.mk 16 (.cons 8 (.ptr (.mk 8 .nil) true 0) .nil)) true 0)] }

-- `fstat` fills 144 bytes: into thirty-two of stack, refused
example : checkProgram (prog ([(0, .mov .w32 (.rm_i (.reg .rax) 5), 5),
    (5, .lea .w64 .rsi (.sib (some .rsp) none 0), 4), (9, .syscall, 2)] ++ exitAt 11))
    [lab 0 Pw] 10 0 = false := by decide +kernel
-- `clock_gettime` fills sixteen: into the stack, typed
example : checkProgram (prog ([(0, .mov .w32 (.rm_i (.reg .rax) 228), 5),
    (5, .lea .w64 .rsi (.sib (some .rsp) none 0), 4), (9, .syscall, 2)] ++ exitAt 11))
    [lab 0 Pw] 10 0 = true := by decide +kernel
-- through a register nothing is known of: refused
example : checkProgram (prog ([(0, .mov .w32 (.rm_i (.reg .rax) 228), 5), (5, .syscall, 2)] ++
    exitAt 7)) [lab 0 Pw] 10 0 = false := by decide +kernel
-- `getrandom` of as many bytes as a register nothing is known of says: refused
example : checkProgram (prog ([(0, .mov .w32 (.rm_i (.reg .rax) 318), 5),
    (5, .lea .w64 .rdi (.sib (some .rsp) none 0), 4), (9, .syscall, 2)] ++ exitAt 11))
    [lab 0 Pw] 10 0 = false := by decide +kernel
-- what holds of a load and a store holds of every instruction with a memory
-- operand. `neg` at an index nothing is known of: refused
example : checkProgram (prog ([(0, .unary .neg .w64 (.mem (.sib (some .rbx) (some (.rcx, .s8)) 0)),
    4)] ++ exitAt 4)) [lab 0 Pq] 10 0 = false := by decide +kernel
-- `not` of the eight plain bytes: typed
example : checkProgram (prog ([(0, .unary .not .w64 (.mem (.sib (some .rbx) none 0)), 3)] ++
    exitAt 3)) [lab 0 Pq] 10 0 = true := by decide +kernel
-- of the eight that hold a pointer: refused, they would no longer hold one
example : checkProgram (prog ([(0, .unary .not .w64 (.mem (.sib (some .rbx) none 8)), 4)] ++
    exitAt 4)) [lab 0 Pq] 10 0 = false := by decide +kernel
-- `add` to four bytes that run into the pointer: refused
example : checkProgram (prog ([(0, .alu .add .w32 (.rm_i (.mem (.sib (some .rbx) none 6)) 1), 4)] ++
    exitAt 4)) [lab 0 Pq] 10 0 = false := by decide +kernel
-- two bytes stored across the pointer's start: refused
example : checkProgram (prog ([(0, .store16 (.sib (some .rbx) none 7) .rax, 4)] ++ exitAt 4))
    [lab 0 Pq] 10 0 = false := by decide +kernel
-- a shift of four bytes that run past the end of the block: refused
example : checkProgram (prog ([(0, .shift .shl .w32 (.mem (.sib (some .rbx) none 14)) (.imm 1),
    4)] ++ exitAt 4)) [lab 0 Pq] 10 0 = false := by decide +kernel
-- a multiply by four bytes that run past the end: refused
example : checkProgram (prog ([(0, .imul2 .w32 .rax (.mem (.sib (some .rbx) none 14)), 4)] ++
    exitAt 4)) [lab 0 Pq] 10 0 = false := by decide +kernel

/-! ## What a system call leaves in the registers

A call that returns leaves its answer in `rax`, the address it returns to
in `rcx`, and in `r11` the flags the processor saved when the call was
made: no number a program can count on. -/

/-- `getpid`; then the program ends with what this register holds. -/
def codeAfterCall (r : Reg) : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .mov .w32 (.rm_i (.reg .rax) 39), 5), (5, .syscall, 2),
   (7, .mov .w64 (.rm_r (.reg .rdi) r), 3),
   (10, .mov .w32 (.rm_i (.reg .rax) 60), 5), (15, .syscall, 2)]

/-- The program, to end with this status. -/
def pgAfterCall (r : Reg) (status : BitVec 32) : Prog :=
  { code := codeAfterCall r, pre := preExits (· == status) }

-- `rcx` holds the address the call returned to, which is seven
example : checkProgram (pgAfterCall .rcx 7) [lab 0 Pw] 10 0 = true := by decide +kernel
-- `r11` does not hold nought, nor any number that can be said: refused
example : checkProgram (pgAfterCall .r11 0) [lab 0 Pw] 10 0 = false := by decide +kernel
-- in the model too it is what the world says, which is anything
example (s : State) (v : BitVec 64) : (Linux.ret s v).getReg .r11 = s.world.saved 0 := rfl
-- and the next call has the next
example (s : State) (v w : BitVec 64) :
    (Linux.ret (Linux.ret s v) w).getReg .r11 = s.world.saved 1 := rfl

end Tests.Unified
