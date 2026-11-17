import TypedAsm.U.Span
import TypedAsm.U.Loader
import TypedAsm.U.Exits
import TypedAsm.U.Writes
import TypedAsm.U.Pages
import TypedAsm.Linux
import TypedAsm.U.Stack
import TypedAsm.U.Loaded
import TypedAsm.U.Whole
import TypedAsm.U.Order
import TypedAsm.U.Know
import TypedAsm.U.Labels
import TypedAsm.U.Open
import Tests.Typed.Memory

/-!
# The checker's tests: calls

Divides, and the system calls: mapping, filling, ending and writing. Each is checked by the kernel as this file is compiled: what the
checker accepts, and what it refuses.
-/

open TypedAsm TypedAsm.U

namespace Tests.Unified

/-! ## Divides -/

/-- `test rcx, rcx; je out; xor edx, edx; div rcx; out: exit`: the divisor is
known not to be nought, and the high half is nought, so the divide does not
fault. -/
def codeD : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .test .w64 (.reg .rcx) (.reg .rcx), 3), (3, .jcc .e 5, 2),
   (5, .alu .xor .w32 (.rm_r (.reg .rdx) .rdx), 2), (7, .mulDiv .div .w64 (.reg .rcx), 3),
   (10, .mov .w32 (.rm_i (.reg .rax) 60), 5), (15, .syscall, 2)]

example : checkProgram codeD [lab 0 Pw] 10 0 = true := by decide +kernel
-- entered past the test, the divisor may be nought: refused
example : checkProgram codeD [lab 5 Pw] 10 0 = false := by decide +kernel
-- entered past the clearing of the high half, the quotient may not fit: refused
example : checkProgram codeD [lab 0 Pw, lab 7 Pw] 10 0 = false := by decide +kernel

/-- `cmp rcx, 1; jl out; cqo; idiv rcx; out: exit`: the divisor is at least
one, and the high half is the sign of the low, so the signed divide does not
fault. -/
def codeI : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .alu .cmp .w64 (.rm_i (.reg .rcx) 1), 4), (4, .jcc .l 5, 2),
   (6, .cqo, 2), (8, .mulDiv .idiv .w64 (.reg .rcx), 3),
   (11, .mov .w32 (.rm_i (.reg .rax) 60), 5), (16, .syscall, 2)]

example : checkProgram codeI [lab 0 Pw] 10 0 = true := by decide +kernel
-- entered past the comparison, the divisor may be nought or minus one: refused
example : checkProgram codeI [lab 6 Pw] 10 0 = false := by decide +kernel
-- without the sign carried into the high half: refused
example : checkProgram codeI [lab 0 Pw, lab 8 Pw] 10 0 = false := by decide +kernel

/-- `shr rdi, 1; jne on; cmp rdi, 1; jae nowhere; on: exit`: after the
shift, not taking `jne` means the result is zero, so it is not at least one. -/
def codeS : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .shift .shr .w64 (.reg .rdi) (.imm 1), 4), (4, .jcc .ne 6, 2),
   (6, .alu .cmp .w64 (.rm_i (.reg .rdi) 1), 4), (10, .jcc .ae 188, 2),
   (12, .mov .w32 (.rm_i (.reg .rax) 60), 5), (17, .syscall, 2)]

-- a shift leaves the zero flag that of its result: the jump after the
-- comparison is seen to be impossible
example : checkProgram codeS [lab 0 Pw] 10 0 = true := by decide +kernel

/-- `popcnt rax, rdi; jne on; cmp rdi, 1; jae nowhere; on: exit`: not taking
`jne` means `rdi` was zero. -/
def codeP : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .popcnt .w64 .rax (.reg .rdi), 5), (5, .jcc .ne 6, 2),
   (7, .alu .cmp .w64 (.rm_i (.reg .rdi) 1), 4), (11, .jcc .ae 187, 2),
   (13, .mov .w32 (.rm_i (.reg .rax) 60), 5), (18, .syscall, 2)]

example : checkProgram codeP [lab 0 Pw] 10 0 = true := by decide +kernel

/-- `cmp rdi, rsi; adc rax, 0; je out; out: exit`: the comparison leaves the
carry defined, so the addition with carry does not fault and leaves the
flags defined, so the jump is decided. And a widening multiply, which never
faults. -/
def codeA : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .alu .cmp .w64 (.rm_r (.reg .rdi) .rsi), 3), (3, .alu .adc .w64 (.rm_i (.reg .rax) 0), 4),
   (7, .jcc .e 3, 2), (9, .mulDiv .mul .w64 (.reg .rsi), 3),
   (12, .mov .w32 (.rm_i (.reg .rax) 60), 5), (17, .syscall, 2)]

example : checkProgram codeA [lab 0 Pw] 10 0 = true := by decide +kernel
-- entered at the addition with carry, the carry is not known to be defined: refused
example : checkProgram codeA [lab 3 Pw] 10 0 = false := by decide +kernel

/-! ## Memory mapped, used and given back

`mmap` hands back an error number or the address of fresh memory; `munmap`
hands back zero, or an error number with the memory held still. The
program's own tests of what is handed back tell the cases apart. -/

/-- The stack, and `rdx` and `r10` as `mmap` is asked for memory to read and
write, private and of no file. -/
def Pm : CtxS := { Pw with regs := (Pw.regs.set .rdx (.lit 3)).set .r10 (.lit 0x22) }

/-- `top: mmap(0, 4096); if error goto out; store rdi there;` then `tail`;
`out: exit`. -/
def codeM (tail : List (BitVec 64 × Instr × BitVec 64)) : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .mov .w32 (.rm_i (.reg .rax) 9), 5), (5, .mov .w32 (.rm_i (.reg .rdi) 0), 5),
   (10, .mov .w32 (.rm_i (.reg .rsi) 4096), 5), (15, .syscall, 2),
   (17, .alu .cmp .w64 (.rm_i (.reg .rax) (-4095)), 6), (23, .jcc .ae 75, 2),
   (25, .mov .w64 (.rm_r (.mem (.sib (some .rax) none 0)) .rdi), 3)] ++ tail ++
  [(100, .mov .w32 (.rm_i (.reg .rax) 60), 5), (105, .syscall, 2)]

/-- `munmap(rax, 4096)`. -/
def unmapIt : List (BitVec 64 × Instr × BitVec 64) :=
  [(28, .mov .w64 (.rm_r (.reg .rdi) .rax), 3), (31, .mov .w32 (.rm_i (.reg .rax) 11), 5),
   (36, .syscall, 2)]

-- mapped, used, given back, and the program ends: typed
example : checkProgram (codeM (unmapIt ++ [(38, .jmp (.rel 57), 5)])) [lab 0 Pm] 20 0 = true := by
  decide +kernel
-- mapped, used, and the program ends holding it: typed. A program may end
-- holding memory
example : checkProgram (codeM [(28, .jmp (.rel 67), 5)]) [lab 0 Pm] 20 0 = true := by
  decide +kernel
-- mapped, used, and round again without giving it back: refused. The label
-- at the top holds no such memory
example : checkProgram (codeM [(28, .jmp (.rel (-33)), 5)]) [lab 0 Pm] 20 0 = false := by
  decide +kernel
-- given back, and round again without asking whether it was: refused. If
-- `munmap` refused, the memory is held still
example : checkProgram (codeM (unmapIt ++ [(38, .jmp (.rel (-43)), 5)])) [lab 0 Pm] 20 0
    = false := by decide +kernel
-- given back, the result tested, and round again only if it was: typed
example : checkProgram (codeM (unmapIt ++
    [(38, .test .w64 (.reg .rax) (.reg .rax), 3), (41, .jcc .ne 57, 2),
     (43, .jmp (.rel (-48)), 5)])) [lab 0 Pm] 20 0 = true := by decide +kernel
-- the store made without asking whether memory was handed back: refused
example : checkProgram
    (prog [(0, .mov .w32 (.rm_i (.reg .rax) 9), 5), (5, .mov .w32 (.rm_i (.reg .rdi) 0), 5),
      (10, .mov .w32 (.rm_i (.reg .rsi) 4096), 5), (15, .syscall, 2),
      (17, .mov .w64 (.rm_r (.mem (.sib (some .rax) none 0)) .rdi), 3),
      (20, .mov .w32 (.rm_i (.reg .rax) 60), 5), (25, .syscall, 2)])
    [lab 0 Pm] 20 0 = false := by decide +kernel
-- asked for without saying it is to be read and written, private and of no
-- file: refused. The kernel is modelled for that one form of the call only
example : checkProgram (codeM [(28, .jmp (.rel 67), 5)]) [lab 0 Pw] 20 0 = false := by
  decide +kernel
-- asked for at an address of the program's choosing: refused
example : checkProgram
    (prog [(0, .mov .w32 (.rm_i (.reg .rax) 9), 5), (5, .mov .w32 (.rm_i (.reg .rdi) 0x10000), 5),
      (10, .mov .w32 (.rm_i (.reg .rsi) 4096), 5), (15, .syscall, 2),
      (17, .mov .w32 (.rm_i (.reg .rax) 60), 5), (22, .syscall, 2)])
    [lab 0 Pm] 20 0 = false := by decide +kernel

/-! ## A call that stores bytes -/

/-- `mov [rsp], rdi; read(0, rsp, <count>); exit`: the buffer is the stack
from the stack pointer on, of which `Pw`'s family holds thirty-two bytes. -/
def codeRd (count : BitVec 32) : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .mov .w64 (.rm_r (.mem (.sib (some .rsp) none 0)) .rdi), 4),
   (4, .mov .w32 (.rm_i (.reg .rax) 0), 5), (9, .mov .w32 (.rm_i (.reg .rdi) 0), 5),
   (14, .mov .w64 (.rm_r (.reg .rsi) .rsp), 3), (17, .mov .w32 (.rm_i (.reg .rdx) count), 5),
   (22, .syscall, 2), (24, .mov .w32 (.rm_i (.reg .rax) 60), 5), (29, .syscall, 2)]

-- thirty-two bytes read into the thirty-two held above the stack pointer: typed
example : checkProgram (codeRd 32) [lab 0 Pw] 20 0 = true := by decide +kernel
-- thirty-three, one past the end of what is held: refused
example : checkProgram (codeRd 33) [lab 0 Pw] 20 0 = false := by decide +kernel

/-- The same, the program then going round to a label that says the stack
still holds at its thirty-second byte what `rdi` held: which the call may
have written over. -/
def afterRead (keeps : Bool) : Bool :=
  checkProgram
    (prog [(0, .mov .w64 (.rm_r (.mem (.sib (some .rsp) none 0)) .rdi), 4),
     (4, .mov .w32 (.rm_i (.reg .rax) 0), 5), (9, .mov .w64 (.rm_r (.reg .rsi) .rsp), 3),
     (12, .mov .w32 (.rm_i (.reg .rdx) 8), 5), (17, .syscall, 2), (19, .jmp (.rel 76), 5),
     (100, .jmp (.rel (-5)), 5)])
    [lab 0 Pw,
     lab 100 { Pw with
       regs := anyRegs.set .rsp (.add (.bvar 0 16) (.lit 32))
       held := [(.bvar 0 16, ⟨64, if keeps then [(32, .bvar 0 7)] else []⟩)] }] 20 0

-- what the bytes held is no longer known after the call: a label saying it is, refused
example : afterRead true = false := by decide +kernel
example : afterRead false = true := by decide +kernel

/-! ## How a program ends -/

/-- `mov eax, 60; <set edi>; syscall`. -/
def codeX (setEdi : Instr) : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .mov .w32 (.rm_i (.reg .rax) 60), 5), (5, setEdi, 2), (7, .syscall, 2)]

/-- `xor edi, edi`. -/
def zeroEdi : Instr := .alu .xor .w32 (.rm_r (.reg .rdi) .rdi)

-- the status is nought, which is what is wanted
example : checkProgram { code := codeX zeroEdi, pre := preExits (· == 0) } [lab 0 Pw] 10 0
    = true := by decide +kernel
-- one is wanted, and the status is nought: refused
example : checkProgram { code := codeX zeroEdi, pre := preExits (· == 1) } [lab 0 Pw] 10 0
    = false := by decide +kernel
-- the status is whatever `rdi` held: refused
example : checkProgram { code := codeX .nop, pre := preExits (· == 0) } [lab 0 Pw] 10 0
    = false := by decide +kernel
-- with nothing asked of how it ends, the same program is typed: it is safe
example : checkProgram (codeX .nop) [lab 0 Pw] 10 0 = true := by decide +kernel

/-! ## What a program writes -/

/-- The bytes of `Hi` and a new line. -/
def msg : List (BitVec 8) := [72, 105, 10]

/-- `mov eax, 1; mov edi, <fd>; lea rsi, [0x2000]; mov edx, <len>; syscall;
mov eax, 60; xor edi, edi; syscall`: write so many bytes of a message, and
end. -/
def codeHi (fd len : BitVec 32) : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .mov .w32 (.rm_i (.reg .rax) 1), 5), (5, .mov .w32 (.rm_i (.reg .rdi) fd), 5),
   (10, .lea .w64 .rsi (.rip 8175), 7), (17, .mov .w32 (.rm_i (.reg .rdx) len), 5),
   (22, .syscall, 2), (24, .mov .w32 (.rm_i (.reg .rax) 60), 5),
   (29, .alu .xor .w32 (.rm_r (.reg .rdi) .rdi), 2), (31, .syscall, 2)]

/-- It is to end with status nought, and to write these bytes to descriptor
1; the block at `0x2000` says it holds the message. -/
def want (bs : List (BitVec 8)) : CtxS → Bool :=
  preOut [(0x2000, msg)] (· == 0) (fun fd b => fd == 1 && b == bs)

-- the three bytes offered are the message, to descriptor 1; and it ends with nought
example : checkProgram { code := codeHi 1 3, pre := want msg } [lab 0 Pw] 12 0 = true := by
  decide +kernel
-- a fourth byte is past what the block says: refused
example : checkProgram { code := codeHi 1 4, pre := want msg } [lab 0 Pw] 12 0 = false := by
  decide +kernel
-- to another descriptor: refused
example : checkProgram { code := codeHi 2 3, pre := want msg } [lab 0 Pw] 12 0 = false := by
  decide +kernel
-- the message, where other bytes are wanted: refused
example : checkProgram { code := codeHi 1 3, pre := want [72, 105] } [lab 0 Pw] 12 0 = false := by
  decide +kernel
-- its first two bytes, where those are wanted
example : checkProgram { code := codeHi 1 2, pre := want [72, 105] } [lab 0 Pw] 12 0 = true := by
  decide +kernel

end Tests.Unified
