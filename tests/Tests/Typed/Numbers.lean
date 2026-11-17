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
import Tests.Typed.Calls

/-!
# The checker's tests: numbers

Which is the larger, by what is known; loops over tables and rows. Each is checked by the kernel as this file is compiled: what the
checker accepts, and what it refuses.
-/

open TypedAsm TypedAsm.U

namespace Tests.Unified

/-! ## Which is the larger -/

-- x ≤ 4, 4 - x ≠ 0 taken as 1 ≤ 4 - x: so x + 1 ≤ 4
example : entails 4 [⟨[(1, .var 0)], -4⟩, ⟨[(1, .var 0)], -3⟩] ⟨[(1, .var 0)], -3⟩ = true := by
  decide +kernel
-- x ≤ y, y ≤ 7: so x ≤ 7; and not x ≤ 6
example : entails 4 [⟨[(1, .var 0), (-1, .var 1)], 0⟩, ⟨[(1, .var 1)], -7⟩] ⟨[(1, .var 0)], -7⟩
    = true := by decide +kernel
example : entails 4 [⟨[(1, .var 0), (-1, .var 1)], 0⟩, ⟨[(1, .var 1)], -7⟩] ⟨[(1, .var 0)], -6⟩
    = false := by decide +kernel

/-! ## How large, by what is known -/

-- of a count known to be at most four, and four less it known not to be nought:
-- one more than it is at most four
example : rangeHolds [(.var 0, .range 0 4), (.add (.lit 4) (.un (.neg .w64) (.var 0)), .range 1 (-1))]
    (.add (.var 0) (.lit 1)) 0 4 = true := by decide +kernel
-- without the second, it may be five
example : rangeHolds [(.var 0, .range 0 4)] (.add (.var 0) (.lit 1)) 0 4 = false := by
  decide +kernel
-- a range that goes round: not three, and at most four, so three more is not six
example : rangeHolds [(.var 0, .range 0 4), (.var 0, .range 4 2)]
    (.add (.var 0) (.lit 3)) 7 5 = true := by decide +kernel

/-! ## Between what numbers, by everything known -/

/-- The stack, `rdx` at most so much, and `rcx` below `rdx`. -/
def Pbelow (top : BitVec 64) : CtxS :=
  { Pw with known := [(.bvar 0 2, .range 0 top), (.bvar 0 1, .upTo (.bvar 0 2) true)] }

-- a value below one that is at most four is at most three; and the one it
-- is below is at least one
example : (Pbelow 4).within (.bvar 0 1) = some (0, 3) := by decide +kernel
example : (Pbelow 4).within (.bvar 0 2) = some (1, 4) := by decide +kernel
-- eight times it past the stack pointer: from thirty-two into the region, for
-- at most twenty-four more
example : (Pbelow 4).spanFrom (.add (.add (.bvar 0 16) (.lit 32)) (.un (.shl 3) (.bvar 0 1)))
    (.bvar 0 16) = some (32, 24) := by decide +kernel
-- an address nothing ties to the region: no answer
example : (Pbelow 4).spanFrom (.bvar 0 5) (.bvar 0 16) = none := by decide +kernel

/-- `mov rax, [rsp + rcx*8]`, and the program ends. -/
def codeBelow : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .mov .w64 (.r_m .rax (.sib (some .rsp) (some (.rcx, .s8)) 0)), 4),
   (4, .mov .w32 (.rm_i (.reg .rax) 60), 5), (9, .syscall, 2)]

-- thirty-two bytes above the stack pointer are held: an index below a count
-- of at most four reads inside them
example : checkProgram (prog codeBelow) [lab 0 (Pbelow 4)] 10 0 = true := by decide +kernel
-- of at most five, it may read past them: refused
example : checkProgram (prog codeBelow) [lab 0 (Pbelow 5)] 10 0 = false := by decide +kernel
-- and with nothing known of the index: refused
example : checkProgram (prog codeBelow) [lab 0 Pw] 10 0 = false := by decide +kernel

/-! ## A loop over a table

A family that ties two registers: the pointer is at element `i`, the count
is five less `i`. Going round, `i` is found from the count, and the pointer
checked against it. -/

/-- The loop's family: `rdi` at element `i` of a table of five at 0x5000,
`rsi` five less `i`, `i` at most four. -/
def Ploop : CtxS where
  regs := ⟨.bvar 0 0, .bvar 0 1, .bvar 0 2, .bvar 0 3, .add (.bvar 0 16) (.lit 32), .bvar 0 5,
    .add (.lit 5) (.un (.neg .w64) (.bvar 0 17)), .add (.lit 0x5000) (.shl (.bvar 0 17) 3),
    .bvar 0 8, .bvar 0 9, .bvar 0 10, .bvar 0 11, .bvar 0 12, .bvar 0 13, .bvar 0 14, .bvar 0 15⟩
  flags := .bvar 0
  held := [(.bvar 0 16, ⟨64, []⟩)]
  known := [(.bvar 0 17, .range 0 4)]

/-- `mov edi, 0x5000; mov esi, 5; xor eax, eax;
loop: add rax, [rdi]; add rdi, 8; sub rsi, 1; jne loop; mov eax, 60; syscall`. -/
def codeSum : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .mov .w32 (.rm_i (.reg .rdi) 0x5000), 5), (5, .mov .w32 (.rm_i (.reg .rsi) 5), 5),
   (10, .alu .xor .w32 (.rm_r (.reg .rax) .rax), 2),
   (12, .alu .add .w64 (.r_m .rax (.sib (some .rdi) none 0)), 3),
   (15, .alu .add .w64 (.rm_i (.reg .rdi) 8), 4), (19, .alu .sub .w64 (.rm_i (.reg .rsi) 1), 4),
   (23, .jcc .ne (-13), 2), (25, .mov .w32 (.rm_i (.reg .rax) 60), 5), (30, .syscall, 2)]

def pgSum : Prog := { code := codeSum, statics := [(.lit 0x5000, .ptr (.mk 40 .nil) false 0)] }

-- the loop goes round with the pointer one element on and the count one less, and
-- `i` still at most four, since the count was not nought: typed, nothing said
example : checkProgram pgSum [⟨0, Pw⟩, ⟨12, Ploop⟩] 12 0 = true := by decide +kernel

-- a table of four: the fifth read is past its end. Refused
example : checkProgram { pgSum with statics := [(.lit 0x5000, .ptr (.mk 32 .nil) false 0)] }
    [⟨0, Pw⟩, ⟨12, Ploop⟩] 12 0 = false := by decide +kernel
-- a loop said to hold for `i` up to five: the read at five is past the end. Refused
example : checkProgram pgSum
    [⟨0, Pw⟩, ⟨12, { Ploop with known := [(.bvar 0 17, .range 0 5)] }⟩] 12 0 = false := by
  decide +kernel
-- a loop said to hold for `i` up to three only: going round from three is not in it. Refused
example : checkProgram pgSum
    [⟨0, Pw⟩, ⟨12, { Ploop with known := [(.bvar 0 17, .range 0 3)] }⟩] 12 0 = false := by
  decide +kernel
-- stepping by sixteen: the pointer is not at the element the loop says. Refused
example : checkProgram { pgSum with code := codeSum.map fun e =>
      if e.1 = 15 then (15, .alu .add .w64 (.rm_i (.reg .rdi) 16), 4) else e }
    [⟨0, Pw⟩, ⟨12, Ploop⟩] 12 0 = false := by decide +kernel
-- counting from six: the loop is entered with a count it does not allow. Refused
example : checkProgram { pgSum with code := codeSum.map fun e =>
      if e.1 = 5 then (5, .mov .w32 (.rm_i (.reg .rsi) 6), 5) else e }
    [⟨0, Pw⟩, ⟨12, Ploop⟩] 12 0 = false := by decide +kernel

/-! ## A row of values, as many as a value says

How many there are is a value a register holds, not a number written out.
An index is known to be below it by the program's own comparison of the two
registers. -/

/-- `rbx` is the address of as many values in a row as `rdx` says. -/
def Parr : CtxS := { Pw with known := [(.bvar 0 3, .arr (.bvar 0 2) .any)] }

/-- `cmp rcx, <reg>; <jcc> out; mov rax, [rbx + rcx*8 + disp]; out: exit`. -/
def codeArr (other : Reg) (c : Cond) (disp : BitVec 32) : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .alu .cmp .w64 (.rm_r (.reg .rcx) other), 3), (3, .jcc c 5, 2),
   (5, .mov .w64 (.r_m .rax (.sib (some .rbx) (some (.rcx, .s8)) disp)), 5),
   (10, .mov .w32 (.rm_i (.reg .rax) 60), 5), (15, .syscall, 2)]

-- past the comparison the index is below the count: the value there may be read
example : checkProgram (codeArr .rdx .ae 0) [lab 0 Parr] 10 0 = true := by decide +kernel
-- an index that may equal the count: refused
example : checkProgram (codeArr .rdx .a 0) [lab 0 Parr] 10 0 = false := by decide +kernel
-- an index below some other value: refused
example : checkProgram (codeArr .rsi .ae 0) [lab 0 Parr] 10 0 = false := by decide +kernel
-- the value one further along: it may be past the last. Refused
example : checkProgram (codeArr .rdx .ae 8) [lab 0 Parr] 10 0 = false := by decide +kernel
-- eight bytes that are not one of the values: refused
example : checkProgram (codeArr .rdx .ae 4) [lab 0 Parr] 10 0 = false := by decide +kernel

/-- `rbx` is the address of a row of `rdx` values, and `rdx` is not nought. -/
def Prow : CtxS :=
  { Pw with known := [(.bvar 0 3, .arr (.bvar 0 2) .any), (.bvar 0 2, .range 1 (-1))] }

/-- `loop: add rax, [rbx]; add rbx, <step>; sub rdx, 1; jne loop; exit`. -/
def codeRow (step : BitVec 32) : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .alu .add .w64 (.r_m .rax (.sib (some .rbx) none 0)), 3),
   (3, .alu .add .w64 (.rm_i (.reg .rbx) step), 4), (7, .alu .sub .w64 (.rm_i (.reg .rdx) 1), 4),
   (11, .jcc .ne (-13), 2), (13, .mov .w32 (.rm_i (.reg .rax) 60), 5), (18, .syscall, 2)]

-- the rest of a row is a row: one value on and one fewer, going round, for any row
example : checkProgram (codeRow 8) [lab 0 Prow] 10 0 = true := by decide +kernel
-- two values on for one fewer: the rest may be shorter than is said. Refused
example : checkProgram (codeRow 16) [lab 0 Prow] 10 0 = false := by decide +kernel
-- a row that may be of none: the first read may be past it. Refused
example : checkProgram (codeRow 8)
    [lab 0 { Pw with known := [(.bvar 0 3, .arr (.bvar 0 2) .any)] }] 10 0 = false := by
  decide +kernel

end Tests.Unified
