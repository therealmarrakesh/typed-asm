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
import Tests.Typed.Control

/-!
# The checker's tests: memory

Ranges, pointers by shape and by kind, indexes, text, publishing, static data. Each is checked by the kernel as this file is compiled: what the
checker accepts, and what it refuses.
-/

open TypedAsm TypedAsm.U

namespace Tests.Unified

/-! ## Ranges, and ways that cannot be taken -/

/-- `cmp rdi, 5; jb out; cmp rdi, 3; jb nowhere; out: mov eax, 60; syscall`:
the second jump goes where there is no code, and can never be taken. -/
def codeR : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .alu .cmp .w64 (.rm_i (.reg .rdi) 5), 4), (4, .jcc .b 6, 2),
   (6, .alu .cmp .w64 (.rm_i (.reg .rdi) 3), 4), (10, .jcc .b 188, 2),
   (12, .mov .w32 (.rm_i (.reg .rax) 60), 5), (17, .syscall, 2)]

-- past the first jump `rdi` is at least five; taking the second would make it
-- less than three: that way is seen to be impossible, and nothing is asked of it
example : checkProgram codeR [lab 0 Pw] 10 0 = true := by decide +kernel
-- entered past the first comparison, the second jump may be taken, to nowhere: refused
example : checkProgram codeR [lab 6 Pw] 10 0 = false := by decide +kernel

/-- The same at 32 bits: `mov edi, edi; cmp edi, 5; jb out; cmp edi, 3;
jb nowhere; out: exit`. The move leaves `rdi` below two to the thirty-second,
so what the 32-bit comparisons say of its low half they say of it. -/
def codeR32 : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .mov .w32 (.rm_r (.reg .rdi) .rdi), 2),
   (2, .alu .cmp .w32 (.rm_i (.reg .rdi) 5), 3), (5, .jcc .b 5, 2),
   (7, .alu .cmp .w32 (.rm_i (.reg .rdi) 3), 3), (10, .jcc .b 188, 2),
   (12, .mov .w32 (.rm_i (.reg .rax) 60), 5), (17, .syscall, 2)]

-- the second jump is seen to be impossible, as at 64 bits
example : checkProgram codeR32 [lab 0 Pw] 10 0 = true := by decide +kernel
-- entered past the move, nothing says `rdi` fits in 32 bits, so the comparisons
-- of its low half say nothing of it: the second jump may be taken. Refused
example : checkProgram codeR32 [lab 2 Pw] 10 0 = false := by decide +kernel
-- the range an operator's result lies in is read off the operator
example : (Val.un (.trunc .w32) (.var 3)).bound = ⟨0, 0xffffffff⟩ := by decide +kernel
example : (Val.un .low8 (.var 3)).bound = ⟨0, 0xff⟩ := by decide +kernel
example : (Val.fop (.condByte .e) (.var 0) (.lit 0) (.lit 0)).bound = ⟨0, 1⟩ := by decide +kernel

/-! ## Narrow reads -/

-- a byte read and widened is the byte read: the term says by its head that it
-- is a byte, and widening a byte does nothing
example : ((stepHeld noKinds { Γ0 with known := [(.var 7, .ptr (.mk 16 .nil) false 0)] } 20 100
      (.movzx .w32 .rax .w8 (.mem (.sib (some .rdi) none 3)))).map fun r => r.1.regs.rax)
    = some (.un .low8 (.var 20)) := by decide +kernel
-- and its range is read off it
example : (Val.un .low8 (.var 20)).bound = ⟨0, 0xff⟩ := by decide +kernel

/-! ## Pointers by kind -/

/-- A list node: sixteen bytes, the first eight nought or a pointer to
another node. The kind is number 7. -/
def node : ShapeS := .mk 16 (.cons 0 (.nullable (.ref 7 false 0)) .nil)

def kinds7 : Nat → Option ShapeS := fun t => if t = 7 then some node else none

/-- `rdi` is nought or points to a node. -/
def Pl : CtxS := { Pw with known := [(.bvar 0 7, .nullable (.ref 7 false 0))] }

/-- `loop: test rdi, rdi; je out; mov rdi, [rdi]; jmp loop; out: exit`: a
walk down a list to its end. -/
def codeList : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .test .w64 (.reg .rdi) (.reg .rdi), 3), (3, .jcc .e 8, 2),
   (5, .mov .w64 (.r_m .rdi (.sib (some .rdi) none 0)), 3), (8, .jmp (.rel (-13)), 5),
   (13, .mov .w32 (.rm_i (.reg .rax) 60), 5), (18, .syscall, 2)]

-- past the test `rdi` is not nought, so it points to a node; what is read
-- there is nought or points to a node again: the label's context, round the loop
example : checkProgram { code := codeList, kinds := kinds7 } [lab 0 Pl] 10 0 = true := by
  decide +kernel
-- the same program, the kind's shape not said: nothing is known to be at the pointer. Refused
example : checkProgram { code := codeList } [lab 0 Pl] 10 0 = false := by decide +kernel
-- entered at the load, `rdi` may be nought: refused
example : checkProgram { code := codeList, kinds := kinds7 } [lab 0 Pl, lab 5 Pl] 10 0 = false := by
  decide +kernel

/-! ## A call that stores bytes in a block others may point into -/

/-- `mov eax, 0; mov edx, 8; syscall; exit`: read eight bytes to where `rsi`
points. -/
def codeRdS : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .mov .w32 (.rm_i (.reg .rax) 0), 5), (5, .mov .w32 (.rm_i (.reg .rdx) 8), 5),
   (10, .syscall, 2), (12, .mov .w32 (.rm_i (.reg .rax) 60), 5), (17, .syscall, 2)]

/-- `rsi` points four bytes into a block of the given shape. -/
def buf (Sh : ShapeS) (w : Bool) : CtxS := { Pw with known := [(.bvar 0 6, .ptr Sh w 4)] }

-- sixteen plain bytes that may be written: the eight from the fourth lie in them
example : checkProgram codeRdS [lab 0 (buf (.mk 16 .nil) true)] 10 0 = true := by decide +kernel
-- through a pointer that may not be written through: refused
example : checkProgram codeRdS [lab 0 (buf (.mk 16 .nil) false)] 10 0 = false := by
  decide +kernel
-- over bytes that hold a pointer: refused, the block would no longer hold one
example : checkProgram codeRdS
    [lab 0 (buf (.mk 16 (.cons 8 (.ptr (.mk 8 .nil) false 0) .nil)) true)] 10 0 = false := by
  decide +kernel
-- past the end of the block: refused
example : checkProgram codeRdS [lab 0 (buf (.mk 8 .nil) true)] 10 0 = false := by decide +kernel
-- to an address nothing is known of: refused
example : checkProgram codeRdS [lab 0 Pw] 10 0 = false := by decide +kernel

/-! ## How large a value may be -/

/-- `rcx` is known to be at most nine. -/
def Γix : CtxS := { Γ0 with known := [(.var 1, .range 0 9)] }

-- an index scaled by eight is at most seventy-two; with twenty-four added, ninety-six
example : Γix.upper (.shl (.var 1) 3) = some 72 := by decide +kernel
example : Γix.upper (.add (.shl (.var 1) 3) (.lit 24)) = some 96 := by decide +kernel
-- a byte is at most 255, by its operator
example : Γix.upper (.un .low8 (.var 2)) = some 255 := by decide +kernel
-- of a value nothing is known of, the most a value can be
example : Γix.upper (.var 2) = some (2 ^ 64 - 1) := by decide +kernel
-- a range that wraps says nothing of how large
example : ({ Γ0 with known := [(.var 1, .range (-4) 9)] } : CtxS).upper (.var 1)
    = some (2 ^ 64 - 1) := by decide +kernel

/-- `cmp rdx, <most>; ja out; mov eax, 0; syscall; out: exit`: read as many
bytes as `rdx` says, once it is known to say no more than so many. -/
def codeRdN (most : BitVec 32) : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .alu .cmp .w64 (.rm_i (.reg .rdx) most), 4), (4, .jcc .a 7, 2),
   (6, .mov .w32 (.rm_i (.reg .rax) 0), 5), (11, .syscall, 2),
   (13, .mov .w32 (.rm_i (.reg .rax) 60), 5), (18, .syscall, 2)]

-- at most twelve bytes, from the fourth of sixteen: they lie in the block
example : checkProgram (codeRdN 12) [lab 0 (buf (.mk 16 .nil) true)] 10 0 = true := by
  decide +kernel
-- thirteen may run past the end: refused
example : checkProgram (codeRdN 13) [lab 0 (buf (.mk 16 .nil) true)] 10 0 = false := by
  decide +kernel
-- entered past the comparison, the room may be anything: refused
example : checkProgram (codeRdN 12)
    [lab 0 (buf (.mk 16 .nil) true), lab 6 (buf (.mk 16 .nil) true)] 10 0 = false := by
  decide +kernel

/-! ## An index with a bound -/

/-- `rbx` points to a table of eight values. -/
def Pt : CtxS := { Pw with known := [(.bvar 0 3, .ptr (.mk 64 .nil) false 0)] }

/-- `cmp rcx, <bound>; jae out; mov rax, [rbx + rcx*8]; out: exit`. -/
def codeIx (bound : BitVec 32) : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .alu .cmp .w64 (.rm_i (.reg .rcx) bound), 4), (4, .jcc .ae 4, 2),
   (6, .mov .w64 (.r_m .rax (.sib (some .rbx) (some (.rcx, .s8)) 0)), 4),
   (10, .mov .w32 (.rm_i (.reg .rax) 60), 5), (15, .syscall, 2)]

-- past the comparison the index is below eight, so the eight bytes read lie in the table
example : checkProgram (codeIx 8) [lab 0 Pt] 10 0 = true := by decide +kernel
-- an index that may be eight: the read may be past the end. Refused
example : checkProgram (codeIx 9) [lab 0 Pt] 10 0 = false := by decide +kernel
-- entered past the comparison, the index may be anything: refused
example : checkProgram (codeIx 8) [lab 0 Pt, lab 6 Pt] 10 0 = false := by decide +kernel

/-- `cmp rcx, <bound>; jae out; mov [rsp + rcx*8], rdi; out: exit`: a store
into the stack at an index. -/
def codeSt (bound : BitVec 32) : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .alu .cmp .w64 (.rm_i (.reg .rcx) bound), 4), (4, .jcc .ae 4, 2),
   (6, .mov .w64 (.rm_r (.mem (.sib (some .rsp) (some (.rcx, .s8)) 0)) .rdi), 4),
   (10, .mov .w32 (.rm_i (.reg .rax) 60), 5), (15, .syscall, 2)]

-- thirty-two bytes are held above the stack pointer: four slots
example : checkProgram (codeSt 4) [lab 0 Pw] 10 0 = true := by decide +kernel
-- a fifth would be past what is held: refused
example : checkProgram (codeSt 5) [lab 0 Pw] 10 0 = false := by decide +kernel

/-! ## Text -/

/-- `rdi` points to text. -/
def Ps : CtxS := { Pw with known := [(.bvar 0 7, .str (.lit 0))] }

/-- `loop: movzx eax, byte [rdi]; test eax, eax; je out; add rdi, <step>;
add rcx, 1; jmp loop; out: exit`: the length of a text, counted in `rcx`. -/
def codeLen (step : BitVec 32) : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .movzx .w32 .rax .w8 (.mem (.sib (some .rdi) none 0)), 3),
   (3, .test .w32 (.reg .rax) (.reg .rax), 2), (5, .jcc .e 13, 2),
   (7, .alu .add .w64 (.rm_i (.reg .rdi) step), 4), (11, .alu .add .w64 (.rm_i (.reg .rcx) 1), 4),
   (15, .jmp (.rel (-20)), 5),
   (20, .mov .w32 (.rm_i (.reg .rax) 60), 5), (25, .syscall, 2)]

-- the byte read is not nought past the test, so there is more text, and the
-- address one on points to text: the label's context again, round the loop
example : checkProgram (codeLen 1) [lab 0 Ps] 12 0 = true := by decide +kernel
-- two bytes at a time: the second may be past the end. Refused
example : checkProgram (codeLen 2) [lab 0 Ps] 12 0 = false := by decide +kernel
-- entered past the test, the byte is not known not to be nought: refused
example : checkProgram (codeLen 1) [lab 0 Ps, lab 7 Ps] 12 0 = false := by decide +kernel
-- through a value not known to point to text: refused
example : checkProgram (codeLen 1) [lab 0 Pw] 12 0 = false := by decide +kernel

/-! ## A region published -/

/-- `rbx` is the address of sixteen bytes held, the first eight holding what
`rdi` does; with what is known besides. -/
def Phold (known : List (Val × TyS)) : CtxS :=
  { Pw with held := Pw.held ++ [(.bvar 0 3, ⟨16, [(0, .bvar 0 7)]⟩)], known := known }

/-- `rbx` points to a list node that may be written; nothing is held there. -/
def Pref : CtxS := { Pw with known := [(.bvar 0 3, .ref 7 true 0)] }

/-- `rdi` is nought or points to a node. -/
def rdiNode : List (Val × TyS) := [(.bvar 0 7, .nullable (.ref 7 false 0))]

/-- `nop; exit`: at the `nop` the region at `rbx` becomes a list node. -/
def codePub : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .nop, 1), (1, .mov .w32 (.rm_i (.reg .rax) 60), 5), (6, .syscall, 2)]

-- the region is held whole, is a node's size, and holds at its first eight
-- bytes a value known to be nought or a pointer to a node: it becomes a node
example : checkProgram { code := codePub, kinds := kinds7, pubs := [⟨0, .rbx, node, some 7⟩] }
    [lab 0 (Phold rdiNode), lab 1 Pref] 10 0 = true := by decide +kernel
-- nothing known of what its first eight bytes hold: refused, it would not be a node
example : checkProgram { code := codePub, kinds := kinds7, pubs := [⟨0, .rbx, node, some 7⟩] }
    [lab 0 (Phold []), lab 1 Pref] 10 0 = false := by decide +kernel
-- the program does not say it is published: the region is still held, and is
-- not a node. Refused: publishing is never done unasked
example : checkProgram { code := codePub, kinds := kinds7 }
    [lab 0 (Phold rdiNode), lab 1 Pref] 10 0 = false := by decide +kernel
-- as a block of another size: refused
example : checkProgram { code := codePub, kinds := kinds7, pubs := [⟨0, .rbx, .mk 24 .nil, none⟩] }
    [lab 0 (Phold rdiNode), lab 1 Pref] 10 0 = false := by decide +kernel
-- as a kind the program does not give the shape of: refused
example : checkProgram { code := codePub, pubs := [⟨0, .rbx, node, some 7⟩] }
    [lab 0 (Phold rdiNode), lab 1 Pref] 10 0 = false := by decide +kernel

/-! ## Static data -/

/-- `mov edi, 0x5000; movzx eax, byte [rdi]; exit`: a byte read from an
address written out. -/
def codeStat : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .mov .w32 (.rm_i (.reg .rdi) 0x5000), 5),
   (5, .movzx .w32 .rax .w8 (.mem (.sib (some .rdi) none 0)), 3),
   (8, .mov .w32 (.rm_i (.reg .rax) 60), 5), (13, .syscall, 2)]

-- the program says its static data has text there: every walk starts out knowing it
example : checkProgram { code := codeStat, statics := [(.lit 0x5000, .str (.lit 0))] }
    [lab 0 Pw] 10 0 = true := by decide +kernel
-- said of another address: refused
example : checkProgram { code := codeStat, statics := [(.lit 0x6000, .str (.lit 0))] }
    [lab 0 Pw] 10 0 = false := by decide +kernel
-- not said at all: refused
example : checkProgram codeStat [lab 0 Pw] 10 0 = false := by decide +kernel

end Tests.Unified
