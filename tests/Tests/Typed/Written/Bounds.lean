import TypedAsm
import TypedAsm.U.Checked

/-!
# Indices bounded by what they are made of

A value nothing is known of, the count of arguments, is made into indices
into a table of thirty-two bytes by operators no other test bounds: or,
exclusive or, a quotient, what is left of a division by a divisor known
only to lie in a range, a shift left at thirty-two bits, a difference, and
a choice between two. Each read is typed only where the index is shown to
lie in the table, by what each operator does to the ranges of its operands.
-/

open TypedAsm TypedAsm.U

namespace Tests.Written.Bounds

inductive L
  | start | table
  deriving DecidableEq, Hashable

def rd : Asm L := .ins (.movzx .w32 .rdx .w8 (.mem (.sib (some .rbx) (some (.rax, .s1)) 0)))

def code : List (Asm L) := [
  .label .start,
  .ref (.lea .w64 .rbx (.rip 0)) .table,
  .ins (.mov .w64 (.r_m .rcx (.sib (some .rsp) none 0))),        -- x: nothing known
  -- (x and 7) or 8: at most 15
  .ins (.mov .w32 (.rm_r (.reg .rax) .rcx)),
  .ins (.alu .and .w32 (.rm_i (.reg .rax) 7)),
  .ins (.alu .or .w32 (.rm_i (.reg .rax) 8)),
  rd,
  -- (x and 15) xor 5: at most 15
  .ins (.mov .w32 (.rm_r (.reg .rax) .rcx)),
  .ins (.alu .and .w32 (.rm_i (.reg .rax) 15)),
  .ins (.alu .xor .w32 (.rm_i (.reg .rax) 5)),
  rd,
  -- (x and 255) / 16: at most 15
  .ins (.mov .w32 (.rm_r (.reg .rax) .rcx)),
  .ins (.alu .and .w32 (.rm_i (.reg .rax) 255)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdx) .rdx)),
  .ins (.mov .w32 (.rm_i (.reg .r8) 16)),
  .ins (.mulDiv .div .w64 (.reg .r8)),
  rd,
  -- x mod ((x and 7) + 1): below 8
  .ins (.mov .w32 (.rm_r (.reg .r9) .rcx)),
  .ins (.alu .and .w32 (.rm_i (.reg .r9) 7)),
  .ins (.alu .add .w32 (.rm_i (.reg .r9) 1)),
  .ins (.mov .w64 (.rm_r (.reg .rax) .rcx)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdx) .rdx)),
  .ins (.mulDiv .div .w64 (.reg .r9)),
  .ins (.mov .w64 (.rm_r (.reg .rax) .rdx)),
  rd,
  -- (x and 3) shl 3 at thirty-two bits: at most 24
  .ins (.mov .w32 (.rm_r (.reg .rax) .rcx)),
  .ins (.alu .and .w32 (.rm_i (.reg .rax) 3)),
  .ins (.shift .shl .w32 (.reg .rax) (.imm 3)),
  rd,
  -- 31 - (x and 7): from 24 to 31
  .ins (.mov .w32 (.rm_r (.reg .r10) .rcx)),
  .ins (.alu .and .w32 (.rm_i (.reg .r10) 7)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 31)),
  .ins (.alu .sub .w32 (.rm_r (.reg .rax) .r10)),
  rd,
  -- the one or the other of two at most 15
  .ins (.mov .w32 (.rm_r (.reg .rax) .rcx)),
  .ins (.alu .and .w32 (.rm_i (.reg .rax) 15)),
  .ins (.mov .w32 (.rm_i (.reg .r11) 9)),
  .ins (.alu .cmp .w64 (.rm_r (.reg .rcx) .r11)),
  .ins (.cmov .b .w32 .rax (.reg .r11)),
  rd,
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .segment .ro,
  .label .table, .bytes (List.replicate 32 0)]

asm_program code start .start stack 0

#guard exitsWith 0 (runMem linux 1000 start)

def blocks : List (BitVec 64 × U.LayoutS) :=
  blocksWith code .start [(Asm.addr code base .table, plainBlock 32 false)]

def pg : Prog :=
  { code := progCode (Asm.table base code), pre := preExits (· == 0)
    statics := staticIn blocks (Asm.addr code base .table) }

def labels : List U.Label := [⟨entry, inProgram 0⟩]

asm_checked code start .start stack 0 program pg labels labels blocks blocks exits (· == 0)

end Tests.Written.Bounds
