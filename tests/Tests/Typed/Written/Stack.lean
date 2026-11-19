import TypedAsm
import TypedAsm.U.Checked

/-!
A stack of 64-bit numbers in a 256-byte region of main's frame:
  [s+0]  = top (count of items), [s+8 + 8*i] = item i, capacity 31.
push(rdi = &s, rsi = x) -> eax = 0 ok, 1 overflow
pop(rdi = &s)           -> rax = value, edx = 0 ok, 1 underflow
main pushes 1..5, pops five times, exits with the sum (15).
-/

open TypedAsm TypedAsm.U

namespace Tests.Written.Stack

inductive L
  | start | pushLoop | popLoop | done | fail
  | push | overflow | pop | underflow
  deriving DecidableEq, Hashable

def code : List (Asm L) := [
  .label .start,
  .ins (.alu .sub .w64 (.rm_i (.reg .rsp) 256)),
  .ins (.mov .w64 (.rm_i (.mem (.sib (some .rsp) none 0)) 0)),   -- top = 0
  .ins (.mov .w32 (.rm_i (.reg .rbx) 1)),
  .label .pushLoop,
  .ins (.mov .w64 (.rm_r (.reg .rdi) .rsp)),
  .ins (.mov .w64 (.rm_r (.reg .rsi) .rbx)),
  .call .push,
  .ins (.test .w32 (.reg .rax) (.reg .rax)),
  .jcc .ne .fail,
  .ins (.alu .add .w64 (.rm_i (.reg .rbx) 1)),
  .ins (.alu .cmp .w64 (.rm_i (.reg .rbx) 6)),
  .jcc .ne .pushLoop,
  .ins (.alu .xor .w32 (.rm_r (.reg .r12) .r12)),               -- sum
  .ins (.mov .w32 (.rm_i (.reg .rbx) 5)),
  .label .popLoop,
  .ins (.mov .w64 (.rm_r (.reg .rdi) .rsp)),
  .call .pop,
  .ins (.test .w32 (.reg .rdx) (.reg .rdx)),
  .jcc .ne .fail,
  .ins (.alu .add .w64 (.rm_r (.reg .r12) .rax)),
  .ins (.alu .sub .w64 (.rm_i (.reg .rbx) 1)),
  .jcc .ne .popLoop,
  .label .done,
  .ins (.mov .w32 (.rm_r (.reg .rdi) .r12)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .fail,
  .ins (.mov .w32 (.rm_i (.reg .rdi) 255)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  -- push(&s, x)
  .label .push,
  .ins (.mov .w64 (.r_m .rax (.sib (some .rdi) none 0))),
  .ins (.alu .cmp .w64 (.rm_i (.reg .rax) 31)),
  .jcc .ae .overflow,
  .ins (.mov .w64 (.rm_r (.mem (.sib (some .rdi) (some (.rax, .s8)) 8)) .rsi)),
  .ins (.alu .add .w64 (.rm_i (.reg .rax) 1)),
  .ins (.mov .w64 (.rm_r (.mem (.sib (some .rdi) none 0)) .rax)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .ins .ret,
  .label .overflow,
  .ins (.mov .w32 (.rm_i (.reg .rax) 1)),
  .ins .ret,
  -- pop(&s)
  .label .pop,
  .ins (.mov .w64 (.r_m .rax (.sib (some .rdi) none 0))),
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .e .underflow,
  .ins (.alu .sub .w64 (.rm_i (.reg .rax) 1)),
  .ins (.mov .w64 (.rm_r (.mem (.sib (some .rdi) none 0)) .rax)),
  .ins (.mov .w64 (.r_m .rax (.sib (some .rdi) (some (.rax, .s8)) 8))),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdx) .rdx)),
  .ins .ret,
  .label .underflow,
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 1)),
  .ins .ret]

asm_program code start .start stack 33

#guard exitsWith 15 (runMem linux 1000 start)

def pg : Prog := { code := progCode (Asm.table base code) }

/-- push and pop each take the 256-byte stack at rdi. The top, at offset 0,
is at most 31: said where each function is entered. -/
def top : Val := .named 0

def labels : List U.Label :=
  [⟨entry, inProgram 33⟩,
   ⟨Asm.addr code base .pushLoop, inProgram 33 (pushed := [.bytes 248, .val top])
     (known := [(top, .range 0 31)])⟩,
   ⟨Asm.addr code base .popLoop, inProgram 33 (pushed := [.bytes 248, .val top])
     (known := [(top, .range 0 31)])⟩,
   ⟨Asm.addr code base .push,
     inFunction (takes := [(.was .rdi, 256)]) (holds := [(.was .rdi, [(0, top)])])
       (known := [(top, .range 0 31)])
       (leaves := [(.was .rdi, [(0, .made 0)])]) (returns := [(.made 0, .range 0 31)])⟩,
   ⟨Asm.addr code base .pop,
     inFunction (takes := [(.was .rdi, 256)]) (holds := [(.was .rdi, [(0, top)])])
       (known := [(top, .range 0 31)])
       (leaves := [(.was .rdi, [(0, .made 0)])]) (returns := [(.made 0, .range 0 31)])⟩]

asm_checked code start .start stack 33 program pg labels labels

/-- The labels, `push` said to be entered with a top of up to thirty-two. -/
def labelsOver : List U.Label :=
  [⟨entry, inProgram 33⟩,
   ⟨Asm.addr code base .pushLoop, inProgram 33 (pushed := [.bytes 248, .val top])
     (known := [(top, .range 0 31)])⟩,
   ⟨Asm.addr code base .popLoop, inProgram 33 (pushed := [.bytes 248, .val top])
     (known := [(top, .range 0 31)])⟩,
   ⟨Asm.addr code base .push,
     inFunction (takes := [(.was .rdi, 256)]) (holds := [(.was .rdi, [(0, top)])])
       (known := [(top, .range 0 32)])
       (leaves := [(.was .rdi, [(0, .made 0)])]) (returns := [(.made 0, .range 0 31)])⟩,
   ⟨Asm.addr code base .pop,
     inFunction (takes := [(.was .rdi, 256)]) (holds := [(.was .rdi, [(0, top)])])
       (known := [(top, .range 0 31)])
       (leaves := [(.was .rdi, [(0, .made 0)])]) (returns := [(.made 0, .range 0 31)])⟩]

-- a thirty-third value would be stored past the memory it takes. Refused
#guard !wholeOkWith code .start 33 [] (blocksOf code .start) pg labelsOver (needFuel pg labelsOver [])

end Tests.Written.Stack
