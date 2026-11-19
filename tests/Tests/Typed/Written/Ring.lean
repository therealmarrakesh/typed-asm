import TypedAsm
import TypedAsm.U.Checked

/-!
A ring buffer of 16 bytes in main's frame:
  [r+0] head (count of gets), [r+8] tail (count of puts), [r+16..32) data.
put(rdi = &r, sil = byte) -> eax = 0 ok, 1 full
get(rdi = &r)             -> eax = byte, or -1 when empty
main: for i = 0..19: put(i); sum += get(). Exits with the sum, 190.
-/

open TypedAsm TypedAsm.U

namespace Tests.Written.Ring

inductive L
  | start | loop | fail | put | full | get | empty
  deriving DecidableEq, Hashable

def code : List (Asm L) := [
  .label .start,
  .ins (.alu .sub .w64 (.rm_i (.reg .rsp) 32)),
  .ins (.mov .w64 (.rm_i (.mem (.sib (some .rsp) none 0)) 0)),
  .ins (.mov .w64 (.rm_i (.mem (.sib (some .rsp) none 8)) 0)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rbx) .rbx)),     -- i
  .ins (.alu .xor .w32 (.rm_r (.reg .r12) .r12)),     -- sum
  .label .loop,
  .ins (.mov .w64 (.rm_r (.reg .rdi) .rsp)),
  .ins (.mov .w32 (.rm_r (.reg .rsi) .rbx)),
  .call .put,
  .ins (.test .w32 (.reg .rax) (.reg .rax)),
  .jcc .ne .fail,
  .ins (.mov .w64 (.rm_r (.reg .rdi) .rsp)),
  .call .get,
  .ins (.test .w32 (.reg .rax) (.reg .rax)),
  .jcc .s .fail,
  .ins (.alu .add .w64 (.rm_r (.reg .r12) .rax)),
  .ins (.alu .add .w64 (.rm_i (.reg .rbx) 1)),
  .ins (.alu .cmp .w64 (.rm_i (.reg .rbx) 20)),
  .jcc .ne .loop,
  .ins (.mov .w32 (.rm_r (.reg .rdi) .r12)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .fail,
  .ins (.mov .w32 (.rm_i (.reg .rdi) 255)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  -- put(&r, byte)
  .label .put,
  .ins (.mov .w64 (.r_m .rax (.sib (some .rdi) none 8))),
  .ins (.mov .w64 (.rm_r (.reg .rcx) .rax)),
  .ins (.alu .sub .w64 (.r_m .rcx (.sib (some .rdi) none 0))),
  .ins (.alu .cmp .w64 (.rm_i (.reg .rcx) 16)),
  .jcc .ae .full,
  .ins (.alu .and .w32 (.rm_i (.reg .rax) 15)),
  .ins (.store8 (.sib (some .rdi) (some (.rax, .s1)) 16) .rsi),
  .ins (.alu .add .w64 (.rm_i (.mem (.sib (some .rdi) none 8)) 1)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .ins .ret,
  .label .full,
  .ins (.mov .w32 (.rm_i (.reg .rax) 1)),
  .ins .ret,
  -- get(&r)
  .label .get,
  .ins (.mov .w64 (.r_m .rax (.sib (some .rdi) none 0))),
  .ins (.alu .cmp .w64 (.r_m .rax (.sib (some .rdi) none 8))),
  .jcc .e .empty,
  .ins (.mov .w64 (.rm_r (.reg .rcx) .rax)),
  .ins (.alu .and .w32 (.rm_i (.reg .rcx) 15)),
  .ins (.movzx .w32 .rdx .w8 (.mem (.sib (some .rdi) (some (.rcx, .s1)) 16))),
  .ins (.alu .add .w64 (.rm_i (.reg .rax) 1)),
  .ins (.mov .w64 (.rm_r (.mem (.sib (some .rdi) none 0)) .rax)),
  .ins (.mov .w32 (.rm_r (.reg .rax) .rdx)),
  .ins .ret,
  .label .empty,
  .ins (.mov .w64 (.rm_i (.reg .rax) (-1))),
  .ins .ret]

asm_program code start .start stack 5

#guard exitsWith 190 (runMem linux 10000 start)

def pg : Prog := { code := progCode (Asm.table base code) }

def labels : List U.Label :=
  [⟨entry, inProgram 5⟩,
   ⟨Asm.addr code base .loop, inProgram 5 (pushed := [.bytes 32])⟩,
   ⟨Asm.addr code base .put, inFunction (takes := [(.was .rdi, 32)])⟩,
   ⟨Asm.addr code base .get, inFunction (takes := [(.was .rdi, 32)])⟩]

asm_checked code start .start stack 5 program pg labels labels

/-- The labels, `put` said to take thirty-one bytes. -/
def labelsShort : List U.Label :=
  [⟨entry, inProgram 5⟩,
   ⟨Asm.addr code base .loop, inProgram 5 (pushed := [.bytes 32])⟩,
   ⟨Asm.addr code base .put, inFunction (takes := [(.was .rdi, 31)])⟩,
   ⟨Asm.addr code base .get, inFunction (takes := [(.was .rdi, 32)])⟩]

-- the last of the sixteen bytes it may store into is the thirty-second. Refused
#guard !wholeOkWith code .start 5 [] (blocksOf code .start) pg labelsShort (needFuel pg labelsShort [])

end Tests.Written.Ring
