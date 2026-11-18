import TypedAsm
import TypedAsm.U.Checked
import Buffer

/-!
# What is written is what was read

```asm
_start:
     sub   rsp, 16
     xor   edi, edi
     mov   rsi, rsp
     mov   edx, 16
     xor   eax, eax
     syscall              ; read(0, buf, 16)
     test  rax, rax
     js    done           ; an error number
     jz    done           ; nothing more to read
     mov   rdx, rax       ; as many as were read
     mov   edi, 1
     mov   eax, 1
     syscall              ; write(1, buf, that many)
done:
     xor   edi, edi
     mov   eax, 60
     syscall
```

The program is proved to offer, at every `write`, a stretch of what its
last `read` stored: here, all of it. It is typed because the `read` leaves
the buffer said to be those bytes, and nothing has stored into it since.
-/

open TypedAsm TypedAsm.U

namespace Tests.Written.CatOnce

inductive L
  | start | done
  deriving DecidableEq, Hashable

/-- The program, with instructions more between the count's being set and
the `write`. -/
def codeOf (more : List (Asm L)) : List (Asm L) := [
  .label .start,
  .ins (.alu .sub .w64 (.rm_i (.reg .rsp) 16)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w64 (.rm_r (.reg .rsi) .rsp)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 16)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .ins .syscall,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .s .done,
  .jcc .e .done,
  .ins (.mov .w64 (.rm_r (.reg .rdx) .rax))] ++ more ++ [
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 1)),
  .ins .syscall,
  .label .done,
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall]

def code : List (Asm L) := codeOf []

asm_program code start .start stack 2

/-- Whether the program with those instructions more is typed, every
`write` to offer a stretch of the last `read`. -/
def typed (more : List (Asm L)) : Bool :=
  let pg : Prog :=
    { code := progCode (Asm.table (Asm.base (codeOf more)) (codeOf more))
      pre := preEcho (· == 0) }
  let labels : List U.Label :=
    [⟨Asm.addr (codeOf more) (Asm.base (codeOf more)) .start, inProgram 2⟩]
  wholeOkWith (codeOf more) .start 2 [] (blocksOf (codeOf more) .start) pg labels
    (needFuel pg labels [])

#guard typed []
-- one byte more offered than was read. Refused
#guard !typed [.ins (.alu .add .w64 (.rm_i (.reg .rdx) 1))]
-- a byte stored into the buffer before it is written. Refused
#guard !typed [.ins (.store8 (.sib (some .rsp) none 0) .rax)]
-- as many offered from one byte further in. Refused
#guard !typed [.ins (.alu .add .w64 (.rm_i (.reg .rsi) 1))]

def pg : Prog := { code := progCode (Asm.table base code), pre := preEcho (· == 0) }

def labels : List U.Label := [⟨entry, inProgram 2⟩]

asm_checked code start .start stack 2 program pg labels labels exits (· == 0) echoes

/-! The program of `examples/Buffer` reads and writes so in a loop, until
there is no more: it is typed the same way, with the labels it has. -/

/-- That program, asked of every `write` that it offer a stretch of the
last `read`. -/
def loopPg : Prog := { code := Buffer.pg.code, pre := preEcho (· == 0) }

#guard wholeOkWith Buffer.code .start 2 [] (blocksOf Buffer.code .start) loopPg Buffer.labels
  (needFuel loopPg Buffer.labels [])

end Tests.Written.CatOnce
