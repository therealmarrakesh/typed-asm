import TypedAsm

/-!
# A stack address kept across a call, proved safe

The program takes the address of a buffer in its own stack frame, calls a
function, and only then reads into the buffer through the address it took
before the call.

```asm
_start:
     sub   rsp, 16              ; the buffer
     lea   rbx, [rsp]           ; its address, kept in a preserved register
     call  pause
back:
     xor   eax, eax             ; `read`
     xor   edi, edi
     mov   rsi, rbx             ; into the buffer
     mov   edx, 16
     syscall
     test  rax, rax
     jle   done
     mov   rdx, rax
     mov   eax, 1               ; `write` what was read
     mov   edi, 1
     syscall
done:
     mov   eax, 60              ; `exit`
     xor   edi, edi
     syscall
pause:
     ret
```

For the `read` to be typed, the address in `rsi` must be known to lie in
this frame's two slots. It was computed from the stack pointer before the
call, so the stack pointer afterwards must be known to be where it was.
The function's signature says so: it lists `rsp` among the registers the
function preserves.

`lake exe keep` runs it in the model on this process's standard input;
`lake exe keep --elf FILE` writes an executable that Linux can run.
-/

open TypedAsm

namespace Keep

/-! ## The program -/

/-- Labels mark where control can arrive from elsewhere. -/
inductive Label
  | start | back | done | pause
  deriving DecidableEq

def code : List (Asm Label) := [
  .label .start,
  .ins (.alu .sub .w64 (.rm_i (.reg .rsp) 16)),
  .ins (.lea .w64 .rbx (.sib (some .rsp) none 0)),
  .call .pause,
  .label .back,
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w64 (.rm_r (.reg .rsi) .rbx)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 16)),
  .ins .syscall,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .le .done,
  .ins (.mov .w64 (.rm_r (.reg .rdx) .rax)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins .syscall,
  .label .done,
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins .syscall,
  .label .pause,
  .ins .ret]

/-- Where the code is loaded. -/
def base : BitVec 64 := Asm.base code

def fetch : Fetch := Asm.fetch base code

/-- What the program puts in memory, line by line. -/
def parts : List (Nat × Perm × List Byte) := Asm.parts base code

/-- The address execution starts at. -/
def entry : BitVec 64 := Asm.addr code base .start

-- Every jump and call reaches the label it names.
#guard Asm.offsetsFit base code

/-- The starting state but for `rip`: the program in memory, and with it three
free stack slots below `rsp`, two for the buffer and one for the return
address. -/
def prepared : State :=
  ((Asm.load State.init base code).setPerm 0x7fffffe8 24 .rw).setReg .rsp 0x80000000

/-- A starting state: `prepared`, with `rip` at the entry. -/
def start : State :=
  { prepared with rip := entry }

/-- The starting state with the given input waiting. -/
def startWith (input : List ReadEvent) : State :=
  { start with world := { input := input } }

-- What is read comes back out.
#guard wroteAndExited "kept\n" 0 (runMemFinal linux 1000 (startWith [.bytes (bytesOf "kept\n")]))

end Keep

/-- The program, with what running it takes. -/
def Keep.program : Runnable where
  name := "keep"
  elf := Asm.elf Keep.base Keep.code .start
  start := Keep.start
  readsInput := true
