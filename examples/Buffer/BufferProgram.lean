import TypedAsm

/-!
# Reading into a buffer on the stack, proved safe

The same program as `Echo`, copying standard input to standard output
sixteen bytes at a time, but with its buffer in two stack slots, not in
the data.

```asm
_start:
     sub   rsp, 16              ; the buffer
loop:
     xor   eax, eax             ; `read`
     xor   edi, edi             ; from standard input
     lea   rsi, [rsp]           ; into the buffer
     mov   edx, 16
     syscall
     test  rax, rax
     jle   done                 ; nothing left, or an error
     mov   rdx, rax             ; as many bytes as were read
     mov   eax, 1               ; `write`
     mov   edi, 1               ; to standard output
     syscall
     jmp   loop
done:
     mov   eax, 60              ; `exit`
     xor   edi, edi
     syscall
```

For the `read` to be safe the kernel must be storing into stack slots that
hold integers. The address in `rsi` is computed from `rsp`, so the typing
has to know where `rsp` points: its value is given a name, the `lea` then
yields a known address, and the `read` is checked against the slots that
address covers.

`lake exe buffer` runs it in the model on this process's standard input;
`lake exe buffer --elf FILE` writes an executable that Linux can run.
-/

open TypedAsm

namespace Buffer

/-! ## The program -/

/-- Labels mark where control can arrive from elsewhere. -/
inductive Label
  | start | loop | done
  deriving DecidableEq

def code : List (Asm Label) := [
  .label .start,
  .ins (.alu .sub .w64 (.rm_i (.reg .rsp) 16)),
  .label .loop,
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.lea .w64 .rsi (.sib (some .rsp) none 0)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 16)),
  .ins .syscall,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .le .done,
  .ins (.mov .w64 (.rm_r (.reg .rdx) .rax)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins .syscall,
  .jmp .loop,
  .label .done,
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins .syscall]

/-- Where the code is loaded. -/
def base : BitVec 64 := BitVec.ofNat 64 Elf.codeBase

/-- The program has no data; this is where its empty data segment goes. -/
def dataBase : BitVec 64 := BitVec.ofNat 64 Elf.dataBase

def fetch : Fetch := Asm.fetch base code

/-- The program's bytes. -/
def image : List Byte := Asm.image base code

/-- The address execution starts at. -/
def entry : BitVec 64 := Asm.addr code base .start

-- Every jump reaches the label it names.
#guard Asm.offsetsFit base code

/-- Everything in the starting state except the program itself: two free
stack slots below `rsp`. -/
def prepared : State :=
  ((State.init.loadData dataBase [] .ro).setPerm 0x7ffffff0 16 .rw).setReg .rsp 0x80000000

/-- A starting state: `prepared`, with the program's bytes in executable
memory and `rip` at the entry. Nothing is waiting to be read. -/
def start : State :=
  { prepared.loadCode base image with rip := entry }

/-- The starting state with the given input waiting, one event per `read`. -/
def startWith (input : List ReadEvent) : State :=
  { start with world := { input := input } }

/-! ## Running it -/

-- With nothing to read it exits at once, having written nothing.
#guard wroteAndExited "" 0 (runMemFinal linux 1000 start)

-- Input comes back unchanged, in pieces no longer than the buffer.
#guard wroteAndExited "hello, world: this is longer than sixteen bytes\n" 0
  (runMemFinal linux 1000
    (startWith [.bytes (bytesOf "hello, "),
      .bytes (bytesOf "world: this is longer than sixteen bytes\n")]))

end Buffer

/-- The program, with what running it takes. -/
def Buffer.program : Runnable where
  name := "buffer"
  entry := Buffer.entry.toNat
  image := Buffer.image
  start := Buffer.start
  readsInput := true
