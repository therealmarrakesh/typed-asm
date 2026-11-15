import TypedAsm

/-!
# A function that hands back two pages, called through a pointer, proved safe

Takes the address of a function, calls it through that address, and gets two
pages back, one in `rax` and one in `rdx`. It stores each page's address in
the other, follows the two addresses round to where it started, gives both
pages back, and exits with status 0, or 1 if the kernel has no memory to
give.

```asm
_start:
     lea   r12, [rip + two]      ; the function's address
     call  r12                   ; two pages, at addresses in `rax` and `rdx`
back:
     mov   rbx, rax              ; the first page
     mov   r13, rdx              ; the second
     mov   [rbx], r13            ; in each, the address of the other
     mov   [r13], rbx
     mov   rcx, [rbx]            ; from the first to the second
     mov   rcx, [rcx]            ; and back to the first
     mov   eax, 11               ; `munmap` the page that led back to
     mov   rdi, rcx
     mov   esi, 4096
     syscall
     mov   eax, 11               ; and the other
     mov   rdi, r13
     mov   esi, 4096
     syscall
     xor   edi, edi
     mov   eax, 231              ; `exit_group`
     syscall
two:                             ; returns two pages nobody else has
     mov   eax, 9                ; `mmap` the first
     xor   edi, edi
     mov   esi, 4096
     mov   edx, 3
     mov   r10d, 0x22
     mov   r8, -1
     xor   r9d, r9d
     syscall
     test  rax, rax
     js    fail
     push  rax                   ; keep it while asking for the second
     mov   eax, 9
     xor   edi, edi
     mov   esi, 4096
     mov   edx, 3
     mov   r10d, 0x22
     mov   r8, -1
     xor   r9d, r9d
     syscall
     test  rax, rax
     js    fail
     mov   rdx, rax
     pop   rax
     ret
fail:
     mov   edi, 1
     mov   eax, 231
     syscall
```

What `two` chooses as it returns is a pair of addresses, and its signature
says that whatever pair that is, the caller owns a page at each. The call is
through a register that holds a pointer to the function: the pointer's type
carries the whole signature, so calling through it is typed exactly as
calling the function by name would be.

`lake exe pair` runs it in the model; `lake exe pair --elf FILE` writes an
executable that Linux can run.
-/

open TypedAsm

namespace Pair

/-! ## The program -/

inductive Label
  | start | back | two | fail
  deriving DecidableEq

/-- The arguments of an `mmap` of one page, the call, and the test that sends
an error number to `fail`. -/
def askPage : List (Asm Label) := [
  .ins (.mov .w32 (.rm_i (.reg .rax) 9)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rsi) 4096)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 3)),
  .ins (.mov .w32 (.rm_i (.reg .r10) 0x22)),
  .ins (.mov .w64 (.rm_i (.reg .r8) (-1))),
  .ins (.alu .xor .w32 (.rm_r (.reg .r9) .r9)),
  .ins .syscall,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .s .fail]

/-- How far the function is from the instruction after the `lea`. -/
def toTwo : BitVec 32 := 61

def code : List (Asm Label) := [
  .label .start,
  .ins (.lea .w64 .r12 (.rip toTwo)),
  .ins (.call (.ind (.reg .r12))),
  .label .back,
  .ins (.mov .w64 (.rm_r (.reg .rbx) .rax)),
  .ins (.mov .w64 (.rm_r (.reg .r13) .rdx)),
  .ins (.mov .w64 (.rm_r (.mem (.sib (some .rbx) none 0)) .r13)),
  .ins (.mov .w64 (.rm_r (.mem (.sib (some .r13) none 0)) .rbx)),
  .ins (.mov .w64 (.r_m .rcx (.sib (some .rbx) none 0))),
  .ins (.mov .w64 (.r_m .rcx (.sib (some .rcx) none 0))),
  .ins (.mov .w32 (.rm_i (.reg .rax) 11)),
  .ins (.mov .w64 (.rm_r (.reg .rdi) .rcx)),
  .ins (.mov .w32 (.rm_i (.reg .rsi) 4096)),
  .ins .syscall,
  .ins (.mov .w32 (.rm_i (.reg .rax) 11)),
  .ins (.mov .w64 (.rm_r (.reg .rdi) .r13)),
  .ins (.mov .w32 (.rm_i (.reg .rsi) 4096)),
  .ins .syscall,
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 231)),
  .ins .syscall,
  .label .two] ++ askPage ++ [
  .ins (.push .rax)] ++ askPage ++ [
  .ins (.mov .w64 (.rm_r (.reg .rdx) .rax)),
  .ins (.pop .rax),
  .ins .ret,
  .label .fail,
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 231)),
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

-- Every jump reaches the label it names, and the address computation gives
-- the address of the function.
#guard Asm.offsetsFit base code
#guard base + 7 + toTwo.signExtend 64 == Asm.addr code base .two

/-- Everything in the starting state except the program itself: two free
stack slots, for a return address and the page the function keeps while it
asks for another. -/
def prepared : State :=
  ((State.init.loadData dataBase [] .ro).setPerm 0x7ffffff0 16 .rw).setReg .rsp 0x80000000

/-- A starting state: `prepared`, with the program's bytes in executable
memory and `rip` at the entry. Every request for memory is refused. -/
def start : State :=
  { prepared.loadCode base image with rip := entry }

/-- A page for each request for memory, one after another. -/
def pages : Nat → Option (BitVec 64) :=
  fun i => some (BitVec.ofNat 64 (0x10000000 + 4096 * i))

/-- The starting state with the given answers to requests for memory. -/
def startWith (place : Nat → Option (BitVec 64)) : State :=
  { start with world := { place := place } }

/-! ## Running it -/

-- With no memory to be had it exits with status 1.
#guard wroteAndExited "" 1 (runMemFinal linux 1000 start)

-- With memory, it exits with status 0, and both pages are inaccessible again.
#guard wroteAndExited "" 0 (runMemFinal linux 1000 (startWith pages))
#guard (runMemFinal linux 1000 (startWith pages)).1.perm 0x10000000 == .none
#guard (runMemFinal linux 1000 (startWith pages)).1.perm 0x10001000 == .none

-- If only the first request is granted it exits with status 1.
#guard wroteAndExited "" 1
  (runMemFinal linux 1000 (startWith fun i => if i = 0 then pages 0 else none))

end Pair

/-- The program, with what running it takes. -/
def Pair.program : Runnable where
  name := "pair"
  entry := Pair.entry.toNat
  image := Pair.image
  start := Pair.start
