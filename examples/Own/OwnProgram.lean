import TypedAsm

/-!
# Owning memory, proved safe

Takes a page from the kernel, uses it and gives it back; takes two more,
gives one of them back, fills the other in, and keeps it as an ordinary
block. It exits with status 100.

```asm
_start:
     mov   eax, 9                ; `mmap` one page
     xor   edi, edi
     mov   esi, 4096
     mov   edx, 3
     mov   r10d, 0x22
     mov   r8, -1
     xor   r9d, r9d
     syscall
     test  rax, rax
     js    fail
     mov   rbx, rax              ; the page: ours
     mov   ecx, 40
     mov   [rbx], rcx            ; a number
     mov   ecx, 2
     mov   [rbx + 8], rcx        ; another
     mov   [rbx + 16], rbx       ; and the page's own address
     mov   rdx, [rbx + 16]       ; read the address back
     mov   r12, [rdx]            ; and use it: 40
     add   r12, [rbx + 8]        ; 42
     mov   eax, 11               ; `munmap`: give the page back
     mov   rdi, rbx
     mov   esi, 4096
     syscall
     mov   eax, 9                ; `mmap` two more
     xor   edi, edi
     mov   esi, 8192
     mov   edx, 3
     mov   r10d, 0x22
     syscall
     test  rax, rax
     js    fail
     mov   rbx, rax
     lea   rdi, [rbx + 4096]     ; the second of them
     mov   esi, 4096
     mov   eax, 11               ; `munmap`: give it back, and keep the first
     syscall
     lea   rcx, [rip + record]
     mov   [rbx], rcx            ; its first field: a pointer to the record
     mov   rdx, [rbx]            ; now an ordinary block: follow the pointer
     mov   rdi, [rdx]            ; 58
     add   rdi, r12              ; 100
     mov   eax, 231              ; `exit_group`
     syscall
fail:
     mov   edi, 1
     mov   eax, 231
     syscall
```

The first page is never anything but the program's own. Its fields take the
type of whatever is stored in them, a number or an address, because nothing
else can be looking; and once it is given back, the context no longer lists
it, so nothing typed can touch it again.

The two pages that come next arrive as one block, and the program gives one
of them back and keeps the other. Giving back part of a block is typed by
regarding the block as two, the part given back and the rest: no instruction
does that, it is how the memory the program already has is looked at, and
the checker looks at it so where a `munmap` asks for it.

The page that is kept shows what owning is for besides scratch space: a
field of it is given an address, a pointer that is never null, which fresh
memory, being zero, could not be said to hold. The field takes the type of
what is stored in it, and what is loaded from it is that pointer.

An owned block can also be split wherever the author likes, two that lie end
to end joined, and a block that has been filled in frozen into an ordinary
block that others may point to (`ty_split`, `ty_join`, `ty_freeze`); this
program needs none of that said.

`lake exe own` runs it in the model; `lake exe own --elf FILE` writes an
executable that Linux can run.
-/

open TypedAsm

namespace Own

/-! ## The program -/

inductive Label
  | start | fail | record
  deriving DecidableEq

/-- The data's bytes: a record of one number, 58. -/
def recordBytes : List Byte := [58, 0, 0, 0, 0, 0, 0, 0]

def code : List (Asm Label) := [
  .label .start,
  .ins (.mov .w32 (.rm_i (.reg .rax) 9)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rsi) 4096)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 3)),
  .ins (.mov .w32 (.rm_i (.reg .r10) 0x22)),
  .ins (.mov .w64 (.rm_i (.reg .r8) (-1))),
  .ins (.alu .xor .w32 (.rm_r (.reg .r9) .r9)),
  .ins .syscall,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .s .fail,
  .ins (.mov .w64 (.rm_r (.reg .rbx) .rax)),
  .ins (.mov .w32 (.rm_i (.reg .rcx) 40)),
  .ins (.mov .w64 (.rm_r (.mem (.sib (some .rbx) none 0)) .rcx)),
  .ins (.mov .w32 (.rm_i (.reg .rcx) 2)),
  .ins (.mov .w64 (.rm_r (.mem (.sib (some .rbx) none 8)) .rcx)),
  .ins (.mov .w64 (.rm_r (.mem (.sib (some .rbx) none 16)) .rbx)),
  .ins (.mov .w64 (.r_m .rdx (.sib (some .rbx) none 16))),
  .ins (.mov .w64 (.r_m .r12 (.sib (some .rdx) none 0))),
  .ins (.alu .add .w64 (.r_m .r12 (.sib (some .rbx) none 8))),
  .ins (.mov .w32 (.rm_i (.reg .rax) 11)),
  .ins (.mov .w64 (.rm_r (.reg .rdi) .rbx)),
  .ins (.mov .w32 (.rm_i (.reg .rsi) 4096)),
  .ins .syscall,
  .ins (.mov .w32 (.rm_i (.reg .rax) 9)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rsi) 8192)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 3)),
  .ins (.mov .w32 (.rm_i (.reg .r10) 0x22)),
  .ins .syscall,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .s .fail,
  .ins (.mov .w64 (.rm_r (.reg .rbx) .rax)),
  .ins (.lea .w64 .rdi (.sib (some .rbx) none 4096)),
  .ins (.mov .w32 (.rm_i (.reg .rsi) 4096)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 11)),
  .ins .syscall,
  .ref (.lea .w64 .rcx (.rip 0)) .record,
  .ins (.mov .w64 (.rm_r (.mem (.sib (some .rbx) none 0)) .rcx)),
  .ins (.mov .w64 (.r_m .rdx (.sib (some .rbx) none 0))),
  .ins (.mov .w64 (.r_m .rdi (.sib (some .rdx) none 0))),
  .ins (.alu .add .w64 (.rm_r (.reg .rdi) .r12)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 231)),
  .ins .syscall,
  .label .fail,
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 231)),
  .ins .syscall,
  .segment .ro,
  .label .record, .bytes recordBytes]

-- Where the program is loaded, what it puts in memory, where it starts and the
-- state it starts in, all from the lines above.
-- The starting state but for `rip`: the program in memory, and with it the
-- record, in read-only memory. The program uses no stack.
asm_program code start .start stack 0 named "own"

/-- A page for each request for memory, one after another. -/
def pages : Nat → Option (BitVec 64) :=
  fun i => some (BitVec.ofNat 64 (0x10000000 + 4096 * i))

/-- The starting state with the given answers to requests for memory. -/
def startWith (place : Nat → Option (BitVec 64)) : State :=
  { start with world := { place := place } }

/-! ## Running it -/

-- With no memory to be had it exits with status 1.
#guard wroteAndExited "" 1 (runMemFinal linux 1000 start)

-- With memory, it exits with status 100.
#guard wroteAndExited "" 100 (runMemFinal linux 1000 (startWith pages))

-- The kernel may put the second page where the first was, now that it has
-- been given back.
#guard wroteAndExited "" 100
  (runMemFinal linux 1000 (startWith fun _ => some 0x10000000))

-- By the end the first page is inaccessible again, and of the two that
-- followed, the one that was kept is not and the one given back is.
#guard (runMemFinal linux 1000 (startWith pages)).1.perm 0x10000000 == .none
#guard (runMemFinal linux 1000 (startWith pages)).1.perm 0x10001000 == .rw
#guard (runMemFinal linux 1000 (startWith pages)).1.perm 0x10002000 == .none

-- If only the first request is granted it gives that page back and exits
-- with status 1.
#guard wroteAndExited "" 1
  (runMemFinal linux 1000 (startWith fun i => if i = 0 then pages 0 else none))

end Own

