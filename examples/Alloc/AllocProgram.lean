import TypedAsm

/-!
# Allocating memory, proved safe

Reads standard input in pieces of up to 64 bytes, keeps each piece in a node
of a linked list, and then writes the pieces out, last one first. The nodes
do not exist when the program starts: each is memory asked of the kernel
with `mmap` while the program runs.

```asm
_start:
     xor   ebx, ebx              ; the list is empty
next:
     mov   eax, 9                ; `mmap`
     xor   edi, edi              ; anywhere
     mov   esi, 80               ; one node: a link, a length, 64 bytes
     mov   edx, 3                ; to read and write
     mov   r10d, 0x22            ; private, not a file
     mov   r8, -1
     xor   r9d, r9d
     syscall
     test  rax, rax
     js    print                 ; no memory: write what there is
     mov   r12, rax
     mov   [r12], rbx            ; the new node links to the list so far
     mov   rbx, rax              ; and is now its head
     xor   eax, eax              ; `read`
     xor   edi, edi
     mov   rsi, r12
     add   rsi, 16               ; into the node's 64 bytes
     mov   edx, 64
     syscall
     test  rax, rax
     jle   print                 ; nothing left, or an error
     mov   [r12 + 8], rax        ; how many bytes the node holds
     jmp   next
print:
     test  rbx, rbx
     jz    done                  ; end of the list
     mov   eax, 1                ; `write`
     mov   edi, 1
     mov   rsi, rbx
     add   rsi, 16
     mov   rdx, [rbx + 8]
     syscall
     mov   rbx, [rbx]            ; on to the node before
     jmp   print
done:
     xor   edi, edi
     mov   eax, 60               ; `exit`
     syscall
```

Two things make this safe. What `mmap` hands back is an error number or the
address of a new node, and the program may use it as a node only after the
test that tells the two apart. And a new node is typed as it comes, all
zero: its link is a null link and its length is zero, so it is a proper node
before anything is stored in it. A node whose `read` finds nothing stays in
the list holding no bytes.

Like `Echo`, the program trusts each `write` to take everything it is given.

`lake exe alloc` runs it in the model on this process's standard input;
`lake exe alloc --elf FILE` writes an executable that Linux can run.
-/

open TypedAsm

namespace Alloc

/-! ## The program -/

/-- Labels mark where control can arrive from elsewhere. -/
inductive Label
  | start | next | linked | print | done
  deriving DecidableEq, Hashable

def code : List (Asm Label) := [
  .label .start,
  .ins (.alu .xor .w32 (.rm_r (.reg .rbx) .rbx)),
  .label .next,
  .ins (.mov .w32 (.rm_i (.reg .rax) 9)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rsi) 80)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 3)),
  .ins (.mov .w32 (.rm_i (.reg .r10) 0x22)),
  .ins (.mov .w64 (.rm_i (.reg .r8) (-1))),
  .ins (.alu .xor .w32 (.rm_r (.reg .r9) .r9)),
  .ins .syscall,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .s .print,
  .ins (.mov .w64 (.rm_r (.reg .r12) .rax)),
  .ins (.mov .w64 (.rm_r (.mem (.sib (some .r12) none 0)) .rbx)),
  .label .linked,
  .ins (.mov .w64 (.rm_r (.reg .rbx) .rax)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w64 (.rm_r (.reg .rsi) .r12)),
  .ins (.alu .add .w64 (.rm_i (.reg .rsi) 16)),
  .ins (.mov .w32 (.rm_i (.reg .rdx) 64)),
  .ins .syscall,
  .ins (.test .w64 (.reg .rax) (.reg .rax)),
  .jcc .le .print,
  .ins (.mov .w64 (.rm_r (.mem (.sib (some .r12) none 8)) .rax)),
  .jmp .next,
  .label .print,
  .ins (.test .w64 (.reg .rbx) (.reg .rbx)),
  .jcc .e .done,
  .ins (.mov .w32 (.rm_i (.reg .rax) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ins (.mov .w64 (.rm_r (.reg .rsi) .rbx)),
  .ins (.alu .add .w64 (.rm_i (.reg .rsi) 16)),
  .ins (.mov .w64 (.r_m .rdx (.sib (some .rbx) none 8))),
  .ins .syscall,
  .ins (.mov .w64 (.r_m .rbx (.sib (some .rbx) none 0))),
  .jmp .print,
  .label .done,
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall]

-- Where the program is loaded, what it puts in memory, where it starts and the
-- state it starts in, all from the lines above.
-- The starting state but for `rip`: the program in memory. The program uses no
-- stack.
asm_program code start .start stack 0

/-- A page for each request for memory, one after another. -/
def pages : Nat → Option (BitVec 64) :=
  fun i => some (BitVec.ofNat 64 (0x10000000 + 4096 * i))

/-- The starting state with the given input waiting, one event per `read`,
and the given answers to requests for memory. -/
def startWith (input : List ReadEvent) (place : Nat → Option (BitVec 64) := pages) : State :=
  { start with world := { input := input, place := place } }

/-! ## Running it -/

-- With no memory to be had it exits at once, having written nothing.
#guard wroteAndExited "" 0 (runMemFinal linux 1000 start)

-- The pieces come back last one first.
#guard wroteAndExited "three two one " 0
  (runMemFinal linux 1000
    (startWith [.bytes (bytesOf "one "), .bytes (bytesOf "two "), .bytes (bytesOf "three ")]))

-- A piece longer than a node is split across several.
#guard wroteAndExited (String.ofList (List.replicate 6 'b') ++ String.ofList (List.replicate 64 'a')) 0
  (runMemFinal linux 1000
    (startWith [.bytes (bytesOf (String.ofList (List.replicate 64 'a' ++ List.replicate 6 'b')))]))

-- When memory runs out, what was read up to then is still written.
#guard wroteAndExited "two one " 0
  (runMemFinal linux 1000
    (startWith [.bytes (bytesOf "one "), .bytes (bytesOf "two "), .bytes (bytesOf "three ")]
      (fun i => if i < 2 then pages i else none)))

-- The kernel never hands out memory that is already in use. A world that
-- proposes the program's own code as the place for a node is refused.
#guard wroteAndExited "" 0
  (runMemFinal linux 1000 (startWith [.bytes (bytesOf "one ")] (fun _ => some base)))

end Alloc

/-- The program, with what running it takes. -/
def Alloc.program : Runnable where
  name := "alloc"
  elf := Asm.elf Alloc.base Alloc.code .start
  startArgs := Alloc.startArgs
  readsInput := true
