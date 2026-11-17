import TypedAsm.U.Upper
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
import Tests.Typed.Refused

/-!
# The checker's tests: whole

A state's whole memory, and programs end to end. Each is checked by the kernel as this file is compiled: what the
checker accepts, and what it refuses.
-/

open TypedAsm TypedAsm.U

namespace Tests.Unified

/-! ## All the memory a first state has -/

/-- Two pages that may be written, and one of code. -/
def sLoad : State := (State.init.setPerm 0x10000 8192 .rw).setPerm 0x400000 4096 .rx

theorem sLoad_within : PermsWithin sLoad [(0x400000, 4096), (0x10000, 8192)] :=
  (PermsWithin.init.setPerm 0x10000 8192 .rw).setPerm 0x400000 4096 .rx

-- every byte the machine can touch is in one of the two ranges of bytes
example (a : BitVec 64) (ha : sLoad.perm a ≠ .none) :
    ∃ c ∈ [((0x10000 : BitVec 64), 8192), (0x400000, 4096)], (a - c.1).toNat < c.2 :=
  sLoad_within.covered (by decide +kernel) ha
-- a range one page short does not cover the pages given: the check says so
example : [((0x400000 : BitVec 64), (4096 : BitVec 64)), (0x10000, 8192)].all
    (stretchIn [(0x10000, 4096), (0x400000, 4096)]) = false := by decide +kernel

/-! ## A program end to end: Hello

The program as written; and one check, that its labels' code is typed and
that the state it is loaded into starts as its entry asks. So it is safe, on the machine that
decodes its instructions from memory; it ends only with status nought; and
at its one `write` it offers exactly its message, to descriptor 1. -/

namespace HelloU
inductive Label
  | start | message
  deriving DecidableEq
def message : List Byte := "Hello, world!\n".toUTF8.toList.map fun b => BitVec.ofNat 8 b.toNat
def code : List (Asm Label) := [
  .label .start,
  .ins (.mov .w32 (.rm_i (.reg .rax) 1)),
  .ins (.mov .w32 (.rm_i (.reg .rdi) 1)),
  .ref (.lea .w64 .rsi (.rip 0)) .message,
  .ins (.mov .w32 (.rm_i (.reg .rdx) 14)),
  .ins .syscall,
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins .syscall,
  .segment .ro,
  .label .message, .bytes message]
/-- The page the message is on says its bytes: the message, then nought. -/
def said : List (BitVec 64 × List (BitVec 8)) :=
  [(Asm.addr code (Asm.base code) .message, message ++ List.replicate (4096 - 14) 0)]
def pg : Prog :=
  { code := progCode (Asm.table (Asm.base code) code)
    pre := preOut said (· == 0) (fun fd b => fd == 1 && b == message) }
def labels : List U.Label := [⟨Asm.addr code (Asm.base code) .start, entryOf 0⟩]

theorem checked : wholeOk code .start 0 pg labels 12 = true := by decide +kernel
theorem saidOk : saidCheck (denBlocks (blocksOf code .start)) said = true := by decide +kernel

/-- **Hello is safe on the machine that decodes its instructions from
memory, ends only with status nought, and offers at its `write` exactly its
message, to descriptor 1: whatever the world outside it holds.** -/
theorem hello (w : World) :
    SafeMem linux (startIn code .start 0 w) ∧
      (∀ s', TypedAsm.Steps (Asm.fetch (Asm.base code) code) linux (startIn code .start 0 w) s' →
        ∀ len c, Asm.fetch (Asm.base code) code s'.rip = some (.syscall, len) →
        linux { s' with rip := s'.rip + len } = .exit c → c = 0) ∧
      (∀ s', TypedAsm.Steps (Asm.fetch (Asm.base code) code) linux (startIn code .start 0 w) s' →
        ∀ len, Asm.fetch (Asm.base code) code s'.rip = some (.syscall, len) →
        s'.getReg .rax = 1 → s'.getReg .rdi = 1 ∧ s'.offered = message) :=
  whole_outputs checked (Q := fun c => c = 0) (q := fun c => c == 0) (fun c h => by simpa using h)
    (R := fun fd bs => fd = 1 ∧ bs = message) (r := fun fd b => fd == 1 && b == message)
    (fun fd bs h => by simpa using h) saidOk rfl rfl w
end HelloU

/-! ## A program end to end, with a stack

The stack's page is a region the entry context holds, the stack pointer at
its end. -/

namespace PushU

inductive Label
  | start
  deriving DecidableEq

/-- `push rbx; pop rbx; mov eax, 60; xor edi, edi; syscall`. -/
def code : List (Asm Label) := [
  .label .start,
  .ins (.push .rbx),
  .ins (.pop .rbx),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins .syscall]

def pg : Prog := { code := progCode (Asm.table (Asm.base code) code), pre := preExits (· == 0) }

/-- One slot of stack: the page it is on is the region the entry holds. -/
def labels : List U.Label := [⟨Asm.addr code (Asm.base code) .start, entryOf 1⟩]

theorem checked : wholeOk code .start 1 pg labels 12 = true := by decide +kernel

/-- **A program that pushes and pops is safe, on the machine that decodes
its instructions from memory, and ends only with status nought.** -/
theorem pushPop (w : World) :
    SafeMem linux (startIn code .start 1 w) ∧
      ∀ s', TypedAsm.Steps (Asm.fetch (Asm.base code) code) linux (startIn code .start 1 w) s' →
        ∀ len c, Asm.fetch (Asm.base code) code s'.rip = some (.syscall, len) →
        linux { s' with rip := s'.rip + len } = .exit c → c = 0 :=
  whole_exits checked (Q := fun c => c = 0) (q := fun c => c == 0) (fun c h => by simpa using h)
    rfl rfl w

end PushU

end Tests.Unified
