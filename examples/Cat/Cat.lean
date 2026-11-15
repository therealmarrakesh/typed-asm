import CatProgram
import TypedAsm.Tactic

/-!
# Cat: typing and safety

The program is in `CatProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Cat

/-! ## The typing -/

/-- The context everywhere: nothing is known about any register, and the
three slots from `rsp` up hold numbers. They are the count of arguments and
the addresses of the first two, the program's name and the file's. -/
def ctx : Ctx := entryCtxArgs 0 3

/-- The contexts allowed at each label. The descriptor in `r12` is a number
like any other. -/
inductive At : Label → Ctx → Prop
  | start : At .start ctx
  | next : At .next ctx
  | done : At .done ctx
  | fail : At .fail ctx
  | usage : At .usage ctx

/-- The code typing: those contexts, at the addresses of their labels. -/
def Φ : CodeTy := .ofLabels code base At

/-- The buffer: eight integer fields, 64 bytes, writable. -/
def bufferLayout : Layout := ⟨[.int, .int, .int, .int, .int, .int, .int, .int], true, none⟩

/-- One memory block, the buffer. -/
def blocks : List (BitVec 64 × Layout) := [(dataBase, bufferLayout)]

def Ψ : MemTy := .ofList blocks []

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  | start =>
    -- the count of arguments, and the test that there is one to use
    ty_steps
    ty_branch
    -- the name's address from the stack, the `openat`, the test of its answer
    ty_steps
    ty_branch
    -- mov r12, rax, and on into `next`
    ty_into At.next
  | next =>
    -- xor eax, eax; mov rdi, r12; lea rsi, [rip + buffer]
    ty_step
    ty_step
    ty_step
    -- `rsi` holds exactly the buffer's address, so it is a pointer to it
    refine BlockOk.castPtr (r := .rsi) (base := dataBase) (i := 0) (w := true) (by decide) rfl rfl
      (by decide) (fun _ => rfl) ?_
    -- the `read`, the test of its result, the `write`, and round again
    ty_block
  | done => ty_block
  | fail => ty_block
  | usage => ty_block

/-! ## The memory typing and the entry contract -/

theorem memOk : Ψ.WF := MemTy.wf_of_check (by decide)

/-- What the program needs of the state it starts in: its bytes in
executable memory, its buffer readable and writable, and three stack slots
from `rsp` up, which Linux always provides. Nothing is asked of what the
arguments are or of the files there are. -/
abbrev Entry : State → Prop := TypedAsm.Entry entry base image dataBase dataBytes blocks 0 3

/-- Any state meeting the entry contract is well typed. -/
theorem Entry.stateOk {s : State} (h : Entry s) : StateOk Φ fetch linux Ψ s :=
  ⟨ctx, by rw [h.rip]; exact .intro At.start,
    fun _ => h.matchesArgs HasTy.int (by simp [blocks, bufferLayout])⟩

/-! ## Safety -/

/-- **From any state meeting the entry contract, whatever arguments it was
given, whatever files there are and whatever they hold, the program is safe
on the machine that fetches instructions by decoding memory.** It never gets
stuck and never faults. -/
theorem safeMem_of_entry {s : State} (h : Entry s) : SafeMem linux s :=
  .of_safe linux_frame (Asm.loaded h.code)
    (soundness_blocks blocksOk memOk h.stateOk)

theorem image_length : image.length = 139 := by decide +kernel

/-- The starting state used by the simulator meets the entry contract,
whatever the arguments. -/
theorem start_entry (args : List (List Byte)) : Entry (startArgs args) :=
  Entry.ofLoadArgs args (by decide) (by decide) (by rw [image_length]; decide)
    (State.hasData_loadData _ _ _ _ (by decide)) (by rw [image_length]; decide)
    (by decide) (by rw [image_length]; decide) (by rw [image_length]; decide)

/-- The simulator's run is safe whatever arguments and files it is given. -/
theorem safeMem (args : List String) (files : List File) : SafeMem linux (startWith args files) :=
  safeMem_of_entry ((start_entry _).withWorld _)

end Cat
