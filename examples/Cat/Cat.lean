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

/-- The context inside the loop, for a program given `c` arguments that is
about to do argument number `v`: `r13` holds exactly `c`, `r14` exactly `v`,
and the stack is as the program found it. -/
def loopCtx (c v : BitVec 64) : Ctx :=
  ⟨fun r => if r = .r13 then .eq c else if r = .r14 then .eq v else .int,
    [.slot (.eq c), .raw (8 * (c.toNat + 4))], 0, Flags.Any, [], 0⟩

/-- The contexts allowed at each label, one for every number of arguments
and, in the loop, every argument reached. The descriptor in `r12` is a
number like any other. -/
inductive At : Label → Ctx → Prop
  | start (c : BitVec 64) : At .start (argsCtx 0 c)
  | file (c v : BitVec 64) : At .file (loopCtx c v)
  | next (c v : BitVec 64) : At .next (loopCtx c v)
  | eof (c v : BitVec 64) : At .eof (loopCtx c v)
  | done (c : BitVec 64) : At .done (argsCtx 0 c)
  | fail (c : BitVec 64) : At .fail (argsCtx 0 c)

/-- The code typing: those contexts, at the addresses of their labels. -/
def Φ : CodeTy := .ofLabels code base At

/-- The buffer: 64 plain bytes, writable. -/
def bufferLayout : Layout := ⟨.raw 64, true, none, 0⟩

/-- One memory block, the buffer. -/
def blocks : List (BitVec 64 × Layout) := [(dataBase, bufferLayout)]

def Ψ : MemTy := .ofList blocks []

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  | start c =>
    -- mov r13, [rsp]: the count, exactly; mov r14d, 1, and on into `file`
    ty_step
    ty_into (At.file c 1)
  | file c v =>
    -- cmp r14, r13; jae done
    ty_step
    ty_branch
    -- carrying on, the argument's number is below the count (`hlt`), so its
    -- slot is there to load; then the `openat` and the test of its answer
    ty_steps
    ty_branch
    -- mov r12, rax, and on into `next`
    ty_into (At.next c v)
  | next c v =>
    -- xor eax, eax; mov rdi, r12; lea rsi, [rip + buffer]
    ty_step
    ty_step
    ty_step
    -- `rsi` holds exactly the buffer's address, so it is a pointer to it
    refine BlockOk.castPtr (r := .rsi) (base := dataBase) (i := 0) (w := true) (by decide) rfl rfl
      (by decide) (fun _ => rfl) ?_
    -- the `read`, the test of its result, the `write`, and round again
    ty_block
  | eof c v => ty_block
  | done c => ty_block
  | fail c => ty_block

/-! ## The memory typing and the entry contract -/

theorem memOk : Ψ.WF := MemTy.wf_of_check (by decide)

/-- What the program needs of the state it starts in: its bytes in
executable memory, its buffer readable and writable, and the stack as Linux
leaves it for a new program: the number of arguments at `[rsp]` and a slot
for each after it. Nothing is asked of what the arguments are or of the
files there are. -/
abbrev Entry : State → Prop := TypedAsm.EntryArgs entry parts blocks 0

/-! ## Safety -/

/-- **From any state meeting the entry contract, however many arguments it
was given and whatever they are, whatever files there are and whatever they
hold, the program is safe on the machine that fetches instructions by
decoding memory.** It never gets stuck and never faults. -/
theorem safeMem_of_entry {s : State} (h : Entry s) : SafeMem linux s :=
  h.safeMem blocksOk memOk At.start (by simp [blocks, bufferLayout])

/-- The starting state used by the simulator meets the entry contract,
whatever the arguments. -/
theorem start_entry (args : List (List Byte)) : Entry (startArgs args) := by ty_loaded

/-- The simulator's run is safe whatever arguments and files it is given. -/
theorem safeMem (args : List String) (files : List File) : SafeMem linux (startWith args files) :=
  safeMem_of_entry ((start_entry _).withWorld _)

end Cat

-- The proof rests on Lean's three standard axioms and nothing else.
/-- info: 'Cat.safeMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cat.safeMem
