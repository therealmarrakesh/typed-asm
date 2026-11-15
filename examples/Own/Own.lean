import OwnProgram
import TypedAsm.Tactic

/-!
# Own: typing and safety

The program is in `OwnProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Own

/-! ## The typing -/

/-- The contexts allowed at each label: nothing is known about any register,
and nothing is owned. In particular the program may not arrive at `fail`
still holding a page. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 0)
  | fail : At .fail (entryCtx 0)

/-- The code typing: those contexts, at the addresses of their labels. -/
def Φ : CodeTy := .ofLabels code base At

/-- The record: one number, read-only. -/
def recordLayout : Layout := ⟨.raw 8, false, none, 0⟩

def blocks : List (BitVec 64 × Layout) := [(dataBase, recordLayout)]

def Ψ : MemTy := .ofList blocks []

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  | start =>
    -- the arguments, then the `mmap` for a page to own, at an address called `p`
    ty_steps
    ty_mmap_own as p
    -- an error number is negative: the test sends control to `fail`
    · ty_block
    -- a page: `p` is not negative, so the test lets control through
    · ty_step
      ty_branch
      -- mov rbx, rax
      ty_step
      -- regard the page as two blocks: its first sixteen bytes, and the rest
      ty_split .rbx at 16
      -- the stores give the fields their types, in whichever block each
      -- address falls; the loads find them
      ty_steps
      -- one block again, and give it back: the context owns nothing
      ty_join .rbx
      ty_munmap
      -- two more pages, at `q`
      ty_steps
      ty_mmap_own as q
      · ty_block
      · ty_step
        ty_branch
        -- mov rbx, rax
        ty_step
        -- a block for each page; give the second back
        ty_split .rbx at 4096
        ty_steps
        ty_munmap
        -- lea rcx, [rip + record]
        ty_step
        -- `rcx` holds exactly the record's address, so it is a pointer to it
        refine BlockOk.castPtr (r := .rcx) (base := dataBase) (i := 0) (w := false) (by decide)
          rfl rfl (by decide) (fun h => absurd h (by decide)) ?_
        -- mov [rbx], rcx: the page's first field is now a pointer to the record
        ty_step
        -- so the page can become an ordinary block with that field
        ty_freeze .rbx
        ty_block
  | fail => ty_block

/-! ## The memory typing and the entry contract -/

theorem memOk : Ψ.WF := MemTy.wf_of_check (by decide)

/-- What the program needs of the state it starts in: its bytes in
executable memory, and its record readable. Nothing is asked of how requests
for memory are answered. -/
abbrev Entry : State → Prop := TypedAsm.Entry entry parts blocks 0 0

/-! ## Safety -/

/-- **From any state meeting the entry contract, wherever the kernel puts
the memory it asks for, the program is safe on the machine that fetches
instructions by decoding memory.** It never gets stuck and never faults:
in particular it never touches the page it gave back. -/
theorem safeMem_of_entry {s : State} (h : Entry s) : SafeMem linux s :=
  h.safeMem blocksOk memOk At.start (Entry.plain (by simp [blocks, recordLayout]))

/-- The starting state used by the simulator meets the entry contract. -/
theorem start_entry : Entry start := by ty_loaded

/-- The simulator's run is safe however its requests for memory are answered. -/
theorem safeMem (place : Nat → Option (BitVec 64)) : SafeMem linux (startWith place) :=
  safeMem_of_entry (start_entry.withWorld _)

end Own

-- The proof rests on Lean's three standard axioms and nothing else.
/-- info: 'Own.safeMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Own.safeMem
