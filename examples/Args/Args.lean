import ArgsProgram
import TypedAsm.Tactic

/-!
# Args: typing and safety

The program is in `ArgsProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Args

/-! ## The typing -/

/-- The stack as the program finds it when given `c` arguments: the count,
the address of each one's text, and four more words. -/
def slots (c : BitVec 64) : List Shape :=
  [.slot (.eq c), (ShapeOf.slot (.str false)).rep c.toNat, .raw 32]

/-- Between arguments: `r13` holds exactly the count `c` and `r14` exactly
the number `v` of the argument to do next. -/
def loopCtx (c v : BitVec 64) : Ctx :=
  ⟨fun r => if r = .r13 then .eq c else if r = .r14 then .eq v else .int, slots c, 0, Flags.Any, [], 0⟩

/-- Within an argument: also `rsi` points at the start of its text and `rdi`
at the place reached in it. -/
def scanCtx (c v : BitVec 64) : Ctx :=
  ⟨fun r => if r = .r13 then .eq c else if r = .r14 then .eq v
      else if r = .rsi then .str false else if r = .rdi then .str false else .int,
    slots c, 0, Flags.Any, [], 0⟩

/-- The contexts allowed at each label, one for every number of arguments
and every argument reached. -/
inductive At : Label → Ctx → Prop
  | start (c : BitVec 64) : At .start (textsCtx 0 c)
  | arg (c v : BitVec 64) : At .arg (loopCtx c v)
  | scan (c v : BitVec 64) : At .scan (scanCtx c v)
  | done (c : BitVec 64) : At .done (textsCtx 0 c)

/-- The code typing: those contexts, at the addresses of their labels. -/
def Φ : CodeTy := .ofLabels code base At

/-- The program has no memory blocks of its own. The texts of its arguments
are blocks, but they are there only when it runs. -/
def blocks : List (BitVec 64 × Layout) := []

def Ψ : MemTy := .ofList blocks []

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  | start c =>
    -- mov r13, [rsp]: the count, exactly; mov r14d, 1, and on into `arg`
    ty_step
    ty_into (At.arg c 1)
  | arg c v =>
    -- cmp r14, r13; jae done
    ty_step
    ty_branch
    -- carrying on, the argument's number is below the count, so its slot is
    -- there and holds the address of a text
    have hlt := cmp_not_ae hcond
    ty_step
    -- mov rdi, rsi, and on into `scan`
    ty_into (At.scan c v)
  | scan c v =>
    -- the byte at the place reached is zero or it is not
    ty_byte as b
    -- zero: the test sends control to `found`
    · ty_block
    -- not zero: so not the text's last byte, and the place may move on
    · ty_block
  | done c => ty_block

/-! ## The memory typing and the entry contract -/

theorem memOk : Ψ.WF := MemTy.wf_of_check (by decide)

/-- What the program needs of the state it starts in: its bytes in
executable memory, and the stack as Linux leaves it for a new program: the
number of arguments at `[rsp]`, then the address of each one's text, each
text readable and ended by a zero. Nothing is asked of what the arguments
say. -/
abbrev Entry : State → Prop := TypedAsm.EntryTexts entry parts blocks 0

/-! ## Safety -/

/-- **From any state meeting the entry contract, however many arguments it
was given and whatever they say, the program is safe on the machine that
fetches instructions by decoding memory.** It never gets stuck and never
faults. -/
theorem safeMem_of_entry {s : State} (h : Entry s) : SafeMem linux s :=
  h.safeMem blocksOk rfl At.start (by simp [blocks])

/-- The starting state used by the simulator meets the entry contract,
whatever the arguments. -/
theorem start_entry (args : List (List Byte)) : Entry (startArgs args) := by ty_loaded

/-- The simulator's run is safe whatever arguments it is given. -/
theorem safeMem (args : List String) : SafeMem linux (startWith args) :=
  safeMem_of_entry (start_entry _)

end Args

-- The proof rests on Lean's three standard axioms and nothing else.
/-- info: 'Args.safeMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Args.safeMem
