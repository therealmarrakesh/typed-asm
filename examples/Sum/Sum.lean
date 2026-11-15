import SumProgram
import TypedAsm.Tactic

/-!
# Sum: typing and safety

The program is in `SumProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Sum

/-! ## The typing -/

/-- A pointer to element `i` of a read-only array of `n` integers. -/
def elem (n i : Nat) : Ty := .ptr (List.replicate n .int) false i

/-- The counter after `i` of `n` elements have been consumed. -/
def left (n i : Nat) : BitVec 64 := BitVec.ofNat 64 (n - i)

/-- Register types inside `sum` after `i` elements: the pointer is at element
`i`, the counter is exactly `n - i`, and the callee-saved registers have
whatever types the caller gave them. -/
def sumRegs (n i : Nat) (saved : Reg → Ty) : Reg → Ty :=
  fun r => if calleeSaved r then saved r
    else if r = .rdi then elem n i else if r = .rsi then .eq (left n i) else .int

/-- `sum` takes a pointer to `n` integers in `rdi` and exactly `n` in `rsi`,
and preserves the callee-saved registers. -/
def sumSig (n : Nat) : FnSig where
  args := sumRegs n 0 (fun _ => .int)
  results := fun _ => .int
  preserved := calleeSaved
  need := 0

/-- After the call: nothing is known about any register. -/
def fin : Ctx := ⟨fun _ => .int, [], 1, Flags.Any⟩

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 1)
  | afterCall : At .afterCall fin
  | sum (n : Nat) (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat) :
    (sumSig n).CallerOk saved ret rest room → At .sum ((sumSig n).entry saved ret rest room)
  /-- The loop invariant, for `i < n` elements consumed. -/
  | loop (n i : Nat) (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat) :
    (sumSig n).CallerOk saved ret rest room → i < n →
    At .loop ⟨sumRegs n i saved, .code ret :: rest, room, Flags.Any⟩
  | done (n : Nat) (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat) :
    (sumSig n).CallerOk saved ret rest room → At .done ((sumSig n).exit saved ret rest room)

/-- The code typing: those contexts, at the addresses of their labels. -/
def Φ : CodeTy := .ofLabels code base At

def arrayLayout : Layout := ⟨List.replicate 5 .int, false, none⟩

/-- One memory block: the array. -/
def blocks : List (BitVec 64 × Layout) := [(dataBase, arrayLayout)]

def Ψ : MemTy := .ofList blocks []

/-! ## Arithmetic facts the loop relies on -/

theorem left_ne_zero {n i : Nat} (h : left n i ≠ 0) : i < n := by
  apply Nat.lt_of_sub_ne_zero
  intro h0
  exact h (by simp [left, h0])

/-- Decrementing the counter gives the counter for one more element consumed. -/
theorem decr {n i : Nat} (hi : i < n) :
    (AluOp.apply .sub (left n i) ((1 : BitVec 32).signExtend 64)).1 = left n (i + 1) := by
  have h1 : ((1 : BitVec 32).signExtend 64) = 1 := by decide
  simp only [AluOp.apply, subBorrow_fst, h1, left]
  bv_omega

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  | start =>
    -- lea rdi, [rip + array]; mov esi, 5
    ty_steps
    -- `rdi` holds exactly the array's address, so it is a pointer to its first element
    refine BlockOk.castPtr (r := .rdi) (base := dataBase) (i := 0) (w := false) (by decide) rfl rfl
      (by decide) (fun h => absurd h (by decide)) ?_
    ty_call (sumSig 5)
  | afterCall => ty_block
  | sum n saved ret rest room hK =>
    ty_block
    -- entering the loop: the count is not zero, so the invariant holds with `i = 0`
    apply left_ne_zero
    intro h0
    simp [Cond.eval, Flags.ofResult, h0] at hcond
  | loop n i saved ret rest room hK hi =>
    ty_block
    -- going round again: the counter is the one for `i + 1` elements consumed,
    · exact Sub.of_eq (decr hi)
    -- and it is not zero, so `i + 1 < n`
    · apply left_ne_zero
      intro h0
      rw [← decr hi] at h0
      simp [Cond.eval, AluOp.apply, subBorrow_zf] at hcond
      exact hcond (by simpa [AluOp.apply] using h0)
  | done n saved ret rest room hK => ty_block

/-! ## The memory typing and the entry contract -/

theorem memOk : Ψ.WF := MemTy.wf_of_check (by decide)

/-- What the program needs of the state it starts in: its bytes in
executable memory, the array readable, and one writable stack slot below `rsp` that
does not overlap it. This is the contract with whatever loads the program;
for the ELF file, with the Linux kernel. -/
abbrev Entry : State → Prop := TypedAsm.Entry entry base image dataBase arrayBytes blocks 1 0

/-- Any state meeting the entry contract is well typed. -/
theorem Entry.stateOk {s : State} (h : Entry s) : StateOk Φ fetch linux Ψ s :=
  ⟨entryCtx 1, by rw [h.rip]; exact .intro At.start,
    fun _ => h.matchesInt HasTy.int (by simp [blocks, arrayLayout])⟩

/-! ## Safety -/

/-- **From any state meeting the entry contract, the program is safe on the
machine that fetches instructions by decoding memory.** It never gets stuck,
never faults: no page fault, no invalid opcode and no divide error. -/
theorem safeMem_of_entry {s : State} (h : Entry s) : SafeMem linux s :=
  .of_safe linux_frame (Asm.loaded h.code)
    (soundness_blocks blocksOk memOk h.stateOk)

theorem image_length : image.length = 55 := by decide

/-- The starting state used by the simulator meets the entry contract. -/
theorem start_entry : Entry start :=
  Entry.ofLoad (by rw [image_length]; decide) (by decide)
    ((State.hasData_loadData _ _ _ _ (by decide)).congr rfl) (by rw [image_length]; decide)
    (by decide) (by decide) (by decide)
    (by simp only [image_length]; decide) (by rw [image_length]; decide)

/-- The simulator's run is safe, with instructions decoded from memory. -/
theorem safeMem : SafeMem linux start :=
  safeMem_of_entry start_entry

/-- It is also safe on the table machine, which is what the type system reasons about. -/
theorem safe : Safe fetch linux start :=
  soundness_blocks blocksOk memOk start_entry.stateOk

end Sum
