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

/-- For the last part of `_start`: nothing is known about any register. -/
def fin : Ctx := ⟨fun _ => .int, [], 1, Flags.Any⟩

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start fin
  | afterCall : At .afterCall fin
  | spin : At .spin fin
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

def arrayLayout : Layout := ⟨List.replicate 5 .int, false⟩

/-- One memory block: the array. -/
def blocks : List (BitVec 64 × Layout) := [(dataBase, arrayLayout)]

def Ψ : MemTy := .ofList blocks

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
  | spin => ty_block
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

/-! ## The memory typing and the starting state -/

theorem memOk : Ψ.WF := MemTy.wf_of_check (by decide)

/-- What the program needs of the state it starts in. This is the contract
with whatever loads it: for the ELF file, with the Linux kernel. -/
structure Entry (s : State) : Prop where
  /-- Execution starts at the entry point. -/
  rip : s.rip = entry
  /-- The program's bytes are in executable memory. -/
  code : s.HasCode base image
  /-- The array is readable. -/
  data : s.canRead dataBase 40 = true
  /-- There is room to push one return address. -/
  stack : s.canWrite (s.getReg .rsp - 8) 8 = true
  /-- That stack slot is not part of the array. -/
  apart : Disjoint (s.getReg .rsp - 8) 8 dataBase 40

/-- Any state meeting the entry contract is well typed. Nothing is assumed
about the registers other than `rsp`, or about the contents of the array. -/
theorem Entry.stateOk {s : State} (h : Entry s) : StateOk Φ fetch linux Ψ s := by
  refine ⟨fin, by rw [h.rip]; exact .intro At.start, fun n => ?_⟩
  have hblock : ∀ a l, Ψ a = some l → a = dataBase ∧ l = arrayLayout := by
    intro a l hl
    have := MemTy.mem_of_ofList hl
    simpa [blocks] using this
  exact {
    regs := fun _ _ => HasTy.int _
    flags := trivial
    stackPerm := h.stack
    stackSize_lt := by decide
    stack := fun i τ hi => by simp [fin] at hi
    heapPerm := fun a l hl => by
      obtain ⟨rfl, rfl⟩ := hblock a l hl
      exact ⟨h.data, fun hw => absurd hw (by decide)⟩
    heap := fun a l hl i τ hi => by
      obtain ⟨rfl, rfl⟩ := hblock a l hl
      have : τ = .int := by simpa [arrayLayout] using List.mem_of_getElem? hi
      subst this
      exact HasTy.int _
    stackHeap := fun a l hl => by
      obtain ⟨rfl, rfl⟩ := hblock a l hl
      exact h.apart }

/-! ## Safety -/

/-- **From any state meeting the entry contract, the program is safe on the
machine that fetches instructions by decoding memory.** It never gets stuck,
never page-faults and never executes an invalid opcode; in particular every
array access is in bounds. -/
theorem safeMem_of_entry {s : State} (h : Entry s) : SafeMem linux s :=
  .of_safe linux_frame (Asm.loaded h.code)
    (soundness_blocks blocksOk memOk (linuxOk fetch Ψ) h.stateOk)

/-- The program is 60 bytes long. -/
theorem image_length : image.length = 60 := by decide

theorem base_eq : base = 0x4000b0 := by decide

theorem dataBase_eq : dataBase = 0x401000 := by decide

theorem start_rsp : start.getReg .rsp = 0x80000000 := by decide

/-- The starting state used by the simulator meets the entry contract. The
facts about the array and the stack are checked on the state before the
program is loaded, and carried over because the program is nowhere near them. -/
theorem start_entry : Entry start where
  rip := rfl
  code := (State.hasCode_loadCode prepared base image (by rw [image_length]; decide)).congr rfl rfl
  data := by
    rw [State.canRead_congr (s := prepared.loadCode base image) (t := start) rfl,
      State.canRead_loadCode (fun k hk => by rw [image_length, base_eq, dataBase_eq]; bv_omega)]
    decide
  stack := by
    rw [start_rsp, State.canWrite_congr (s := prepared.loadCode base image) (t := start) rfl,
      State.canWrite_loadCode (fun k hk => by rw [image_length, base_eq]; bv_omega)]
    decide
  apart := by
    rw [start_rsp, dataBase_eq]
    decide

/-- The simulator's run is safe, with instructions decoded from memory. -/
theorem safeMem : SafeMem linux start :=
  safeMem_of_entry start_entry

/-- It is also safe on the table machine, which is what the type system reasons about. -/
theorem safe : Safe fetch linux start :=
  soundness_blocks blocksOk memOk (linuxOk fetch Ψ) start_entry.stateOk

/-- So running it for any number of steps gives an acceptable outcome. -/
theorem run_safe (n : Nat) : (run fetch linux n start).isSafe = true :=
  safe.run n

end Sum
