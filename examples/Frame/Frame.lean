import FrameProgram
import TypedAsm.Tactic

/-!
# Frame: typing and safety

The program is in `FrameProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Frame

/-! ## The typing -/

/-- A pointer to a writable record of two integers. -/
def pair : Ty := .ptr [.int, .int] true 0

/-- `pick` takes the pointer in `rdi`, uses two stack slots, and preserves
the callee-saved registers. -/
def pickSig : FnSig where
  args := fun r => if r = .rdi then pair else .int
  results := fun _ => .int
  preserved := calleeSaved
  need := 2

/-- Nothing is known about any register. -/
def fin : Ctx := ⟨fun _ => .int, [], 3, Flags.Any⟩

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start ⟨fun r => if r = .rdi then pair else .int, [], 3, Flags.Any⟩
  | afterCall : At .afterCall fin
  | spin : At .spin fin
  | pick (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat) :
    pickSig.CallerOk saved ret rest room → At .pick (pickSig.entry saved ret rest room)
  /-- At `skip` the frame is still allocated: local 0 is the pointer, local 1 an integer. -/
  | skip (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (m : Nat) :
    pickSig.CallerOk saved ret rest (m + 2) →
    At .skip ⟨fun r => if calleeSaved r then saved r else .int,
      pair :: .int :: .code ret :: rest, m, Flags.Any⟩

/-- The code typing: those contexts, at the addresses of their labels. -/
def Φ : CodeTy := .ofLabels code 0 At

def recordLayout : Layout := ⟨[.int, .int], true⟩

def blocks : List (BitVec 64 × Layout) := [(0x1000, recordLayout)]

def Ψ : MemTy := .ofList blocks

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  | start =>
    -- mov esi, 7; mov edx, 7; cmp rsi, rdx
    ty_steps
    -- jne spin: both values are exactly 7, so the jump cannot be taken
    refine .branch rfl ?_ ?_ ?_
    · rintro f rfl; exact ⟨_, rfl⟩
    · rintro f rfl hne
      exact absurd hne (by decide)
    · rintro f rfl -
      -- call pick
      exact .last rfl (FnSig.call_ok (sig := pickSig)
        (FnSig.at_label fun _ _ _ _ hK => At.pick _ _ _ _ hK) rfl (.intro At.afterCall)
        (by sub_regs) (by ctx_sub) (by decide))
  | afterCall =>
    ty_steps
    exact .last rfl (.syscall (by ty_accept At.spin))
  | spin => exact .last rfl (.jmp (by ty_accept At.spin))
  | pick saved ret rest room hK =>
    obtain ⟨m, rfl⟩ := hK.room_split
    -- sub rsp, 16; mov [rsp], rdi; mov eax, [rdi+8]; mov [rsp+8], rax;
    -- mov [rdi+12], eax; mov [rdi+1], al; test rax, rax
    ty_steps
    -- je skip
    refine .branch rfl (Cond.decided_of_known (fun _ h => h) _) ?_ ?_
    · intro f _ _
      ty_accept (At.skip saved ret rest m hK)
    · intro f _ _
      -- mov rcx, [rsp]; movzx eax, byte ptr [rcx]; add rsp, 16
      ty_steps
      exact .last rfl (FnSig.ret_of hK (by sub_regs) rfl rfl)
  | skip saved ret rest m hK =>
    -- add rsp, 16; ret
    ty_steps
    exact .last rfl (FnSig.ret_of hK (by sub_regs) rfl rfl)

/-! ## The memory typing and the starting state -/

theorem memOk : Ψ.WF := MemTy.wf_of_check (by decide)

theorem startOk : StateOk Φ fetch linux Ψ start := by
  refine ⟨_, .intro At.start, fun n => Matches.ofCheck (by decide) ?_ trivial ?_ ?_⟩
  · intro r _
    cases r <;> first
      | exact HasTy.int _
      | exact hasTy_ptr.mpr ⟨0x1000, recordLayout, rfl, rfl, fun _ => rfl, by decide⟩
  · intro i τ h; simp at h
  · intro x hx i τ hi
    simp only [blocks, List.mem_singleton] at hx
    subst hx
    have : τ = .int := by simpa [recordLayout] using List.mem_of_getElem? hi
    subst this
    exact HasTy.int _

/-! ## Safety -/

/-- The program never gets stuck, never page-faults and never executes an invalid opcode. -/
theorem safe : Safe fetch linux start :=
  soundness_blocks blocksOk memOk (linuxOk fetch Ψ) startOk

end Frame
