import SwapProgram
import TypedAsm.Tactic

/-!
# Swap: typing and safety

The program is in `SwapProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Swap

/-! ## The typing -/

/-- A pointer to a writable record of two integers. -/
def pair : Ty := .ptr [.int, .int] true 0

/-- `swap` takes the pointer in `rdi`, promises nothing about the registers
it uses, and preserves the callee-saved registers. -/
def swapSig : FnSig where
  args := fun r => if r = .rdi then pair else .int
  results := fun _ => .int
  preserved := calleeSaved
  need := 0

/-- Register types with the pointer in one register and nothing known about the rest. -/
def only (reg : Reg) : Reg → Ty := fun r => if r = reg then pair else .int

/-- For the last instruction of `_start`: nothing is known about any register. -/
def done : Ctx := ⟨fun _ => .int, [], 2, Flags.Any⟩

/-- The contexts allowed at each label. -/
inductive At : Label → Ctx → Prop
  | start : At .start ⟨only .rdi, [], 2, Flags.Any⟩
  /-- After the first call the pointer is still in `rbx`. -/
  | afterFirst : At .afterFirst ⟨only .rbx, [], 2, Flags.Any⟩
  | afterSecond : At .afterSecond ⟨only .rbx, [pair], 1, Flags.Any⟩
  | spin : At .spin done
  | swap (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat) :
    swapSig.CallerOk saved ret rest room → At .swap (swapSig.entry saved ret rest room)

/-- The code typing: those contexts, at the addresses of their labels. -/
def Φ : CodeTy := .ofLabels code 0 At

def recordLayout : Layout := ⟨[.int, .int], true⟩

/-- One memory block: the record. -/
def blocks : List (BitVec 64 × Layout) := [(0x1000, recordLayout)]

def Ψ : MemTy := .ofList blocks

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  | start =>
    -- mov rbx, rdi; call swap
    ty_steps
    exact .last rfl (FnSig.call_ok (sig := swapSig)
      (FnSig.at_label fun _ _ _ _ hK => At.swap _ _ _ _ hK) rfl (.intro At.afterFirst)
      (by sub_regs) (by ctx_sub) (by decide))
  | afterFirst =>
    -- push rbx; mov rdi, rbx; call swap
    ty_steps
    exact .last rfl (FnSig.call_ok (sig := swapSig)
      (FnSig.at_label fun _ _ _ _ hK => At.swap _ _ _ _ hK) rfl (.intro At.afterSecond)
      (by sub_regs) (by ctx_sub) (by decide))
  | afterSecond =>
    -- pop rdi; mov eax, 60; xor edi, edi; syscall
    ty_steps
    exact .last rfl (.syscall (by ty_accept At.spin))
  | spin => exact .last rfl (.jmp (by ty_accept At.spin))
  | swap saved ret rest room hK =>
    -- the four moves, then ret
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

/-- So running it for any number of steps gives an acceptable outcome. -/
theorem run_safe (n : Nat) : (run fetch linux n start).isSafe = true :=
  safe.run n

end Swap
