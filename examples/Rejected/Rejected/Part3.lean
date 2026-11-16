import Rejected.Common

/-!
# Rejections, part 3

See `Rejected.lean`. The tests are spread over the parts so that they are
checked side by side; which part a test is in means nothing.
-/

open TypedAsm

namespace Rejected

/-- error: at address 43: cannot type `shl dword ptr [rsi], 1` in the current context
• `rsi` must hold a writable pointer, but its type is `read-only pointer to 16 bytes`. A store to memory that is read-only is a page fault -/
#guard_msgs in
example : BlockOk Φ fetch linux Ψ (Asm.addr code 0 .i14) Γ := by ty_step

/-- error: no context allowed at label `needsSlot` accepts the current one
• needsSlot: the stack, the free room or the flags do not match -/
#guard_msgs in
example : BlockOk Φj jumpFetch linux Ψ (Asm.addr jumps 0 .start) bare := by ty_block

/-- error: `ret`: pieces of the stack are still detached; a function must attach them again (`ty_stack_attach`) and leave the stack as it found it -/
#guard_msgs in
example (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat)
    (hK : plain.CallerOk saved ret rest room) :
    BlockOk Φc callFetch linux Ψ (Asm.addr calls 0 .f) (plain.entry saved ret rest room) := by
  ty_name .rsp as sp
  ty_stack_detach at 8
  ty_block

/-- error: `fstat` could overwrite something that is not plain bytes: the buffer in `rsi` does not have room in plain bytes of its block for the 144 bytes the kernel stores -/
#guard_msgs in
example : BlockOk Φy fillFetch linux Ψ (Asm.addr fills 0 .statSmall) (twoAt .rsi) := by ty_block

/-- error: `mmap`: the memory typing declares no kind 7 -/
#guard_msgs in
example : BlockOk Φy mapFetch linux Ψ (Asm.addr maps 0 .noKind) bare := by
  ty_steps
  ty_mmap_kind 7

/-- error: `munmap` is typed for a block the context owns: `rax` must hold exactly 11, `rdi` exactly the address of an owned block, and `rsi` an exactly known length -/
#guard_msgs in
example : BlockOk Φm ownFetch linux Ψ (Asm.addr owning 0 .notOwned) bare := by
  ty_steps
  ty_munmap

example : ∃ Γ', Straight Ψ 10 Γ₂ (.mov .w64 (.rm_r (.mem (.sib (some .rdx) none 8)) .rdi)) Γ' :=
  ⟨_, by ty_straight⟩

example : Straight Ψ 10 Γ₄ (.mov .w64 (.r_m .rax (.sib (some .rsi) (some (.rcx, .s8)) 8)))
    (Γ₄.setReg .rax (.ptr (.raw 16) true 0)) := by
  ty_straight

example (a b c d e f : BitVec 64) :
    Straight Ψ 10 (Γ₆ a b c d e f) (.mov .w64 (.r_m .rax (.sib (some .rbx) none 0)))
      ((Γ₆ a b c d e f).setReg .rax (.eq 7)) := by
  ty_straight

example (i : BitVec 64) (hlt : i.toNat < 64) :
    Straight Ψ 10 (filling i) (.store8 (.sib (some .rbx) (some (.rcx, .s1)) 16) .rax)
      (filling i) := by
  ty_straight

example (n k : Nat) (hk : k < n) :
    Straight Ψ 10 (walking n k) (.mov .w64 (.r_m .rax (.sib (some .rbx) none 8)))
      ((walking n k).setReg .rax (.ptr (.raw 16) true 0)) := by
  ty_straight

example (n k : Nat) :
    ∃ Γ', Straight Ψ 10 (walking n k) (.alu .add .w64 (.rm_i (.reg .rbx) 24)) Γ' ∧
      Γ'.regs .rbx = .ptr (entryShape.rep n) true (24 * (k + 1)) :=
  ⟨_, by ty_straight, rfl⟩

theorem signed_ok : BlocksOk Φs signedFetch linux Ψ := by
  refine BlocksOk.of_labels ?_
  intro l Γ h
  cases h with
  -- the tactic finds both facts about the divisor among the hypotheses
  | start a v hv hv1 => ty_block
  | out => ty_block

-- A load from the kernel's half, or from an address with nothing there, is a
-- page fault: the address exists, the memory is not the program's.
#guard match exec linux (.mov .w64 (.r_m .rax (.sib (some .rcx) none 0)))
    (nowhere.setReg .rcx 0xffff800000000000) with
  | .fault .pageFault => true
  | _ => false

/-! ## What a program ends with

Typed against the system that lets a program end only with a status that is
as wanted, an exit is typed where the status is exactly known and is so. -/

inductive Ending
  | known | unknown
  deriving DecidableEq

def ending : List (Asm Ending) := [
  .label .known,
  .ins (.mov .w32 (.rm_i (.reg .rdi) 3)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .unknown,
  .ins (.mov .w32 (.rm_r (.reg .rdi) .rcx)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall]

def endingFetch : Fetch := Asm.fetch 0 ending

def Φz : CodeTy := .ofLabels ending 0 (fun _ Δ => Δ = bare)

example : BlockOk Φz endingFetch (linux.exitsOnly (· = 3)) Ψ (Asm.addr ending 0 .known) bare := by
  ty_block

/-- error: unsolved goals
case status
⊢ BitVec.setWidth 32 3#64 = 4 -/
#guard_msgs in
example : BlockOk Φz endingFetch (linux.exitsOnly (· = 4)) Ψ (Asm.addr ending 0 .known) bare := by
  ty_block

/-- error: `syscall`: what the program ends with is being shown, so the status in `rdi` must be exactly known here, but its type is `int` -/
#guard_msgs in
example :
    BlockOk Φz endingFetch (linux.exitsOnly (· = 3)) Ψ (Asm.addr ending 0 .unknown) bare := by
  ty_block

end Rejected
