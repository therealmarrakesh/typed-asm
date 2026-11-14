import TypedAsm

/-!
# Swapping two fields, proved safe

A complete program that is type-checked and then proved safe by the soundness
theorem. A function that swaps the two fields of a record is typed once and
called from two places whose stacks differ. The caller keeps its pointer in
`rbx` across both calls, relying on `swap` to preserve that register.

```asm
_start:                       ; rdi = pointer to a record of two integers
   0  mov   rbx, rdi          ; keep the pointer in a callee-saved register
   3  call  swap              ; called with an empty stack
   8  push  rbx
   9  mov   rdi, rbx          ; rbx is still a pointer after the call
  12  call  swap              ; called with one slot on the stack
  17  pop   rdi
  18  mov   eax, 60           ; Linux `exit`
  23  xor   edi, edi
  25  syscall
spin:
  27  jmp   spin              ; not reached: `exit` does not return
swap:                         ; rdi = pointer to the record
  32  mov   rax, [rdi]
  35  mov   rcx, [rdi+8]
  39  mov   [rdi], rcx
  42  mov   [rdi+8], rax
  46  ret
```
-/

open TypedAsm

namespace Swap

/-! ## The program -/

def field (disp : BitVec 32) : Mem := .sib (some .rdi) none disp

inductive Label
  | swap | spin
  deriving DecidableEq

def code : List (Asm Label) := [
  .ins (.mov .w64 (.rm_r (.reg .rbx) .rdi)) 3,
  .call .swap,
  .ins (.push .rbx) 1,
  .ins (.mov .w64 (.rm_r (.reg .rdi) .rbx)) 3,
  .call .swap,
  .ins (.pop .rdi) 1,
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)) 5,
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)) 2,
  .ins .syscall 2,
  .label .spin,
  .jmp .spin,
  .label .swap,
  .ins (.mov .w64 (.r_m .rax (field 0))) 3,
  .ins (.mov .w64 (.r_m .rcx (field 8))) 4,
  .ins (.mov .w64 (.rm_r (.mem (field 0)) .rcx)) 3,
  .ins (.mov .w64 (.rm_r (.mem (field 8)) .rax)) 4,
  .ins .ret 1]

def fetch : Fetch := Asm.fetch 0 code

/-- The starting state: a record holding 3 and 5 at `0x1000`, two free stack
slots below `rsp`, and `rdi` pointing at the record. -/
def start : State :=
  (((State.init.setPerm 0x1000 16 .rw).setPerm 0x7ff0 16 .rw).store64 0x1000 3).store64 0x1008 5
    |>.setReg .rsp 0x8000 |>.setReg .rdi 0x1000

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

/-- Contexts are given only where control arrives from elsewhere. -/
inductive Φ : BitVec 64 → Ctx → Prop
  | start : Φ 0 ⟨only .rdi, [], 2, Flags.Any⟩
  /-- After the first call the pointer is still in `rbx`. -/
  | afterFirst : Φ 8 ⟨only .rbx, [], 2, Flags.Any⟩
  | afterSecond : Φ 17 ⟨only .rbx, [pair], 1, Flags.Any⟩
  | spin : Φ 27 done
  | swap (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat) :
    swapSig.CallerOk saved ret rest room → Φ 32 (swapSig.entry saved ret rest room)

def recordLayout : Layout := ⟨[.int, .int], true⟩

/-- One memory block: the record. -/
def blocks : List (BitVec 64 × Layout) := [(0x1000, recordLayout)]

def Ψ : MemTy := .ofList blocks

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch := by
  intro a Γ h
  cases h with
  | start =>
    -- mov rbx, rdi; call swap
    ty_steps
    exact .last rfl (FnSig.call_ok (sig := swapSig) (fun _ _ _ _ hK => .swap _ _ _ _ hK) rfl
      Φ.afterFirst (by sub_regs) (by ctx_sub) (by decide))
  | afterFirst =>
    -- push rbx; mov rdi, rbx; call swap
    ty_steps
    exact .last rfl (FnSig.call_ok (sig := swapSig) (fun _ _ _ _ hK => .swap _ _ _ _ hK) rfl
      Φ.afterSecond (by sub_regs) (by ctx_sub) (by decide))
  | afterSecond =>
    -- pop rdi; mov eax, 60; xor edi, edi; syscall
    ty_steps
    exact .last rfl (.syscall (by ty_accept Φ.spin))
  | spin => exact .last rfl (.jmp (by ty_accept Φ.spin))
  | swap saved ret rest room hK =>
    -- the four moves, then ret
    ty_steps
    exact .last rfl (FnSig.ret_of hK (by sub_regs) rfl rfl)

/-! ## The memory typing and the starting state -/

theorem memOk : Ψ.WF := MemTy.wf_of_check (by decide)

theorem startOk : StateOk Φ fetch linux Ψ start := by
  refine ⟨_, Φ.start, fun n => Matches.ofCheck (by decide) ?_ trivial ?_ ?_⟩
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

/-! ## Running it -/

def describe : Outcome → String
  | .next s => s!"running: record = ({(s.load64 0x1000).toNat}, {(s.load64 0x1008).toNat})"
  | .fault f => s!"fault: {repr f}"
  | .exit code => s!"exit {code.toNat}"
  | .stuck => "stuck"

def recordIs (x y : BitVec 64) : Outcome → Bool
  | .next s => s.load64 0x1000 == x && s.load64 0x1008 == y
  | _ => false

-- After the first call returns (seven steps) the fields are exchanged, and
-- after the second (eight more) they are back.
#guard recordIs 5 3 (run fetch linux 7 start)
#guard recordIs 3 5 (run fetch linux 15 start)

end Swap

def main : IO Unit := do
  IO.println (Swap.describe (run Swap.fetch linux 0 Swap.start))
  IO.println (Swap.describe (run Swap.fetch linux 7 Swap.start))
  IO.println (Swap.describe (run Swap.fetch linux 15 Swap.start))
  IO.println (Swap.describe (run Swap.fetch linux 100 Swap.start))
