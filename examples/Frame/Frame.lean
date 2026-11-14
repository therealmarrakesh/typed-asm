import TypedAsm

/-!
# A function with a stack frame, proved safe

Exercises stack-frame allocation, locals, 32-bit and byte loads, a
conditional jump in the middle of a block, and a comparison of two exactly
known values.

```asm
_start:                       ; rdi = pointer to a record of two integers
   0  mov   esi, 7
   5  mov   edx, 7
  10  cmp   rsi, rdx
  13  jne   spin              ; never taken, and the types know it
  19  call  pick
  24  mov   edi, eax
  26  mov   eax, 60           ; Linux `exit`
  31  syscall
spin:
  33  jmp   spin
pick:                         ; rdi = pointer to the record; result in rax
  38  sub   rsp, 16           ; two locals
  42  mov   [rsp], rdi        ; local 0: the pointer
  46  mov   eax, [rdi+8]      ; low half of the second field
  49  mov   [rsp+8], rax      ; local 1: that value
  54  test  rax, rax
  57  je    skip
  63  mov   rcx, [rsp]        ; the local is still a pointer
  67  movzx eax, byte ptr [rcx]
skip:
  70  add   rsp, 16
  74  ret
```
-/

open TypedAsm

namespace Frame

/-! ## The program -/

def rspSlot (disp : BitVec 32) : Mem := .sib (some .rsp) none disp

inductive Label
  | pick | skip | spin
  deriving DecidableEq

def code : List (Asm Label) := [
  .ins (.mov .w32 (.rm_i (.reg .rsi) 7)) 5,
  .ins (.mov .w32 (.rm_i (.reg .rdx) 7)) 5,
  .ins (.alu .cmp .w64 (.rm_r (.reg .rsi) .rdx)) 3,
  .jcc .ne .spin,
  .call .pick,
  .ins (.mov .w32 (.rm_r (.reg .rdi) .rax)) 2,
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)) 5,
  .ins .syscall 2,
  .label .spin,
  .jmp .spin,
  .label .pick,
  .ins (.alu .sub .w64 (.rm_i (.reg .rsp) 16)) 4,
  .ins (.mov .w64 (.rm_r (.mem (rspSlot 0)) .rdi)) 4,
  .ins (.mov .w32 (.r_m .rax (.sib (some .rdi) none 8))) 3,
  .ins (.mov .w64 (.rm_r (.mem (rspSlot 8)) .rax)) 5,
  .ins (.test .w64 (.reg .rax) (.reg .rax)) 3,
  .jcc .e .skip,
  .ins (.mov .w64 (.r_m .rcx (rspSlot 0))) 4,
  .ins (.movzx .w32 .rax .w8 (.mem (.sib (some .rcx) none 0))) 3,
  .label .skip,
  .ins (.alu .add .w64 (.rm_i (.reg .rsp) 16)) 4,
  .ins .ret 1]

def fetch : Fetch := Asm.fetch 0 code

/-- The starting state: a record holding `0x1234` and 1 at `0x1000`, three
free stack slots below `rsp`, and `rdi` pointing at the record. -/
def start : State :=
  (((State.init.setPerm 0x1000 16 .rw).setPerm 0x7fe8 24 .rw).store64 0x1000 0x1234).store64
      0x1008 1
    |>.setReg .rsp 0x8000 |>.setReg .rdi 0x1000

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

inductive Φ : BitVec 64 → Ctx → Prop
  | start : Φ 0 ⟨fun r => if r = .rdi then pair else .int, [], 3, Flags.Any⟩
  | afterCall : Φ 24 fin
  | spin : Φ 33 fin
  | pick (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat) :
    pickSig.CallerOk saved ret rest room → Φ 38 (pickSig.entry saved ret rest room)
  /-- At `skip` the frame is still allocated: local 0 is the pointer, local 1 an integer. -/
  | skip (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (m : Nat) :
    pickSig.CallerOk saved ret rest (m + 2) →
    Φ 70 ⟨fun r => if calleeSaved r then saved r else .int,
      pair :: .int :: .code ret :: rest, m, Flags.Any⟩

def recordLayout : Layout := ⟨[.int, .int], true⟩

def blocks : List (BitVec 64 × Layout) := [(0x1000, recordLayout)]

def Ψ : MemTy := .ofList blocks

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch := by
  intro a Γ h
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
      exact .last rfl (FnSig.call_ok (sig := pickSig) (fun _ _ _ _ hK => .pick _ _ _ _ hK) rfl
        Φ.afterCall (by sub_regs) (by ctx_sub) (by decide))
  | afterCall =>
    ty_steps
    exact .last rfl (.syscall (by ty_accept Φ.spin))
  | spin => exact .last rfl (.jmp (by ty_accept Φ.spin))
  | pick saved ret rest room hK =>
    obtain ⟨m, rfl⟩ := hK.room_split
    -- sub rsp, 16; mov [rsp], rdi; mov eax, [rdi+8]; mov [rsp+8], rax; test rax, rax
    ty_steps
    -- je skip
    refine .branch rfl (Cond.decided_of_known (fun _ h => h) _) ?_ ?_
    · intro f _ _
      ty_accept (Φ.skip saved ret rest m hK)
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

/-! ## Running it -/

def describe : Outcome → String
  | .next s => s!"still running at rip = {s.rip.toNat}"
  | .fault f => s!"fault: {repr f}"
  | .exit code => s!"exit {code.toNat}"
  | .stuck => "stuck"

def exitsWith (code : BitVec 32) : Outcome → Bool
  | .exit c => c == code
  | _ => false

-- The second field is not zero, so the result is the low byte of the first: 0x34.
#guard exitsWith 0x34 (run fetch linux 100 start)

end Frame

def main : IO Unit :=
  IO.println (Frame.describe (run Frame.fetch linux 100 Frame.start))
