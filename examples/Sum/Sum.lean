import TypedAsm

/-!
# Summing an array, proved safe

A function that sums `n` 64-bit integers through a moving pointer, with a
loop counter. Its safety depends on the counter and the pointer staying in
step, which the typing expresses with types that depend on values: the
contexts inside the loop are indexed by how many elements have been consumed.

```asm
_start:
   0  lea   rdi, [rip + array]   ; the array is at 0x1000
   7  mov   esi, 5
  12  call  sum
  17  mov   edi, eax
  19  mov   eax, 60              ; Linux `exit`
  24  syscall
  26  jmp   26                   ; not reached: `exit` does not return
sum:                             ; rdi = pointer, rsi = count, result in rax
  31  xor   eax, eax
  33  test  rsi, rsi
  36  je    done
loop:
  42  add   rax, [rdi]
  45  add   rdi, 8
  49  sub   rsi, 1
  53  jne   loop
done:
  59  ret
```
-/

open TypedAsm

namespace Sum

/-! ## The program -/

inductive Label
  | sum | loop | done | spin
  deriving DecidableEq

def code : List (Asm Label) := [
  .ins (.lea .w64 .rdi (.rip 0xff9)) 7,
  .ins (.mov .w32 (.rm_i (.reg .rsi) 5)) 5,
  .call .sum,
  .ins (.mov .w32 (.rm_r (.reg .rdi) .rax)) 2,
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)) 5,
  .ins .syscall 2,
  .label .spin,
  .jmp .spin,
  .label .sum,
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)) 2,
  .ins (.test .w64 (.reg .rsi) (.reg .rsi)) 3,
  .jcc .e .done,
  .label .loop,
  .ins (.alu .add .w64 (.r_m .rax (.sib (some .rdi) none 0))) 3,
  .ins (.alu .add .w64 (.rm_i (.reg .rdi) 8)) 4,
  .ins (.alu .sub .w64 (.rm_i (.reg .rsi) 1)) 4,
  .jcc .ne .loop,
  .label .done,
  .ins .ret 1]

def fetch : Fetch := Asm.fetch 0 code

def array : List (BitVec 64) := [3, 1, 4, 1, 5]

/-- The starting state: the array in read-only memory at `0x1000` and one
free stack slot below `rsp`. No register points anywhere yet. -/
def start : State :=
  let s := (State.init.setPerm 0x1000 40 .ro).setPerm 0x7ff8 8 .rw
  let s := (array.zipIdx).foldl (fun s (v, i) => s.store64 (0x1000 + 8 * BitVec.ofNat 64 i) v) s
  s.setReg .rsp 0x8000

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

/-- Contexts are given only where control arrives from elsewhere. -/
inductive Φ : BitVec 64 → Ctx → Prop
  | start : Φ 0 fin
  | afterCall : Φ 17 fin
  | spin : Φ 26 fin
  | sum (n : Nat) (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat) :
    (sumSig n).CallerOk saved ret rest room → Φ 31 ((sumSig n).entry saved ret rest room)
  /-- The loop invariant, for `i < n` elements consumed. -/
  | loop (n i : Nat) (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat) :
    (sumSig n).CallerOk saved ret rest room → i < n →
    Φ 42 ⟨sumRegs n i saved, .code ret :: rest, room, Flags.Any⟩
  | done (n : Nat) (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat) :
    (sumSig n).CallerOk saved ret rest room → Φ 59 ((sumSig n).exit saved ret rest room)

def arrayLayout : Layout := ⟨List.replicate 5 .int, false⟩

/-- One memory block: the array. -/
def blocks : List (BitVec 64 × Layout) := [(0x1000, arrayLayout)]

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
  intro a Γ h
  cases h with
  | start =>
    -- lea rdi, [rip + array]; mov esi, 5
    ty_steps
    -- `rdi` holds exactly the array's address, so it is a pointer to its first element
    refine BlockOk.castPtr (r := .rdi) (base := 0x1000) (i := 0) (w := false) (by decide) rfl rfl
      (by decide) (fun h => absurd h (by decide)) ?_
    -- call sum
    exact .last rfl (FnSig.call_ok (sig := sumSig 5) (fun _ _ _ _ hK => .sum 5 _ _ _ _ hK) rfl
      Φ.afterCall (by sub_regs) (by ctx_sub) (by decide))
  | afterCall =>
    -- mov edi, eax; mov eax, 60; syscall
    ty_steps
    exact .last rfl (.syscall (by ty_accept Φ.spin))
  | spin => exact .last rfl (.jmp (by ty_accept Φ.spin))
  | sum n saved ret rest room hK =>
    -- xor eax, eax; test rsi, rsi; je done
    ty_steps
    refine .last rfl (.jcc ?_ ?_ ?_)
    · rintro f rfl; exact ⟨_, rfl⟩
    · rintro f rfl -
      ty_accept (Φ.done n saved ret rest room hK)
    · -- not taken: the count is not zero, so the invariant holds with `i = 0`
      rintro f rfl hne
      ty_accept (Φ.loop n 0 saved ret rest room hK ?_)
      apply left_ne_zero
      intro h0
      simp [Cond.eval, Flags.ofResult, h0] at hne
  | loop n i saved ret rest room hK hi =>
    -- add rax, [rdi]; add rdi, 8; sub rsi, 1; jne loop
    ty_steps
    refine .last rfl (.jcc ?_ ?_ ?_)
    · rintro f rfl; exact ⟨_, rfl⟩
    · -- taken: the counter is not zero, so `i + 1 < n` and the invariant holds again
      rintro f rfl hne
      have h0 : left n (i + 1) ≠ 0 := by
        intro h0
        rw [← decr hi] at h0
        simp [Cond.eval, AluOp.apply, subBorrow_zf] at hne
        exact hne (by simpa [AluOp.apply] using h0)
      ty_accept (Φ.loop n (i + 1) saved ret rest room hK (left_ne_zero h0))
      exact Sub.of_eq (decr hi)
    · rintro f rfl -
      ty_accept (Φ.done n saved ret rest room hK)
  | done n saved ret rest room hK => exact .last rfl (FnSig.ret_ok hK)

/-! ## The memory typing and the starting state -/

theorem memOk : Ψ.WF := MemTy.wf_of_check (by decide)

theorem startOk : StateOk Φ fetch linux Ψ start := by
  refine ⟨_, Φ.start, fun n => Matches.ofCheck (by decide) ?_ trivial ?_ ?_⟩
  · intro r _
    exact HasTy.int _
  · intro i τ h; simp [fin] at h
  · intro x hx i τ hi
    simp only [blocks, List.mem_singleton] at hx
    subst hx
    have : τ = .int := by simpa [arrayLayout] using List.mem_of_getElem? hi
    subst this
    exact HasTy.int _

/-! ## Safety -/

/-- The program never gets stuck, never page-faults and never executes an
invalid opcode. In particular every array access is in bounds. -/
theorem safe : Safe fetch linux start :=
  soundness_blocks blocksOk memOk (linuxOk fetch Ψ) startOk

/-- So running it for any number of steps gives an acceptable outcome. -/
theorem run_safe (n : Nat) : (run fetch linux n start).isSafe = true :=
  safe.run n

/-! ## Running it -/

def describe : Outcome → String
  | .next s => s!"still running at rip = {s.rip.toNat}"
  | .fault f => s!"fault: {repr f}"
  | .exit code => s!"exit {code.toNat}"
  | .stuck => "stuck"

def exitsWith (code : BitVec 32) : Outcome → Bool
  | .exit c => c == code
  | _ => false

-- The program exits with status 14 = 3 + 1 + 4 + 1 + 5.
#guard exitsWith 14 (run fetch linux 100 start)

end Sum

def main : IO Unit :=
  IO.println (Sum.describe (run Sum.fetch linux 100 Sum.start))
