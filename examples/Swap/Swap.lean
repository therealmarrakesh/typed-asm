import TypedAsm

/-!
# Swapping two fields, proved safe

A complete program that is type-checked and then proved safe by the soundness
theorem. A function that swaps the two fields of a record is typed once and
called from two places whose stacks differ.

```asm
_start:                       ; rdi = pointer to a record of two integers
   0  call  swap              ; called with an empty stack
   5  push  rdi
   6  call  swap              ; called with one slot on the stack
  11  pop   rdi
  12  mov   eax, 60           ; Linux `exit`
  17  xor   edi, edi
  19  syscall
  21  jmp   21                ; not reached: `exit` does not return
swap:
  26  mov   rax, [rdi]
  29  mov   rcx, [rdi+8]
  33  mov   [rdi], rcx
  36  mov   [rdi+8], rax
  40  ret
```
-/

open TypedAsm

namespace Swap

/-! ## The program -/

def field (disp : BitVec 32) : Mem := .sib (some .rdi) none disp

def code : List (Instr × BitVec 64) := [
  (.call (.rel 21), 5),
  (.push .rdi, 1),
  (.call (.rel 15), 5),
  (.pop .rdi, 1),
  (.mov .w32 (.rm_i (.reg .rax) 60), 5),
  (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi), 2),
  (.syscall, 2),
  (.jmp (.rel (-5)), 5),
  (.mov .w64 (.r_m .rax (field 0)), 3),
  (.mov .w64 (.r_m .rcx (field 8)), 4),
  (.mov .w64 (.rm_r (.mem (field 0)) .rcx), 3),
  (.mov .w64 (.rm_r (.mem (field 8)) .rax), 4),
  (.ret, 1)]

def fetch : Fetch := .layout 0 code

/-- A small model of Linux: `exit` ends the program; every other system call
fails with `-ENOSYS` in `rax`. Like the real kernel, it overwrites `rcx` and
`r11` and leaves the flags unknown. -/
def linux : Syscall := fun s =>
  if s.getReg .rax = 60 then .exit (s.readReg .w32 .rdi)
  else .next { ((s.setReg .rax (-38)).setReg .rcx s.rip).setReg .r11 0 with flags := .unknown }

/-- The starting state: a record holding 3 and 5 at `0x1000`, two free stack
slots below `rsp`, and `rdi` pointing at the record. -/
def start : State :=
  (((State.init.setPerm 0x1000 16 .rw).setPerm 0x7ff0 16 .rw).store64 0x1000 3).store64 0x1008 5
    |>.setReg .rsp 0x8000 |>.setReg .rdi 0x1000

/-! ## The typing -/

/-- A pointer to a writable record of two integers. -/
def pair : Ty := .ptr [.int, .int] true

/-- Register types while `rdi` points to the record. -/
def ptrRegs : Reg → Ty := fun r => if r = .rdi then pair else .int

/-- A context in which `rdi` points to the record. -/
def withPtr (stack : List Ty) (room : Nat) : Ctx := ⟨ptrRegs, stack, room, false⟩

/-- For the last part of `_start`: nothing is known about any register. -/
def done : Ctx := ⟨fun _ => .int, [], 2, false⟩

/-- The context inside `swap`, for a caller that expects `ret` on return and
has `rest` on its stack. This is where `swap` is polymorphic: it is typed for
every such caller at once. -/
def swapCtx (ret : Ctx) (rest : List Ty) (room : Nat) : Ctx :=
  withPtr (.code ret :: rest) room

/-- What `swap` needs of its caller: the state it returns (pointer still in
`rdi`, the caller's stack untouched) must be acceptable to the caller. -/
def CallerOk (ret : Ctx) (rest : List Ty) (room : Nat) : Prop :=
  CtxSub (withPtr rest (room + 1)) ret

def swapBody : List (BitVec 64) := [26, 29, 33, 36, 40]

inductive Φ : BitVec 64 → Ctx → Prop
  | start : Φ 0 (withPtr [] 2)
  | afterFirst : Φ 5 (withPtr [] 2)
  | second : Φ 6 (withPtr [pair] 1)
  | afterSecond : Φ 11 (withPtr [pair] 1)
  | done (a : BitVec 64) : a ∈ [12, 17, 19, 21] → Φ a done
  | swap (a : BitVec 64) (ret : Ctx) (rest : List Ty) (room : Nat) :
    a ∈ swapBody → CallerOk ret rest room → Φ a (swapCtx ret rest room)

def recordLayout : Layout := ⟨[.int, .int], true⟩

/-- One memory block: the record. -/
def Ψ : MemTy := fun a => if a = 0x1000 then some recordLayout else none

/-! ## The program is well typed -/

theorem subDone (Γ : Ctx) (hs : Γ.stack = []) (hm : Γ.room = 2) : CtxSub Γ done :=
  ⟨fun _ _ => .int _, by rw [hs]; exact .nil, hm, fun h => absurd h (by decide)⟩

theorem accDone {a : BitVec 64} (ha : a ∈ [12, 17, 19, 21]) (Γ : Ctx) (hs : Γ.stack = [])
    (hm : Γ.room = 2) : Accepts Φ a Γ :=
  ⟨done, .done a ha, subDone Γ hs hm⟩

/-- Inside `swap`, a context that still has the pointer in `rdi` and the same
stack is accepted at any later instruction of `swap`. -/
theorem accSwap {a : BitVec 64} {ret : Ctx} {rest : List Ty} {room : Nat} (ha : a ∈ swapBody)
    (hK : CallerOk ret rest room) (Γ : Ctx) (hr : ∀ r, r ≠ .rsp → Sub (Γ.regs r) (ptrRegs r))
    (hs : Γ.stack = .code ret :: rest) (hm : Γ.room = room) : Accepts Φ a Γ :=
  ⟨swapCtx ret rest room, .swap a ret rest room ha hK,
    ⟨hr, by rw [hs]; exact .refl _, hm, fun h => absurd h Bool.false_ne_true⟩⟩

/-- Setting a register other than `rdi` to an integer keeps the pointer in `rdi`. -/
theorem setInt (Γ : Ctx) (hΓ : Γ.regs = ptrRegs) (d : Reg) (hd : d ≠ .rdi) :
    ∀ r, r ≠ .rsp → Sub ((Γ.setReg d .int).regs r) (ptrRegs r) := by
  intro r _
  simp only [CtxOf.setReg, hΓ]
  split
  · next h => subst h; simp only [ptrRegs, hd, ite_false]; exact .refl _
  · exact .refl _

/-- `swap` is well typed for every caller. -/
theorem swapOk {a : BitVec 64} {ret : Ctx} {rest : List Ty} {room : Nat} (ha : a ∈ swapBody)
    (hK : CallerOk ret rest room) :
    ∃ i len, fetch a = some (i, len) ∧ HasType Φ (a + len) (swapCtx ret rest room) i := by
  have : a = 26 ∨ a = 29 ∨ a = 33 ∨ a = 36 ∨ a = 40 := by simpa [swapBody] using ha
  rcases this with rfl | rfl | rfl | rfl | rfl
  · -- mov rax, [rdi]
    exact ⟨_, _, rfl, .straight
      (.loadField (i := 0) (by decide) (by decide) rfl rfl ⟨rfl, by decide⟩)
      (accSwap (by decide) hK _ (setInt _ rfl .rax (by decide)) rfl rfl)⟩
  · -- mov rcx, [rdi+8]
    exact ⟨_, _, rfl, .straight
      (.loadField (i := 1) (by decide) (by decide) rfl rfl ⟨rfl, by decide⟩)
      (accSwap (by decide) hK _ (setInt _ rfl .rcx (by decide)) rfl rfl)⟩
  · -- mov [rdi], rcx
    exact ⟨_, _, rfl, .straight
      (.storeField (i := 0) (by decide) (by decide) rfl rfl (.refl _) ⟨rfl, by decide⟩)
      (accSwap (by decide) hK _ (fun _ _ => .refl _) rfl rfl)⟩
  · -- mov [rdi+8], rax
    exact ⟨_, _, rfl, .straight
      (.storeField (i := 1) (by decide) (by decide) rfl rfl (.refl _) ⟨rfl, by decide⟩)
      (accSwap (by decide) hK _ (fun _ _ => .refl _) rfl rfl)⟩
  · -- ret: the caller's requirement is exactly what the rule asks for
    exact ⟨_, _, rfl, .ret rfl hK⟩

theorem programOk : ProgramOk Φ fetch := by
  intro a Γ h
  cases h with
  | start => -- call swap, from an empty stack
    exact ⟨_, _, rfl, .call (n := 1) rfl Φ.afterFirst
      ⟨_, .swap 26 (withPtr [] 2) [] 1 (by decide) (CtxSub.refl _), CtxSub.refl _⟩⟩
  | afterFirst => -- push rdi
    exact ⟨_, _, rfl, .straight (.push (n := 1) (by decide) rfl) ⟨_, Φ.second, CtxSub.refl _⟩⟩
  | second => -- call swap, with one slot on the stack
    exact ⟨_, _, rfl, .call (n := 0) rfl Φ.afterSecond
      ⟨_, .swap 26 (withPtr [pair] 1) [pair] 0 (by decide) (CtxSub.refl _), CtxSub.refl _⟩⟩
  | afterSecond => -- pop rdi
    exact ⟨_, _, rfl, .straight (.pop (by decide) rfl) (accDone (by decide) _ rfl rfl)⟩
  | done a ha =>
    have : a = 12 ∨ a = 17 ∨ a = 19 ∨ a = 21 := by simpa using ha
    rcases this with rfl | rfl | rfl | rfl
    · -- mov eax, 60
      exact ⟨_, _, rfl, .straight (.movRI (by decide)) (accDone (by decide) _ rfl rfl)⟩
    · -- xor edi, edi
      exact ⟨_, _, rfl, .straight (.aluRR (by decide) (fun h => absurd h (by decide)))
        (accDone (by decide) _ rfl rfl)⟩
    · -- syscall
      exact ⟨_, _, rfl, .syscall (accDone (by decide) _ rfl rfl)⟩
    · -- jmp 21
      exact ⟨_, _, rfl, .jmp (accDone (by decide) _ rfl rfl)⟩
  | swap a ret rest room ha hK => exact swapOk ha hK

/-! ## The memory typing, the starting state and the operating system -/

theorem Ψ_cases {a : BitVec 64} {l : Layout} (h : Ψ a = some l) :
    a = 0x1000 ∧ l = recordLayout := by
  unfold Ψ at h
  split at h
  · next ha => exact ⟨ha, (Option.some.inj h).symm⟩
  · cases h

theorem memOk : Ψ.WF := by
  constructor
  · intro a l h
    obtain ⟨rfl, rfl⟩ := Ψ_cases h
    decide
  · intro a b la lb ha hb hne
    obtain ⟨rfl, rfl⟩ := Ψ_cases ha
    obtain ⟨rfl, rfl⟩ := Ψ_cases hb
    exact absurd rfl hne

theorem startOk : StateOk Φ fetch linux Ψ start := by
  refine ⟨withPtr [] 2, Φ.start, fun n => ?_⟩
  constructor
  · intro r _
    simp only [withPtr, ptrRegs]
    split
    · next h => subst h; exact hasTy_ptr.mpr ⟨recordLayout, rfl, rfl, fun _ => rfl⟩
    · exact HasTy.int _
  · intro h; exact absurd h (by decide)
  · decide
  · decide
  · intro i τ h; simp [withPtr] at h
  · intro a l h
    obtain ⟨rfl, rfl⟩ := Ψ_cases h
    constructor <;> decide
  · intro a l h i τ hi
    obtain ⟨rfl, rfl⟩ := Ψ_cases h
    have : τ = .int := by
      have := List.mem_of_getElem? hi
      simpa [recordLayout] using this
    subst this
    exact HasTy.int _
  · intro a l h
    obtain ⟨rfl, rfl⟩ := Ψ_cases h
    constructor <;> decide

/-- The Linux model satisfies what the type system assumes of the operating
system, for any program and memory typing. -/
theorem linuxOk (fetch : Fetch) (Ψ : MemTy) : SysOk fetch linux Ψ := by
  intro n Γ s h
  unfold linux
  split
  · exact ⟨rfl, fun s' he => by cases he⟩
  · refine ⟨rfl, fun s' he => ?_⟩
    cases he
    exact ⟨rfl, (((h.setReg (by decide) (HasTy.int _)).setReg (by decide) (HasTy.int _)).setReg
      (by decide) (HasTy.int _)).setFlags (b := false) (fun hf => absurd hf (by decide))⟩

/-! ## Safety -/

/-- The program never gets stuck, never page-faults and never executes an invalid opcode. -/
theorem safe : Safe fetch linux start :=
  soundness programOk memOk (linuxOk fetch Ψ) startOk

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

-- After the first call returns (six steps) the fields are exchanged, and
-- after the second (seven more) they are back.
#guard recordIs 5 3 (run fetch linux 6 start)
#guard recordIs 3 5 (run fetch linux 13 start)

end Swap

def main : IO Unit := do
  IO.println (Swap.describe (run Swap.fetch Swap.linux 0 Swap.start))
  IO.println (Swap.describe (run Swap.fetch Swap.linux 6 Swap.start))
  IO.println (Swap.describe (run Swap.fetch Swap.linux 13 Swap.start))
  IO.println (Swap.describe (run Swap.fetch Swap.linux 100 Swap.start))
