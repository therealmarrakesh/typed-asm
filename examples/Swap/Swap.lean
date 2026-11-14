import TypedAsm

/-!
# Swapping two fields, proved safe

A complete program that is type-checked and then proved safe by the soundness
theorem. It calls a function that swaps the two fields of a record, then exits.

```asm
_start:                       ; rdi = pointer to a record of two integers
   0  call  swap
   5  mov   eax, 60           ; Linux `exit`
  10  xor   edi, edi
  12  syscall
  14  jmp   14                ; not reached: `exit` does not return
swap:
  19  mov   rax, [rdi]
  22  mov   rcx, [rdi+8]
  26  mov   [rdi], rcx
  29  mov   [rdi+8], rax
  33  ret
```
-/

open TypedAsm

namespace Swap

/-! ## The program -/

def field (disp : BitVec 32) : Mem := .sib (some .rdi) none disp

def code : List (Instr × BitVec 64) := [
  (.call (.rel 14), 5),
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

/-- The starting state: a record holding 3 and 5 at `0x1000`, one free stack
slot below `rsp`, and `rdi` pointing at the record. -/
def start : State :=
  (((State.init.setPerm 0x1000 16 .rw).setPerm 0x7ff8 8 .rw).store64 0x1000 3).store64 0x1008 5
    |>.setReg .rsp 0x8000 |>.setReg .rdi 0x1000

/-! ## The typing -/

/-- A pointer to a writable record of two integers. -/
def pair : Ty := .ptr [.int, .int] true

/-- After the call returns, and for the rest of `_start`: nothing is known
about any register, the stack is empty, and one slot is free. -/
def after : Ctx := ⟨fun _ => .int, [], 1, false⟩

/-- On entry to `_start`: `rdi` points to the record. -/
def entry : Ctx := ⟨fun r => if r = .rdi then pair else .int, [], 1, false⟩

/-- Throughout `swap`: `rdi` points to the record and the return address is on the stack. -/
def body : Ctx := ⟨fun r => if r = .rdi then pair else .int, [.code after], 0, false⟩

def Φ : CodeTy := fun a =>
  if a = 0 then some entry
  else if a ∈ [5, 10, 12, 14] then some after
  else if a ∈ [19, 22, 26, 29, 33] then some body
  else none

def recordLayout : Layout := ⟨[.int, .int], true⟩

/-- One memory block: the record. -/
def Ψ : MemTy := fun a => if a = 0x1000 then some recordLayout else none

/-! ## The program is well typed -/

theorem Φ_cases {a : BitVec 64} {Γ : Ctx} (h : Φ a = some Γ) :
    (a = 0 ∧ Γ = entry) ∨
    ((a = 5 ∨ a = 10 ∨ a = 12 ∨ a = 14) ∧ Γ = after) ∨
    ((a = 19 ∨ a = 22 ∨ a = 26 ∨ a = 29 ∨ a = 33) ∧ Γ = body) := by
  unfold Φ at h
  split at h
  · next ha => exact .inl ⟨ha, (Option.some.inj h).symm⟩
  · split at h
    · next ha => exact .inr (.inl ⟨by simpa using ha, (Option.some.inj h).symm⟩)
    · split at h
      · next ha => exact .inr (.inr ⟨by simpa using ha, (Option.some.inj h).symm⟩)
      · cases h

/-- Any context with an empty stack and one free slot is accepted where `after` is required. -/
theorem subAfter (Γ : Ctx) (hs : Γ.stack = []) (hm : Γ.room = 1) : CtxSub Γ after :=
  ⟨fun _ _ => .int _, by rw [hs]; exact .nil, hm, fun h => absurd h (by decide)⟩

theorem subBody (Γ : Ctx) (hr : ∀ r, r ≠ .rsp → Sub (Γ.regs r) (body.regs r))
    (hs : Γ.stack = body.stack) (hm : Γ.room = 0) : CtxSub Γ body :=
  ⟨hr, by rw [hs]; exact .cons (.refl _) .nil, hm, fun h => absurd h (by decide)⟩

/-- Setting a register other than `rdi` to an integer keeps `swap`'s register types. -/
theorem setInt (d : Reg) (hd : d ≠ .rdi) :
    ∀ r, r ≠ .rsp → Sub ((body.setReg d .int).regs r) (body.regs r) := by
  intro r _
  simp only [CtxOf.setReg]
  split
  · next h => subst h; simp only [body, hd, ite_false]; exact .refl _
  · exact .refl _

theorem programOk : ProgramOk Φ fetch := by
  intro a Γ h
  rcases Φ_cases h with ⟨rfl, rfl⟩ | ⟨h5 | h10 | h12 | h14, rfl⟩ |
    ⟨h19 | h22 | h26 | h29 | h33, rfl⟩
  · -- call swap
    exact ⟨_, _, rfl, .call (n := 0) rfl (rfl : Φ 5 = some after)
      ⟨body, rfl, subBody _ (fun _ _ => .refl _) rfl rfl⟩⟩
  · subst h5 -- mov eax, 60
    exact ⟨_, _, rfl, .straight (.movRI (by decide)) ⟨after, rfl, subAfter _ rfl rfl⟩⟩
  · subst h10 -- xor edi, edi
    exact ⟨_, _, rfl, .straight (.aluRR (by decide) (fun h => absurd h (by decide)))
      ⟨after, rfl, subAfter _ rfl rfl⟩⟩
  · subst h12 -- syscall
    exact ⟨_, _, rfl, .syscall ⟨after, rfl, subAfter _ rfl rfl⟩⟩
  · subst h14 -- jmp 14
    exact ⟨_, _, rfl, .jmp ⟨after, rfl, subAfter _ rfl rfl⟩⟩
  · subst h19 -- mov rax, [rdi]
    exact ⟨_, _, rfl, .straight
      (.loadField (i := 0) (by decide) (by decide) rfl rfl ⟨rfl, by decide⟩)
      ⟨body, rfl, subBody _ (setInt .rax (by decide)) rfl rfl⟩⟩
  · subst h22 -- mov rcx, [rdi+8]
    exact ⟨_, _, rfl, .straight
      (.loadField (i := 1) (by decide) (by decide) rfl rfl ⟨rfl, by decide⟩)
      ⟨body, rfl, subBody _ (setInt .rcx (by decide)) rfl rfl⟩⟩
  · subst h26 -- mov [rdi], rcx
    exact ⟨_, _, rfl, .straight
      (.storeField (i := 0) (by decide) (by decide) rfl rfl (.refl _) ⟨rfl, by decide⟩)
      ⟨body, rfl, subBody _ (fun _ _ => .refl _) rfl rfl⟩⟩
  · subst h29 -- mov [rdi+8], rax
    exact ⟨_, _, rfl, .straight
      (.storeField (i := 1) (by decide) (by decide) rfl rfl (.refl _) ⟨rfl, by decide⟩)
      ⟨body, rfl, subBody _ (fun _ _ => .refl _) rfl rfl⟩⟩
  · subst h33 -- ret
    exact ⟨_, _, rfl, .ret rfl (subAfter _ rfl rfl)⟩

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

theorem startOk : StateOk Φ Ψ start := by
  refine ⟨entry, rfl, ?_⟩
  constructor
  · intro r _
    simp only [entry]
    split
    · next h => subst h; exact ⟨recordLayout, rfl, rfl, fun _ => rfl⟩
    · trivial
  · intro h; exact absurd h (by decide)
  · decide
  · decide
  · intro i τ h; simp [entry] at h
  · intro a l h
    obtain ⟨rfl, rfl⟩ := Ψ_cases h
    constructor <;> decide
  · intro a l h i τ hi
    obtain ⟨rfl, rfl⟩ := Ψ_cases h
    have : τ = .int := by
      have := List.mem_of_getElem? hi
      simpa [recordLayout] using this
    subst this
    trivial
  · intro a l h
    obtain ⟨rfl, rfl⟩ := Ψ_cases h
    constructor <;> decide

/-- The Linux model satisfies what the type system assumes of the operating
system, for any code and memory typing. -/
theorem linuxOk (Φ : CodeTy) (Ψ : MemTy) : SysOk Φ Ψ linux := by
  intro Γ s h
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
  soundness programOk memOk (linuxOk Φ Ψ) startOk

/-- So running it for any number of steps gives an acceptable outcome. -/
theorem run_safe (n : Nat) : (run fetch linux n start).isSafe = true :=
  safe.run n

/-! ## Running it -/

def describe : Outcome → String
  | .next s => s!"running: record = ({(s.load64 0x1000).toNat}, {(s.load64 0x1008).toNat})"
  | .fault f => s!"fault: {repr f}"
  | .exit code => s!"exit {code.toNat}"
  | .stuck => "stuck"

/-- After the call returns (six steps), the two fields have been exchanged. -/
def swapped : Outcome → Bool
  | .next s => s.load64 0x1000 == 5 && s.load64 0x1008 == 3
  | _ => false

#guard swapped (run fetch linux 6 start)

end Swap

def main : IO Unit := do
  IO.println (Swap.describe (run Swap.fetch Swap.linux 0 Swap.start))
  IO.println (Swap.describe (run Swap.fetch Swap.linux 6 Swap.start))
  IO.println (Swap.describe (run Swap.fetch Swap.linux 100 Swap.start))
