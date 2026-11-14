import TypedAsm

/-!
# Summing an array, proved safe

A function that sums `n` 64-bit integers through a moving pointer, with a
loop counter. Its safety depends on the counter and the pointer staying in
step, which the typing expresses with types that depend on values: the
contexts inside the loop are indexed by how many elements have been consumed.

```asm
_start:                       ; rdi = pointer to an array of five integers
   0  mov   esi, 5
   5  call  sum
  10  mov   edi, eax
  12  mov   eax, 60           ; Linux `exit`
  17  syscall
  19  jmp   19                ; not reached: `exit` does not return
sum:                          ; rdi = pointer, rsi = count, result in rax
  24  xor   eax, eax
  26  test  rsi, rsi
  29  je    done
loop:
  35  add   rax, [rdi]
  38  add   rdi, 8
  42  sub   rsi, 1
  46  jne   loop
done:
  52  ret
```
-/

open TypedAsm

namespace Sum

/-! ## The program -/

def code : List (Instr × BitVec 64) := [
  (.mov .w32 (.rm_i (.reg .rsi) 5), 5),
  (.call (.rel 14), 5),
  (.mov .w32 (.rm_r (.reg .rdi) .rax), 2),
  (.mov .w32 (.rm_i (.reg .rax) 60), 5),
  (.syscall, 2),
  (.jmp (.rel (-5)), 5),
  -- sum
  (.alu .xor .w32 (.rm_r (.reg .rax) .rax), 2),
  (.test .w64 (.reg .rsi) (.reg .rsi), 3),
  (.jcc .e 17, 6),
  -- loop
  (.alu .add .w64 (.r_m .rax (.sib (some .rdi) none 0)), 3),
  (.alu .add .w64 (.rm_i (.reg .rdi) 8), 4),
  (.alu .sub .w64 (.rm_i (.reg .rsi) 1), 4),
  (.jcc .ne (-17), 6),
  -- done
  (.ret, 1)]

def fetch : Fetch := .layout 0 code

/-- A small model of Linux: `exit` ends the program; every other system call
fails with `-ENOSYS` in `rax`. Like the real kernel, it overwrites `rcx` and
`r11` and leaves the flags unknown. -/
def linux : Syscall := fun s =>
  if s.getReg .rax = 60 then .exit (s.readReg .w32 .rdi)
  else .next { ((s.setReg .rax (-38)).setReg .rcx s.rip).setReg .r11 0 with flags := .unknown }

def array : List (BitVec 64) := [3, 1, 4, 1, 5]

/-- The starting state: the array in read-only memory at `0x1000`, one free
stack slot below `rsp`, and `rdi` pointing at the array. -/
def start : State :=
  let s := (State.init.setPerm 0x1000 40 .ro).setPerm 0x7ff8 8 .rw
  let s := (array.zipIdx).foldl (fun s (v, i) => s.store64 (0x1000 + 8 * BitVec.ofNat 64 i) v) s
  (s.setReg .rsp 0x8000).setReg .rdi 0x1000

/-! ## The typing -/

/-- A pointer to element `i` of a read-only array of `n` integers. -/
def elem (n i : Nat) : Ty := .ptr (List.replicate n .int) false i

/-- Register types with given types for the pointer and the counter. -/
def regsWith (ptr count : Ty) : Reg → Ty :=
  fun r => if r = .rdi then ptr else if r = .rsi then count else .int

/-- For the last part of `_start`: nothing is known about any register. -/
def fin : Ctx := ⟨fun _ => .int, [], 1, Flags.Any⟩

/-- A context inside `sum`, for a caller that expects `ret` on return and has
`rest` on its stack. -/
def inSum (ret : Ctx) (rest : List Ty) (room : Nat) (ptr count : Ty) (flags : Flags → Prop) :
    Ctx :=
  ⟨regsWith ptr count, .code ret :: rest, room, flags⟩

/-- What `sum` needs of its caller: the state it returns (nothing known about
any register, the caller's stack untouched) must be acceptable to the caller. -/
def CallerOk (ret : Ctx) (rest : List Ty) (room : Nat) : Prop :=
  CtxSub ⟨fun _ => .int, rest, room + 1, Flags.Any⟩ ret

/-- The counter after `i` of `n` elements have been consumed. -/
def left (n i : Nat) : BitVec 64 := BitVec.ofNat 64 (n - i)

/-- The flags after `test rsi, rsi` on entry. -/
def testFlags (n : Nat) : Flags := .ofResult (left n 0 &&& left n 0) false false

/-- The counter and flags after `sub rsi, 1` in iteration `i`. -/
def decr (n i : Nat) : BitVec 64 × Flags := subBorrow (left n i) ((1 : BitVec 32).signExtend 64) false

inductive Φ : BitVec 64 → Ctx → Prop
  | start : Φ 0 ⟨regsWith (elem 5 0) .int, [], 1, Flags.Any⟩
  | counted : Φ 5 ⟨regsWith (elem 5 0) (.eq 5), [], 1, Flags.Any⟩
  | fin (a : BitVec 64) : a ∈ [10, 12, 17, 19] → Φ a fin
  /-- On entry to `sum`: the pointer is at element 0 and the counter is exactly `n`. -/
  | entry (a : BitVec 64) (ret : Ctx) (rest : List Ty) (room n : Nat) :
    a ∈ [24, 26] → CallerOk ret rest room →
    Φ a (inSum ret rest room (elem n 0) (.eq (left n 0)) Flags.Any)
  | tested (ret : Ctx) (rest : List Ty) (room n : Nat) : CallerOk ret rest room →
    Φ 29 (inSum ret rest room (elem n 0) (.eq (left n 0)) (· = testFlags n))
  /-- The loop invariant: after `i` elements, with `i < n`, the pointer is at
  element `i` and the counter is exactly `n - i`. -/
  | loop (a : BitVec 64) (ret : Ctx) (rest : List Ty) (room n i : Nat) :
    a ∈ [35, 38] → CallerOk ret rest room → i < n →
    Φ a (inSum ret rest room (elem n i) (.eq (left n i)) Flags.Any)
  | advanced (ret : Ctx) (rest : List Ty) (room n i : Nat) : CallerOk ret rest room → i < n →
    Φ 42 (inSum ret rest room (elem n (i + 1)) (.eq (left n i)) Flags.Any)
  | decremented (ret : Ctx) (rest : List Ty) (room n i : Nat) : CallerOk ret rest room → i < n →
    Φ 46 (inSum ret rest room (elem n (i + 1)) (.eq (decr n i).1) (· = (decr n i).2))
  | done (ret : Ctx) (rest : List Ty) (room n : Nat) : CallerOk ret rest room →
    Φ 52 ⟨fun _ => .int, .code ret :: rest, room, Flags.Any⟩

def arrayLayout : Layout := ⟨List.replicate 5 .int, false⟩

/-- One memory block: the array. -/
def Ψ : MemTy := fun a => if a = 0x1000 then some arrayLayout else none

/-! ## Arithmetic facts the loop relies on -/

theorem left_ne_zero {n i : Nat} (h : left n i ≠ 0) : i < n := by
  apply Nat.lt_of_sub_ne_zero
  intro h0
  exact h (by simp [left, h0])

theorem decr_fst {n i : Nat} (hi : i < n) : (decr n i).1 = left n (i + 1) := by
  have h1 : ((1 : BitVec 32).signExtend 64) = 1 := by decide
  simp only [decr, subBorrow_fst, h1, left]
  bv_omega

/-! ## The program is well typed -/

/-- Every register type is an integer type. -/
theorem subInt (Γ : Ctx) : ∀ r, r ≠ .rsp → Sub (Γ.regs r) Ty.int := fun _ _ => .int _

theorem accFin {a : BitVec 64} (ha : a ∈ [10, 12, 17, 19]) (Γ : Ctx) (hs : Γ.stack = [])
    (hm : Γ.room = 1) : Accepts Φ a Γ :=
  ⟨fin, .fin a ha, ⟨subInt Γ, by rw [hs]; exact .nil, hm, fun _ _ => trivial⟩⟩

/-- Register types are compared one register at a time. -/
macro "regs_sub" : tactic =>
  `(tactic| (intro r _; cases r <;> first | exact Sub.refl _ | exact Sub.int _))

/-- `sum` is well typed for every caller and every array length. -/
theorem sumOk {a : BitVec 64} {Γ : Ctx} (h : Φ a Γ) (ha : 24 ≤ a) :
    ∃ i len, fetch a = some (i, len) ∧ HasType Φ (a + len) Γ i := by
  cases h with
  | start => exact absurd ha (by decide)
  | counted => exact absurd ha (by decide)
  | fin a h =>
    have : a = 10 ∨ a = 12 ∨ a = 17 ∨ a = 19 := by simpa using h
    rcases this with rfl | rfl | rfl | rfl <;> exact absurd ha (by decide)
  | entry a ret rest room n h hK =>
    have : a = 24 ∨ a = 26 := by simpa using h
    rcases this with rfl | rfl
    · -- xor eax, eax
      exact ⟨_, _, rfl, .straight (.aluRR (by decide) (fun h => absurd h (by decide)))
        ⟨_, .entry 26 ret rest room n (by decide) hK, ⟨by regs_sub, .refl _, rfl, fun _ _ => trivial⟩⟩⟩
    · -- test rsi, rsi: the flags now say exactly whether the count is zero
      exact ⟨_, _, rfl, .straight (.testExact (by decide) (by decide) rfl rfl)
        ⟨_, .tested ret rest room n hK, CtxSub.refl _⟩⟩
  | tested ret rest room n hK =>
    -- je done
    refine ⟨_, _, rfl, .jcc ?_ ?_ ?_⟩
    · rintro f rfl; exact ⟨_, rfl⟩
    · -- taken: nothing more is needed at `done`
      rintro f rfl -
      exact ⟨_, .done ret rest room n hK, ⟨subInt _, .refl _, rfl, fun _ _ => trivial⟩⟩
    · -- not taken: the count is not zero, so the loop invariant holds with `i = 0`
      rintro f rfl hne
      have h0 : left n 0 ≠ 0 := by
        intro h0
        simp [Cond.eval, testFlags, Flags.ofResult, h0] at hne
      exact ⟨_, .loop 35 ret rest room n 0 (by decide) hK (left_ne_zero h0),
        ⟨fun _ _ => .refl _, .refl _, rfl, fun _ _ => trivial⟩⟩
  | loop a ret rest room n i h hK hi =>
    have : a = 35 ∨ a = 38 := by simpa using h
    rcases this with rfl | rfl
    · -- add rax, [rdi]: in bounds because `i < n`
      exact ⟨_, _, rfl, .straight
        (.aluMem (i := 0) (τ := .int) (by decide) (by decide) rfl
          (by simp [hi]) ⟨rfl, by decide⟩ (fun h => absurd h (by decide)))
        ⟨_, .loop 38 ret rest room n i (by decide) hK hi,
          ⟨by regs_sub, .refl _, rfl, fun _ _ => trivial⟩⟩⟩
    · -- add rdi, 8: still a pointer into the array, one element on
      exact ⟨_, _, rfl, .straight (.addPtr (k := 1) (by decide) rfl ⟨rfl, by decide⟩)
        ⟨_, .advanced ret rest room n i hK hi, ⟨by regs_sub, .refl _, rfl, fun _ _ => trivial⟩⟩⟩
  | advanced ret rest room n i hK hi =>
    -- sub rsi, 1: the counter and the flags are known exactly
    exact ⟨_, _, rfl, .straight (.aluExact (by decide) rfl rfl)
      ⟨_, .decremented ret rest room n i hK hi, ⟨by regs_sub, .refl _, rfl, fun _ h => h⟩⟩⟩
  | decremented ret rest room n i hK hi =>
    -- jne loop
    refine ⟨_, _, rfl, .jcc ?_ ?_ ?_⟩
    · rintro f rfl; exact ⟨_, rfl⟩
    · -- taken: the counter is not zero, so `i + 1 < n` and the invariant holds again
      rintro f rfl hne
      have hd := decr_fst (n := n) hi
      have h0 : left n (i + 1) ≠ 0 := by
        intro h0
        rw [← hd] at h0
        simp [Cond.eval, decr, subBorrow_zf] at hne
        exact hne (by simpa [decr] using h0)
      refine ⟨_, .loop 35 ret rest room n (i + 1) (by decide) hK (left_ne_zero h0),
        ⟨?_, .refl _, rfl, fun _ _ => trivial⟩⟩
      intro r _
      cases r <;> first | exact Sub.refl _ | exact Sub.int _ | exact hd ▸ Sub.refl _
    · -- not taken: fall through to `done`
      rintro f rfl -
      exact ⟨_, .done ret rest room n hK, ⟨subInt _, .refl _, rfl, fun _ _ => trivial⟩⟩
  | done ret rest room n hK =>
    -- ret
    exact ⟨_, _, rfl, .ret rfl hK⟩

theorem programOk : ProgramOk Φ fetch := by
  intro a Γ h
  by_cases ha : 24 ≤ a
  · exact sumOk h ha
  · cases h with
    | start => -- mov esi, 5
      exact ⟨_, _, rfl, .straight (.movRI (by decide))
        ⟨_, .counted, ⟨by regs_sub, .nil, rfl, fun _ _ => trivial⟩⟩⟩
    | counted => -- call sum
      exact ⟨_, _, rfl, .call (n := 0) rfl (Φ.fin 10 (by decide))
        ⟨_, .entry 24 fin [] 0 5 (by decide) (CtxSub.refl _), CtxSub.refl _⟩⟩
    | fin a h =>
      have : a = 10 ∨ a = 12 ∨ a = 17 ∨ a = 19 := by simpa using h
      rcases this with rfl | rfl | rfl | rfl
      · -- mov edi, eax
        exact ⟨_, _, rfl, .straight (.movRR32 (by decide)) (accFin (by decide) _ rfl rfl)⟩
      · -- mov eax, 60
        exact ⟨_, _, rfl, .straight (.movRI (by decide)) (accFin (by decide) _ rfl rfl)⟩
      · -- syscall
        exact ⟨_, _, rfl, .syscall (accFin (by decide) _ rfl rfl)⟩
      · -- jmp 19
        exact ⟨_, _, rfl, .jmp (accFin (by decide) _ rfl rfl)⟩
    | entry a _ _ _ _ h =>
      have : a = 24 ∨ a = 26 := by simpa using h
      rcases this with rfl | rfl <;> exact absurd (by decide) ha
    | tested => exact absurd (by decide) ha
    | loop a _ _ _ _ _ h =>
      have : a = 35 ∨ a = 38 := by simpa using h
      rcases this with rfl | rfl <;> exact absurd (by decide) ha
    | advanced => exact absurd (by decide) ha
    | decremented => exact absurd (by decide) ha
    | done => exact absurd (by decide) ha

/-! ## The memory typing, the starting state and the operating system -/

theorem Ψ_cases {a : BitVec 64} {l : Layout} (h : Ψ a = some l) :
    a = 0x1000 ∧ l = arrayLayout := by
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
  refine ⟨_, Φ.start, fun n => ?_⟩
  constructor
  · intro r _
    cases r <;> first
      | exact HasTy.int _
      | exact hasTy_ptr.mpr ⟨0x1000, arrayLayout, rfl, rfl, fun h => absurd h (by decide), by decide⟩
  · trivial
  · decide
  · decide
  · intro i τ h; simp at h
  · intro a l h
    obtain ⟨rfl, rfl⟩ := Ψ_cases h
    exact ⟨by decide, fun h => absurd h (by decide)⟩
  · intro a l h i τ hi
    obtain ⟨rfl, rfl⟩ := Ψ_cases h
    have : τ = .int := by
      have := List.mem_of_getElem? hi
      simpa [arrayLayout] using this
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
      (by decide) (HasTy.int _)).setFlags (P := Flags.Any) trivial⟩

/-! ## Safety -/

/-- The program never gets stuck, never page-faults and never executes an
invalid opcode. In particular every array access is in bounds. -/
theorem safe : Safe fetch linux start :=
  soundness programOk memOk (linuxOk fetch Ψ) startOk

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
  IO.println (Sum.describe (run Sum.fetch Sum.linux 100 Sum.start))
