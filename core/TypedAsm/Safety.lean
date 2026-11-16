import TypedAsm.Step

/-!
# Safety

What it means for a machine state to be safe to run: no state it can reach
takes a step with a bad outcome.

The outcomes that count as bad are getting stuck and every fault: a page
fault, an invalid opcode and a divide error. Only continuing and exiting are
acceptable.

Safety is relative to the instructions (`fetch`) and to the operating system
(`sys`). A system call that itself returns a bad outcome makes a program
unsafe, so a `syscall` is typed only where the operating system is shown to
behave: see `SysReturns` and `SysExits`.
-/

namespace TypedAsm

/-- Whether an outcome is acceptable for a safe program: it continues or it
exits. No fault is acceptable, a divide error included. -/
def Result.isSafe {α : Type} : Result α → Bool
  | .next _ => true
  | .exit _ => true
  | .fault _ => false
  | .stuck => false

variable (fetch : Fetch) (sys : Syscall)

/-- `Steps fetch sys s s'`: the machine can get from `s` to `s'` in zero or more steps. -/
inductive Steps : State → State → Prop
  | refl (s : State) : Steps s s
  | step {s s' s'' : State} : step fetch sys s = .next s' → Steps s' s'' → Steps s s''

/-- A state is safe if every state reachable from it takes a step with an
acceptable outcome. -/
def Safe (s : State) : Prop :=
  ∀ s', Steps fetch sys s s' → (step fetch sys s').isSafe = true

variable {fetch : Fetch} {sys : Syscall}

theorem Steps.single {s s' : State} (h : TypedAsm.step fetch sys s = .next s') : Steps fetch sys s s' :=
  .step h (.refl s')

theorem Steps.trans {s s' s'' : State} (h₁ : Steps fetch sys s s') (h₂ : Steps fetch sys s' s'') :
    Steps fetch sys s s'' := by
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact .step h (ih h₂)

/-- A safe state stays safe after a step. -/
theorem Safe.step {s s' : State} (hs : Safe fetch sys s) (h : TypedAsm.step fetch sys s = .next s') :
    Safe fetch sys s' :=
  fun s'' h' => hs s'' (.step h h')

/-- A property that holds now and is kept by every step holds in every reachable state. -/
theorem Steps.invariant {Inv : State → Prop} {s s' : State}
    (hstep : ∀ s s', Inv s → TypedAsm.step fetch sys s = .next s' → Inv s')
    (h : Steps fetch sys s s') (hs : Inv s) : Inv s' := by
  induction h with
  | refl => exact hs
  | step h _ ih => exact ih (hstep _ _ hs h)

/-- The standard route to safety: find a property of states that holds at the
start, guarantees an acceptable next step (progress), and is kept by every
step (preservation). Soundness of the type system is this theorem with
"is well typed" as the property. -/
theorem safe_of_invariant {Inv : State → Prop} {s : State} (hs : Inv s)
    (progress : ∀ s, Inv s → (TypedAsm.step fetch sys s).isSafe = true)
    (preservation : ∀ s s', Inv s → TypedAsm.step fetch sys s = .next s' → Inv s') :
    Safe fetch sys s :=
  fun _ h => progress _ (h.invariant preservation hs)

/-- If `run` continues to a state, that state is reachable. -/
theorem steps_of_run {n : Nat} {s s' : State} (h : run fetch sys n s = .next s') :
    Steps fetch sys s s' := by
  induction n generalizing s with
  | zero =>
    simp only [run, Result.next.injEq] at h
    exact h ▸ .refl s
  | succ n ih =>
    simp only [run] at h
    split at h
    next s₁ h₁ => exact .step h₁ (ih h)
    next => simp_all

/-- Running a safe state for any number of steps never produces a bad outcome. -/
theorem Safe.run {s : State} (hs : Safe fetch sys s) (n : Nat) :
    (run fetch sys n s).isSafe = true := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [TypedAsm.run]
    split
    next s₁ h₁ => exact ih (hs.step h₁)
    next o h₁ =>
      have := hs s (.refl s)
      cases h : TypedAsm.step fetch sys s <;> simp_all [Result.isSafe]

/-! ## Safety for a bounded number of steps

`SafeN n s` says the first `n` steps from `s` have acceptable outcomes. It is
what the meaning of a code-pointer type is built on, because it can be
defined by recursion on `n` where `Safe` cannot. -/

/-- The next `n` steps from `s` all have acceptable outcomes. -/
def SafeN (fetch : Fetch) (sys : Syscall) : Nat → State → Prop
  | 0, _ => True
  | n + 1, s =>
    (TypedAsm.step fetch sys s).isSafe = true ∧
    ∀ s', TypedAsm.step fetch sys s = .next s' → SafeN fetch sys n s'

/-- Being safe for more steps implies being safe for fewer. -/
theorem SafeN.mono {n m : Nat} {s : State} (h : SafeN fetch sys n s) (hle : m ≤ n) :
    SafeN fetch sys m s := by
  induction m generalizing n s with
  | zero => trivial
  | succ m ih =>
    cases n with
    | zero => omega
    | succ n => exact ⟨h.1, fun s' hs' => ih (h.2 s' hs') (by omega)⟩

/-- A state that is safe for every number of steps is safe. -/
theorem safe_of_safeN {s : State} (h : ∀ n, SafeN fetch sys n s) : Safe fetch sys s := by
  intro s' hs'
  induction hs' with
  | refl => exact (h 1).1
  | step hstep _ ih => exact ih (fun n => (h (n + 1)).2 _ hstep)

/-! ## What a program exits with

Safety says a program does nothing bad; it does not say what the program
does. One thing it does that can be said in the same terms is end, with a
status. An operating system that refuses every exit whose status is not as
wanted makes such an exit a bad step: so a program that is safe under that
operating system is safe under the real one, and ends only as wanted. The
typing of a program against it is then a proof of what the program exits
with. -/

/-- The operating system `sys`, refusing to end a program with a status that
does not satisfy `Q`. -/
noncomputable def Syscall.exitsOnly (sys : Syscall) (Q : BitVec 32 → Prop) : Syscall :=
  fun s =>
    match sys s with
    | .exit c => haveI := Classical.propDecidable (Q c); if Q c then .exit c else .stuck
    | r => r

variable {Q : BitVec 32 → Prop}

theorem Syscall.exitsOnly_next {s t : State} (h : sys s = .next t) :
    sys.exitsOnly Q s = .next t := by
  simp [Syscall.exitsOnly, h]

theorem Syscall.exitsOnly_exit {s : State} {c : BitVec 32} (h : sys s = .exit c) (hQ : Q c) :
    sys.exitsOnly Q s = .exit c := by
  simp [Syscall.exitsOnly, h, hQ]

/-- What the stricter system lets through, the plain one did. -/
theorem Syscall.safe_of_exitsOnly {s : State} (h : (sys.exitsOnly Q s).isSafe = true) :
    (sys s).isSafe = true ∧ ∀ c, sys s = .exit c → Q c := by
  unfold Syscall.exitsOnly at h
  cases hs : sys s with
  | next t => exact ⟨rfl, fun c hc => by cases hc⟩
  | fault f => rw [hs] at h; exact absurd h (by simp [Result.isSafe])
  | stuck => rw [hs] at h; exact absurd h (by simp [Result.isSafe])
  | exit c =>
    rw [hs] at h
    refine ⟨rfl, fun c' hc => ?_⟩
    cases hc
    haveI := Classical.propDecidable (Q c)
    by_cases hQ : Q c
    · exact hQ
    · simp [hQ, Result.isSafe] at h

/-- An instruction other than a system call does the same whatever the
operating system. -/
theorem exec_congr {sys' : Syscall} {i : Instr} (hi : i ≠ .syscall) (s : State) :
    exec sys' i s = exec sys i s := by
  cases i <;> first
    | rfl
    | exact absurd rfl hi
    | (rename_i t; cases t <;> rfl)
    | (rename_i op _ _; cases op <;> rfl)

theorem step_exitsOnly_of_next {s s' : State} (h : step fetch sys s = .next s') :
    step fetch (sys.exitsOnly Q) s = .next s' := by
  unfold step at h ⊢
  cases hf : fetch s.rip with
  | none => rw [hf] at h; cases h
  | some x =>
    obtain ⟨i, len⟩ := x
    rw [hf] at h
    by_cases hi : i = .syscall
    · subst hi
      exact Syscall.exitsOnly_next h
    · show exec (sys.exitsOnly Q) i _ = _
      rw [exec_congr hi]
      exact h

theorem Steps.exitsOnly {s s' : State} (h : Steps fetch sys s s') :
    Steps fetch (sys.exitsOnly Q) s s' := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (step_exitsOnly_of_next hs) ih

/-- **A program safe under the system that refuses unwanted exits is safe,
and ends only as wanted**: wherever it reaches a system call that ends it,
the status satisfies `Q`. -/
theorem Safe.of_exitsOnly {s : State} (h : Safe fetch (sys.exitsOnly Q) s) :
    Safe fetch sys s ∧
      ∀ s', Steps fetch sys s s' → ∀ len c, fetch s'.rip = some (.syscall, len) →
        sys { s' with rip := s'.rip + len } = .exit c → Q c := by
  refine ⟨fun s' hs' => ?_, fun s' hs' len c hf hc => ?_⟩
  · have hsafe := h s' hs'.exitsOnly
    unfold TypedAsm.step at hsafe ⊢
    cases hf : fetch s'.rip with
    | none => rw [hf] at hsafe; exact hsafe
    | some x =>
      obtain ⟨i, len⟩ := x
      rw [hf] at hsafe
      by_cases hi : i = .syscall
      · subst hi
        exact (Syscall.safe_of_exitsOnly hsafe).1
      · have e : exec (sys.exitsOnly Q) i { s' with rip := s'.rip + len }
            = exec sys i { s' with rip := s'.rip + len } := exec_congr hi _
        show (exec sys i _).isSafe = true
        rw [← e]
        exact hsafe
  · have hsafe := h s' hs'.exitsOnly
    unfold TypedAsm.step at hsafe
    rw [hf] at hsafe
    exact (Syscall.safe_of_exitsOnly hsafe).2 c hc

/-! ## What a program writes

The same device says what a program writes. The system is made to refuse a
`write` unless what the program offers it satisfies a condition; a program
shown safe under that system offers only such writes, under the plain one. -/

/-- What a `write` about to be made offers the kernel: the bytes at `rsi`,
as many as `rdx` says. The kernel may take fewer. -/
def State.offered (s : State) : List (BitVec 8) :=
  s.loadBytes (s.getReg .rsi) (s.getReg .rdx).toNat

/-- The operating system `sys`, refusing a `write` unless the descriptor and
the bytes offered satisfy `R`. -/
noncomputable def Syscall.writesOnly (sys : Syscall) (R : BitVec 64 → List (BitVec 8) → Prop) :
    Syscall :=
  fun s =>
    haveI := Classical.propDecidable (s.getReg .rax = 1 → R (s.getReg .rdi) s.offered)
    if s.getReg .rax = 1 → R (s.getReg .rdi) s.offered then sys s else .stuck

variable {R : BitVec 64 → List (BitVec 8) → Prop}

theorem Syscall.writesOnly_eq {s : State} (h : s.getReg .rax = 1 → R (s.getReg .rdi) s.offered) :
    sys.writesOnly R s = sys s := by
  simp only [Syscall.writesOnly]
  rw [ite_cond_eq_true _ _ (eq_true h)]

/-- What the stricter system lets through is what the plain one does, and
if it is a `write`, what was offered satisfies the condition. -/
theorem Syscall.safe_of_writesOnly {s : State} (h : (sys.writesOnly R s).isSafe = true) :
    sys.writesOnly R s = sys s ∧ (s.getReg .rax = 1 → R (s.getReg .rdi) s.offered) := by
  haveI := Classical.propDecidable (s.getReg .rax = 1 → R (s.getReg .rdi) s.offered)
  by_cases hR : s.getReg .rax = 1 → R (s.getReg .rdi) s.offered
  · exact ⟨Syscall.writesOnly_eq hR, hR⟩
  · simp only [Syscall.writesOnly] at h
    rw [ite_cond_eq_false _ _ (eq_false hR)] at h
    exact absurd h (by simp [Result.isSafe])

/-- A step the stricter system lets through is the plain system's step. -/
theorem step_of_writesOnly {s : State} (h : (step fetch (sys.writesOnly R) s).isSafe = true) :
    step fetch (sys.writesOnly R) s = step fetch sys s := by
  unfold step at h ⊢
  cases hf : fetch s.rip with
  | none => rfl
  | some x =>
    obtain ⟨i, len⟩ := x
    rw [hf] at h
    by_cases hi : i = .syscall
    · subst hi
      exact (Syscall.safe_of_writesOnly h).1
    · exact exec_congr hi _

/-- A run under the plain system, from a state safe under the stricter one,
is a run under the stricter one. -/
theorem Steps.writesOnly {s s' : State} (hs : Steps fetch sys s s') :
    Safe fetch (sys.writesOnly R) s → Steps fetch (sys.writesOnly R) s s' := by
  induction hs with
  | refl => exact fun _ => .refl _
  | step hstep _ ih =>
    intro h
    have e := step_of_writesOnly (h _ (.refl _))
    have hw := e.trans hstep
    exact .step hw (ih fun s'' hs'' => h s'' (.step hw hs''))

/-- **A program safe under the system that refuses unwanted writes is safe,
and writes only as wanted**: wherever it reaches a `write`, the descriptor
and the bytes it offers satisfy `R`. -/
theorem Safe.of_writesOnly {s : State} (h : Safe fetch (sys.writesOnly R) s) :
    Safe fetch sys s ∧
      ∀ s', Steps fetch sys s s' → ∀ len, fetch s'.rip = some (.syscall, len) →
        s'.getReg .rax = 1 → R (s'.getReg .rdi) s'.offered := by
  refine ⟨fun s' hs' => ?_, fun s' hs' len hf hax => ?_⟩
  · have hsafe := h s' (hs'.writesOnly h)
    rw [step_of_writesOnly hsafe] at hsafe
    exact hsafe
  · have hsafe := h s' (hs'.writesOnly h)
    unfold TypedAsm.step at hsafe
    rw [hf] at hsafe
    exact (Syscall.safe_of_writesOnly hsafe).2 hax

end TypedAsm
