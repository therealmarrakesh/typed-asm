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
unsafe, so results about safety need an assumption about `sys`.
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

end TypedAsm
