/-!
# Results of execution

A computation in the machine either continues with a value or stops for one of
three reasons. `Result` is a monad, so a sequence of operations stops at the
first one that does not continue.
-/

namespace TypedAsm

/-- Exceptions the hardware raises. -/
inductive Fault
  /-- Division by zero, or a quotient that does not fit. -/
  | divideError
  /-- An undefined instruction, including `ud2`. -/
  | invalidOpcode
  /-- An access to an address the processor has, but where the memory is not
  there or does not allow it: a read of memory that is not readable, a write
  to memory that is not writable, or execution of memory that is not
  executable. -/
  | pageFault
  /-- An access to an address the processor does not have: one that is not
  canonical. No memory can be there, so the pointer itself is wrong. -/
  | generalProtection
  /-- The same, for an access made through the stack: a `push`, `pop`, `call`
  or `ret`, or a memory operand whose base is `rsp` or `rbp`. -/
  | stackFault
  deriving DecidableEq, Repr

inductive Result (α : Type)
  /-- Execution continued normally. -/
  | next (a : α)
  /-- The hardware would raise an exception. -/
  | fault (f : Fault)
  /-- The program asked the operating system to end it, with this status. -/
  | exit (code : BitVec 32)
  /-- The model does not say what happens. -/
  | stuck

namespace Result

def bind {α β : Type} (x : Result α) (f : α → Result β) : Result β :=
  match x with
  | .next a => f a
  | .fault e => .fault e
  | .exit code => .exit code
  | .stuck => .stuck

instance : Monad Result where
  pure := .next
  bind := bind

/-- `none` becomes `stuck`. -/
def ofOption {α : Type} : Option α → Result α
  | some a => .next a
  | none => .stuck

@[simp] theorem pure_eq {α : Type} (a : α) : (pure a : Result α) = .next a := rfl

@[simp] theorem next_bind {α β : Type} (a : α) (f : α → Result β) :
    (Result.next a >>= f) = f a := rfl

@[simp] theorem fault_bind {α β : Type} (e : Fault) (f : α → Result β) :
    (Result.fault e >>= f) = .fault e := rfl

@[simp] theorem exit_bind {α β : Type} (code : BitVec 32) (f : α → Result β) :
    (Result.exit code >>= f) = .exit code := rfl

@[simp] theorem stuck_bind {α β : Type} (f : α → Result β) :
    (Result.stuck >>= f) = .stuck := rfl

/-- The result of an access made through the stack: an address the processor
does not have is a stack fault there, not a general-protection fault. -/
def onStack {α : Type} : Result α → Result α
  | .fault .generalProtection => .fault .stackFault
  | r => r

@[simp] theorem onStack_next {α : Type} (a : α) : (Result.next a).onStack = .next a := rfl

@[simp] theorem onStack_eq_next {α : Type} {r : Result α} {a : α} :
    r.onStack = .next a ↔ r = .next a := by
  cases r with
  | fault f => cases f <;> simp [onStack]
  | _ => simp [onStack]

/-- `x.All P`: if the computation continues with a value, the value satisfies `P`. -/
def All {α : Type} (P : α → Prop) : Result α → Prop
  | .next a => P a
  | _ => True

@[simp] theorem all_next {α : Type} (P : α → Prop) (a : α) : (Result.next a).All P ↔ P a := Iff.rfl

@[simp] theorem all_pure {α : Type} (P : α → Prop) (a : α) : (pure a : Result α).All P ↔ P a :=
  Iff.rfl

@[simp] theorem all_fault {α : Type} (P : α → Prop) (e : Fault) : (Result.fault e : Result α).All P :=
  trivial

@[simp] theorem all_stuck {α : Type} (P : α → Prop) : (Result.stuck : Result α).All P := trivial

@[simp] theorem all_exit {α : Type} (P : α → Prop) (c : BitVec 32) :
    (Result.exit c : Result α).All P := trivial

/-- A property of the final value is a property of each step's value in turn. -/
@[simp] theorem all_bind {α β : Type} (x : Result α) (f : α → Result β) (P : β → Prop) :
    (x >>= f).All P ↔ x.All (fun a => (f a).All P) := by
  cases x <;> rfl

@[simp] theorem all_onStack {α : Type} (P : α → Prop) (x : Result α) :
    x.onStack.All P ↔ x.All P := by
  cases x with
  | fault f => cases f <;> simp [onStack, All]
  | _ => simp [onStack]

theorem All.of_forall {α : Type} {P : α → Prop} {x : Result α} (h : ∀ a, P a) : x.All P := by
  cases x <;> first | exact h _ | trivial

theorem All.mono {α : Type} {P Q : α → Prop} {x : Result α} (h : x.All Q) (hqp : ∀ a, Q a → P a) :
    x.All P := by
  cases x <;> first | exact hqp _ h | trivial

theorem all_iff {α : Type} {P : α → Prop} {x : Result α} : x.All P ↔ ∀ a, x = .next a → P a := by
  cases x <;> simp [All]

end Result

end TypedAsm
