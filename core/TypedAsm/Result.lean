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
  /-- A read from memory that is not readable, or a write to memory that is
  not writable. This also stands in for the general-protection fault the
  hardware raises on a non-canonical address. -/
  | pageFault
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

end Result

end TypedAsm
