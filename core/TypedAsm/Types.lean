import TypedAsm.Safety

/-!
# Types

What the type system can say about a 64-bit value, about the machine as a
whole, and what those statements mean.

Every stack slot and every field of a memory block is 8 bytes.
-/

namespace TypedAsm

/-- A description of the machine at one program point, over some notion `τ` of type.
`Ctx` below is this with `τ` filled in. -/
structure CtxOf (τ : Type) where
  /-- The type of each register. The entry for `rsp` is ignored: the stack
  pointer is described by `stack` and `room`. -/
  regs : Reg → τ
  /-- The types of the stack slots, from `[rsp]` upward. -/
  stack : List τ
  /-- How many more slots may be pushed. -/
  room : Nat
  /-- Whether all four flags hold known values. -/
  flags : Bool

/-- The type of a 64-bit value. -/
inductive Ty
  /-- Any value. Every value has this type, so it also serves as "unknown". -/
  | int
  /-- The address of a memory block whose fields have these types. A value of
  this type with `writable` set may be stored through. -/
  | ptr (fields : List Ty) (writable : Bool)
  /-- The address of code that is safe to enter when the machine matches `pre`. -/
  | code (pre : CtxOf Ty)

/-- A description of the machine at one program point. -/
abbrev Ctx := CtxOf Ty

/-- The layout of one memory block. -/
structure Layout where
  fields : List Ty
  writable : Bool

/-- The size of a block in bytes. -/
def Layout.size (l : Layout) : Nat :=
  8 * l.fields.length

/-- Memory typing: the layout of the block starting at each address, for the
addresses where a block starts. It is fixed for the whole run. -/
abbrev MemTy := BitVec 64 → Option Layout

/-- Code typing: the context required on entry to each instruction address. -/
abbrev CodeTy := BitVec 64 → Option Ctx

/-- Two byte ranges, given by start and length, do not overlap. Stated so that
it also covers ranges that wrap around the end of the address space. -/
def Disjoint (a : BitVec 64) (n : Nat) (b : BitVec 64) (m : Nat) : Prop :=
  BitVec.ofNat 64 n ≤ b - a ∧ BitVec.ofNat 64 m ≤ a - b

/-- A memory typing makes sense: blocks fit in the address space and no two overlap. -/
structure MemTy.WF (Ψ : MemTy) : Prop where
  size_lt : ∀ a l, Ψ a = some l → l.size < 2 ^ 64
  disjoint : ∀ a b la lb, Ψ a = some la → Ψ b = some lb → a ≠ b → Disjoint a la.size b lb.size

/-! ## What the types mean

A code-pointer type means "safe to jump to", not "listed in a table". That
meaning refers to the meaning of every type inside the context the code
expects, including other code pointers, so it cannot be defined directly.
Instead every meaning carries a step count `n`: a code pointer at count `n`
is safe to jump to for any smaller number of steps. Statements about real
programs quantify over all `n`. -/

/-- Whether all four flags hold known values. -/
def Flags.defined (f : Flags) : Bool :=
  f.cf.isSome && f.zf.isSome && f.sf.isSome && f.of.isSome

/-- The address of the lowest byte of the stack region a context describes:
`room` free slots below `rsp`. -/
def stackBase (Γ : Ctx) (s : State) : BitVec 64 :=
  s.getReg .rsp - BitVec.ofNat 64 (8 * Γ.room)

/-- The size in bytes of the stack region a context describes. -/
def stackSize (Γ : Ctx) : Nat :=
  8 * (Γ.room + Γ.stack.length)

/-- `Matches H Ψ Γ s`: the state `s` matches the context `Γ`, where `H τ v`
says what it means for the value `v` to have type `τ`. -/
structure Matches (H : Ty → BitVec 64 → Prop) (Ψ : MemTy) (Γ : Ctx) (s : State) : Prop where
  /-- Each register other than `rsp` holds a value of its type. -/
  regs : ∀ r, r ≠ .rsp → H (Γ.regs r) (s.getReg r)
  /-- If the context says the flags are known, they are. -/
  flags : Γ.flags = true → s.flags.defined = true
  /-- The stack region, free slots included, is writable. -/
  stackPerm : s.canWrite (stackBase Γ s) (stackSize Γ) = true
  stackSize_lt : stackSize Γ < 2 ^ 64
  /-- Each described stack slot holds a value of its type. -/
  stack : ∀ i τ, Γ.stack[i]? = some τ →
    H τ (s.load64 (s.getReg .rsp + BitVec.ofNat 64 (8 * i)))
  /-- Each memory block is readable, and writable if its layout says so. -/
  heapPerm : ∀ a l, Ψ a = some l →
    s.canRead a l.size = true ∧ (l.writable = true → s.canWrite a l.size = true)
  /-- Each field of each memory block holds a value of its type. -/
  heap : ∀ a l, Ψ a = some l → ∀ i τ, l.fields[i]? = some τ →
    H τ (s.load64 (a + BitVec.ofNat 64 (8 * i)))
  /-- No memory block overlaps the stack region. -/
  stackHeap : ∀ a l, Ψ a = some l → Disjoint (stackBase Γ s) (stackSize Γ) a l.size

/-- `HasTy fetch sys Ψ n τ v`: the value `v` has type `τ`, at step count `n`.
This does not depend on the machine state. -/
def HasTy (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) : Nat → Ty → BitVec 64 → Prop
  | _, .int, _ => True
  | _, .ptr fields writable, v =>
    ∃ l, Ψ v = some l ∧ l.fields = fields ∧ (writable = true → l.writable = true)
  | n, .code pre, v =>
    ∀ k, (hk : k < n) → ∀ s : State, s.rip = v →
      Matches (fun τ w => HasTy fetch sys Ψ k τ w) Ψ pre s → SafeN fetch sys k s
termination_by n => n

/-- `WellTyped fetch sys Ψ n Γ s`: the state `s` matches the context `Γ`, at step count `n`. -/
abbrev WellTyped (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (n : Nat) (Γ : Ctx) (s : State) :
    Prop :=
  Matches (HasTy fetch sys Ψ n) Ψ Γ s

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy} {n : Nat}

theorem HasTy.int (v : BitVec 64) : HasTy fetch sys Ψ n .int v := by
  simp [HasTy]

theorem hasTy_ptr {fields : List Ty} {writable : Bool} {v : BitVec 64} :
    HasTy fetch sys Ψ n (.ptr fields writable) v ↔
      ∃ l, Ψ v = some l ∧ l.fields = fields ∧ (writable = true → l.writable = true) := by
  simp [HasTy]

/-- A value is a code pointer if jumping to it, in any state matching the
context it expects, is safe for any smaller number of steps. -/
theorem hasTy_code {pre : Ctx} {v : BitVec 64} :
    HasTy fetch sys Ψ n (.code pre) v ↔
      ∀ k, k < n → ∀ s : State, s.rip = v → WellTyped fetch sys Ψ k pre s → SafeN fetch sys k s := by
  rw [HasTy]

/-- A type's meaning at a step count implies its meaning at every smaller one. -/
theorem HasTy.mono {m : Nat} {τ : Ty} {v : BitVec 64} (h : HasTy fetch sys Ψ n τ v)
    (hle : m ≤ n) : HasTy fetch sys Ψ m τ v := by
  cases τ with
  | int => exact HasTy.int v
  | ptr fields writable => exact hasTy_ptr.mpr (hasTy_ptr.mp h)
  | code pre =>
    rw [hasTy_code] at h ⊢
    exact fun k hk => h k (by omega)

/-- Matching a context carries over to any weaker notion of "has type". -/
theorem Matches.imp {H H' : Ty → BitVec 64 → Prop} {Γ : Ctx} {s : State}
    (h : Matches H Ψ Γ s) (himp : ∀ τ v, H τ v → H' τ v) : Matches H' Ψ Γ s :=
  { regs := fun r hr => himp _ _ (h.regs r hr)
    flags := h.flags
    stackPerm := h.stackPerm
    stackSize_lt := h.stackSize_lt
    stack := fun i τ hi => himp _ _ (h.stack i τ hi)
    heapPerm := h.heapPerm
    heap := fun a l hl i τ hi => himp _ _ (h.heap a l hl i τ hi)
    stackHeap := h.stackHeap }

/-- A state well typed at a step count is well typed at every smaller one. -/
theorem WellTyped.mono {m : Nat} {Γ : Ctx} {s : State} (h : WellTyped fetch sys Ψ n Γ s)
    (hle : m ≤ n) : WellTyped fetch sys Ψ m Γ s :=
  Matches.imp h (fun _ _ hv => hv.mono hle)

end TypedAsm
