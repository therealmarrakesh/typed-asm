import TypedAsm.Memory

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
  /-- The address of code that may be entered when the machine matches `pre`. -/
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

/-! ## What the types mean -/

/-- `HasTy Φ Ψ τ v`: the value `v` has type `τ`. This does not depend on the
machine state, only on the fixed code and memory typings. -/
def HasTy (Φ : CodeTy) (Ψ : MemTy) : Ty → BitVec 64 → Prop
  | .int, _ => True
  | .ptr fields writable, v =>
    ∃ l, Ψ v = some l ∧ l.fields = fields ∧ (writable = true → l.writable = true)
  | .code pre, v => Φ v = some pre

theorem HasTy.int {Φ : CodeTy} {Ψ : MemTy} (v : BitVec 64) : HasTy Φ Ψ .int v :=
  trivial

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

/-- `WellTyped Φ Ψ Γ s`: the state `s` matches the context `Γ`. -/
structure WellTyped (Φ : CodeTy) (Ψ : MemTy) (Γ : Ctx) (s : State) : Prop where
  /-- Each register other than `rsp` holds a value of its type. -/
  regs : ∀ r, r ≠ .rsp → HasTy Φ Ψ (Γ.regs r) (s.getReg r)
  /-- If the context says the flags are known, they are. -/
  flags : Γ.flags = true → s.flags.defined = true
  /-- The stack region, free slots included, is writable. -/
  stackPerm : s.canWrite (stackBase Γ s) (stackSize Γ) = true
  stackSize_lt : stackSize Γ < 2 ^ 64
  /-- Each described stack slot holds a value of its type. -/
  stack : ∀ i τ, Γ.stack[i]? = some τ →
    HasTy Φ Ψ τ (s.load64 (s.getReg .rsp + BitVec.ofNat 64 (8 * i)))
  /-- Each memory block is readable, and writable if its layout says so. -/
  heapPerm : ∀ a l, Ψ a = some l →
    s.canRead a l.size = true ∧ (l.writable = true → s.canWrite a l.size = true)
  /-- Each field of each memory block holds a value of its type. -/
  heap : ∀ a l, Ψ a = some l → ∀ i τ, l.fields[i]? = some τ →
    HasTy Φ Ψ τ (s.load64 (a + BitVec.ofNat 64 (8 * i)))
  /-- No memory block overlaps the stack region. -/
  stackHeap : ∀ a l, Ψ a = some l → Disjoint (stackBase Γ s) (stackSize Γ) a l.size

end TypedAsm
