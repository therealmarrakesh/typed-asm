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
  /-- The type of each register. What the stack pointer points at is
  described by `stack` and `room`; its entry here says what is known of its
  value, which is usually nothing (`int`) and otherwise exactly what it is. -/
  regs : Reg → τ
  /-- The types of the stack slots, from `[rsp]` upward. -/
  stack : List τ
  /-- How many more slots may be pushed. -/
  room : Nat
  /-- What is known about the flags. -/
  flags : Flags → Prop

/-- The type of a 64-bit value. -/
inductive Ty
  /-- Any value. Every value has this type, so it also serves as "unknown". -/
  | int
  /-- Exactly this value. Combined with a code typing that allows a family of
  contexts at one address, this is how types depend on values: the family is
  indexed by the values, and the registers are typed as exactly those. -/
  | eq (v : BitVec 64)
  /-- The address of field `index` of a memory block whose fields have these
  types. A value of this type with `writable` set may be stored through.
  `index` may equal the number of fields (one past the end); such a pointer
  cannot be dereferenced. -/
  | ptr (fields : List Ty) (writable : Bool) (index : Nat)
  /-- The address of code that is safe to enter when the machine matches `pre`. -/
  | code (pre : CtxOf Ty)
  /-- The address of a function with this signature (see `FnSig`): it may be
  called by any caller that meets the signature, whatever that caller's own
  stack and whatever it keeps in the preserved registers. -/
  | fn (args results : Reg → Ty) (preserved : Reg → Bool) (need : Nat)
  /-- The address of field `index` of a memory block of the kind named
  `tag`. The type does not spell out the block's fields, so a field of a
  block may have this type with the block's own tag: that is how a record
  points to another of its kind. To use the pointer it is first opened into
  a `ptr`, with the fields that blocks of that kind have. -/
  | ref (tag : Nat) (writable : Bool) (index : Nat)
  /-- Zero, or a value of type `τ`. -/
  | nullable (τ : Ty)
  /-- What a system call hands back when success gives a value of type `τ`:
  an error number (a value from -4095 to -1), or a value of type `τ`. -/
  | orErr (τ : Ty)

/-- A description of the machine at one program point. -/
abbrev Ctx := CtxOf Ty

/-- The layout of one memory block. -/
structure Layout where
  fields : List Ty
  writable : Bool
  /-- The kind of block this is, for blocks that `Ty.ref` pointers refer to. -/
  tag : Option Nat
  /-- How many bytes of text follow the fields. Text is bytes a program may
  read but never writes, and its last byte is zero: a name, a message, an
  argument the program was given. A block that is only text has no fields. -/
  text : Nat

/-- The size of a block in bytes: its fields, then its text. -/
def Layout.size (l : Layout) : Nat :=
  8 * l.fields.length + l.text

/-- Memory typing: the layout of the block starting at each address, for the
addresses where a block starts, and the fields that blocks of each kind
have. Blocks are never removed or changed during a run, but new ones may
appear (see `MemTy.Ext`); the kinds are fixed. -/
structure MemTy where
  blocks : BitVec 64 → Option Layout
  /-- The fields of each kind of block that `Ty.ref` pointers may refer to.
  A kind is declared here whether or not a block of it exists yet. -/
  kinds : Nat → Option (List Ty)

/-- `Ψ a` is the layout of the block starting at `a`, if one does. -/
instance : CoeFun MemTy (fun _ => BitVec 64 → Option Layout) := ⟨MemTy.blocks⟩

/-- `Ψ.Ext Ψ'`: `Ψ'` is `Ψ` with perhaps more blocks. This is how the memory
typing changes while a program runs: a block, once there, stays as it is. -/
structure MemTy.Ext (Ψ Ψ' : MemTy) : Prop where
  blocks : ∀ a l, Ψ a = some l → Ψ' a = some l
  kinds : Ψ'.kinds = Ψ.kinds

theorem MemTy.Ext.refl (Ψ : MemTy) : Ψ.Ext Ψ :=
  ⟨fun _ _ h => h, rfl⟩

theorem MemTy.Ext.trans {Ψ Ψ' Ψ'' : MemTy} (h₁ : Ψ.Ext Ψ') (h₂ : Ψ'.Ext Ψ'') : Ψ.Ext Ψ'' :=
  ⟨fun a l h => h₂.blocks a l (h₁.blocks a l h), h₂.kinds.trans h₁.kinds⟩

/-- A system call's error result: one of the values from -4095 to -1. -/
def SysErr (v : BitVec 64) : Prop :=
  (-4095 : BitVec 64) ≤ v

instance (v : BitVec 64) : Decidable (SysErr v) := by
  unfold SysErr
  infer_instance

/-- Code typing: `Φ a Γ` says the instruction at address `a` may be entered
in context `Γ`. One address may allow many contexts, which is how a function
is typed once and called from several places. -/
abbrev CodeTy := BitVec 64 → Ctx → Prop

/-- Whether all four flags hold known values. -/
def Flags.defined (f : Flags) : Bool :=
  f.cf.isSome && f.zf.isSome && f.sf.isSome && f.of.isSome

/-- The flags predicate "all four hold known values". -/
def Flags.Known : Flags → Prop := fun f => f.defined = true

/-- The flags predicate that says nothing. -/
def Flags.Any : Flags → Prop := fun _ => True

/-- The type of a value after a known amount is added to it: an exactly
known value stays exactly known, and nothing is known of anything else. This
is what happens to the stack pointer's type when the stack pointer moves. -/
def Ty.shift (τ : Ty) (d : BitVec 64) : Ty :=
  match τ with
  | .eq v => .eq (v + d)
  | _ => .int

/-- Two moves of the stack pointer are one move by the sum. -/
theorem Ty.shift_shift (τ : Ty) (a b : BitVec 64) : (τ.shift a).shift b = τ.shift (a + b) := by
  cases τ <;> simp [Ty.shift, BitVec.add_assoc]

/-! ## Subtyping -/

/-- `Sub τ υ`: every value of type `τ` also has type `υ`. -/
inductive Sub : Ty → Ty → Prop
  | refl (τ : Ty) : Sub τ τ
  /-- Any value may be treated as an integer. -/
  | int (τ : Ty) : Sub τ .int
  /-- A writable pointer may be used as a read-only one. -/
  | readOnly (fields : List Ty) (writable : Bool) (index : Nat) :
    Sub (.ptr fields true index) (.ptr fields writable index)
  | refReadOnly (tag : Nat) (writable : Bool) (index : Nat) :
    Sub (.ref tag true index) (.ref tag writable index)
  /-- A value may be used where it or zero is expected. -/
  | nullable {τ υ : Ty} : Sub τ υ → Sub τ (.nullable υ)
  /-- So may zero. -/
  | null (τ : Ty) : Sub (.eq 0) (.nullable τ)
  | nullableMono {τ υ : Ty} : Sub τ υ → Sub (.nullable τ) (.nullable υ)
  /-- A value may be used where it or an error number is expected. -/
  | orErr {τ υ : Ty} : Sub τ υ → Sub τ (.orErr υ)
  | orErrMono {τ υ : Ty} : Sub τ υ → Sub (.orErr τ) (.orErr υ)

/-- Subtyping slot by slot, for two stacks of the same length. -/
inductive SubList : List Ty → List Ty → Prop
  | nil : SubList [] []
  | cons {τ υ : Ty} {σ ρ : List Ty} : Sub τ υ → SubList σ ρ → SubList (τ :: σ) (υ :: ρ)

/-- `CtxSub Γ Δ`: every state matching `Γ` also matches `Δ`. The stack shape
and room must agree exactly; only the types of registers and slots may be weakened. -/
structure CtxSub (Γ Δ : Ctx) : Prop where
  regs : ∀ r, r ≠ .rsp → Sub (Γ.regs r) (Δ.regs r)
  stack : SubList Γ.stack Δ.stack
  room : Γ.room = Δ.room
  flags : ∀ f, Γ.flags f → Δ.flags f
  /-- What is known of the stack pointer's value may also be weakened. -/
  sp : Sub (Γ.regs .rsp) (Δ.regs .rsp)

/-! ## Function signatures -/

/-- A function signature. -/
structure FnSig where
  /-- The types expected in the registers on entry. -/
  args : Reg → Ty
  /-- The types left in the registers on return. -/
  results : Reg → Ty
  /-- The registers whose types are the same on return as on entry, whatever
  they were. `args` and `results` are ignored for these. -/
  preserved : Reg → Bool
  /-- The number of stack slots the function uses below its return address. -/
  need : Nat

namespace FnSig

/-- Register types on entry, when the preserved registers have types `saved`. -/
def regsIn (sig : FnSig) (saved : Reg → Ty) : Reg → Ty :=
  fun r => if sig.preserved r then saved r else sig.args r

/-- Register types on return, when the preserved registers have types `saved`. -/
def regsOut (sig : FnSig) (saved : Reg → Ty) : Reg → Ty :=
  fun r => if sig.preserved r then saved r else sig.results r

/-- The context at the function's first instruction, for a caller that
expects `ret` on return and has `rest` on its stack. -/
def entry (sig : FnSig) (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat) : Ctx :=
  ⟨sig.regsIn saved, .code ret :: rest, room, Flags.Any⟩

/-- The context at the function's `ret` instruction. -/
def exit (sig : FnSig) (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat) : Ctx :=
  ⟨sig.regsOut saved, .code ret :: rest, room, Flags.Any⟩

/-- The context the caller is in once the function has returned. The stack
pointer is 8 above where it was at the function's `ret`, having popped the
return address; so a function that leaves the stack pointer's type as it
found it has, for its caller, put the stack pointer back. -/
def returned (sig : FnSig) (saved : Reg → Ty) (rest : List Ty) (room : Nat) : Ctx :=
  ⟨fun r => if r = .rsp then (sig.regsOut saved .rsp).shift 8 else sig.regsOut saved r, rest,
    room + 1, Flags.Any⟩

theorem returned_regs {sig : FnSig} {saved : Reg → Ty} {rest : List Ty} {room : Nat} {r : Reg}
    (hr : r ≠ .rsp) : (sig.returned saved rest room).regs r = sig.regsOut saved r := by
  simp only [returned, hr, ↓reduceIte]

theorem returned_sp (sig : FnSig) (saved : Reg → Ty) (rest : List Ty) (room : Nat) :
    (sig.returned saved rest room).regs .rsp = (sig.regsOut saved .rsp).shift 8 := by
  simp only [returned, ↓reduceIte]

/-- What a function needs of its caller: the state it returns must be
acceptable where it returns to, and there must be enough stack. -/
structure CallerOk (sig : FnSig) (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat) :
    Prop where
  ret : CtxSub (sig.returned saved rest room) ret
  room : sig.need ≤ room

/-- `sig.At Φ a`: the code typing lets address `a` be entered as a function
with signature `sig`, by any caller. -/
def At (sig : FnSig) (Φ : CodeTy) (a : BitVec 64) : Prop :=
  ∀ saved ret rest room, sig.CallerOk saved ret rest room → Φ a (sig.entry saved ret rest room)

/-- The type of a pointer to a function with this signature. -/
def ty (sig : FnSig) : Ty :=
  .fn sig.args sig.results sig.preserved sig.need

end FnSig

/-- Two byte ranges, given by start and length, do not overlap. Stated so that
it also covers ranges that wrap around the end of the address space. An
empty range overlaps nothing, wherever it starts. -/
def Disjoint (a : BitVec 64) (n : Nat) (b : BitVec 64) (m : Nat) : Prop :=
  (m ≠ 0 → BitVec.ofNat 64 n ≤ b - a) ∧ (n ≠ 0 → BitVec.ofNat 64 m ≤ a - b)

/-- For two ranges that are not empty, what not overlapping comes to. -/
theorem Disjoint.of_pos {a b : BitVec 64} {n m : Nat} (h : Disjoint a n b m) (hn : n ≠ 0)
    (hm : m ≠ 0) : BitVec.ofNat 64 n ≤ b - a ∧ BitVec.ofNat 64 m ≤ a - b :=
  ⟨h.1 hm, h.2 hn⟩

/-- A memory typing makes sense: blocks fit in the address space, none is
empty, no two overlap, and a block of a kind has that kind's fields. -/
structure MemTy.WF (Ψ : MemTy) : Prop where
  size_lt : ∀ a l, Ψ a = some l → l.size < 2 ^ 64
  disjoint : ∀ a b la lb, Ψ a = some la → Ψ b = some lb → a ≠ b → Disjoint a la.size b lb.size
  nonempty : ∀ a l, Ψ a = some l → 0 < l.size
  kinds : ∀ a l, Ψ a = some l → ∀ tag, l.tag = some tag → Ψ.kinds tag = some l.fields

/-! ## What the types mean

A code-pointer type means "safe to jump to", not "listed in a table". That
meaning refers to the meaning of every type inside the context the code
expects, including other code pointers, so it cannot be defined directly.
Instead every meaning carries a step count `n`: a code pointer at count `n`
is safe to jump to for any smaller number of steps. Statements about real
programs quantify over all `n`.

A code pointer must also stay good while the memory typing grows: code that
was safe to jump to before a block was allocated is safe to jump to after.
So "safe to jump to" is asked for every well-formed extension of the memory
typing, not only the present one. -/

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
  /-- The flags are as the context says. -/
  flags : Γ.flags s.flags
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
  /-- The stack pointer holds a value of its type. -/
  sp : H (Γ.regs .rsp) (s.getReg .rsp)
  /-- The text of each block that has some ends in a zero byte. -/
  text : ∀ a l, Ψ a = some l → l.text ≠ 0 → s.mem (a + BitVec.ofNat 64 (l.size - 1)) = 0

/-- `HasTy fetch sys Ψ n τ v`: the value `v` has type `τ`, at step count `n`.
This does not depend on the machine state. -/
def HasTy (fetch : Fetch) (sys : Syscall) : MemTy → Nat → Ty → BitVec 64 → Prop
  | _, _, .int, _ => True
  | _, _, .eq x, v => v = x
  | Ψ, _, .ptr fields writable index, v =>
    ∃ a l, Ψ a = some l ∧ l.fields = fields ∧ (writable = true → l.writable = true) ∧
      v = a + BitVec.ofNat 64 (8 * index)
  | Ψ, n, .code pre, v =>
    ∀ k, (hk : k < n) → ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → ∀ s : State, s.rip = v →
      Matches (fun τ w => HasTy fetch sys Ψ' k τ w) Ψ' pre s → SafeN fetch sys k s
  | Ψ, _, .ref tag writable index, v =>
    ∃ a l, Ψ a = some l ∧ l.tag = some tag ∧ (writable = true → l.writable = true) ∧
      v = a + BitVec.ofNat 64 (8 * index)
  | Ψ, n, .nullable τ, v => v = 0 ∨ HasTy fetch sys Ψ n τ v
  | Ψ, n, .orErr τ, v => SysErr v ∨ HasTy fetch sys Ψ n τ v
  | Ψ, n, .fn args results preserved need, v =>
    ∀ k, (hk : k < n) → ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF →
      ∀ (saved : Reg → Ty) (ret : Ctx) (rest : List Ty) (room : Nat),
      FnSig.CallerOk ⟨args, results, preserved, need⟩ saved ret rest room →
      ∀ s : State, s.rip = v →
      Matches (fun τ w => HasTy fetch sys Ψ' k τ w) Ψ'
        (FnSig.entry ⟨args, results, preserved, need⟩ saved ret rest room) s →
      SafeN fetch sys k s
termination_by _ n τ => (n, τ)

/-- `WellTyped fetch sys Ψ n Γ s`: the state `s` matches the context `Γ`, at step count `n`. -/
abbrev WellTyped (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (n : Nat) (Γ : Ctx) (s : State) :
    Prop :=
  Matches (HasTy fetch sys Ψ n) Ψ Γ s

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy} {n : Nat}

theorem HasTy.int (v : BitVec 64) : HasTy fetch sys Ψ n .int v := by
  simp [HasTy]

theorem hasTy_eq {x v : BitVec 64} : HasTy fetch sys Ψ n (.eq x) v ↔ v = x := by
  simp [HasTy]

theorem hasTy_ptr {fields : List Ty} {writable : Bool} {index : Nat} {v : BitVec 64} :
    HasTy fetch sys Ψ n (.ptr fields writable index) v ↔
      ∃ a l, Ψ a = some l ∧ l.fields = fields ∧ (writable = true → l.writable = true) ∧
        v = a + BitVec.ofNat 64 (8 * index) := by
  simp [HasTy]

/-- A value is a code pointer if jumping to it, in any state matching the
context it expects, is safe for any smaller number of steps, now and however
the memory typing grows. -/
theorem hasTy_code {pre : Ctx} {v : BitVec 64} :
    HasTy fetch sys Ψ n (.code pre) v ↔
      ∀ k, k < n → ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → ∀ s : State, s.rip = v →
        WellTyped fetch sys Ψ' k pre s → SafeN fetch sys k s := by
  rw [HasTy]

theorem hasTy_ref {tag : Nat} {writable : Bool} {index : Nat} {v : BitVec 64} :
    HasTy fetch sys Ψ n (.ref tag writable index) v ↔
      ∃ a l, Ψ a = some l ∧ l.tag = some tag ∧ (writable = true → l.writable = true) ∧
        v = a + BitVec.ofNat 64 (8 * index) := by
  simp [HasTy]

theorem hasTy_nullable {τ : Ty} {v : BitVec 64} :
    HasTy fetch sys Ψ n (.nullable τ) v ↔ v = 0 ∨ HasTy fetch sys Ψ n τ v := by
  rw [HasTy]

theorem hasTy_orErr {τ : Ty} {v : BitVec 64} :
    HasTy fetch sys Ψ n (.orErr τ) v ↔ SysErr v ∨ HasTy fetch sys Ψ n τ v := by
  rw [HasTy]

/-- A value is a pointer to a function if entering it, from any caller that
meets the signature, is safe for any smaller number of steps. -/
theorem hasTy_fn {sig : FnSig} {v : BitVec 64} :
    HasTy fetch sys Ψ n sig.ty v ↔
      ∀ k, k < n → ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF →
        ∀ saved ret rest room, sig.CallerOk saved ret rest room →
        ∀ s : State, s.rip = v → WellTyped fetch sys Ψ' k (sig.entry saved ret rest room) s →
        SafeN fetch sys k s := by
  rw [FnSig.ty, HasTy]

/-- A type's meaning at a step count implies its meaning at every smaller one. -/
theorem HasTy.mono {m : Nat} {τ : Ty} {v : BitVec 64} (h : HasTy fetch sys Ψ n τ v)
    (hle : m ≤ n) : HasTy fetch sys Ψ m τ v := by
  cases τ with
  | ref tag writable index => exact hasTy_ref.mpr (hasTy_ref.mp h)
  | nullable τ =>
    rw [hasTy_nullable] at h ⊢
    exact h.imp id (fun h' => HasTy.mono h' hle)
  | orErr τ =>
    rw [hasTy_orErr] at h ⊢
    exact h.imp id (fun h' => HasTy.mono h' hle)
  | int => exact HasTy.int v
  | eq x => exact hasTy_eq.mpr (hasTy_eq.mp h)
  | ptr fields writable index => exact hasTy_ptr.mpr (hasTy_ptr.mp h)
  | code pre =>
    rw [hasTy_code] at h ⊢
    exact fun k hk => h k (by omega)
  | fn args results preserved need =>
    have e : Ty.fn args results preserved need = FnSig.ty ⟨args, results, preserved, need⟩ := rfl
    rw [e, hasTy_fn] at h ⊢
    exact fun k hk => h k (by omega)
termination_by sizeOf τ

/-- A value keeps its type when the memory typing grows. -/
theorem HasTy.ext {Ψ' : MemTy} {τ : Ty} {v : BitVec 64} (h : HasTy fetch sys Ψ n τ v)
    (he : Ψ.Ext Ψ') : HasTy fetch sys Ψ' n τ v := by
  cases τ with
  | ref tag writable index =>
    obtain ⟨a, l, hl, h'⟩ := hasTy_ref.mp h
    exact hasTy_ref.mpr ⟨a, l, he.blocks a l hl, h'⟩
  | nullable τ =>
    rw [hasTy_nullable] at h ⊢
    exact h.imp id (fun h' => HasTy.ext h' he)
  | orErr τ =>
    rw [hasTy_orErr] at h ⊢
    exact h.imp id (fun h' => HasTy.ext h' he)
  | int => exact HasTy.int v
  | eq x => exact hasTy_eq.mpr (hasTy_eq.mp h)
  | ptr fields writable index =>
    obtain ⟨a, l, hl, h'⟩ := hasTy_ptr.mp h
    exact hasTy_ptr.mpr ⟨a, l, he.blocks a l hl, h'⟩
  | code pre =>
    rw [hasTy_code] at h ⊢
    exact fun k hk Ψ'' he' => h k hk Ψ'' (he.trans he')
  | fn args results preserved need =>
    have e : Ty.fn args results preserved need = FnSig.ty ⟨args, results, preserved, need⟩ := rfl
    rw [e, hasTy_fn] at h ⊢
    exact fun k hk Ψ'' he' => h k hk Ψ'' (he.trans he')
termination_by sizeOf τ

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
    stackHeap := h.stackHeap
    sp := himp _ _ h.sp
    text := h.text }

/-- A state well typed at a step count is well typed at every smaller one. -/
theorem WellTyped.mono {m : Nat} {Γ : Ctx} {s : State} (h : WellTyped fetch sys Ψ n Γ s)
    (hle : m ≤ n) : WellTyped fetch sys Ψ m Γ s :=
  Matches.imp h (fun _ _ hv => hv.mono hle)

end TypedAsm
