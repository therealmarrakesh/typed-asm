import TypedAsm.Shape

/-!
# Types

What the type system can say about a 64-bit value, about the machine as a
whole, and what those statements mean.

The stack and every block of memory are described byte for byte.
-/

namespace TypedAsm

/-- The number of bytes a run of pieces of the stack comes to. -/
def stackLen {τ : Type} : List (ShapeOf τ) → Nat
  | [] => 0
  | S :: σ => S.size + stackLen σ

/-- How many bytes above the stack pointer piece `k` of the stack starts. -/
def stackOff {τ : Type} (σ : List (ShapeOf τ)) (k : Nat) : Nat :=
  match k, σ with
  | 0, _ => 0
  | _ + 1, [] => 0
  | k + 1, S :: σ => S.size + stackOff σ k
termination_by structural k

@[simp] theorem stackOff_zero {τ : Type} (σ : List (ShapeOf τ)) : stackOff σ 0 = 0 := rfl

@[simp] theorem stackOff_nil {τ : Type} (k : Nat) : stackOff ([] : List (ShapeOf τ)) k = 0 := by
  cases k <;> rfl

@[simp] theorem stackOff_cons_succ {τ : Type} (S : ShapeOf τ) (σ : List (ShapeOf τ)) (k : Nat) :
    stackOff (S :: σ) (k + 1) = S.size + stackOff σ k := rfl

@[simp] theorem stackLen_nil {τ : Type} : stackLen ([] : List (ShapeOf τ)) = 0 := rfl

@[simp] theorem stackLen_cons {τ : Type} (S : ShapeOf τ) (σ : List (ShapeOf τ)) :
    stackLen (S :: σ) = S.size + stackLen σ := rfl

/-- What is left of the stack once the pieces at its top that come to exactly
`k` bytes are gone, if pieces do end there. -/
def stackDrop {τ : Type} : List (ShapeOf τ) → Nat → Option (List (ShapeOf τ))
  | σ, 0 => some σ
  | [], _ + 1 => none
  | S :: σ, k + 1 => if S.size ≤ k + 1 then stackDrop σ (k + 1 - S.size) else none

theorem stackDrop_eq {τ : Type} {σ rest : List (ShapeOf τ)} {k : Nat}
    (h : stackDrop σ k = some rest) : ∃ top, σ = top ++ rest ∧ stackLen top = k := by
  induction σ generalizing k with
  | nil =>
    cases k with
    | zero => exact ⟨[], by simpa [stackDrop] using h, rfl⟩
    | succ k => simp [stackDrop] at h
  | cons S σ ih =>
    cases k with
    | zero =>
      simp only [stackDrop, Option.some.injEq] at h
      exact ⟨[], by simpa using h, rfl⟩
    | succ k =>
      simp only [stackDrop] at h
      split at h
      · next hle =>
        obtain ⟨top, rfl, hlen⟩ := ih h
        exact ⟨S :: top, rfl, by simp only [stackLen_cons, hlen]; omega⟩
      · cases h

/-- A piece of the stack ends where the stack does or before. -/
theorem stackOff_add_le {τ : Type} {σ : List (ShapeOf τ)} {k : Nat} {S : ShapeOf τ}
    (h : σ[k]? = some S) : stackOff σ k + S.size ≤ stackLen σ := by
  induction σ generalizing k with
  | nil => simp at h
  | cons T σ ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [stackOff_zero, stackLen_cons]
      omega
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      have := ih h
      simp only [stackOff_cons_succ, stackLen_cons]
      omega

/-- An earlier piece of the stack ends where a later one starts or before. -/
theorem stackOff_le {τ : Type} {σ : List (ShapeOf τ)} {j k : Nat} {T : ShapeOf τ}
    (hjk : j < k) (h : σ[j]? = some T) : stackOff σ j + T.size ≤ stackOff σ k := by
  induction σ generalizing j k with
  | nil => simp at h
  | cons U σ ih =>
    cases k with
    | zero => omega
    | succ k =>
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        subst h
        simp only [stackOff_zero, stackOff_cons_succ]
        omega
      | succ j =>
        simp only [List.getElem?_cons_succ] at h
        have := ih (by omega : j < k) h
        simp only [stackOff_cons_succ]
        omega

theorem stackLen_append {τ : Type} (top rest : List (ShapeOf τ)) :
    stackLen (top ++ rest) = stackLen top + stackLen rest := by
  induction top with
  | nil => simp [stackLen]
  | cons S top ih => simp only [List.cons_append, stackLen, ih]; omega

theorem stackOff_append {τ : Type} (top rest : List (ShapeOf τ)) (j : Nat) :
    stackOff (top ++ rest) (top.length + j) = stackLen top + stackOff rest j := by
  induction top with
  | nil => simp [stackLen]
  | cons S top ih =>
    rw [List.cons_append, List.length_cons, show top.length + 1 + j = (top.length + j) + 1 by omega]
    simp only [stackOff, stackLen, ih]
    omega

theorem stackOff_append_le {τ : Type} (A B : List (ShapeOf τ)) {k : Nat} (h : k ≤ A.length) :
    stackOff (A ++ B) k = stackOff A k := by
  induction A generalizing k with
  | nil =>
    have : k = 0 := by simpa using h
    subst this
    simp
  | cons S A ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.cons_append, stackOff_cons_succ]
      rw [ih (by simpa using h)]

/-- Replacing a piece by one of the same size moves no piece. -/
theorem stackOff_set {τ : Type} {σ : List (ShapeOf τ)} {k : Nat} {S S' : ShapeOf τ}
    (hk : σ[k]? = some S) (hs : S'.size = S.size) (j : Nat) :
    stackOff (σ.set k S') j = stackOff σ j := by
  induction σ generalizing k j with
  | nil => simp
  | cons T σ ih =>
    cases j with
    | zero => cases k <;> simp [stackOff]
    | succ j =>
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        simp only [List.set_cons_zero, stackOff, hs]
      | succ k =>
        simp only [List.getElem?_cons_succ] at hk
        simp only [List.set_cons_succ, stackOff, ih hk]

theorem stackLen_set {τ : Type} {σ : List (ShapeOf τ)} {k : Nat} {S S' : ShapeOf τ}
    (hk : σ[k]? = some S) (hs : S'.size = S.size) : stackLen (σ.set k S') = stackLen σ := by
  induction σ generalizing k with
  | nil => simp
  | cons T σ ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      simp only [List.set_cons_zero, stackLen, hs]
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk
      simp only [List.set_cons_succ, stackLen, ih hk]

/-- A description of the machine at one program point, over some notion `τ` of type.
`Ctx` below is this with `τ` filled in. -/
structure CtxOf (τ : Type) where
  /-- The type of each register. What the stack pointer points at is
  described by `stack` and `room`; its entry here says what is known of its
  value, which is usually nothing (`int`) and otherwise exactly what it is. -/
  regs : Reg → τ
  /-- The stack from `[rsp]` upward, as pieces laid end to end: each is so
  many bytes, with typed values at some of them. A `push` adds a piece of
  eight bytes; making room for locals adds a piece of as many as are asked
  for. -/
  stack : List (ShapeOf τ)
  /-- How many more bytes the stack may grow by. -/
  room : Nat
  /-- What is known about the flags. -/
  flags : Flags → Prop
  /-- The blocks of memory this code owns outright: where each is, how many
  bytes long, and which of its bytes hold typed values. Nothing else points
  into an owned block that the types know of, so what it holds may change
  type as it is stored to, and the block may be given back. A pointer to one is just its address, exactly
  known; what makes it usable is the entry here. -/
  owned : List (BitVec 64 × ShapeOf τ) := []
  /-- How many bytes above the pieces of `stack` have been detached from it:
  pieces that were the stack's topmost and are for now blocks this code or
  its callers own, so that a function can be handed one. They can be
  attached again, and the count says there is room for them. -/
  above : Nat := 0

/-- The type of a 64-bit value. -/
inductive Ty
  /-- Any value. Every value has this type, so it also serves as "unknown". -/
  | int
  /-- Exactly this value. Combined with a code typing that allows a family of
  contexts at one address, this is how types depend on values: the family is
  indexed by the values, and the registers are typed as exactly those. -/
  | eq (v : BitVec 64)
  /-- The address of byte `off` of a memory block of this shape. A value of
  this type with `writable` set may be stored through. `off` may be the
  block's size or more; such a pointer cannot be dereferenced. -/
  | ptr (shape : ShapeOf Ty) (writable : Bool) (off : Nat)
  /-- The address of code that is safe to enter when the machine matches `pre`. -/
  | code (pre : CtxOf Ty)
  /-- The address of code that is safe to enter when the machine matches
  `pre x`, whichever `x` that is. A function that hands back something it
  made, at an address not known until it runs, returns through one of
  these: the place it returns to is ready for any address. The family is
  indexed by sequences of 64-bit values, which is enough to stand for
  whatever a function may choose as it returns (see `Chosen`). -/
  | codeAll (pre : (Nat → BitVec 64) → CtxOf Ty)
  /-- The address of a function whose results, and the blocks it gives,
  depend on values it chooses as it returns (see `FnSigEx`). -/
  | fnAll (args : Reg → Ty) (preserved : Reg → Bool) (need : Nat)
      (takes : List (BitVec 64 × ShapeOf Ty)) (results : (Nat → BitVec 64) → Reg → Ty)
      (gives : (Nat → BitVec 64) → List (BitVec 64 × ShapeOf Ty))
  /-- The address of a function with this signature (see `FnSig`): it may be
  called by any caller that meets the signature, whatever that caller's own
  stack and whatever it keeps in the preserved registers. -/
  | fn (args results : Reg → Ty) (preserved : Reg → Bool) (need : Nat)
      (takes gives : List (BitVec 64 × ShapeOf Ty))
  /-- The address of byte `off` of a memory block of the kind named `tag`.
  The type does not spell out the block's shape, so a value in a block may
  have this type with the block's own tag: that is how a record points to
  another of its kind. To use the pointer it is first opened into a `ptr`,
  with the shape that blocks of that kind have. -/
  | ref (tag : Nat) (writable : Bool) (off : Nat)
  /-- Zero, or a value of type `τ`. -/
  | nullable (τ : Ty)
  /-- What a system call hands back when success gives a value of type `τ`:
  an error number (a value from -4095 to -1), or a value of type `τ`. -/
  | orErr (τ : Ty)
  /-- The address of a byte of some block's text. With `more` set it is not
  the text's last byte, so the address after it is a byte of that text too.
  A text's last byte is zero, so a byte that is not zero is not the last:
  that is how a program walks along a text without knowing its length. -/
  | str (more : Bool)

/-- A description of the machine at one program point. -/
abbrev Ctx := CtxOf Ty

/-- What a block of memory holds, byte for byte. -/
abbrev Shape := ShapeOf Ty

/-- Whether a type is the type of plain numbers. -/
def Ty.isInt : Ty → Bool
  | .int => true
  | _ => false

theorem Ty.eq_int_of_isInt {τ : Ty} (h : τ.isInt = true) : τ = .int := by
  cases τ <;> first | rfl | exact absurd h (by simp [Ty.isInt])

/-- The layout of one memory block. -/
structure Layout where
  /-- What the block holds, byte for byte, before any text. -/
  shape : Shape
  writable : Bool
  /-- The kind of block this is, for blocks that `Ty.ref` pointers refer to. -/
  tag : Option Nat
  /-- How many bytes of text follow those. Text is bytes a program may read
  but never writes, and its last byte is zero: a name, a message, an argument
  the program was given. A block that is only text has a shape of no bytes. -/
  text : Nat
  /-- The bytes the whole block holds, where that is said: a message, a
  table of constants. A block that says its bytes is never written, so it
  holds them for as long as the program runs, and what a program writes out
  from it is known. -/
  said : Option (List (BitVec 8)) := none

/-- The size of a block in bytes: what its shape describes, then its text. -/
def Layout.size (l : Layout) : Nat :=
  l.shape.size + l.text

/-- Memory typing: the layout of the block starting at each address, for the
addresses where a block starts, and the shape that blocks of each kind
have. Blocks are never removed or changed during a run, but new ones may
appear (see `MemTy.Ext`); the kinds are fixed. -/
structure MemTy where
  blocks : BitVec 64 → Option Layout
  /-- The shape of each kind of block that `Ty.ref` pointers may refer to.
  A kind is declared here whether or not a block of it exists yet. -/
  kinds : Nat → Option Shape

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
  | readOnly (shape : Shape) (writable : Bool) (off : Nat) :
    Sub (.ptr shape true off) (.ptr shape writable off)
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
  /-- An address known not to be a text's last may be used as any address in it. -/
  | strLess (more : Bool) : Sub (.str true) (.str more)
  /-- Code ready for every one of a family of contexts is ready for each. -/
  | codeAll (pre : (Nat → BitVec 64) → CtxOf Ty) (x : Nat → BitVec 64) :
    Sub (.codeAll pre) (.code (pre x))
  /-- And for any part of the family, however the part is picked out. -/
  | codeAllMap (pre : (Nat → BitVec 64) → CtxOf Ty) (f : (Nat → BitVec 64) → Nat → BitVec 64) :
    Sub (.codeAll pre) (.codeAll fun s => pre (f s))

/-- `SubShape S T`: bytes described by `S` are also described by `T`. The two
are the same size, and each typed value of `T` is one of `S` at a weaker
type; typed values of `S` may be forgotten. -/
structure SubShape (S T : ShapeOf Ty) : Prop where
  size : S.size = T.size
  vals : ∀ q ∈ T.vals, ∃ p ∈ S.vals, p.1 = q.1 ∧ Sub p.2 q.2

/-- Subtyping piece by piece, for two stacks cut into pieces the same way. -/
inductive SubList : List (ShapeOf Ty) → List (ShapeOf Ty) → Prop
  | nil : SubList [] []
  | cons {S T : ShapeOf Ty} {σ ρ : List (ShapeOf Ty)} :
    SubShape S T → SubList σ ρ → SubList (S :: σ) (T :: ρ)

/-- `CtxSub Γ Δ`: every state matching `Γ` also matches `Δ`. The stack's
pieces and room must agree exactly; only the types of registers and of the
stack's typed values may be weakened. -/
structure CtxSub (Γ Δ : Ctx) : Prop where
  regs : ∀ r, r ≠ .rsp → Sub (Γ.regs r) (Δ.regs r)
  stack : SubList Γ.stack Δ.stack
  room : Γ.room = Δ.room
  flags : ∀ f, Γ.flags f → Δ.flags f
  /-- What is known of the stack pointer's value may also be weakened. -/
  sp : Sub (Γ.regs .rsp) (Δ.regs .rsp)
  /-- The owned blocks agree exactly. -/
  owned : Γ.owned = Δ.owned
  /-- So does what has been detached from the stack. -/
  above : Γ.above = Δ.above

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
  /-- The number of bytes of stack the function uses below its return address. -/
  need : Nat
  /-- The blocks the function is handed to own: the caller owns them before
  the call and not while the function runs. A signature that takes a block
  names its address, so it is one of a family, a signature for each address. -/
  takes : List (BitVec 64 × Shape) := []
  /-- The blocks the function hands back for the caller to own from the
  return on. Often those it took, with the types its work has given them. -/
  gives : List (BitVec 64 × Shape) := []

namespace FnSig

/-- Register types on entry, when the preserved registers have types `saved`. -/
def regsIn (sig : FnSig) (saved : Reg → Ty) : Reg → Ty :=
  fun r => if sig.preserved r then saved r else sig.args r

/-- Register types on return, when the preserved registers have types `saved`. -/
def regsOut (sig : FnSig) (saved : Reg → Ty) : Reg → Ty :=
  fun r => if sig.preserved r then saved r else sig.results r

/-- The context at the function's first instruction, for a caller that
expects `ret` on return and has `rest` on its stack. The function owns the
blocks it takes, and after them whatever else the caller owns: those are the
blocks the return point expects after the ones the function gives back, and
the function leaves them alone, whatever they are. -/
def entry (sig : FnSig) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) : Ctx :=
  ⟨sig.regsIn saved, .slot (.code ret) :: rest, room, Flags.Any,
    sig.takes ++ ret.owned.drop sig.gives.length, ret.above⟩

/-- The context at the function's `ret` instruction. -/
def exit (sig : FnSig) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) : Ctx :=
  ⟨sig.regsOut saved, .slot (.code ret) :: rest, room, Flags.Any, ret.owned, ret.above⟩

/-- The context the caller is in once the function has returned. The stack
pointer is 8 above where it was at the function's `ret`, having popped the
return address; so a function that leaves the stack pointer's type as it
found it has, for its caller, put the stack pointer back. -/
def returned (sig : FnSig) (saved : Reg → Ty) (rest : List Shape) (room : Nat)
    (owned : List (BitVec 64 × Shape)) (above : Nat) : Ctx :=
  ⟨fun r => if r = .rsp then (sig.regsOut saved .rsp).shift 8 else sig.regsOut saved r, rest,
    room + 8, Flags.Any, owned, above⟩

theorem returned_regs {sig : FnSig} {saved : Reg → Ty} {rest : List Shape} {room : Nat}
    {owned : List (BitVec 64 × Shape)} {above : Nat} {r : Reg}
    (hr : r ≠ .rsp) : (sig.returned saved rest room owned above).regs r = sig.regsOut saved r := by
  simp only [returned, hr, ↓reduceIte]

theorem returned_sp (sig : FnSig) (saved : Reg → Ty) (rest : List Shape) (room : Nat)
    (owned : List (BitVec 64 × Shape)) (above : Nat) :
    (sig.returned saved rest room owned above).regs .rsp = (sig.regsOut saved .rsp).shift 8 := by
  simp only [returned, ↓reduceIte]

/-- What a function needs of its caller: the state it returns must be
acceptable where it returns to, there must be enough stack, and the blocks
the return point expects to own must begin with those the function gives. -/
structure CallerOk (sig : FnSig) (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat) :
    Prop where
  gives : ret.owned.take sig.gives.length = sig.gives
  ret : CtxSub (sig.returned saved rest room ret.owned ret.above) ret
  room : sig.need ≤ room

/-- A caller is ready if the state the function returns is acceptable where
it returns to with as much detached from the stack as there is now. -/
theorem CallerOk.ofBack {sig : FnSig} {saved : Reg → Ty} {ret : Ctx} {rest : List Shape}
    {room above : Nat} (hgives : ret.owned.take sig.gives.length = sig.gives)
    (hback : CtxSub (sig.returned saved rest room ret.owned above) ret) (hneed : sig.need ≤ room) :
    sig.CallerOk saved ret rest room := by
  have e : above = ret.above := hback.above
  subst e
  exact ⟨hgives, hback, hneed⟩

/-- At its return, a function that owns the blocks it gives and after them
what the caller owned besides owns what the return point expects. -/
theorem CallerOk.owned_back {sig : FnSig} {saved : Reg → Ty} {ret : Ctx} {rest : List Shape}
    {room : Nat} {owned : List (BitVec 64 × Shape)} (h : sig.CallerOk saved ret rest room)
    (ho : owned = sig.gives ++ ret.owned.drop sig.gives.length) : owned = ret.owned := by
  rw [ho]
  conv => lhs; arg 1; rw [← h.gives]
  exact List.take_append_drop _ _

/-- `sig.At Φ a`: the code typing lets address `a` be entered as a function
with signature `sig`, by any caller. -/
def At (sig : FnSig) (Φ : CodeTy) (a : BitVec 64) : Prop :=
  ∀ saved ret rest room, sig.CallerOk saved ret rest room → Φ a (sig.entry saved ret rest room)

/-- The type of a pointer to a function with this signature. -/
def ty (sig : FnSig) : Ty :=
  .fn sig.args sig.results sig.preserved sig.need sig.takes sig.gives

end FnSig

/-! ## Signatures with results chosen at the return -/

/-- A kind of value a function may choose as it returns, for its results to
depend on: the address of a block it made, two such addresses, and so on.
What is asked is that the value can be written as a sequence of 64-bit
values and read back, which is how it is carried in types. -/
class Chosen (ι : Type) where
  enc : ι → Nat → BitVec 64
  dec : (Nat → BitVec 64) → ι
  dec_enc : ∀ x, dec (enc x) = x

instance : Chosen (Nat → BitVec 64) := ⟨id, id, fun _ => rfl⟩

instance : Chosen (BitVec 64) := ⟨fun x _ => x, fun s => s 0, fun _ => rfl⟩

instance : Chosen Unit := ⟨fun _ _ => 0, fun _ => (), fun _ => rfl⟩

/-- Two chosen values: one in the even places of the sequence, the other in
the odd ones. -/
instance {α β : Type} [Chosen α] [Chosen β] : Chosen (α × β) where
  enc x := fun n => if n % 2 = 0 then Chosen.enc x.1 (n / 2) else Chosen.enc x.2 (n / 2)
  dec s := (Chosen.dec fun n => s (2 * n), Chosen.dec fun n => s (2 * n + 1))
  dec_enc x := by
    have h₁ : (fun n => if 2 * n % 2 = 0 then Chosen.enc x.1 (2 * n / 2)
        else Chosen.enc x.2 (2 * n / 2)) = Chosen.enc x.1 := by
      funext n
      simp only [show 2 * n % 2 = 0 by omega, ↓reduceIte, show 2 * n / 2 = n by omega]
    have h₂ : (fun n => if (2 * n + 1) % 2 = 0 then Chosen.enc x.1 ((2 * n + 1) / 2)
        else Chosen.enc x.2 ((2 * n + 1) / 2)) = Chosen.enc x.2 := by
      funext n
      simp only [show (2 * n + 1) % 2 = 1 by omega, Nat.reduceEqDiff, ↓reduceIte,
        show (2 * n + 1) / 2 = n by omega]
    show (Chosen.dec _, Chosen.dec _) = x
    rw [h₁, h₂, Chosen.dec_enc, Chosen.dec_enc]

/-- A function signature whose results depend on a value of type `ι` chosen
at the return: typically the address of something the function made. -/
structure FnSigEx (ι : Type) where
  /-- The types expected in the registers on entry. -/
  args : Reg → Ty
  /-- The registers whose types are the same on return as on entry. -/
  preserved : Reg → Bool
  /-- The number of bytes of stack the function uses below its return address. -/
  need : Nat
  /-- The blocks the function is handed to own. -/
  takes : List (BitVec 64 × Shape) := []
  /-- The types left in the registers on return, for the value chosen. -/
  results : ι → Reg → Ty
  /-- The blocks the function hands back, for the value chosen. -/
  gives : ι → List (BitVec 64 × Shape)

namespace FnSigEx

variable {ι : Type}

/-- The ordinary signature the function meets once the value is chosen. -/
def pick (sig : FnSigEx ι) (x : ι) : FnSig :=
  ⟨sig.args, sig.results x, sig.preserved, sig.need, sig.takes, sig.gives x⟩

/-- Register types on entry, when the preserved registers have types `saved`. -/
def regsIn (sig : FnSigEx ι) (saved : Reg → Ty) : Reg → Ty :=
  fun r => if sig.preserved r then saved r else sig.args r

/-- The context at the function's first instruction, for a caller that
expects `ret x` on return, whichever `x` the function chooses, has `rest` on
its stack and owns `frame` besides what the function takes. -/
def entry [Chosen ι] (sig : FnSigEx ι) (saved : Reg → Ty) (ret : ι → Ctx) (rest : List Shape)
    (room : Nat) (frame : List (BitVec 64 × Shape)) (above : Nat) : Ctx :=
  ⟨sig.regsIn saved, .slot (.codeAll (fun s => ret (Chosen.dec s))) :: rest, room, Flags.Any,
    sig.takes ++ frame, above⟩

/-- What the function needs of its caller: what an ordinary function with
each of the signatures would need, and that what the caller owns besides is
the same whichever value is chosen. -/
structure CallerOk (sig : FnSigEx ι) (saved : Reg → Ty) (ret : ι → Ctx) (rest : List Shape)
    (room : Nat) (frame : List (BitVec 64 × Shape)) (above : Nat) : Prop where
  each : ∀ x, (sig.pick x).CallerOk saved (ret x) rest room
  frame : ∀ x, (ret x).owned.drop (sig.gives x).length = frame
  /-- What has been detached from the stack is the same whichever value is
  chosen. -/
  detached : ∀ x, (ret x).above = above

/-- `sig.At Φ a`: the code typing lets address `a` be entered as a function
with signature `sig`, by any caller. -/
def At [Chosen ι] (sig : FnSigEx ι) (Φ : CodeTy) (a : BitVec 64) : Prop :=
  ∀ saved ret rest room frame above, sig.CallerOk saved ret rest room frame above →
    Φ a (sig.entry saved ret rest room frame above)

/-- The signature with its chosen value written as a sequence, which is the
form a type carries it in. -/
def raw [Chosen ι] (sig : FnSigEx ι) : FnSigEx (Nat → BitVec 64) :=
  ⟨sig.args, sig.preserved, sig.need, sig.takes, fun s => sig.results (Chosen.dec s),
    fun s => sig.gives (Chosen.dec s)⟩

/-- The type of a pointer to a function with this signature. -/
def ty [Chosen ι] (sig : FnSigEx ι) : Ty :=
  .fnAll sig.args sig.preserved sig.need sig.takes (fun s => sig.results (Chosen.dec s))
    (fun s => sig.gives (Chosen.dec s))

end FnSigEx

/-- A memory typing makes sense: blocks fit in the address space, none is
empty, no two overlap, each typed value lies inside its block, and a block of
a kind has that kind's shape. -/
structure MemTy.WF (Ψ : MemTy) : Prop where
  size_lt : ∀ a l, Ψ a = some l → l.size < 2 ^ 64
  disjoint : ∀ a b la lb, Ψ a = some la → Ψ b = some lb → a ≠ b → Disjoint a la.size b lb.size
  nonempty : ∀ a l, Ψ a = some l → 0 < l.size
  fits : ∀ a l, Ψ a = some l → ∀ p ∈ l.shape.vals, p.1 + 8 ≤ l.shape.size
  kinds : ∀ a l, Ψ a = some l → ∀ tag, l.tag = some tag → Ψ.kinds tag = some l.shape
  /-- A block that says its bytes may not be written, and says all of them. -/
  said : ∀ a l (bs : List (BitVec 8)), Ψ a = some l → l.said = some bs →
    l.writable = false ∧ bs.length = l.size

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
`room` free bytes below `rsp`. -/
def stackBase (Γ : Ctx) (s : State) : BitVec 64 :=
  s.getReg .rsp - BitVec.ofNat 64 Γ.room

/-- The size in bytes of the stack region a context describes. -/
def stackSize (Γ : Ctx) : Nat :=
  Γ.room + stackLen Γ.stack

/-- What a context's owned blocks ask of a state: each is writable, each
typed value in it is of its type, and the blocks overlap neither the stack
region, nor any block of the memory typing, nor one another. -/
structure OwnedOk (H : Ty → BitVec 64 → Prop) (Ψ : MemTy) (Γ : Ctx) (s : State) : Prop where
  perm : ∀ b ∈ Γ.owned, s.canWrite b.1 b.2.size = true
  size_lt : ∀ b ∈ Γ.owned, b.2.size < 2 ^ 64
  /-- Each typed value lies inside its block. -/
  fits : ∀ b ∈ Γ.owned, ∀ p ∈ b.2.vals, p.1 + 8 ≤ b.2.size
  vals : ∀ b ∈ Γ.owned, ∀ p ∈ b.2.vals, H p.2 (s.load64 (b.1 + BitVec.ofNat 64 p.1))
  stack : ∀ b ∈ Γ.owned, Disjoint (stackBase Γ s) (stackSize Γ) b.1 b.2.size
  heap : ∀ b ∈ Γ.owned, ∀ a l, Ψ a = some l → Disjoint b.1 b.2.size a l.size
  apart : Γ.owned.Pairwise fun b c => Disjoint b.1 b.2.size c.1 c.2.size

/-- `Matches H Ψ Γ s`: the state `s` matches the context `Γ`, where `H τ v`
says what it means for the value `v` to have type `τ`. -/
structure Matches (H : Ty → BitVec 64 → Prop) (Ψ : MemTy) (Γ : Ctx) (s : State) : Prop where
  /-- Each register other than `rsp` holds a value of its type. -/
  regs : ∀ r, r ≠ .rsp → H (Γ.regs r) (s.getReg r)
  /-- The flags are as the context says. -/
  flags : Γ.flags s.flags
  /-- The stack region, free bytes included, is writable. -/
  stackPerm : s.canWrite (stackBase Γ s) (stackSize Γ) = true
  /-- The stack region, with what has been detached from above it, is
  smaller than the address space. -/
  stackBound : stackSize Γ + Γ.above < 2 ^ 64
  /-- Each typed value of each piece of the stack lies inside the piece. -/
  stackFits : ∀ S ∈ Γ.stack, ∀ p ∈ S.vals, p.1 + 8 ≤ S.size
  /-- Each typed value of each piece of the stack is of its type. -/
  stack : ∀ k S, Γ.stack[k]? = some S → ∀ p ∈ S.vals,
    H p.2 (s.load64 (s.getReg .rsp + BitVec.ofNat 64 (stackOff Γ.stack k + p.1)))
  /-- Each memory block is readable, and writable if its layout says so. -/
  heapPerm : ∀ a l, Ψ a = some l →
    s.canRead a l.size = true ∧ (l.writable = true → s.canWrite a l.size = true)
  /-- Each typed value of each memory block is of its type. -/
  heap : ∀ a l, Ψ a = some l → ∀ p ∈ l.shape.vals,
    H p.2 (s.load64 (a + BitVec.ofNat 64 p.1))
  /-- No memory block overlaps the stack region. -/
  stackHeap : ∀ a l, Ψ a = some l → Disjoint (stackBase Γ s) (stackSize Γ) a l.size
  /-- The stack pointer holds a value of its type. -/
  sp : H (Γ.regs .rsp) (s.getReg .rsp)
  /-- The text of each block that has some ends in a zero byte. -/
  text : ∀ a l, Ψ a = some l → l.text ≠ 0 → s.mem (a + BitVec.ofNat 64 (l.size - 1)) = 0
  /-- A block that says its bytes holds them. -/
  said : ∀ a l (bs : List (BitVec 8)), Ψ a = some l → l.said = some bs →
    ∀ k (hk : k < bs.length), s.mem (a + BitVec.ofNat 64 k) = bs[k]
  /-- The owned blocks are there and hold what the context says. -/
  owned : OwnedOk H Ψ Γ s

/-- The stack region is smaller than the address space. -/
theorem Matches.stackSize_lt {H : Ty → BitVec 64 → Prop} {Ψ : MemTy} {Γ : Ctx} {s : State}
    (h : Matches H Ψ Γ s) : stackSize Γ < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h.stackBound

/-- `HasTy fetch sys Ψ n τ v`: the value `v` has type `τ`, at step count `n`.
This does not depend on the machine state. -/
def HasTy (fetch : Fetch) (sys : Syscall) : MemTy → Nat → Ty → BitVec 64 → Prop
  | _, _, .int, _ => True
  | _, _, .eq x, v => v = x
  | Ψ, _, .ptr shape writable off, v =>
    ∃ a l, Ψ a = some l ∧ l.shape = shape ∧ (writable = true → l.writable = true) ∧
      v = a + BitVec.ofNat 64 off
  | Ψ, n, .code pre, v =>
    ∀ k, (hk : k < n) → ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → ∀ s : State, s.rip = v →
      Matches (fun τ w => HasTy fetch sys Ψ' k τ w) Ψ' pre s → SafeN fetch sys k s
  | Ψ, n, .fnAll args preserved need takes results gives, v =>
    ∀ k, (hk : k < n) → ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF →
      ∀ (saved : Reg → Ty) (ret : (Nat → BitVec 64) → Ctx) (rest : List Shape) (room : Nat)
        (frame : List (BitVec 64 × Shape)) (above : Nat),
      FnSigEx.CallerOk ⟨args, preserved, need, takes, results, gives⟩ saved ret rest room frame above →
      ∀ s : State, s.rip = v →
      Matches (fun τ w => HasTy fetch sys Ψ' k τ w) Ψ'
        (FnSigEx.entry ⟨args, preserved, need, takes, results, gives⟩ saved ret rest room
          frame above) s →
      SafeN fetch sys k s
  | Ψ, n, .codeAll pre, v =>
    ∀ x : Nat → BitVec 64, ∀ k, (hk : k < n) → ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → ∀ s : State,
      s.rip = v → Matches (fun τ w => HasTy fetch sys Ψ' k τ w) Ψ' (pre x) s →
      SafeN fetch sys k s
  | Ψ, _, .ref tag writable off, v =>
    ∃ a l, Ψ a = some l ∧ l.tag = some tag ∧ (writable = true → l.writable = true) ∧
      v = a + BitVec.ofNat 64 off
  | Ψ, n, .nullable τ, v => v = 0 ∨ HasTy fetch sys Ψ n τ v
  | Ψ, n, .orErr τ, v => SysErr v ∨ HasTy fetch sys Ψ n τ v
  | Ψ, _, .str more, v =>
    ∃ a l off, Ψ a = some l ∧ off + (if more then 1 else 0) < l.text ∧
      v = a + BitVec.ofNat 64 (l.shape.size + off)
  | Ψ, n, .fn args results preserved need takes gives, v =>
    ∀ k, (hk : k < n) → ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF →
      ∀ (saved : Reg → Ty) (ret : Ctx) (rest : List Shape) (room : Nat),
      FnSig.CallerOk ⟨args, results, preserved, need, takes, gives⟩ saved ret rest room →
      ∀ s : State, s.rip = v →
      Matches (fun τ w => HasTy fetch sys Ψ' k τ w) Ψ'
        (FnSig.entry ⟨args, results, preserved, need, takes, gives⟩ saved ret rest room) s →
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

theorem hasTy_ptr {shape : Shape} {writable : Bool} {off : Nat} {v : BitVec 64} :
    HasTy fetch sys Ψ n (.ptr shape writable off) v ↔
      ∃ a l, Ψ a = some l ∧ l.shape = shape ∧ (writable = true → l.writable = true) ∧
        v = a + BitVec.ofNat 64 off := by
  simp [HasTy]

/-- A value is a code pointer if jumping to it, in any state matching the
context it expects, is safe for any smaller number of steps, now and however
the memory typing grows. -/
theorem hasTy_code {pre : Ctx} {v : BitVec 64} :
    HasTy fetch sys Ψ n (.code pre) v ↔
      ∀ k, k < n → ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → ∀ s : State, s.rip = v →
        WellTyped fetch sys Ψ' k pre s → SafeN fetch sys k s := by
  rw [HasTy]

/-- Code ready for a family of contexts is code ready for each of them. -/
theorem hasTy_codeAll {pre : (Nat → BitVec 64) → Ctx} {v : BitVec 64} :
    HasTy fetch sys Ψ n (.codeAll pre) v ↔ ∀ x, HasTy fetch sys Ψ n (.code (pre x)) v := by
  simp only [hasTy_code]
  rw [HasTy]

theorem hasTy_ref {tag : Nat} {writable : Bool} {off : Nat} {v : BitVec 64} :
    HasTy fetch sys Ψ n (.ref tag writable off) v ↔
      ∃ a l, Ψ a = some l ∧ l.tag = some tag ∧ (writable = true → l.writable = true) ∧
        v = a + BitVec.ofNat 64 off := by
  simp [HasTy]

theorem hasTy_nullable {τ : Ty} {v : BitVec 64} :
    HasTy fetch sys Ψ n (.nullable τ) v ↔ v = 0 ∨ HasTy fetch sys Ψ n τ v := by
  rw [HasTy]

theorem hasTy_orErr {τ : Ty} {v : BitVec 64} :
    HasTy fetch sys Ψ n (.orErr τ) v ↔ SysErr v ∨ HasTy fetch sys Ψ n τ v := by
  rw [HasTy]

theorem hasTy_str {more : Bool} {v : BitVec 64} :
    HasTy fetch sys Ψ n (.str more) v ↔
      ∃ a l off, Ψ a = some l ∧ off + (if more then 1 else 0) < l.text ∧
        v = a + BitVec.ofNat 64 (l.shape.size + off) := by
  simp [HasTy]

/-- A value is a pointer to a function if entering it, from any caller that
meets the signature, is safe for any smaller number of steps. -/
theorem hasTy_fn {sig : FnSig} {v : BitVec 64} :
    HasTy fetch sys Ψ n sig.ty v ↔
      ∀ k, k < n → ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF →
        ∀ saved ret rest room, sig.CallerOk saved ret rest room →
        ∀ s : State, s.rip = v → WellTyped fetch sys Ψ' k (sig.entry saved ret rest room) s →
        SafeN fetch sys k s := by
  rw [FnSig.ty, HasTy]

/-- A value is a pointer to a function with a chosen result if entering it,
from any caller that meets the signature, is safe for any smaller number of
steps. The caller's return contexts are taken over sequences, as the type
carries them. -/
theorem hasTy_fnAll {ι : Type} [Chosen ι] {sig : FnSigEx ι} {v : BitVec 64} :
    HasTy fetch sys Ψ n sig.ty v ↔
      ∀ k, k < n → ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF →
        ∀ saved ret rest room frame above, sig.raw.CallerOk saved ret rest room frame above →
        ∀ s : State, s.rip = v →
        WellTyped fetch sys Ψ' k (sig.raw.entry saved ret rest room frame above) s →
        SafeN fetch sys k s := by
  rw [FnSigEx.ty, HasTy]
  rfl

/-- `τ.Enters Δ`: a value of type `τ` is the address of code that may be
entered in the context `Δ`. Code wanting `Δ` is; code ready for a family of
contexts is, for each of them; and a pointer to a function is, for the
function's entry from any caller that meets its signature. This is what a
jump or a call through a value asks of its type. -/
inductive Ty.Enters : Ty → Ctx → Prop
  | code (Δ : Ctx) : Ty.Enters (.code Δ) Δ
  | codeAll (pre : (Nat → BitVec 64) → Ctx) (x : Nat → BitVec 64) :
    Ty.Enters (.codeAll pre) (pre x)
  | fn {sig : FnSig} {saved : Reg → Ty} {ret : Ctx} {rest : List Shape} {room : Nat} :
    sig.CallerOk saved ret rest room → Ty.Enters sig.ty (sig.entry saved ret rest room)
  | fnAll {ι : Type} [Chosen ι] {sig : FnSigEx ι} {saved : Reg → Ty}
      {ret : (Nat → BitVec 64) → Ctx} {rest : List Shape} {room : Nat}
      {frame : List (BitVec 64 × Shape)} {above : Nat} :
    sig.raw.CallerOk saved ret rest room frame above →
    Ty.Enters sig.ty (sig.raw.entry saved ret rest room frame above)
  /-- The same, for a caller whose contexts on return are given by the value
  chosen, as the signature has it, and not by the sequence that stands for it. -/
  | fnEx {ι : Type} [Chosen ι] {sig : FnSigEx ι} {saved : Reg → Ty} {ret : ι → Ctx}
      {rest : List Shape} {room : Nat} {frame : List (BitVec 64 × Shape)} {above : Nat} :
    sig.CallerOk saved ret rest room frame above →
    Ty.Enters sig.ty (sig.entry saved ret rest room frame above)

/-- A value whose type enters a context is the address of code wanting it. -/
theorem Ty.Enters.sound {τ : Ty} {Δ : Ctx} {v : BitVec 64} (he : τ.Enters Δ)
    (h : HasTy fetch sys Ψ n τ v) : HasTy fetch sys Ψ n (.code Δ) v := by
  cases he with
  | code => exact h
  | codeAll pre x => exact hasTy_codeAll.mp h x
  | fn hK =>
    rw [hasTy_code]
    intro k hk Ψ' he' hΨ' s hs hw
    exact hasTy_fn.mp h k hk Ψ' he' hΨ' _ _ _ _ hK s hs hw
  | fnAll hK =>
    rw [hasTy_code]
    intro k hk Ψ' he' hΨ' s hs hw
    exact hasTy_fnAll.mp h k hk Ψ' he' hΨ' _ _ _ _ _ _ hK s hs hw
  | @fnEx ι _ sig saved ret rest room frame above hK =>
    rw [hasTy_code]
    intro k hk Ψ' he' hΨ' s hs hw
    exact hasTy_fnAll.mp h k hk Ψ' he' hΨ' saved (fun q => ret (Chosen.dec q)) rest room frame
      above ⟨fun q => hK.each (Chosen.dec q), fun q => hK.frame (Chosen.dec q),
        fun q => hK.detached (Chosen.dec q)⟩ s hs hw

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
  | str more => exact hasTy_str.mpr (hasTy_str.mp h)
  | int => exact HasTy.int v
  | eq x => exact hasTy_eq.mpr (hasTy_eq.mp h)
  | ptr fields writable index => exact hasTy_ptr.mpr (hasTy_ptr.mp h)
  | code pre =>
    rw [hasTy_code] at h ⊢
    exact fun k hk => h k (by omega)
  | codeAll pre =>
    simp only [hasTy_codeAll, hasTy_code] at h ⊢
    exact fun x k hk => h x k (by omega)
  | fnAll args preserved need takes results gives =>
    rw [HasTy] at h ⊢
    exact fun k hk => h k (by omega)
  | fn args results preserved need takes gives =>
    have e : Ty.fn args results preserved need takes gives = FnSig.ty ⟨args, results, preserved, need, takes, gives⟩ := rfl
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
  | str more =>
    obtain ⟨a, l, off, hl, h'⟩ := hasTy_str.mp h
    exact hasTy_str.mpr ⟨a, l, off, he.blocks a l hl, h'⟩
  | int => exact HasTy.int v
  | eq x => exact hasTy_eq.mpr (hasTy_eq.mp h)
  | ptr fields writable index =>
    obtain ⟨a, l, hl, h'⟩ := hasTy_ptr.mp h
    exact hasTy_ptr.mpr ⟨a, l, he.blocks a l hl, h'⟩
  | code pre =>
    rw [hasTy_code] at h ⊢
    exact fun k hk Ψ'' he' => h k hk Ψ'' (he.trans he')
  | codeAll pre =>
    simp only [hasTy_codeAll, hasTy_code] at h ⊢
    exact fun x k hk Ψ'' he' => h x k hk Ψ'' (he.trans he')
  | fnAll args preserved need takes results gives =>
    rw [HasTy] at h ⊢
    exact fun k hk Ψ'' he' => h k hk Ψ'' (he.trans he')
  | fn args results preserved need takes gives =>
    have e : Ty.fn args results preserved need takes gives = FnSig.ty ⟨args, results, preserved, need, takes, gives⟩ := rfl
    rw [e, hasTy_fn] at h ⊢
    exact fun k hk Ψ'' he' => h k hk Ψ'' (he.trans he')
termination_by sizeOf τ

/-- Matching a context carries over to any weaker notion of "has type". -/
theorem Matches.imp {H H' : Ty → BitVec 64 → Prop} {Γ : Ctx} {s : State}
    (h : Matches H Ψ Γ s) (himp : ∀ τ v, H τ v → H' τ v) : Matches H' Ψ Γ s :=
  { regs := fun r hr => himp _ _ (h.regs r hr)
    flags := h.flags
    stackPerm := h.stackPerm
    stackBound := h.stackBound
    stackFits := h.stackFits
    stack := fun k S hk p hp => himp _ _ (h.stack k S hk p hp)
    heapPerm := h.heapPerm
    heap := fun a l hl p hp => himp _ _ (h.heap a l hl p hp)
    stackHeap := h.stackHeap
    sp := himp _ _ h.sp
    text := h.text
    said := h.said
    owned := { h.owned with vals := fun b hb p hp => himp _ _ (h.owned.vals b hb p hp) } }

/-- A state well typed at a step count is well typed at every smaller one. -/
theorem WellTyped.mono {m : Nat} {Γ : Ctx} {s : State} (h : WellTyped fetch sys Ψ n Γ s)
    (hle : m ≤ n) : WellTyped fetch sys Ψ m Γ s :=
  Matches.imp h (fun _ _ hv => hv.mono hle)

end TypedAsm
