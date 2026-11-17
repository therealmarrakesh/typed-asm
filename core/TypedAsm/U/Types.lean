import TypedAsm.Types

/-!
# Types, on one model of values and one of memory

A context says the value each register holds, and the flags. A value of which nothing is
known is still a value: it has a name, and anything computed from it is a
term in that name. What is known is known of values, not of the places that
hold them: a context lists facts, each saying something of a value. So a
value moved, saved and brought back is the value it was, with all that was
known of it; there is no type of "exactly this value", no rule for giving a
value a name, and nothing to say of a register a function leaves alone.

Memory is of two standings. Memory the code holds alone is a list of
regions in its context: where each is, how long, and which values it holds.
A store into such a region may change what it holds to anything. Memory
others may point into is the memory typing, as before: a store into it must
leave it holding what its type says.

The stack is memory the code holds alone. The stack pointer is a register
like the others, holding a value; what is free below it is a region of plain
bytes; a return address is a value in a region, known to be code.
-/

namespace TypedAsm.U

/-- A sequence of values: what a family of contexts is indexed by. -/
abbrev Seq := Nat → BitVec 64

/-- A description of the machine at one program point, with `τ` what may be
known of a value. -/
structure CtxOf (τ : Type) where
  /-- The value each register holds. -/
  val : Reg → BitVec 64
  /-- The flags, each as it is or undefined. -/
  flags : Flags
  /-- The regions of memory this code holds alone: where each is, how many
  bytes long, and at which of its bytes it holds a value, and which. Bytes
  that hold no such value are plain. -/
  held : List (BitVec 64 × ShapeOf (BitVec 64)) := []
  /-- What is known of values: each entry says something of one. -/
  known : List (BitVec 64 × τ) := []

/-- What a family of contexts ranges over: values; the flags; and regions
held, whatever they are. Code that wants a family is safe to enter at each
member of it. A family that ranges over regions is how a function is said
to be safe whatever else its caller holds. -/
structure Fam where
  vals : Seq := fun _ => 0
  flags : Flags := ⟨none, none, none, none⟩
  rest : List (BitVec 64 × ShapeOf (BitVec 64)) := []

/-- What may be known of a 64-bit value. -/
inductive Ty
  /-- Nothing. -/
  | any
  /-- It is the address of byte `off` of a memory block of this shape. -/
  | ptr (shape : ShapeOf Ty) (writable : Bool) (off : Nat)
  /-- It is the address of byte `off` of a memory block of the kind `tag`. -/
  | ref (tag : Nat) (writable : Bool) (off : Nat)
  /-- It is zero, or `τ` is known of it. -/
  | nullable (τ : Ty)
  /-- It is an error number, or `τ` is known of it. -/
  | orErr (τ : Ty)
  /-- It is the address of a byte of some block's text; with `more`, not the
  last. -/
  | str (more : Bool)
  /-- It is the address of code that is safe to enter when the machine
  matches `pre x`, whichever member `x` of the family that is. A function is
  such code: its family ranges over what it is handed, what its caller
  keeps, and whatever else its caller holds; and in each member the return
  address is known to be code wanting what the function returns with. -/
  | code (pre : Fam → CtxOf Ty)
  /-- It lies in a range: from `lo` round to `hi`, going up and wrapping. -/
  | range (lo hi : BitVec 64)

abbrev Ctx := CtxOf Ty

/-- What a block of memory others may point into holds, byte for byte. -/
abbrev Shape := ShapeOf Ty

/-- What a region held alone holds: values at some of its bytes. -/
abbrev Held := ShapeOf (BitVec 64)

/-- Something known of a value. -/
abbrev Fact := BitVec 64 × Ty

/-- A region held alone. -/
abbrev Region := BitVec 64 × Held

/-- The layout of one block of the memory others may point into. -/
structure Layout where
  shape : Shape
  writable : Bool
  /-- The kind of block this is, for blocks that `Ty.ref` pointers refer to. -/
  tag : Option Nat
  /-- How many bytes of text follow the shape's. -/
  text : Nat
  /-- The bytes the whole block holds, where that is said. -/
  said : Option (List (BitVec 8)) := none

def Layout.size (l : Layout) : Nat :=
  l.shape.size + l.text

/-- Memory typing: the layout of the block starting at each address where
one starts, and the shape that blocks of each kind have. -/
structure MemTy where
  blocks : BitVec 64 → Option Layout
  kinds : Nat → Option Shape

instance : CoeFun MemTy (fun _ => BitVec 64 → Option Layout) := ⟨MemTy.blocks⟩

/-- `Ψ.Ext Ψ'`: `Ψ'` is `Ψ` with perhaps more blocks. -/
structure MemTy.Ext (Ψ Ψ' : MemTy) : Prop where
  blocks : ∀ a l, Ψ a = some l → Ψ' a = some l
  kinds : Ψ'.kinds = Ψ.kinds

theorem MemTy.Ext.refl (Ψ : MemTy) : Ψ.Ext Ψ :=
  ⟨fun _ _ h => h, rfl⟩

theorem MemTy.Ext.trans {Ψ Ψ' Ψ'' : MemTy} (h₁ : Ψ.Ext Ψ') (h₂ : Ψ'.Ext Ψ'') : Ψ.Ext Ψ'' :=
  ⟨fun a l h => h₂.blocks a l (h₁.blocks a l h), h₂.kinds.trans h₁.kinds⟩

/-- Code typing: `Φ a Γ` says the instruction at address `a` may be entered
in context `Γ`. -/
abbrev CodeTy := BitVec 64 → Ctx → Prop

/-- A memory typing makes sense. -/
structure MemTy.WF (Ψ : MemTy) : Prop where
  size_lt : ∀ a l, Ψ a = some l → l.size < 2 ^ 64
  disjoint : ∀ a b la lb, Ψ a = some la → Ψ b = some lb → a ≠ b → Disjoint a la.size b lb.size
  nonempty : ∀ a l, Ψ a = some l → 0 < l.size
  fits : ∀ a l, Ψ a = some l → ∀ p ∈ l.shape.vals, p.1 + 8 ≤ l.shape.size
  kinds : ∀ a l, Ψ a = some l → ∀ tag, l.tag = some tag → Ψ.kinds tag = some l.shape
  said : ∀ a l (bs : List (BitVec 8)), Ψ a = some l → l.said = some bs →
    l.writable = false ∧ bs.length = l.size

/-! ## What is known of one value follows from what is known of it another way -/

/-- `Sub v τ υ`: if `τ` is known of the value `v`, so is `υ`. The value is
part of the question: zero may be null whatever else is known of it. -/
inductive Sub : BitVec 64 → Ty → Ty → Prop
  | refl (v : BitVec 64) (τ : Ty) : Sub v τ τ
  | any (v : BitVec 64) (τ : Ty) : Sub v τ .any
  | readOnly (v : BitVec 64) (shape : Shape) (writable : Bool) (off : Nat) :
    Sub v (.ptr shape true off) (.ptr shape writable off)
  | refReadOnly (v : BitVec 64) (tag : Nat) (writable : Bool) (off : Nat) :
    Sub v (.ref tag true off) (.ref tag writable off)
  | nullable {v : BitVec 64} {τ υ : Ty} : Sub v τ υ → Sub v τ (.nullable υ)
  | null (τ υ : Ty) : Sub 0 τ (.nullable υ)
  /-- What may be null and is not zero, is not null. -/
  | nonNull {v : BitVec 64} (τ : Ty) : v ≠ 0 → Sub v (.nullable τ) τ
  | nullableMono {v : BitVec 64} {τ υ : Ty} : Sub v τ υ → Sub v (.nullable τ) (.nullable υ)
  | orErr {v : BitVec 64} {τ υ : Ty} : Sub v τ υ → Sub v τ (.orErr υ)
  | err {v : BitVec 64} (τ υ : Ty) : SysErr v → Sub v τ (.orErr υ)
  /-- What may be an error number and is not one, is not. -/
  | noErr {v : BitVec 64} (τ : Ty) : ¬ SysErr v → Sub v (.orErr τ) τ
  | orErrMono {v : BitVec 64} {τ υ : Ty} : Sub v τ υ → Sub v (.orErr τ) (.orErr υ)
  | strLess (v : BitVec 64) (more : Bool) : Sub v (.str true) (.str more)
  /-- Code ready for every one of a family of contexts is ready for any
  part of the family, however the part is picked out. -/
  | codeMap (v : BitVec 64) (pre : Fam → Ctx) (f : Fam → Fam) :
    Sub v (.code pre) (.code fun s => pre (f s))
  /-- What lies in one range lies in another, where being in the first puts
  the value in the second. -/
  | rangeIn {v : BitVec 64} (lo hi lo' hi' : BitVec 64) :
    (v - lo ≤ hi - lo → v - lo' ≤ hi' - lo') → Sub v (.range lo hi) (.range lo' hi')

/-! ## What a context asks of a state -/

/-- What a context's held regions ask of a state: each is writable, each
value in it is there, and the regions overlap neither any block of the
memory typing nor one another. -/
structure HeldOk (Ψ : MemTy) (Γ : Ctx) (s : State) : Prop where
  perm : ∀ b ∈ Γ.held, s.canWrite b.1 b.2.size = true
  size_lt : ∀ b ∈ Γ.held, b.2.size < 2 ^ 64
  fits : ∀ b ∈ Γ.held, ∀ p ∈ b.2.vals, p.1 + 8 ≤ b.2.size
  vals : ∀ b ∈ Γ.held, ∀ p ∈ b.2.vals, s.load64 (b.1 + BitVec.ofNat 64 p.1) = p.2
  heap : ∀ b ∈ Γ.held, ∀ a l, Ψ a = some l → Disjoint b.1 b.2.size a l.size
  apart : Γ.held.Pairwise fun b c => Disjoint b.1 b.2.size c.1 c.2.size

/-- `Matches H Ψ Γ s`: the state `s` matches the context `Γ`, where `H τ v`
says what it means for `τ` to be known of the value `v`. -/
structure Matches (H : Ty → BitVec 64 → Prop) (Ψ : MemTy) (Γ : Ctx) (s : State) : Prop where
  /-- Each register holds the value the context says. -/
  val : ∀ r, s.getReg r = Γ.val r
  /-- What the context says is known of values, is so. -/
  known : ∀ f ∈ Γ.known, H f.2 f.1
  /-- The flags are the ones the context says. -/
  flags : s.flags = Γ.flags
  /-- Each memory block is readable, and writable if its layout says so. -/
  heapPerm : ∀ a l, Ψ a = some l →
    s.canRead a l.size = true ∧ (l.writable = true → s.canWrite a l.size = true)
  /-- Each typed value of each memory block is as its type says. -/
  heap : ∀ a l, Ψ a = some l → ∀ p ∈ l.shape.vals,
    H p.2 (s.load64 (a + BitVec.ofNat 64 p.1))
  /-- The text of each block that has some ends in a zero byte. -/
  text : ∀ a l, Ψ a = some l → l.text ≠ 0 → s.mem (a + BitVec.ofNat 64 (l.size - 1)) = 0
  /-- A block that says its bytes holds them. -/
  said : ∀ a l (bs : List (BitVec 8)), Ψ a = some l → l.said = some bs →
    ∀ k (hk : k < bs.length), s.mem (a + BitVec.ofNat 64 k) = bs[k]
  /-- The held regions are there and hold what the context says. -/
  held : HeldOk Ψ Γ s
  /-- Every byte of memory the machine can touch lies in a region the
  context holds or in a block of the memory typing. With the rest, the held
  regions and the blocks are the accessible memory, each byte once: the
  context says all that is held, not some of it. -/
  complete : ∀ a : BitVec 64, s.perm a ≠ .none →
    (∃ b ∈ Γ.held, (a - b.1).toNat < b.2.size) ∨
    (∃ base l, Ψ base = some l ∧ (a - base).toNat < l.size)

/-- `HasTy fetch sys Ψ n τ v`: `τ` is so of the value `v`, at step count `n`. -/
def HasTy (fetch : Fetch) (sys : Syscall) : MemTy → Nat → Ty → BitVec 64 → Prop
  | _, _, .any, _ => True
  | Ψ, _, .ptr shape writable off, v =>
    ∃ a l, Ψ a = some l ∧ l.shape = shape ∧ (writable = true → l.writable = true) ∧
      v = a + BitVec.ofNat 64 off
  | Ψ, _, .ref tag writable off, v =>
    ∃ a l, Ψ a = some l ∧ l.tag = some tag ∧ (writable = true → l.writable = true) ∧
      v = a + BitVec.ofNat 64 off
  | Ψ, n, .nullable τ, v => v = 0 ∨ HasTy fetch sys Ψ n τ v
  | Ψ, n, .orErr τ, v => SysErr v ∨ HasTy fetch sys Ψ n τ v
  | Ψ, _, .str more, v =>
    ∃ a l off, Ψ a = some l ∧ off + (if more then 1 else 0) < l.text ∧
      v = a + BitVec.ofNat 64 (l.shape.size + off)
  | Ψ, n, .code pre, v =>
    ∀ x : Fam, ∀ k, (hk : k < n) → ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → ∀ s : State,
      s.rip = v → Matches (fun τ w => HasTy fetch sys Ψ' k τ w) Ψ' (pre x) s →
      SafeN fetch sys k s
  | _, _, .range lo hi, v => v - lo ≤ hi - lo
termination_by _ n τ => (n, τ)

/-- `WellTyped fetch sys Ψ n Γ s`: the state `s` matches the context `Γ`, at
step count `n`. -/
abbrev WellTyped (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (n : Nat) (Γ : Ctx) (s : State) :
    Prop :=
  Matches (HasTy fetch sys Ψ n) Ψ Γ s

end TypedAsm.U
