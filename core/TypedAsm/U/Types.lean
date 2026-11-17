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

/-- What a function asks and gives, for each choice of its parameters `p`;
and, as it returns, of the values `y` it chooses. -/
structure SigOf (τ : Type) where
  /-- The registers whose values the function returns with as it found them. -/
  preserved : Reg → Bool
  /-- How many bytes of stack the function may use below its return address. -/
  need : Nat
  /-- What the other registers hold on entry. -/
  args : Seq → Reg → BitVec 64
  /-- The regions the function is handed. -/
  takes : Seq → List (BitVec 64 × ShapeOf (BitVec 64))
  /-- What it is to be known of values, for the function to be entered. -/
  knows : Seq → List (BitVec 64 × τ)
  /-- What the other registers hold as it returns. -/
  results : Seq → Seq → Reg → BitVec 64
  /-- The regions it hands back. -/
  gives : Seq → Seq → List (BitVec 64 × ShapeOf (BitVec 64))
  /-- What is known of values as it returns. -/
  learns : Seq → Seq → List (BitVec 64 × τ)

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
  matches `pre x`, whichever `x` that is. -/
  | code (pre : Seq → CtxOf Ty)
  /-- It is the address of a function: code that is safe to enter from any
  caller that hands it what its signature asks, whatever else the caller
  holds and whatever it keeps in the preserved registers. -/
  | fn (sig : SigOf Ty)

abbrev Ctx := CtxOf Ty

/-- What a block of memory others may point into holds, byte for byte. -/
abbrev Shape := ShapeOf Ty

/-- What a region held alone holds: values at some of its bytes. -/
abbrev Held := ShapeOf (BitVec 64)

/-- Something known of a value. -/
abbrev Fact := BitVec 64 × Ty

/-- A region held alone. -/
abbrev Region := BitVec 64 × Held

abbrev Sig := SigOf Ty

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
  | codeMap (v : BitVec 64) (pre : Seq → Ctx) (f : Seq → Seq) :
    Sub v (.code pre) (.code fun s => pre (f s))

/-! ## A function's entry and what it returns with -/

/-- The flags a value stands for: two bits for each, nothing, clear or set.
Every setting of the flags is what some value stands for, so a family of
contexts over values is one over the flags too. -/
def flagsOf (v : BitVec 64) : Flags :=
  let one (k : Nat) : Option Bool :=
    if (v >>> (2 * k)) &&& 3 = 0 then none else some ((v >>> (2 * k)) &&& 3 ≠ 1)
  ⟨one 0, one 1, one 2, one 3⟩

/-- A value that stands for given flags. -/
def _root_.TypedAsm.Flags.bits (f : Flags) : BitVec 64 :=
  let one (b : Option Bool) : BitVec 64 :=
    match b with
    | none => 0
    | some false => 1
    | some true => 2
  one f.cf ||| (one f.zf <<< 2) ||| (one f.sf <<< 4) ||| (one f.of <<< 6)

theorem flagsOf_bits (f : Flags) : flagsOf f.bits = f := by
  obtain ⟨cf, zf, sf, of⟩ := f
  rcases cf with _ | _ | _ <;> rcases zf with _ | _ | _ <;> rcases sf with _ | _ | _ <;>
    rcases of with _ | _ | _ <;> decide

namespace SigOf

/-- What a function returns with: the stack pointer above the return
address, the preserved registers as they were, the others as the signature
says for the values chosen, and the flags as they happen to be; held, the
stack region it was entered with, now plain, the regions it gives, and whatever its caller held besides; and
known, what the signature says is learnt. -/
def exit (sig : Sig) (p : Seq) (saved : Reg → BitVec 64) (lo : BitVec 64) (m : Nat)
    (frame : List Region) (fl : Flags) (y : Seq) : Ctx where
  val r := if r = .rsp then lo + BitVec.ofNat 64 (m + sig.need + 8)
    else if sig.preserved r then saved r else sig.results p y r
  flags := fl
  held := (lo, ⟨m + sig.need + 8, []⟩) :: (sig.gives p y ++ frame)
  known := sig.learns p y

/-- The contexts a function may return in, as one family over values: the
first stands for the flags, the rest are the values the function chooses. -/
def exits (sig : Sig) (p : Seq) (saved : Reg → BitVec 64) (lo : BitVec 64) (m : Nat)
    (frame : List Region) : Seq → Ctx :=
  fun z => sig.exit p saved lo m frame (flagsOf (z 0)) (fun i => z (i + 1))

/-- What a function is entered with, from a caller that keeps `saved` in the
preserved registers, holds `frame` besides, and has a stack region at `lo`
with `m` bytes more than the function needs: the return address `ra` is the
value at the top of that region, and is known to be code wanting what the
function returns with. -/
def entry (sig : Sig) (p : Seq) (saved : Reg → BitVec 64) (lo : BitVec 64) (m : Nat)
    (ra : BitVec 64) (frame : List Region) (fl : Flags) : Ctx where
  val r := if r = .rsp then lo + BitVec.ofNat 64 (m + sig.need)
    else if sig.preserved r then saved r else sig.args p r
  flags := fl
  held := (lo, ⟨m + sig.need + 8, [(m + sig.need, ra)]⟩) :: (sig.takes p ++ frame)
  known := (ra, .code (sig.exits p saved lo m frame)) :: sig.knows p

end SigOf

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
    ∀ x : Seq, ∀ k, (hk : k < n) → ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → ∀ s : State,
      s.rip = v → Matches (fun τ w => HasTy fetch sys Ψ' k τ w) Ψ' (pre x) s →
      SafeN fetch sys k s
  | Ψ, n, .fn sig, v =>
    ∀ k, (hk : k < n) → ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF →
      ∀ (p : Seq) (saved : Reg → BitVec 64) (lo : BitVec 64) (m : Nat) (ra : BitVec 64)
        (frame : List Region) (fl : Flags) (s : State), s.rip = v →
      Matches (fun τ w => HasTy fetch sys Ψ' k τ w) Ψ' (SigOf.entry sig p saved lo m ra frame fl) s →
      SafeN fetch sys k s
termination_by _ n τ => (n, τ)

/-- `WellTyped fetch sys Ψ n Γ s`: the state `s` matches the context `Γ`, at
step count `n`. -/
abbrev WellTyped (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (n : Nat) (Γ : Ctx) (s : State) :
    Prop :=
  Matches (HasTy fetch sys Ψ n) Ψ Γ s

end TypedAsm.U
