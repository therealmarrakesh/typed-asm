import TypedAsm.Program
import TypedAsm.Blocks
import TypedAsm.RegMap

/-!
# Contexts as data

A context says what is known of the machine at a point of a program. As it
is written (`Ctx`) it is made of functions and propositions: the type of a
register is the value of a function, an exactly known value is any 64-bit
value at all, what is known of the flags is a predicate. That is the right
thing for the typing rules to speak of, and nothing a function can look
into: it cannot tell whether two addresses are the same, since they are
values, not expressions.

Here a context is data. A value is a term built from numbers, variables and
the operations the machine does; a size or an offset is a term too; a type,
a shape, the flags and a context are built from those. Each has a meaning in
the contexts the rules speak of (`den`), given what the variables stand for
(`Env`). Whatever the terms have no form for is a variable: a type the
checker need not look into, such as the type of code, is one.

The checker works on these. Two addresses written from the same variable are
seen to be in the same block, and how far apart they are is a number; that
is decided by looking at the terms, with no one telling it.
-/

namespace TypedAsm

namespace Sym

/-- An operation of one value that the machine does, where the result is
exactly known from the operand. Each stands for the function `Op1.den`. -/
inductive Op1
  /-- The low 32 bits, extended with zeros: what a 32-bit move leaves. -/
  | low32
  deriving DecidableEq, Repr

/-- An operation of two values, likewise. -/
inductive Op2
  /-- The result of an arithmetic or logic operation at a width. -/
  | alu (op : AluOp) (w : Width)
  deriving DecidableEq, Repr

def Op1.den : Op1 → BitVec 64 → BitVec 64
  | .low32, a => (a.setWidth 32).setWidth 64

def Op2.den : Op2 → BitVec 64 → BitVec 64 → BitVec 64
  | .alu op .w64, a, b => (op.apply a b).1
  | .alu op .w32, a, b => (op.apply (a.setWidth 32) (b.setWidth 32)).1.setWidth 64

/-- A 64-bit value as a term. -/
inductive Val
  | lit (n : BitVec 64)
  /-- A value the context does not say more of: whatever the environment
  gives the variable. -/
  | var (i : Nat)
  | add (a b : Val)
  /-- Shifted left by a number of bits: an index scaled. -/
  | shl (a : Val) (k : Nat)
  | app1 (f : Op1) (a : Val)
  | app2 (f : Op2) (a b : Val)
  deriving DecidableEq, Repr

/-- A number as a term: a size, an offset, an amount of room. -/
inductive Num
  | lit (n : Nat)
  | var (i : Nat)
  | add (a b : Num)
  | mul (a b : Num)
  /-- Subtraction of numbers: nothing where there is not enough to take from. -/
  | sub (a b : Num)
  /-- A 64-bit value as a number. -/
  | toNat (v : Val)
  /-- How many bytes a shape that is a variable is. -/
  | size (i : Nat)
  deriving DecidableEq, Repr

mutual

/-- A type as a term. `atom` is a type the checker does not look into: the
type of code, of a function, or one the context only names. -/
inductive TyS
  | int
  | eq (v : Val)
  | ptr (S : ShapeS) (writable : Bool) (off : Num)
  | ref (tag : Nat) (writable : Bool) (off : Num)
  | nullable (τ : TyS)
  | orErr (τ : TyS)
  | str (more : Bool)
  | atom (i : Nat)

/-- The shape of a block as a term. -/
inductive ShapeS
  /-- So many bytes, with typed values at some of them. -/
  | mk (size : Num) (vals : ValsS)
  /-- An array: so many copies of a shape, end to end. -/
  | rep (n : Num) (E : ShapeS)
  | atom (i : Nat)

/-- The typed values of a block: where each starts, and its type. -/
inductive ValsS
  | nil
  | cons (o : Nat) (τ : TyS) (rest : ValsS)

end

/-- What is known of the flags, as a term. -/
inductive FlagsS
  /-- Nothing. -/
  | any
  /-- All four are defined. -/
  | known
  /-- They are exactly what an arithmetic or logic operation left. -/
  | alu (op : AluOp) (w : Width) (a b : Val)
  /-- They are exactly what a `test` of two values left. -/
  | test (a b : Val)
  /-- They are exactly these. -/
  | lit (f : Flags)
  | atom (i : Nat)
  deriving DecidableEq, Repr

/-- A context as a term. The stack and the owned blocks are written out as
far as they are known, and may go on as a variable. -/
structure CtxS where
  regs : RegMap TyS
  stack : List ShapeS
  stackRest : Option Nat := none
  room : Num
  flags : FlagsS
  owned : List (Val × ShapeS) := []
  ownedRest : Option Nat := none
  above : Num := .lit 0

/-- What the variables of terms stand for. -/
structure Env where
  val : List (BitVec 64) := []
  num : List Nat := []
  ty : List Ty := []
  shape : List Shape := []
  flags : List (Flags → Prop) := []
  stack : List (List Shape) := []
  owned : List (List (BitVec 64 × Shape)) := []

namespace Val

/-- The value a term stands for. -/
def den (ρ : Env) : Val → BitVec 64
  | .lit n => n
  | .var i => ρ.val.getD i 0
  | .add a b => a.den ρ + b.den ρ
  | .shl a k => a.den ρ <<< k
  | .app1 f a => f.den (a.den ρ)
  | .app2 f a b => f.den (a.den ρ) (b.den ρ)

end Val

namespace Num

/-- The number a term stands for. -/
def den (ρ : Env) : Num → Nat
  | .lit n => n
  | .var i => ρ.num.getD i 0
  | .add a b => a.den ρ + b.den ρ
  | .mul a b => a.den ρ * b.den ρ
  | .sub a b => a.den ρ - b.den ρ
  | .toNat v => (v.den ρ).toNat
  | .size i => (ρ.shape.getD i ⟨0, []⟩).size

/-- Two numbers added, with what can be added up at once added up. -/
def plus : Num → Num → Num
  | .lit m, .lit n => .lit (m + n)
  | .add x (.lit m), .lit n => .add x (.lit (m + n))
  | a, .lit 0 => a
  -- one element on from element `x` of elements `a` bytes long is element
  -- `x + 1`: the form a loop's invariant is stated in
  | .mul (.lit a) x, .lit n => if a = n then .mul (.lit a) (.add x (.lit 1)) else .add (.mul (.lit a) x) (.lit n)
  | a, b => .add a b

theorem den_plus (ρ : Env) (a b : Num) : (plus a b).den ρ = a.den ρ + b.den ρ := by
  unfold plus
  split
  · rfl
  · simp only [den]; omega
  · rfl
  · split
    · next h => subst h; simp only [den, Nat.mul_add, Nat.mul_one]
    · rfl
  · rfl

end Num

namespace Val

/-- An operation applied to a term, worked out at once where the term is a number. -/
def mk1 (f : Op1) : Val → Val
  | .lit n => .lit (f.den n)
  | a => .app1 f a

/-- An operation applied to two terms, worked out at once where both are numbers. -/
def mk2 (f : Op2) : Val → Val → Val
  | .lit m, .lit n => .lit (f.den m n)
  | a, b => .app2 f a b

theorem den_mk1 (ρ : Env) (f : Op1) (a : Val) : (mk1 f a).den ρ = f.den (a.den ρ) := by
  unfold mk1; split <;> rfl

theorem den_mk2 (ρ : Env) (f : Op2) (a b : Val) :
    (mk2 f a b).den ρ = f.den (a.den ρ) (b.den ρ) := by
  unfold mk2; split <;> rfl

end Val

mutual

/-- The type a term stands for. -/
def TyS.den (ρ : Env) : TyS → Ty
  | .int => .int
  | .eq v => .eq (v.den ρ)
  | .ptr S w off => .ptr (S.den ρ) w (off.den ρ)
  | .ref tag w off => .ref tag w (off.den ρ)
  | .nullable τ => .nullable (τ.den ρ)
  | .orErr τ => .orErr (τ.den ρ)
  | .str more => .str more
  | .atom i => ρ.ty.getD i .int

/-- The shape a term stands for. -/
def ShapeS.den (ρ : Env) : ShapeS → Shape
  | .mk size vals => ⟨size.den ρ, vals.den ρ⟩
  | .rep n E => (E.den ρ).rep (n.den ρ)
  | .atom i => ρ.shape.getD i ⟨0, []⟩

def ValsS.den (ρ : Env) : ValsS → List (Nat × Ty)
  | .nil => []
  | .cons o τ rest => (o, τ.den ρ) :: rest.den ρ

end

namespace FlagsS

/-- What a term says of the flags. -/
def den (ρ : Env) : FlagsS → Flags → Prop
  | .any => Flags.Any
  | .known => Flags.Known
  | .alu op .w64 a b => (· = (op.apply (a.den ρ) (b.den ρ)).2)
  | .alu op .w32 a b => (· = (op.apply ((a.den ρ).setWidth 32) ((b.den ρ).setWidth 32)).2)
  | .test a b => (· = Flags.ofResult (a.den ρ &&& b.den ρ) false false)
  | .lit f => (· = f)
  | .atom i => ρ.flags.getD i Flags.Any

end FlagsS

/-- The pieces of a stack that terms stand for, before whatever it goes on as. -/
def denShapes (ρ : Env) : List ShapeS → List Shape → List Shape
  | [], rest => rest
  | S :: σ, rest => S.den ρ :: denShapes ρ σ rest

/-- The owned blocks that terms stand for. -/
def denOwned (ρ : Env) : List (Val × ShapeS) → List (BitVec 64 × Shape) →
    List (BitVec 64 × Shape)
  | [], rest => rest
  | (a, S) :: bs, rest => (a.den ρ, S.den ρ) :: denOwned ρ bs rest

/-- What a stack goes on as, after the pieces written out. -/
def stackTail (ρ : Env) : Option Nat → List Shape
  | some i => ρ.stack.getD i []
  | none => []

/-- The owned blocks a context has besides those written out. -/
def ownedTail (ρ : Env) : Option Nat → List (BitVec 64 × Shape)
  | some i => ρ.owned.getD i []
  | none => []

namespace CtxS

/-- The context a term stands for. -/
def den (ρ : Env) (Γ : CtxS) : Ctx where
  regs := RegMap.get
    ⟨Γ.regs.rax.den ρ, Γ.regs.rcx.den ρ, Γ.regs.rdx.den ρ, Γ.regs.rbx.den ρ, Γ.regs.rsp.den ρ,
     Γ.regs.rbp.den ρ, Γ.regs.rsi.den ρ, Γ.regs.rdi.den ρ, Γ.regs.r8.den ρ, Γ.regs.r9.den ρ,
     Γ.regs.r10.den ρ, Γ.regs.r11.den ρ, Γ.regs.r12.den ρ, Γ.regs.r13.den ρ, Γ.regs.r14.den ρ,
     Γ.regs.r15.den ρ⟩
  stack := denShapes ρ Γ.stack (stackTail ρ Γ.stackRest)
  room := Γ.room.den ρ
  flags := Γ.flags.den ρ
  owned := denOwned ρ Γ.owned (ownedTail ρ Γ.ownedRest)
  above := Γ.above.den ρ

end CtxS

/-! ## Changing a context -/

end Sym

/-- A table of values with one of them replaced. -/
def RegMap.set {α : Type} (m : RegMap α) (r : Reg) (x : α) : RegMap α :=
  match r with
  | .rax => { m with rax := x }
  | .rcx => { m with rcx := x }
  | .rdx => { m with rdx := x }
  | .rbx => { m with rbx := x }
  | .rsp => { m with rsp := x }
  | .rbp => { m with rbp := x }
  | .rsi => { m with rsi := x }
  | .rdi => { m with rdi := x }
  | .r8 => { m with r8 := x }
  | .r9 => { m with r9 := x }
  | .r10 => { m with r10 := x }
  | .r11 => { m with r11 := x }
  | .r12 => { m with r12 := x }
  | .r13 => { m with r13 := x }
  | .r14 => { m with r14 := x }
  | .r15 => { m with r15 := x }

namespace Sym

namespace CtxS

def setReg (Γ : CtxS) (r : Reg) (τ : TyS) : CtxS := { Γ with regs := Γ.regs.set r τ }

theorem den_regs (ρ : Env) (Γ : CtxS) (r : Reg) : (Γ.den ρ).regs r = (Γ.regs.get r).den ρ := by
  cases r <;> rfl

theorem den_setReg (ρ : Env) (Γ : CtxS) (r : Reg) (τ : TyS) :
    (Γ.setReg r τ).den ρ = (Γ.den ρ).setReg r (τ.den ρ) := by
  have h : ((Γ.setReg r τ).den ρ).regs = ((Γ.den ρ).setReg r (τ.den ρ)).regs := by
    funext r'
    cases r <;> cases r' <;> rfl
  show (⟨_, _, _, _, _, _⟩ : Ctx) = ⟨_, _, _, _, _, _⟩
  congr 1

theorem den_setReg_flags (ρ : Env) (Γ : CtxS) (r : Reg) (τ : TyS) (fl : FlagsS) :
    CtxS.den ρ { Γ.setReg r τ with flags := fl }
      = { (Γ.den ρ).setReg r (τ.den ρ) with flags := fl.den ρ } := by
  show ({ (Γ.setReg r τ).den ρ with flags := fl.den ρ } : Ctx) = _
  rw [den_setReg]

end CtxS

/-! ## What a step leaves to be shown -/

/-- Something left to be shown, as a term. -/
inductive CondS
  /-- One number is at most another. -/
  | le (a b : Num)
  /-- Flags of which this is known have the carry flag defined. -/
  | cf (fl : FlagsS)

def CondS.den (ρ : Env) : CondS → Prop
  | .le a b => a.den ρ ≤ b.den ρ
  | .cf fl => ∀ f, fl.den ρ f → f.cf.isSome = true

/-- All of a list of things left to be shown. -/
def CondS.all (ρ : Env) : List CondS → Prop
  | [] => True
  | c :: cs => c.den ρ ∧ CondS.all ρ cs

/-- What reading the carry flag asks of the flags, where looking does not
settle it: nothing of an operation that does not read it, nothing where the
flags are known to be defined. -/
def carryConds (fl : FlagsS) (op : AluOp) : List CondS :=
  if op.readsCarry then
    match fl with
    | .known => []
    | fl => [.cf fl]
  else []

theorem carryConds_spec {ρ : Env} {fl : FlagsS} {op : AluOp}
    (h : CondS.all ρ (carryConds fl op)) :
    op.readsCarry = true → ∀ f, fl.den ρ f → f.cf.isSome = true := by
  intro hr f hf
  unfold carryConds at h
  simp only [hr, ↓reduceIte] at h
  split at h
  · have hk : Flags.Known f := hf
    simp only [Flags.Known, Flags.defined, Bool.and_eq_true] at hk
    exact hk.1.1.1
  · exact h.1 f hf

/-! ## The checker for one instruction that goes on to the next -/

/-- A constant operand as a value: extended with its sign to the width the
operation works at. -/
def immVal (w : Width) (imm : BitVec 32) : Val :=
  match w with
  | .w64 => .lit (imm.signExtend 64)
  | .w32 => .lit ((imm.signExtend 32).setWidth 64)

theorem cast_ctx {Ψ : MemTy} {next : BitVec 64} {Γ Δ Δ' : Ctx} {i : Instr}
    (h : Straight Ψ next Γ i Δ) (e : Δ' = Δ) : Straight Ψ next Γ i Δ' := e ▸ h

/-- The value a type says is held exactly, if it says so. -/
def exactly : TyS → Option Val
  | .eq v => some v
  | _ => none

theorem exactly_den {ρ : Env} {τ : TyS} {v : Val} (h : exactly τ = some v) :
    τ.den ρ = .eq (v.den ρ) := by
  cases τ <;> simp only [exactly, Option.some.injEq, reduceCtorEq] at h
  subst h; rfl

/-- The context after a two-operand operation whose result is only known to
be a number. -/
def afterAlu (Γ : CtxS) (op : AluOp) (d : Reg) : CtxS :=
  { (bif op.writesDst then Γ.setReg d .int else Γ) with flags := .known }

theorem den_afterAlu (ρ : Env) (Γ : CtxS) (op : AluOp) (d : Reg) :
    (afterAlu Γ op d).den ρ = (Γ.den ρ).afterAlu op d := by
  unfold afterAlu CtxOf.afterAlu
  cases op.writesDst
  · rfl
  · show ({ (Γ.setReg d .int).den ρ with flags := Flags.Known } : Ctx) = _
    rw [CtxS.den_setReg]; rfl


/-! ## The stack -/

/-- A number written as one. -/
def Num.lit? : Num → Option Nat
  | .lit n => some n
  | _ => none

theorem Num.lit?_den {ρ : Env} {a : Num} {n : Nat} (h : a.lit? = some n) : a.den ρ = n := by
  cases a <;> simp only [Num.lit?, Option.some.injEq, reduceCtorEq] at h
  subst h; rfl

/-- A number with `k` taken from it, and what is left to be shown for there
to be that much: nothing, where the number is written as something plus at
least `k`. -/
def Num.minus (a : Num) (k : Nat) : Num × List CondS :=
  match a with
  | .lit m => if k ≤ m then (.lit (m - k), []) else (.sub a (.lit k), [.le (.lit k) a])
  | .add x (.lit m) =>
    if m = k then (x, [])
    else if k ≤ m then (.add x (.lit (m - k)), [])
    else (.sub a (.lit k), [.le (.lit k) a])
  | a => (.sub a (.lit k), [.le (.lit k) a])

theorem Num.minus_spec {ρ : Env} {a : Num} {k : Nat} (h : CondS.all ρ (a.minus k).2) :
    a.den ρ = (a.minus k).1.den ρ + k := by
  revert h
  unfold Num.minus
  split
  · next m =>
    by_cases hk : k ≤ m
    · simp only [hk, ↓reduceIte]; intro _; simp only [Num.den]; omega
    · simp only [hk, ↓reduceIte]; intro h
      have := h.1; simp only [CondS.den, Num.den] at this ⊢; omega
  · next x m =>
    by_cases hm : m = k
    · simp only [hm, ↓reduceIte]; intro _; subst hm; rfl
    · by_cases hk : k ≤ m
      · simp only [hm, hk, ↓reduceIte]; intro _; simp only [Num.den]; omega
      · simp only [hm, hk, ↓reduceIte]; intro h
        have := h.1; simp only [CondS.den, Num.den] at this ⊢; omega
  · intro h; have := h.1; simp only [CondS.den, Num.den] at this ⊢; omega

/-- A value with a number added, added up at once where it can be. -/
def Val.plusLit : Val → BitVec 64 → Val
  | .lit m, d => .lit (m + d)
  | .add x (.lit m), d => if m + d = 0 then x else .add x (.lit (m + d))
  | a, d => if d = 0 then a else .add a (.lit d)

theorem Val.den_plusLit (ρ : Env) (a : Val) (d : BitVec 64) :
    (a.plusLit d).den ρ = a.den ρ + d := by
  unfold Val.plusLit
  split
  · rfl
  · next x m =>
    by_cases h : m + d = 0
    · simp only [h, ↓reduceIte]
      show x.den ρ = x.den ρ + m + d
      rw [BitVec.add_assoc, h]; exact (BitVec.add_zero _).symm
    · simp only [h, ↓reduceIte]
      show x.den ρ + (m + d) = x.den ρ + m + d
      rw [BitVec.add_assoc]
  · by_cases h : d = 0
    · subst h; simp only [↓reduceIte]; exact (BitVec.add_zero _).symm
    · simp only [h, ↓reduceIte]; rfl

/-- The type of a value after a known amount is added to it, where the type
is one the terms have a form for. -/
def TyS.shift? (τ : TyS) (d : BitVec 64) : Option TyS :=
  match τ with
  | .eq v => some (.eq (v.plusLit d))
  | .atom _ => none
  | _ => some .int

theorem TyS.den_shift {ρ : Env} {τ υ : TyS} {d : BitVec 64} (h : τ.shift? d = some υ) :
    υ.den ρ = (τ.den ρ).shift d := by
  cases τ <;> simp only [TyS.shift?, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    try rfl
  show Ty.eq _ = Ty.eq _
  rw [Val.den_plusLit]

namespace CtxS

/-- The context after the stack pointer has moved. -/
def moveSp (Γ : CtxS) (d : BitVec 64) : Option CtxS :=
  ((Γ.regs.get .rsp).shift? d).map (Γ.setReg .rsp ·)

theorem moveSp_spec {Γ Γ' : CtxS} {d : BitVec 64} (h : Γ.moveSp d = some Γ') :
    ∃ υ, Γ' = Γ.setReg .rsp υ ∧ ∀ ρ, υ.den ρ = ((Γ.den ρ).regs .rsp).shift d := by
  unfold moveSp at h
  cases hs : (Γ.regs.get .rsp).shift? d with
  | none => rw [hs] at h; cases h
  | some υ =>
    rw [hs] at h; cases h
    exact ⟨υ, rfl, fun ρ => by rw [TyS.den_shift hs, den_regs]⟩

/-- The meaning of a context with the stack pointer's type, the stack, the
room and the flags replaced. -/
theorem den_sp (ρ : Env) (Γ : CtxS) (υ : TyS) (σ : List ShapeS) (room : Num) (fl : FlagsS) :
    CtxS.den ρ { Γ.setReg .rsp υ with stack := σ, room := room, flags := fl }
      = { (Γ.den ρ).setReg .rsp (υ.den ρ) with
          stack := denShapes ρ σ (stackTail ρ Γ.stackRest), room := room.den ρ,
          flags := fl.den ρ } := by
  show ({ (Γ.setReg .rsp υ).den ρ with stack := _, room := _, flags := _ } : Ctx) = _
  rw [den_setReg]; rfl

end CtxS

/-- How many bytes a shape is, as a term. -/
def ShapeS.size : ShapeS → Num
  | .mk size _ => size
  | .rep n E => .mul n E.size
  | .atom i => .size i

theorem ShapeS.den_size (ρ : Env) : (S : ShapeS) → (S.den ρ).size = S.size.den ρ
  | .mk _ _ => rfl
  | .rep n E => by
    show n.den ρ * (E.den ρ).size = n.den ρ * E.size.den ρ
    rw [ShapeS.den_size ρ E]
  | .atom _ => rfl

namespace ValsS

/-- The type of the value that starts at a byte, if one does. -/
def find : ValsS → Nat → Option TyS
  | .nil, _ => none
  | .cons o τ rest, i => if o == i then some τ else rest.find i

theorem den_find (ρ : Env) : (vs : ValsS) → (i : Nat) →
    ((vs.den ρ).find? fun p => p.1 == i).map (·.2) = (vs.find i).map (TyS.den ρ)
  | .nil, _ => rfl
  | .cons o τ rest, i => by
    show (List.find? _ ((o, τ.den ρ) :: rest.den ρ)).map _ = _
    rw [List.find?_cons]
    unfold find
    cases h : o == i
    · exact den_find ρ rest i
    · rfl

/-- The typed values that keep clear of `n` bytes from `o`. -/
def clear : ValsS → Nat → Nat → ValsS
  | .nil, _, _ => .nil
  | .cons p τ rest, o, n =>
    if p + 8 ≤ o ∨ o + n ≤ p then .cons p τ (rest.clear o n) else rest.clear o n

theorem den_clear (ρ : Env) : (vs : ValsS) → (o n : Nat) →
    (vs.clear o n).den ρ = (vs.den ρ).filter (ShapeOf.clearOf o n)
  | .nil, _, _ => rfl
  | .cons p τ rest, o, n => by
    show _ = List.filter _ ((p, τ.den ρ) :: rest.den ρ)
    unfold clear
    by_cases h : p + 8 ≤ o ∨ o + n ≤ p
    · simp only [h, ↓reduceIte]
      rw [List.filter_cons_of_pos (by simpa [ShapeOf.clearOf] using h)]
      show (p, τ.den ρ) :: _ = _
      rw [den_clear ρ rest o n]
    · simp only [h, ↓reduceIte]
      rw [List.filter_cons_of_neg (by simpa [ShapeOf.clearOf] using h)]
      exact den_clear ρ rest o n

/-- The typed values with one of a given type at byte `i`, in place of
whatever reached into those eight bytes. -/
def set (vs : ValsS) (i : Nat) (τ : TyS) : ValsS := .cons i τ (vs.clear i 8)

end ValsS

/-- The typed value at a byte of a shape whose typed values are written out. -/
def ShapeS.valAt : ShapeS → Nat → Option TyS
  | .mk _ vals, i => vals.find i
  | _, _ => none

theorem ShapeS.den_valAt {ρ : Env} {S : ShapeS} {i : Nat} {τ : TyS} (h : S.valAt i = some τ) :
    (S.den ρ).valAt i = some (τ.den ρ) := by
  cases S with
  | mk size vals =>
    show ((vals.den ρ).find? fun p => p.1 == i).map (·.2) = _
    rw [ValsS.den_find, show vals.find i = some τ from h]; rfl
  | rep _ _ => cases h
  | atom _ => cases h

/-- The pieces of a stack as terms stand for a list of the same length before
whatever it goes on as. -/
theorem denShapes_getElem? (ρ : Env) : (σ : List ShapeS) → (rest : List Shape) → (j : Nat) →
    (S : ShapeS) → σ[j]? = some S → (denShapes ρ σ rest)[j]? = some (S.den ρ)
  | [], _, _, _, h => by cases h
  | T :: σ, rest, 0, S, h => by
    cases h; rfl
  | T :: σ, rest, j + 1, S, h => by
    show (denShapes ρ σ rest)[j]? = _
    exact denShapes_getElem? ρ σ rest j S h

theorem denShapes_set (ρ : Env) : (σ : List ShapeS) → (rest : List Shape) → (j : Nat) →
    (S S' : ShapeS) → σ[j]? = some S →
    denShapes ρ (σ.set j S') rest = (denShapes ρ σ rest).set j (S'.den ρ)
  | [], _, _, _, _, h => by cases h
  | T :: σ, rest, 0, S, S', _ => rfl
  | T :: σ, rest, j + 1, S, S', h => by
    show T.den ρ :: denShapes ρ (σ.set j S') rest = T.den ρ :: (denShapes ρ σ rest).set j _
    rw [denShapes_set ρ σ rest j S S' h]

/-- Which piece of the stack byte `d` above the stack pointer is in, counting
pieces from `k`, and how far into it: found where the pieces before it have
lengths that are numbers. -/
def pieceAt : List ShapeS → Nat → Nat → Option (Nat × ShapeS × Nat × Nat)
  | [], _, _ => none
  | S :: σ, k, d =>
    match S.size.lit? with
    | some sz => if d < sz then some (k, S, d, sz) else pieceAt σ (k + 1) (d - sz)
    | none => none

theorem pieceAt_spec (ρ : Env) (rest : List Shape) : (σ : List ShapeS) → (k₀ d : Nat) →
    {k : Nat} → {S : ShapeS} → {i sz : Nat} → pieceAt σ k₀ d = some (k, S, i, sz) →
    ∃ j, k = k₀ + j ∧ σ[j]? = some S ∧ d = stackOff (denShapes ρ σ rest) j + i ∧ i < sz ∧
      (S.den ρ).size = sz
  | [], _, _, _, _, _, _, h => by cases h
  | T :: σ, k₀, d, k, S, i, sz, h => by
    unfold pieceAt at h
    split at h
    · next tz ht =>
      have hT : (T.den ρ).size = tz := by rw [ShapeS.den_size, Num.lit?_den ht]
      split at h
      · next hlt =>
        cases h
        exact ⟨0, rfl, rfl, by simp, hlt, hT⟩
      · next hge =>
        obtain ⟨j, hk, hj, hd, hi, hs⟩ := pieceAt_spec ρ rest σ (k₀ + 1) (d - tz) h
        refine ⟨j + 1, by omega, hj, ?_, hi, hs⟩
        show d = (T.den ρ).size + stackOff (denShapes ρ σ rest) j + i
        omega
    · cases h

/-- The stack with the pieces at its top that come to `k` bytes taken off,
where their lengths are numbers. -/
def dropPieces : List ShapeS → Nat → Option (List ShapeS)
  | [], k => if k = 0 then some [] else none
  | S :: σ, k =>
    if k = 0 then some (S :: σ)
    else match S.size.lit? with
      | some sz => if sz ≤ k then dropPieces σ (k - sz) else none
      | none => none

theorem dropPieces_spec (ρ : Env) (tail : List Shape) : (σ : List ShapeS) → (k : Nat) →
    {rest : List ShapeS} → dropPieces σ k = some rest →
    ∃ top, denShapes ρ σ tail = top ++ denShapes ρ rest tail ∧ stackLen top = k
  | [], k, rest, h => by
    unfold dropPieces at h
    split at h
    · next hk => cases h; exact ⟨[], rfl, hk.symm⟩
    · cases h
  | S :: σ, k, rest, h => by
    unfold dropPieces at h
    split at h
    · next hk => cases h; exact ⟨[], rfl, hk.symm⟩
    · split at h
      · next sz hs =>
        split at h
        · next hle =>
          obtain ⟨top, he, hl⟩ := dropPieces_spec ρ tail σ (k - sz) h
          refine ⟨S.den ρ :: top, ?_, ?_⟩
          · show S.den ρ :: denShapes ρ σ tail = _
            rw [he]; rfl
          · show (S.den ρ).size + stackLen top = k
            rw [ShapeS.den_size, Num.lit?_den hs]; omega
        · cases h
      · cases h

/-- The stack a context's terms stand for. -/
theorem CtxS.den_stack (ρ : Env) (Γ : CtxS) :
    (Γ.den ρ).stack = denShapes ρ Γ.stack (stackTail ρ Γ.stackRest) := rfl

/-- A `push`. -/
def push (Γ : CtxS) (r : Reg) : Option (CtxS × List CondS) :=
  if r = .rsp then none
  else match Γ.moveSp (-8) with
    | some Γ' =>
      some ({ Γ' with
        stack := .mk (.lit 8) (.cons 0 (Γ.regs.get r) .nil) :: Γ.stack,
        room := (Γ.room.minus 8).1 }, (Γ.room.minus 8).2)
    | none => none

/-- A `pop`. -/
def pop (Γ : CtxS) (r : Reg) : Option (CtxS × List CondS) :=
  if r = .rsp then none
  else match Γ.moveSp 8 with
    | none => none
    | some Γ' =>
      match Γ.stack with
      | .mk (.lit 8) (.cons 0 τ .nil) :: σ =>
        some (CtxS.setReg { Γ' with stack := σ, room := Γ.room.plus (.lit 8) } r τ, [])
      | S :: σ =>
        if S.size.lit? = some 8 then
          some (CtxS.setReg { Γ' with stack := σ, room := Γ.room.plus (.lit 8) } r .int, [])
        else none
      | [] => none

/-- Making room on the stack. -/
def allocFrame (Γ : CtxS) (imm : BitVec 32) : Option (CtxS × List CondS) :=
  if imm.toNat < 2 ^ 31 then
    match Γ.moveSp (-BitVec.ofNat 64 imm.toNat) with
    | some Γ' =>
      some ({ Γ' with
        stack := .mk (.lit imm.toNat) .nil :: Γ.stack,
        room := (Γ.room.minus imm.toNat).1, flags := .known }, (Γ.room.minus imm.toNat).2)
    | none => none
  else none

/-- Giving room on the stack back. -/
def freeFrame (Γ : CtxS) (imm : BitVec 32) : Option (CtxS × List CondS) :=
  if imm.toNat < 2 ^ 31 then
    match dropPieces Γ.stack imm.toNat, Γ.moveSp (BitVec.ofNat 64 imm.toNat) with
    | some rest, some Γ' =>
      some ({ Γ' with stack := rest, room := Γ.room.plus (.lit imm.toNat), flags := .known }, [])
    | _, _ => none
  else none

/-- A 64-bit load from a place on the stack. -/
def loadStack (Γ : CtxS) (r : Reg) (disp : BitVec 32) : Option (CtxS × List CondS) :=
  if r = .rsp ∨ ¬ disp.toNat < 2 ^ 31 then none
  else match pieceAt Γ.stack 0 disp.toNat with
    | some (_, S, i, sz) =>
      match S.valAt i with
      | some τ => some (Γ.setReg r τ, [])
      | none => if i + 8 ≤ sz then some (Γ.setReg r .int, []) else none
    | none => none

/-- A 64-bit store to a place on the stack: the bytes take the type of what
is stored. -/
def storeStack (Γ : CtxS) (s : Reg) (disp : BitVec 32) : Option (CtxS × List CondS) :=
  if s = .rsp ∨ ¬ disp.toNat < 2 ^ 31 then none
  else match pieceAt Γ.stack 0 disp.toNat with
    | some (k, .mk size vals, i, sz) =>
      if i + 8 ≤ sz then
        some ({ Γ with stack := Γ.stack.set k (.mk size (vals.set i (Γ.regs.get s))) }, [])
      else none
    | _ => none

theorem byteDisp_toNat {disp : BitVec 32} (h : disp.toNat < 2 ^ 31) : byteDisp disp.toNat disp :=
  ⟨by simp, h⟩

theorem push_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS} {r : Reg}
    {x : CtxS × List CondS} (h : push Γ r = some x) (hn : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) (.push r) (x.1.den ρ) := by
  unfold push at h
  split at h
  · cases h
  · next hr =>
    split at h
    · next Γ' hm =>
      cases h
      obtain ⟨υ, rfl, hυ⟩ := CtxS.moveSp_spec hm
      refine cast_ctx (.push hr (Num.minus_spec hn)) ?_
      refine (CtxS.den_sp ρ Γ υ _ _ Γ.flags).trans ?_
      rw [hυ, CtxS.den_regs ρ Γ r]; rfl
    · cases h

theorem pop_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS} {r : Reg}
    {x : CtxS × List CondS} (h : pop Γ r = some x) :
    Straight Ψ next (Γ.den ρ) (.pop r) (x.1.den ρ) := by
  unfold pop at h
  split at h
  · cases h
  next hr =>
  split at h
  · cases h
  next Γ' hm =>
  obtain ⟨υ, rfl, hυ⟩ := CtxS.moveSp_spec hm
  have room : ∀ σ : List ShapeS, ∀ τ : TyS,
      (CtxS.setReg { Γ.setReg .rsp υ with stack := σ, room := Γ.room.plus (.lit 8) } r τ).den ρ
        = CtxOf.setReg { (Γ.den ρ).moveSp 8 with
            stack := denShapes ρ σ (stackTail ρ Γ.stackRest),
            room := (Γ.den ρ).room + 8 } r (τ.den ρ) := by
    intro σ τ
    rw [CtxS.den_setReg]
    refine congrArg (fun c => CtxOf.setReg c r (τ.den ρ)) ?_
    refine (CtxS.den_sp ρ Γ υ σ _ Γ.flags).trans ?_
    rw [hυ, Num.den_plus]; rfl
  split at h
  · next τ σ hst =>
    cases h
    rw [room]
    exact .pop hr (by rw [CtxS.den_stack, hst]; rfl)
  · next S σ _ hst =>
    split at h
    · next hsz =>
      cases h
      rw [room]
      exact .popPlain hr (by rw [CtxS.den_stack, hst]; rfl)
        (by rw [ShapeS.den_size, Num.lit?_den hsz])
    · cases h
  · cases h

theorem allocFrame_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS} {imm : BitVec 32}
    {x : CtxS × List CondS} (h : allocFrame Γ imm = some x) (hn : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) (.alu .sub .w64 (.rm_i (.reg .rsp) imm)) (x.1.den ρ) := by
  unfold allocFrame at h
  split at h
  · next hlt =>
    split at h
    · next Γ' hm =>
      cases h
      obtain ⟨υ, rfl, hυ⟩ := CtxS.moveSp_spec hm
      refine cast_ctx (.allocFrame (byteDisp_toNat hlt) (Num.minus_spec hn)) ?_
      refine (CtxS.den_sp ρ Γ υ _ _ .known).trans ?_
      rw [hυ]; rfl
    · cases h
  · cases h

theorem freeFrame_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS} {imm : BitVec 32}
    {x : CtxS × List CondS} (h : freeFrame Γ imm = some x) :
    Straight Ψ next (Γ.den ρ) (.alu .add .w64 (.rm_i (.reg .rsp) imm)) (x.1.den ρ) := by
  unfold freeFrame at h
  split at h
  · next hlt =>
    split at h
    · next rest Γ' hd hm =>
      cases h
      obtain ⟨υ, rfl, hυ⟩ := CtxS.moveSp_spec hm
      obtain ⟨top, he, hl⟩ := dropPieces_spec ρ (stackTail ρ Γ.stackRest) Γ.stack imm.toNat hd
      refine cast_ctx (.freeFrame (byteDisp_toNat hlt) (by rw [CtxS.den_stack]; exact he) hl) ?_
      refine (CtxS.den_sp ρ Γ υ _ _ .known).trans ?_
      rw [hυ, Num.den_plus]; rfl
    · cases h
  · cases h

theorem loadStack_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS} {r : Reg}
    {disp : BitVec 32} {x : CtxS × List CondS} (h : loadStack Γ r disp = some x) :
    Straight Ψ next (Γ.den ρ) (.mov .w64 (.r_m r (.sib (some .rsp) none disp))) (x.1.den ρ) := by
  unfold loadStack at h
  split at h
  · cases h
  next hc =>
  have hr : r ≠ .rsp := fun e => hc (.inl e)
  have hlt : disp.toNat < 2 ^ 31 := Decidable.of_not_not fun e => hc (.inr e)
  split at h
  · next k S i sz hp =>
    obtain ⟨j, _, hj, hoff, hi, hs⟩ := pieceAt_spec ρ _ _ _ _ hp
    have hat : StackAt (Γ.den ρ).stack j (S.den ρ) disp.toNat i :=
      ⟨by rw [CtxS.den_stack]; exact denShapes_getElem? ρ _ _ _ _ hj,
       by rw [CtxS.den_stack]; simpa using hoff⟩
    split at h
    · next τ hv =>
      cases h
      rw [CtxS.den_setReg]
      exact .loadStack hr (byteDisp_toNat hlt) hat (ShapeS.den_valAt hv)
    · split at h
      · next hsz =>
        cases h
        rw [CtxS.den_setReg]
        exact .loadInt hr (.slot (byteDisp_toNat hlt) hat (by rw [hs]; exact hsz))
      · cases h
  · cases h

theorem storeStack_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS} {s : Reg}
    {disp : BitVec 32} {x : CtxS × List CondS} (h : storeStack Γ s disp = some x) :
    Straight Ψ next (Γ.den ρ) (.mov .w64 (.rm_r (.mem (.sib (some .rsp) none disp)) s))
      (x.1.den ρ) := by
  unfold storeStack at h
  split at h
  · cases h
  next hc =>
  have hs : s ≠ .rsp := fun e => hc (.inl e)
  have hlt : disp.toNat < 2 ^ 31 := Decidable.of_not_not fun e => hc (.inr e)
  split at h
  · next k size vals i sz hp =>
    obtain ⟨j, hk, hj, hoff, hi, hsz⟩ := pieceAt_spec ρ _ _ _ _ hp
    have hkj : k = j := by omega
    subst hkj
    have hat : StackAt (Γ.den ρ).stack k ((ShapeS.mk size vals).den ρ) disp.toNat i :=
      ⟨by rw [CtxS.den_stack]; exact denShapes_getElem? ρ _ _ _ _ hj,
       by rw [CtxS.den_stack]; simpa using hoff⟩
    split at h
    · next hin =>
      cases h
      refine cast_ctx (.storeStack hs (byteDisp_toNat hlt) hat (by rw [hsz]; exact hin)) ?_
      have e : denShapes ρ (Γ.stack.set k (.mk size (vals.set i (Γ.regs.get s))))
          (stackTail ρ Γ.stackRest)
          = (Γ.den ρ).stack.set k (((ShapeS.mk size vals).den ρ).set i ((Γ.den ρ).regs s)) := by
        rw [denShapes_set ρ _ _ _ _ _ hj, CtxS.den_regs]
        show List.set _ k (⟨_, (i, _) :: (vals.clear i 8).den ρ⟩ : Shape) = _
        rw [ValsS.den_clear]; rfl
      show ({ Γ.den ρ with stack := denShapes ρ (Γ.stack.set k _) _ } : Ctx) = _
      rw [e]
    · cases h
  · cases h

/-- **The checker** for an instruction that goes on to the next. It gives the
context afterwards and what is left to be shown. -/
def step (next : BitVec 64) (Γ : CtxS) : Instr → Option (CtxS × List CondS)
  | .nop => some (Γ, [])
  | .mov .w64 (.rm_r (.reg d) s) =>
    if d = .rsp ∨ s = .rsp then none else some (Γ.setReg d (Γ.regs.get s), [])
  | .mov .w32 (.rm_r (.reg d) s) =>
    if d = .rsp then none
    else match exactly (Γ.regs.get s) with
      | some a =>
        if s = .rsp then some (Γ.setReg d .int, [])
        else some (Γ.setReg d (.eq (.mk1 .low32 a)), [])
      | none => some (Γ.setReg d .int, [])
  | .mov w (.rm_i (.reg d) imm) =>
    if d = .rsp then none
    else some (Γ.setReg d (.eq (.lit ((imm.signExtend w.bits).setWidth 64))), [])
  | .movAbs d imm => if d = .rsp then none else some (Γ.setReg d (.eq (.lit imm)), [])
  | .lea .w64 d (.rip disp) =>
    if d = .rsp then none else some (Γ.setReg d (.eq (.lit (next + disp.signExtend 64))), [])
  | .alu .sub .w64 (.rm_i (.reg .rsp) imm) => allocFrame Γ imm
  | .alu .add .w64 (.rm_i (.reg .rsp) imm) => freeFrame Γ imm
  | .mov .w64 (.r_m r (.sib (some .rsp) none disp)) => loadStack Γ r disp
  | .mov .w64 (.rm_r (.mem (.sib (some .rsp) none disp)) s) => storeStack Γ s disp
  | .push r => push Γ r
  | .pop r => pop Γ r
  | .alu op w (.rm_r (.reg d) s) =>
    if d = .rsp then none
    else if op = .xor ∧ d = s then
      some ({ Γ.setReg d (.eq (.lit 0)) with
        flags := .lit (Flags.ofResult (0 : BitVec w.bits) false false) }, [])
    else match exactly (Γ.regs.get d), exactly (Γ.regs.get s) with
      | some a, some b =>
        if s = .rsp ∨ op.readsCarry = true then some (afterAlu Γ op d, carryConds Γ.flags op)
        else
          some ({ (bif op.writesDst then Γ.setReg d (.eq (.mk2 (.alu op w) a b)) else Γ) with
            flags := .alu op w a b }, [])
      | _, _ => some (afterAlu Γ op d, carryConds Γ.flags op)
  | .alu op w (.rm_i (.reg d) imm) =>
    if d = .rsp then none
    else match Γ.regs.get d with
      | .eq a =>
        if op.readsCarry = true then some (afterAlu Γ op d, carryConds Γ.flags op)
        else
          some ({ (bif op.writesDst then
              Γ.setReg d (.eq (.mk2 (.alu op w) a (immVal w imm))) else Γ) with
            flags := .alu op w a (immVal w imm) }, [])
      | .int => some (afterAlu Γ op d, carryConds Γ.flags op)
      | .ptr S wr off =>
        -- a pointer moved on stays a pointer into its block, that much further in
        match op, w with
        | .add, .w64 =>
          if imm.toNat < 2 ^ 31 then
            some ({ Γ.setReg d (.ptr S wr (off.plus (.lit imm.toNat))) with flags := .known }, [])
          else none
        | _, _ => none
      | .str true =>
        match op, w with
        | .add, .w64 =>
          if imm = 1 then some ({ Γ.setReg d (.str false) with flags := .known }, []) else none
        | _, _ => none
      | _ => none
  | .test .w64 (.reg r) (.reg r') =>
    match exactly (Γ.regs.get r), exactly (Γ.regs.get r') with
    | some a, some b =>
      if r = .rsp ∨ r' = .rsp then some ({ Γ with flags := .known }, [])
      else some ({ Γ with flags := .test a b }, [])
    | _, _ => some ({ Γ with flags := .known }, [])
  | .test _ (.reg _) _ => some ({ Γ with flags := .known }, [])
  | _ => none

/-- **What the checker works out is a typing step.** -/
theorem step_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS} {i : Instr}
    {x : CtxS × List CondS} (h : step next Γ i = some x) (hn : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) i (x.1.den ρ) := by
  unfold step at h
  split at h
  · cases h; exact .nop
  · split at h
    · cases h
    · next hc =>
      cases h
      rw [CtxS.den_setReg, ← CtxS.den_regs]
      exact .movRR64 (fun e => hc (.inl e)) (fun e => hc (.inr e))
  · split at h
    · cases h
    · next hd =>
      split at h
      · next a ha =>
        split at h
        · cases h; rw [CtxS.den_setReg]; exact .movRR32 hd
        · next hs =>
          cases h
          refine cast_ctx (.mov32Exact hd hs (by rw [CtxS.den_regs, exactly_den ha])) ?_
          rw [CtxS.den_setReg]
          show CtxOf.setReg _ _ (.eq ((Val.mk1 .low32 a).den ρ)) = _
          rw [Val.den_mk1]; rfl
      · cases h; rw [CtxS.den_setReg]; exact .movRR32 hd
  · split at h
    · cases h
    · next hd => cases h; rw [CtxS.den_setReg]; exact .movRI hd
  · split at h
    · cases h
    · next hd => cases h; rw [CtxS.den_setReg]; exact .movAbs hd
  · split at h
    · cases h
    · next hd => cases h; rw [CtxS.den_setReg]; exact .leaRip hd
  · exact allocFrame_sound h hn
  · exact freeFrame_sound h
  · exact loadStack_sound h
  · exact storeStack_sound h
  · exact push_sound h hn
  · exact pop_sound h
  · next op w d s =>
    split at h
    · cases h
    next hd =>
    split at h
    · next hx =>
      obtain ⟨rfl, rfl⟩ := hx
      cases h
      exact cast_ctx (.xorSelf hd) (by rw [CtxS.den_setReg_flags]; rfl)
    next hx =>
    split at h
    · next a b ha hb =>
      split at h
      · cases h; rw [den_afterAlu]; exact .aluRR hd (carryConds_spec hn)
      · next hc =>
        cases h
        have hs : s ≠ .rsp := fun e => hc (.inl e)
        have hcarry : op.readsCarry = false := by
          cases hr : op.readsCarry with
          | false => rfl
          | true => exact absurd (.inr hr) hc
        have hΓd : (Γ.den ρ).regs d = .eq (a.den ρ) := by rw [CtxS.den_regs, exactly_den ha]
        have hΓs : (Γ.den ρ).regs s = .eq (b.den ρ) := by rw [CtxS.den_regs, exactly_den hb]
        cases w with
        | w64 =>
          refine cast_ctx (.aluExactRR hd hs hΓd hΓs hcarry) ?_
          cases op.writesDst
          · rfl
          · show CtxS.den ρ { Γ.setReg d _ with flags := _ } = _
            rw [CtxS.den_setReg_flags]
            show ({ (Γ.den ρ).setReg d (.eq ((Val.mk2 (.alu op .w64) a b).den ρ)) with
              flags := _ } : Ctx) = _
            rw [Val.den_mk2]; rfl
        | w32 =>
          refine cast_ctx (.aluExactRR32 hd hs hΓd hΓs hcarry) ?_
          cases op.writesDst
          · rfl
          · show CtxS.den ρ { Γ.setReg d _ with flags := _ } = _
            rw [CtxS.den_setReg_flags]
            show ({ (Γ.den ρ).setReg d (.eq ((Val.mk2 (.alu op .w32) a b).den ρ)) with
              flags := _ } : Ctx) = _
            rw [Val.den_mk2]; rfl
    · cases h; rw [den_afterAlu]; exact .aluRR hd (carryConds_spec hn)
  · next op w d imm _ _ =>
    split at h
    · cases h
    next hd =>
    split at h
    · next a hΓ =>
      split at h
      · cases h; rw [den_afterAlu]; exact .aluRI hd (carryConds_spec hn)
      · next hc =>
        cases h
        have hcarry : op.readsCarry = false := (Bool.not_eq_true _).mp hc
        have hΓd : (Γ.den ρ).regs d = .eq (a.den ρ) := by rw [CtxS.den_regs, hΓ]; rfl
        cases w with
        | w64 =>
          refine cast_ctx (.aluExact (imm := imm) hd hΓd hcarry) ?_
          cases op.writesDst
          · rfl
          · show CtxS.den ρ { Γ.setReg d _ with flags := _ } = _
            rw [CtxS.den_setReg_flags]
            show ({ (Γ.den ρ).setReg d
              (.eq ((Val.mk2 (.alu op .w64) a (immVal .w64 imm)).den ρ)) with flags := _ } : Ctx) = _
            rw [Val.den_mk2]; rfl
        | w32 =>
          refine cast_ctx (.aluExact32 (imm := imm) hd hΓd hcarry) ?_
          have e : ((imm.signExtend 32).setWidth 64).setWidth 32 = imm.signExtend 32 :=
            BitVec.setWidth_setWidth_of_le _ (by decide)
          cases op.writesDst
          · show ({ Γ.den ρ with flags := (· = (op.apply ((a.den ρ).setWidth 32)
              (((imm.signExtend 32).setWidth 64).setWidth 32)).2) } : Ctx) = _
            rw [e]; rfl
          · show CtxS.den ρ { Γ.setReg d _ with flags := _ } = _
            rw [CtxS.den_setReg_flags]
            show ({ (Γ.den ρ).setReg d
              (.eq ((Val.mk2 (.alu op .w32) a (immVal .w32 imm)).den ρ)) with
              flags := (· = (op.apply ((a.den ρ).setWidth 32)
                (((imm.signExtend 32).setWidth 64).setWidth 32)).2) } : Ctx) = _
            rw [Val.den_mk2]
            show ({ (Γ.den ρ).setReg d (.eq ((op.apply ((a.den ρ).setWidth 32)
              (((imm.signExtend 32).setWidth 64).setWidth 32)).1.setWidth 64)) with
              flags := _ } : Ctx) = _
            rw [e]; rfl
    · cases h; rw [den_afterAlu]; exact .aluRI hd (carryConds_spec hn)
    · next S wr off hΓ =>
      split at h
      · split at h
        · next hlt =>
          cases h
          have hΓd : (Γ.den ρ).regs d = .ptr (S.den ρ) wr (off.den ρ) := by
            rw [CtxS.den_regs, hΓ]; rfl
          refine cast_ctx (.addPtr (k := imm.toNat) (imm := imm) hd hΓd ⟨by simp, hlt⟩) ?_
          rw [CtxS.den_setReg_flags]
          show ({ (Γ.den ρ).setReg d (.ptr (S.den ρ) wr ((off.plus (.lit imm.toNat)).den ρ)) with
            flags := _ } : Ctx) = _
          rw [Num.den_plus]; rfl
        · cases h
      · cases h
    · next hΓ =>
      split at h
      · split at h
        · next hi =>
          cases h; subst hi
          have hΓd : (Γ.den ρ).regs d = .str true := by rw [CtxS.den_regs, hΓ]; rfl
          exact cast_ctx (.strNext hd hΓd) (by rw [CtxS.den_setReg_flags]; rfl)
        · cases h
      · cases h
    · cases h
  · next r r' =>
    split at h
    · next a b ha hb =>
      split at h
      · cases h; exact .testRM (.reg _)
      · next hc =>
        cases h
        exact .testExact (fun e => hc (.inl e)) (fun e => hc (.inr e))
          (by rw [CtxS.den_regs, exactly_den ha]) (by rw [CtxS.den_regs, exactly_den hb])
    · cases h; exact .testRM (.reg _)
  · cases h; exact .testRM (.reg _)
  · cases h

end Sym

end TypedAsm
