import TypedAsm.Loc
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
  | neg (w : Width)
  | not (w : Width)
  | popcnt (w : Width)
  | bswap (w : Width)
  /-- The sign of the low 32 bits, or of all 64, in every bit. -/
  | fill32
  | fill64
  /-- The low 32 bits extended with their sign. -/
  | sext32
  /-- A narrow value extended with zeros, or with its sign, at a width. -/
  | zx (w : Width) (sw : NarrowW)
  | sx (w : Width) (sw : NarrowW)
  deriving DecidableEq, Repr

/-- An operation of two values, likewise. -/
inductive Op2
  /-- The result of an arithmetic or logic operation at a width. -/
  | alu (op : AluOp) (w : Width)
  deriving DecidableEq, Repr

def Op1.den : Op1 → BitVec 64 → BitVec 64
  | .low32, a => (a.setWidth 32).setWidth 64
  | .neg w, a => (subBorrow 0 (a.setWidth w.bits) false).1.setWidth 64
  | .not w, a => (~~~(a.setWidth w.bits)).setWidth 64
  | .popcnt w, a => (popcount (a.setWidth w.bits)).setWidth 64
  | .bswap w, a => (TypedAsm.bswap w (a.setWidth w.bits)).setWidth 64
  | .fill32, a => (signFill (a.setWidth 32)).setWidth 64
  | .fill64, a => signFill a
  | .sext32, a => (a.setWidth 32).signExtend 64
  | .zx w sw, a => ((a.setWidth sw.bits).setWidth w.bits).setWidth 64
  | .sx w sw, a => ((a.setWidth sw.bits).signExtend w.bits).setWidth 64

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
  /-- At least the named ones are defined. -/
  | defined (cf zf sf of : Bool)
  /-- They are exactly what an arithmetic or logic operation left. -/
  | alu (op : AluOp) (w : Width) (a b : Val)
  /-- They are exactly what a `test` of two values left. -/
  | test (a b : Val)
  /-- They are exactly what negating a value, or counting its bits, left. -/
  | neg (w : Width) (a : Val)
  | popcnt (w : Width) (a : Val)
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
  deriving Inhabited

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

/-- Two numbers added, whichever way round the one that is written is. -/
def plus' : Num → Num → Num
  | .lit 0, b => b
  | .lit m, .add x (.lit n) => .add x (.lit (m + n))
  | a, b => plus a b

theorem den_plus' (ρ : Env) (a b : Num) : (plus' a b).den ρ = a.den ρ + b.den ρ := by
  unfold plus'
  split
  · simp only [den]; omega
  · simp only [den]; omega
  · exact den_plus ρ a b

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
  | .defined cf zf sf of => Flags.Defined cf zf sf of
  | .alu op .w64 a b => (· = (op.apply (a.den ρ) (b.den ρ)).2)
  | .alu op .w32 a b => (· = (op.apply ((a.den ρ).setWidth 32) ((b.den ρ).setWidth 32)).2)
  | .test a b => (· = Flags.ofResult (a.den ρ &&& b.den ρ) false false)
  | .neg w a => (· = (subBorrow 0 ((a.den ρ).setWidth w.bits) false).2)
  | .popcnt w a =>
    (· = ⟨some false, some ((a.den ρ).setWidth w.bits == 0), some false, some false⟩)
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

theorem den_setReg_mk1 (ρ : Env) (Γ : CtxS) (r : Reg) (f : Op1) (a : Val) :
    (Γ.setReg r (.eq (.mk1 f a))).den ρ = (Γ.den ρ).setReg r (.eq (f.den (a.den ρ))) := by
  rw [den_setReg]
  show CtxOf.setReg _ _ (.eq ((Val.mk1 f a).den ρ)) = _
  rw [Val.den_mk1]

theorem den_setReg_mk1_flags (ρ : Env) (Γ : CtxS) (r : Reg) (f : Op1) (a : Val) (fl : FlagsS) :
    CtxS.den ρ { Γ.setReg r (.eq (.mk1 f a)) with flags := fl }
      = { (Γ.den ρ).setReg r (.eq (f.den (a.den ρ))) with flags := fl.den ρ } := by
  rw [den_setReg_flags]
  show ({ CtxOf.setReg _ _ (.eq ((Val.mk1 f a).den ρ)) with flags := _ } : Ctx) = _
  rw [Val.den_mk1]

end CtxS

/-! ## What a step leaves to be shown -/

/-- Something left to be shown, as a term. -/
inductive CondS
  /-- One number is at most another. -/
  | le (a b : Num)
  /-- One number is less than another. -/
  | lt (a b : Num)
  /-- Flags of which this is known have the carry flag defined. -/
  | cf (fl : FlagsS)

def CondS.den (ρ : Env) : CondS → Prop
  | .le a b => a.den ρ ≤ b.den ρ
  | .lt a b => a.den ρ < b.den ρ
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

/-! ## Operands in memory

The checker finds where an operand's bytes are by looking at the terms: the
block a pointer points into, from the pointer's type. What it finds is a
`Loc`, and what the instruction needs of the place, that so many bytes are
inside it, is worked out where the numbers are written and left to be shown
where they are not. -/

/-- The kind of place an operand is in, as terms. -/
inductive KindS
  | ptr (writable : Bool)
  | owned (k : Nat) (a : Val)
  | piece (k : Nat)
  | block (writable : Bool)

def KindS.den (ρ : Env) : KindS → Kind
  | .ptr w => .ptr w
  | .owned k a => .owned k (a.den ρ)
  | .piece k => .piece k
  | .block w => .block w

/-- Where an operand's bytes are, as terms: the kind of place, the shape of
the block or piece, and the byte. -/
structure PlaceS where
  kind : KindS
  shape : ShapeS
  off : Num

/-- How many bytes on from its base an operand reaches: its displacement,
and with an index that holds an exactly known value, that value scaled. -/
def reach (Γ : CtxS) : Option (IndexReg × Scale) → BitVec 32 → Option Num
  | none, disp => if disp.toNat < 2 ^ 31 then some (.lit disp.toNat) else none
  | some (x, sc), disp =>
    if disp.toNat < 2 ^ 31 then
      match exactly (Γ.regs.get x.toReg) with
      | some c => some (Num.plus (.mul (.toNat c) (.lit (2 ^ sc.shift))) (.lit disp.toNat))
      | none => none
    else none

theorem reach_none {ρ : Env} {Γ : CtxS} {disp : BitVec 32} {d : Num}
    (h : reach Γ none disp = some d) : byteDisp (d.den ρ) disp := by
  simp only [reach] at h
  split at h
  · next hlt => cases h; exact byteDisp_toNat hlt
  · cases h

theorem reach_some {ρ : Env} {Γ : CtxS} {x : IndexReg} {sc : Scale} {disp : BitVec 32} {d : Num}
    (h : reach Γ (some (x, sc)) disp = some d) :
    ∃ c, (Γ.den ρ).regs x.toReg = .eq c ∧
      (c <<< sc.shift) + disp.signExtend 64 = BitVec.ofNat 64 (d.den ρ) := by
  simp only [reach] at h
  split at h
  · next hlt =>
    split at h
    · next c hc =>
      cases h
      refine ⟨c.den ρ, by rw [CtxS.den_regs, exactly_den hc], ?_⟩
      rw [Num.den_plus]
      exact Check.index_bytes (c.den ρ) sc disp hlt
    · cases h
  · cases h

/-! ### Blocks the context owns

An address is a term. Taken apart into the terms it is a sum of, it is seen
to be in an owned block when the block's own address is among them: what is
left over is how far into the block it is. -/

/-- The sum of what a list of terms stand for. -/
def sumV (ρ : Env) : List Val → BitVec 64
  | [] => 0
  | t :: ts => t.den ρ + sumV ρ ts

theorem sumV_append (ρ : Env) : (as bs : List Val) → sumV ρ (as ++ bs) = sumV ρ as + sumV ρ bs
  | [], bs => by simp [sumV]
  | a :: as, bs => by
    show a.den ρ + sumV ρ (as ++ bs) = a.den ρ + sumV ρ as + sumV ρ bs
    rw [sumV_append ρ as bs, BitVec.add_assoc]

/-- The terms a value is the sum of, and the number among them. -/
def Val.summands : Val → List Val × BitVec 64
  | .lit n => ([], n)
  | .add a b => (a.summands.1 ++ b.summands.1, a.summands.2 + b.summands.2)
  | .app2 (.alu .add .w64) a b => (a.summands.1 ++ b.summands.1, a.summands.2 + b.summands.2)
  | v => ([v], 0)

theorem Val.den_summands (ρ : Env) : (v : Val) → v.den ρ = sumV ρ v.summands.1 + v.summands.2 := by
  intro v
  induction v with
  | lit n => simp [Val.summands, sumV, Val.den]
  | var i => simp [Val.summands, sumV]
  | add a b iha ihb =>
    simp only [Val.summands, Val.den, sumV_append]
    rw [iha, ihb]; ac_rfl
  | shl a k _ => simp [Val.summands, sumV]
  | app1 f a _ => simp [Val.summands, sumV]
  | app2 f a b iha ihb =>
    cases f with
    | alu op w =>
      cases op <;> cases w <;> try (simp [Val.summands, sumV])
      simp only [Val.den, Op2.den, sumV_append, AluOp.apply, addCarry_fst]
      rw [iha, ihb]; ac_rfl

/-- A list of terms with one occurrence of a term taken out. -/
def removeV (a : Val) : List Val → Option (List Val)
  | [] => none
  | t :: ts => if t = a then some ts else (removeV a ts).map (t :: ·)

theorem removeV_spec (ρ : Env) (a : Val) : (l : List Val) → {l' : List Val} →
    removeV a l = some l' → sumV ρ l = a.den ρ + sumV ρ l'
  | [], _, h => by cases h
  | t :: ts, l', h => by
    unfold removeV at h
    split at h
    · next e => cases h; subst e; rfl
    · cases hr : removeV a ts with
      | none => rw [hr] at h; cases h
      | some r =>
        rw [hr] at h; cases h
        show t.den ρ + sumV ρ ts = a.den ρ + (t.den ρ + sumV ρ r)
        rw [removeV_spec ρ a ts hr]; ac_rfl

/-- A list of terms with one occurrence of each of some terms taken out. -/
def removeAll : List Val → List Val → Option (List Val)
  | [], l => some l
  | a :: as, l =>
    match removeV a l with
    | some l' => removeAll as l'
    | none => none

theorem removeAll_spec (ρ : Env) : (as l : List Val) → {l' : List Val} →
    removeAll as l = some l' → sumV ρ l = sumV ρ as + sumV ρ l'
  | [], l, _, h => by cases h; simp [sumV]
  | a :: as, l, l', h => by
    unfold removeAll at h
    split at h
    · next r hr =>
      show _ = a.den ρ + sumV ρ as + sumV ρ l'
      rw [removeV_spec ρ a l hr, removeAll_spec ρ as r h, BitVec.add_assoc]
    · cases h

/-- A term of an address as a number of bytes: an index scaled is that many. -/
def offTerm : Val → Num
  | .shl c s => .mul (.toNat c) (.lit (2 ^ s))
  | t => .toNat t

theorem offTerm_spec (ρ : Env) (t : Val) : BitVec.ofNat 64 ((offTerm t).den ρ) = t.den ρ := by
  unfold offTerm
  split
  · next c s =>
    apply BitVec.eq_of_toNat_eq
    simp only [Num.den, Val.den, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  · simp [Num.den]

/-- The terms of an address left over, as a number of bytes. -/
def offNum : List Val → Num
  | [] => .lit 0
  | t :: ts => (offTerm t).plus' (offNum ts)

theorem offNum_spec (ρ : Env) : (ts : List Val) → BitVec.ofNat 64 ((offNum ts).den ρ) = sumV ρ ts
  | [] => rfl
  | t :: ts => by
    show BitVec.ofNat 64 (((offTerm t).plus' (offNum ts)).den ρ) = t.den ρ + sumV ρ ts
    rw [Num.den_plus', BitVec.ofNat_add, offTerm_spec, offNum_spec ρ ts]

/-- The address a memory operand names, where the registers it is computed
from hold exactly known values. -/
def ea (Γ : CtxS) : Mem → Option Val
  | .sib (some b) none disp =>
    if b = .rsp then none
    else match exactly (Γ.regs.get b) with
      | some v => some (.add v (.lit (disp.signExtend 64)))
      | none => none
  | .sib (some b) (some (x, sc)) disp =>
    if b = .rsp then none
    else match exactly (Γ.regs.get b), exactly (Γ.regs.get x.toReg) with
      | some v, some c => some (.add (.add v (.shl c sc.shift)) (.lit (disp.signExtend 64)))
      | _, _ => none
  | .sib none none disp => some (.lit (disp.signExtend 64))
  | .sib none (some (x, sc)) disp =>
    match exactly (Γ.regs.get x.toReg) with
    | some c => some (.add (.shl c sc.shift) (.lit (disp.signExtend 64)))
    | none => none
  | .rip _ => none

theorem ea_spec {ρ : Env} {Γ : CtxS} {m : Mem} {p : Val} (h : ea Γ m = some p) :
    EaIs (Γ.den ρ) m (p.den ρ) := by
  unfold ea at h
  split at h
  · split at h
    · cases h
    · next hb =>
      split at h
      · next v hv => cases h; exact .base hb (by rw [CtxS.den_regs, exactly_den hv])
      · cases h
  · split at h
    · cases h
    · next hb =>
      split at h
      · next v c hv hc =>
        cases h
        exact .indexed hb (by rw [CtxS.den_regs, exactly_den hv])
          (by rw [CtxS.den_regs, exactly_den hc])
      · cases h
  · cases h; exact .abs
  · split at h
    · next c hc => cases h; exact .absIndexed (by rw [CtxS.den_regs, exactly_den hc])
    · cases h
  · cases h

theorem addr_split (A R kp kb : BitVec 64) : A + R + kp = A + kb + (R + (kp - kb)) := by
  calc A + R + kp = A + (R + (kp - kb + kb)) := by rw [BitVec.sub_add_cancel, BitVec.add_assoc]
    _ = A + kb + (R + (kp - kb)) := by ac_rfl

/-- How far into a block at `a` the address `p` is, given the terms of `p`
left when those of `a` are taken out. -/
def ownedOff (r : List Val) (p a : Val) : Num :=
  (offNum r).plus' (.lit (p.summands.2 - a.summands.2).toNat)

/-- Whether an address so far into a block is taken to be in it: not where
the distance is a number and the block is shorter. -/
def ownedHere (r : List Val) (j : Num) (S : ShapeS) : Bool :=
  match r, j.lit?, S.size.lit? with
  | [], some jn, some sz => decide (jn < sz)
  | _, _, _ => true

/-- The owned block an address is in and how far in: the first whose own
address is among the terms of the address, and, where the rest is a number,
that has that many bytes. -/
def findOwned (p : Val) : List (Val × ShapeS) → Nat → Option (Nat × Val × ShapeS × Num)
  | [], _ => none
  | (a, S) :: rest, k =>
    match removeAll a.summands.1 p.summands.1 with
    | some r =>
      if ownedHere r (ownedOff r p a) S then some (k, a, S, ownedOff r p a)
      else findOwned p rest (k + 1)
    | none => findOwned p rest (k + 1)

theorem denOwned_getElem? (ρ : Env) : (l : List (Val × ShapeS)) →
    (tail : List (BitVec 64 × Shape)) → (i : Nat) → (a : Val) → (S : ShapeS) →
    l[i]? = some (a, S) → (denOwned ρ l tail)[i]? = some (a.den ρ, S.den ρ)
  | [], _, _, _, _, h => by cases h
  | (b, T) :: l, tail, 0, a, S, h => by cases h; rfl
  | (b, T) :: l, tail, i + 1, a, S, h => by
    show (denOwned ρ l tail)[i]? = _
    exact denOwned_getElem? ρ l tail i a S h

theorem findOwned_spec (ρ : Env) (p : Val) : (l : List (Val × ShapeS)) → (k₀ : Nat) →
    {k : Nat} → {a : Val} → {S : ShapeS} → {j : Num} → findOwned p l k₀ = some (k, a, S, j) →
    ∃ i, k = k₀ + i ∧ l[i]? = some (a, S) ∧ p.den ρ = a.den ρ + BitVec.ofNat 64 (j.den ρ)
  | [], _, _, _, _, _, h => by cases h
  | (b, T) :: l, k₀, k, a, S, j, h => by
    have later : findOwned p l (k₀ + 1) = some (k, a, S, j) →
        ∃ i, k = k₀ + i ∧ ((b, T) :: l)[i]? = some (a, S) ∧
          p.den ρ = a.den ρ + BitVec.ofNat 64 (j.den ρ) := fun h' => by
      obtain ⟨i, hk, hi, hp⟩ := findOwned_spec ρ p l (k₀ + 1) h'
      exact ⟨i + 1, by omega, hi, hp⟩
    unfold findOwned at h
    split at h
    · next r hr =>
      split at h
      · cases h
        refine ⟨0, rfl, rfl, ?_⟩
        unfold ownedOff
        rw [Num.den_plus', BitVec.ofNat_add, offNum_spec]
        have hp := Val.den_summands ρ p
        have hb := Val.den_summands ρ b
        have hrm := removeAll_spec ρ _ _ hr
        show _ = _ + (_ + BitVec.ofNat 64 (p.summands.2 - b.summands.2).toNat)
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, hp, hb, hrm]
        exact addr_split _ _ _ _
      · exact later h
    · exact later h

/-! ### The stack, through an index

A byte so far above the stack pointer, plus an index, is past every piece
whose length is a number no greater than how far it is without the index:
the index only takes it further. The first piece it is not seen to be past
is the one the index runs over. -/

/-- The piece of the stack a byte `D` above the stack pointer plus an index
is taken to be in, counting pieces from `k`, and how far into it without the
index. -/
def pieceIdx : List ShapeS → Nat → Nat → Option (Nat × ShapeS × Nat)
  | [], _, _ => none
  | S :: σ, k, D =>
    match S.size.lit? with
    | some sz => if sz ≤ D then pieceIdx σ (k + 1) (D - sz) else some (k, S, D)
    | none => some (k, S, D)

theorem pieceIdx_spec (ρ : Env) (rest : List Shape) : (σ : List ShapeS) → (k₀ D : Nat) →
    {k : Nat} → {S : ShapeS} → {R : Nat} → pieceIdx σ k₀ D = some (k, S, R) →
    ∃ j, k = k₀ + j ∧ σ[j]? = some S ∧ D = stackOff (denShapes ρ σ rest) j + R
  | [], _, _, _, _, _, h => by cases h
  | T :: σ, k₀, D, k, S, R, h => by
    unfold pieceIdx at h
    split at h
    · next tz ht =>
      have hT : (T.den ρ).size = tz := by rw [ShapeS.den_size, Num.lit?_den ht]
      split at h
      · next hle =>
        obtain ⟨j, hk, hj, hd⟩ := pieceIdx_spec ρ rest σ (k₀ + 1) (D - tz) h
        refine ⟨j + 1, by omega, hj, ?_⟩
        show D = (T.den ρ).size + stackOff (denShapes ρ σ rest) j + R
        omega
      · cases h; exact ⟨0, rfl, rfl, by simp⟩
    · cases h; exact ⟨0, rfl, rfl, by simp⟩

/-- Where an operand reached through the stack pointer is. -/
def locateSp (Γ : CtxS) (ix : Option (IndexReg × Scale)) (disp : BitVec 32) :
    Option (PlaceS × List CondS) :=
  if disp.toNat < 2 ^ 31 then
    match ix with
    | none =>
      match pieceAt Γ.stack 0 disp.toNat with
      | some (k, S, i, _) => some (⟨.piece k, S, .lit i⟩, [])
      | none => none
    | some (x, sc) =>
      match exactly (Γ.regs.get x.toReg), pieceIdx Γ.stack 0 disp.toNat with
      | some c, some (k, S, R) =>
        some (⟨.piece k, S, Num.plus (.mul (.toNat c) (.lit (2 ^ sc.shift))) (.lit R)⟩, [])
      | _, _ => none
  else none

theorem locateSp_spec {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    {ix : Option (IndexReg × Scale)} {disp : BitVec 32} {x : PlaceS × List CondS}
    (h : locateSp Γ ix disp = some x) :
    Loc Ψ next (Γ.den ρ) (.sib (some .rsp) ix disp) (x.1.kind.den ρ) (x.1.shape.den ρ)
      (x.1.off.den ρ) := by
  unfold locateSp at h
  split at h
  · next hlt =>
    split at h
    · split at h
      · next k S i sz hp =>
        cases h
        obtain ⟨j, hk, hj, hoff, _, _⟩ := pieceAt_spec ρ (stackTail ρ Γ.stackRest) _ _ _ hp
        have hkj : k = j := by omega
        subst hkj
        exact .slot (byteDisp_toNat hlt)
          ⟨by rw [CtxS.den_stack]; exact denShapes_getElem? ρ _ _ _ _ hj,
           by rw [CtxS.den_stack]; exact hoff⟩
      · cases h
    · next xr sc =>
      split at h
      · next c k S R hc hp =>
        cases h
        obtain ⟨j, hk, hj, hoff⟩ := pieceIdx_spec ρ (stackTail ρ Γ.stackRest) _ _ _ hp
        have hkj : k = j := by omega
        subst hkj
        refine .slotIndexed (d := (c.den ρ).toNat * 2 ^ sc.shift + disp.toNat)
          (by rw [CtxS.den_regs, exactly_den hc]) (Check.index_bytes _ sc disp hlt)
          ⟨by rw [CtxS.den_stack]; exact denShapes_getElem? ρ _ _ _ _ hj, ?_⟩
        rw [CtxS.den_stack, Num.den_plus]
        show _ = _ + ((c.den ρ).toNat * 2 ^ sc.shift + R)
        omega
      · cases h
  · cases h

/-- What is left to be shown for a number to be one a register can hold. -/
def fits64 (j : Num) : Option (List CondS) :=
  match j.lit? with
  | some n => if n < 2 ^ 64 then some [] else none
  | none => some [.lt j (.lit (2 ^ 64))]

theorem fits64_spec {ρ : Env} {j : Num} {cs : List CondS} (h : fits64 j = some cs)
    (hc : CondS.all ρ cs) : j.den ρ < 2 ^ 64 := by
  unfold fits64 at h
  split at h
  · next n hn =>
    split at h
    · next hlt => rw [Num.lit?_den hn]; exact hlt
    · cases h
  · cases h; exact hc.1

/-- **Where an operand's bytes are**, found from the context's terms, and
what is left to be shown for it to be so. -/
def locate (Γ : CtxS) (m : Mem) : Option (PlaceS × List CondS) :=
  match m with
  | .sib (some b) ix disp =>
    if b = .rsp then locateSp Γ ix disp
    else match Γ.regs.get b, reach Γ ix disp with
      | .ptr S w off, some d => some (⟨.ptr w, S, off.plus d⟩, [])
      | .eq _, _ =>
        -- an exactly known address: in a block the context owns
        match ea Γ m with
        | some p =>
          match findOwned p Γ.owned 0 with
          | some (k, a, S, j) => (fits64 j).map fun cs => (⟨.owned k a, S, j⟩, cs)
          | none => none
        | none => none
      | _, _ => none
  | _ => none

theorem CtxS.den_owned (ρ : Env) (Γ : CtxS) :
    (Γ.den ρ).owned = denOwned ρ Γ.owned (ownedTail ρ Γ.ownedRest) := rfl

theorem locate_spec {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS} {m : Mem}
    {x : PlaceS × List CondS} (h : locate Γ m = some x) (hc : CondS.all ρ x.2) :
    Loc Ψ next (Γ.den ρ) m (x.1.kind.den ρ) (x.1.shape.den ρ) (x.1.off.den ρ) := by
  unfold locate at h
  split at h
  · next b ix disp =>
    split at h
    · next hb => subst hb; exact locateSp_spec h
    next hb =>
    split at h
    · next S w off d hΓ hr =>
      cases h
      have hΓ' : (Γ.den ρ).regs b = .ptr (S.den ρ) w (off.den ρ) := by
        rw [CtxS.den_regs, hΓ]; rfl
      show Loc Ψ next _ _ (.ptr w) (S.den ρ) ((off.plus d).den ρ)
      rw [Num.den_plus]
      cases ix with
      | none => exact .field hb hΓ' (reach_none hr)
      | some xs =>
        obtain ⟨c, hx, he⟩ := reach_some (ρ := ρ) (x := xs.1) (sc := xs.2) hr
        exact .indexed hb hΓ' hx he
    · split at h
      · next p hea =>
        split at h
        · next k a S j hf =>
          cases hfit : fits64 j with
          | none => rw [hfit] at h; cases h
          | some cs =>
            rw [hfit] at h; cases h
            obtain ⟨i, hk, hi, hp⟩ := findOwned_spec ρ p Γ.owned 0 hf
            have hki : k = i := by omega
            subst hki
            exact .owned (ea_spec hea)
              (by rw [CtxS.den_owned]; exact denOwned_getElem? ρ _ _ _ _ _ hi) hp
              (fits64_spec hfit hc)
        · cases h
      · cases h
    · cases h
  · cases h

/-- What is left to be shown for `n` bytes from byte `o` to be inside a
block of a given length: nothing where the numbers are written and it is so. -/
def within (o : Num) (n : Nat) (size : Num) : Option (List CondS) :=
  match (o.plus (.lit n)).lit?, size.lit? with
  | some a, some b => if a ≤ b then some [] else none
  | _, _ => some [.le (o.plus (.lit n)) size]

theorem within_spec {ρ : Env} {o : Num} {n : Nat} {size : Num} {cs : List CondS}
    (h : within o n size = some cs) (hc : CondS.all ρ cs) : o.den ρ + n ≤ size.den ρ := by
  unfold within at h
  split at h
  · next a b ha hb =>
    split at h
    · next hle =>
      have := Num.lit?_den (ρ := ρ) ha
      rw [Num.den_plus] at this
      rw [Num.lit?_den hb]
      show o.den ρ + n ≤ b
      have e : (Num.lit n).den ρ = n := rfl
      omega
    · cases h
  · cases h
    have := hc.1
    simp only [CondS.den, Num.den_plus] at this
    exact this

/-- Whether no typed value keeps clear of... -/
def ValsS.allClear : ValsS → Nat → Nat → Bool
  | .nil, _, _ => true
  | .cons p _ rest, o, n => (decide (p + 8 ≤ o) || decide (o + n ≤ p)) && rest.allClear o n

theorem ValsS.den_allClear (ρ : Env) : (vs : ValsS) → (o n : Nat) →
    (vs.den ρ).all (ShapeOf.clearOf o n) = vs.allClear o n
  | .nil, _, _ => rfl
  | .cons p τ rest, o, n => by
    show List.all ((p, τ.den ρ) :: rest.den ρ) _ = _
    rw [List.all_cons, ValsS.den_allClear ρ rest o n]
    rfl

/-- What a shape's terms say is at a byte: a typed value, plain bytes, or
nothing that can be read off them. -/
def ShapeS.look : ShapeS → Num → Option (Option TyS)
  | .mk _ .nil, _ => some none
  | .mk _ vals, .lit i => some (vals.find i)
  | _, _ => none

theorem ShapeS.look_typed {ρ : Env} {S : ShapeS} {o : Num} {τ : TyS}
    (h : S.look o = some (some τ)) : (S.den ρ).valAt (o.den ρ) = some (τ.den ρ) := by
  unfold ShapeS.look at h
  split at h
  · cases h
  · next sz vals i _ =>
    exact ShapeS.den_valAt (S := .mk sz vals) (Option.some.inj h)
  · cases h

/-- Whether `n` bytes of a shape are seen from its terms to be plain. -/
def ShapeS.free : ShapeS → Num → Nat → Bool
  | .mk _ .nil, _, _ => true
  | .mk _ vals, .lit i, n => vals.allClear i n
  | _, _, _ => false

theorem ShapeS.den_free {ρ : Env} {S : ShapeS} {o : Num} {n : Nat} (h : S.free o n = true) :
    (S.den ρ).free (o.den ρ) n = true := by
  unfold ShapeS.free at h
  split at h
  · rfl
  · next sz vals i _ =>
    show (vals.den ρ).all _ = true
    rw [ValsS.den_allClear]; exact h
  · cases h

/-- What is left to be shown for `n` bytes to be read from an operand. -/
def reads (Γ : CtxS) (n : Nat) (m : Mem) : Option (List CondS) :=
  match locate Γ m with
  | some (pl, cs) => (within pl.off n pl.shape.size).map (cs ++ ·)
  | none => none

theorem CondS.all_append {ρ : Env} : (as bs : List CondS) →
    CondS.all ρ (as ++ bs) → CondS.all ρ as ∧ CondS.all ρ bs
  | [], _, h => ⟨trivial, h⟩
  | _ :: as, bs, h => ⟨⟨h.1, (CondS.all_append as bs h.2).1⟩, (CondS.all_append as bs h.2).2⟩

theorem reads_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS} {n : Nat} {m : Mem}
    {cs : List CondS} (h : reads Γ n m = some cs) (hc : CondS.all ρ cs) :
    ReadOk Ψ next (Γ.den ρ) n (.mem m) := by
  unfold reads at h
  split at h
  · next pl cs₀ hl =>
    cases hw : within pl.off n pl.shape.size with
    | none => rw [hw] at h; cases h
    | some ws =>
      rw [hw] at h; cases h
      obtain ⟨h₁, h₂⟩ := CondS.all_append _ _ hc
      refine (locate_spec (Ψ := Ψ) (next := next) hl h₁).read ?_
      rw [ShapeS.den_size]
      exact within_spec hw h₂
  · cases h

/-- A 64-bit load from memory: the typed value there, or a number. -/
def load (Γ : CtxS) (d : Reg) (m : Mem) : Option (CtxS × List CondS) :=
  if d = .rsp then none
  else match locate Γ m with
    | some (pl, cs) =>
      match pl.shape.look pl.off with
      | some (some τ) => some (Γ.setReg d τ, cs)
      -- plain bytes are a number; where the terms do not say what is there,
      -- the checker has no answer, since a number might be a loss
      | some none => (within pl.off 8 pl.shape.size).map fun ws => (Γ.setReg d .int, cs ++ ws)
      | none => none
    | none => none

theorem load_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS} {d : Reg} {m : Mem}
    {x : CtxS × List CondS} (h : load Γ d m = some x) (hc : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) (.mov .w64 (.r_m d m)) (x.1.den ρ) := by
  unfold load at h
  split at h
  · cases h
  next hd =>
  split at h
  · next pl cs hl =>
    split at h
    · next τ hτ =>
      cases h
      rw [CtxS.den_setReg]
      exact (locate_spec (Ψ := Ψ) (next := next) hl hc).load hd (ShapeS.look_typed hτ)
    · cases hw : within pl.off 8 pl.shape.size with
      | none => rw [hw] at h; cases h
      | some ws =>
        rw [hw] at h; cases h
        obtain ⟨h₁, h₂⟩ := CondS.all_append _ _ hc
        rw [CtxS.den_setReg]
        refine .loadInt hd ((locate_spec (Ψ := Ψ) (next := next) hl h₁).read ?_)
        rw [ShapeS.den_size]
        exact within_spec hw h₂
    · cases h
  · cases h

/-! ### Storing plain bytes -/

/-- A shape with `n` bytes made plain, where its terms let that be worked out. -/
def ShapeS.clear : ShapeS → Num → Nat → Option ShapeS
  | .mk size .nil, _, _ => some (.mk size .nil)
  | .mk size vals, .lit i, n => some (.mk size (vals.clear i n))
  | _, _, _ => none

theorem ShapeS.den_clear {ρ : Env} {S S' : ShapeS} {o : Num} {n : Nat}
    (h : S.clear o n = some S') : S'.den ρ = (S.den ρ).clear (o.den ρ) n := by
  unfold ShapeS.clear at h
  split at h
  · cases h; rfl
  · next size vals i _ =>
    cases h
    show (⟨_, (vals.clear i n).den ρ⟩ : Shape) = _
    rw [ValsS.den_clear]; rfl
  · cases h

theorem denOwned_set (ρ : Env) : (l : List (Val × ShapeS)) → (tail : List (BitVec 64 × Shape)) →
    (i : Nat) → (x y : Val × ShapeS) → l[i]? = some x →
    denOwned ρ (l.set i y) tail = (denOwned ρ l tail).set i (y.1.den ρ, y.2.den ρ)
  | [], _, _, _, _, h => by cases h
  | (b, T) :: l, tail, 0, x, y, _ => rfl
  | (b, T) :: l, tail, i + 1, x, y, h => by
    show (b.den ρ, T.den ρ) :: denOwned ρ (l.set i y) tail = (b.den ρ, T.den ρ) :: _
    rw [denOwned_set ρ l tail i x y h]

/-- The block an operand was found in is listed where it was found. -/
theorem locate_listed {Γ : CtxS} {m : Mem} {pl : PlaceS} {cs : List CondS}
    (h : locate Γ m = some (pl, cs)) :
    (∀ k a, pl.kind = .owned k a → Γ.owned[k]? = some (a, pl.shape)) ∧
    (∀ k, pl.kind = .piece k → Γ.stack[k]? = some pl.shape) := by
  unfold locate at h
  split at h
  · next b ix disp =>
    split at h
    · -- the stack
      unfold locateSp at h
      split at h
      · split at h
        · split at h
          · next k S i sz hp =>
            cases h
            obtain ⟨j, hk, hj, _⟩ := pieceAt_spec (default : Env) [] _ _ _ hp
            refine ⟨fun _ _ e => (by cases e), fun k' e => ?_⟩
            cases e
            have : k = j := by omega
            subst this; exact hj
          · cases h
        · split at h
          · next c k S R hc hp =>
            cases h
            obtain ⟨j, hk, hj, _⟩ := pieceIdx_spec (default : Env) [] _ _ _ hp
            refine ⟨fun _ _ e => (by cases e), fun k' e => ?_⟩
            cases e
            have : k = j := by omega
            subst this; exact hj
          · cases h
      · cases h
    · split at h
      · cases h; exact ⟨fun _ _ e => (by cases e), fun _ e => (by cases e)⟩
      · split at h
        · next p hea =>
          split at h
          · next k a S j hf =>
            cases hfit : fits64 j with
            | none => rw [hfit] at h; cases h
            | some cs' =>
              rw [hfit] at h; cases h
              obtain ⟨i, hk, hi, _⟩ := findOwned_spec (default : Env) p Γ.owned 0 hf
              refine ⟨fun k' a' e => ?_, fun _ e => (by cases e)⟩
              cases e
              have : k = i := by omega
              subst this; exact hi
          · cases h
        · cases h
      · cases h
  · cases h

/-- The context after `n` plain bytes are stored to an operand, and what is
left to be shown. In a block others may point into the bytes must be plain
already; in a block the context owns or a piece of the stack, what typed
values reached into them are forgotten. -/
def writes (Γ : CtxS) (n : Nat) (m : Mem) : Option (CtxS × List CondS) :=
  match locate Γ m with
  | some (pl, cs) =>
    match within pl.off n pl.shape.size with
    | some ws =>
      match pl.kind with
      | .ptr true => if pl.shape.free pl.off n then some (Γ, cs ++ ws) else none
      | .block true => if pl.shape.free pl.off n then some (Γ, cs ++ ws) else none
      | .owned k a =>
        match pl.shape.clear pl.off n with
        | some S' => some ({ Γ with owned := Γ.owned.set k (a, S') }, cs ++ ws)
        | none => none
      | .piece k =>
        match pl.shape.clear pl.off n with
        | some S' => some ({ Γ with stack := Γ.stack.set k S' }, cs ++ ws)
        | none => none
      | _ => none
    | none => none
  | none => none

theorem writes_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS} {n : Nat} {m : Mem}
    {x : CtxS × List CondS} (h : writes Γ n m = some x) (hc : CondS.all ρ x.2) :
    WriteIntOk Ψ next (Γ.den ρ) n (.mem m) (x.1.den ρ) ∧ ReadOk Ψ next (Γ.den ρ) n (.mem m) := by
  unfold writes at h
  split at h
  · next pl cs hl =>
    split at h
    · next ws hw =>
      have key : ∀ {Γ' : CtxS}, CondS.all ρ (cs ++ ws) →
          Loc Ψ next (Γ.den ρ) m (pl.kind.den ρ) (pl.shape.den ρ) (pl.off.den ρ) ∧
          pl.off.den ρ + n ≤ (pl.shape.den ρ).size := fun hc' => by
        obtain ⟨h₁, h₂⟩ := CondS.all_append _ _ hc'
        exact ⟨locate_spec hl h₁, by rw [ShapeS.den_size]; exact within_spec hw h₂⟩
      obtain ⟨hown, hpiece⟩ := locate_listed hl
      split at h
      · next hk =>
        split at h
        · next hfree =>
          cases h
          obtain ⟨hloc, hin⟩ := key (Γ' := Γ) hc
          rw [hk] at hloc
          exact ⟨hloc.writeShared (w := true) (.inl rfl) rfl hin (ShapeS.den_free hfree),
            hloc.read hin⟩
        · cases h
      · next hk =>
        split at h
        · next hfree =>
          cases h
          obtain ⟨hloc, hin⟩ := key (Γ' := Γ) hc
          rw [hk] at hloc
          exact ⟨hloc.writeShared (w := true) (.inr rfl) rfl hin (ShapeS.den_free hfree),
            hloc.read hin⟩
        · cases h
      · next k a hk =>
        split at h
        · next S' hcl =>
          cases h
          obtain ⟨hloc, hin⟩ := key (Γ' := Γ) hc
          rw [hk] at hloc
          refine ⟨?_, hloc.read hin⟩
          have := hloc.writeOwned (n := n) hin
          rw [← ShapeS.den_clear hcl] at this
          have e : CtxS.den ρ { Γ with owned := Γ.owned.set k (a, S') }
              = { Γ.den ρ with owned := (Γ.den ρ).owned.set k (a.den ρ, S'.den ρ) } := by
            show ({ Γ.den ρ with owned := denOwned ρ (Γ.owned.set k (a, S')) _ } : Ctx) = _
            rw [denOwned_set ρ _ _ _ _ _ (hown k a hk)]; rfl
          rw [e]; exact this
        · cases h
      · next k hk =>
        split at h
        · next S' hcl =>
          cases h
          obtain ⟨hloc, hin⟩ := key (Γ' := Γ) hc
          rw [hk] at hloc
          refine ⟨?_, hloc.read hin⟩
          have := hloc.writePiece (n := n) hin
          rw [← ShapeS.den_clear hcl] at this
          have e : CtxS.den ρ { Γ with stack := Γ.stack.set k S' }
              = { Γ.den ρ with stack := (Γ.den ρ).stack.set k (S'.den ρ) } := by
            show ({ Γ.den ρ with stack := denShapes ρ (Γ.stack.set k S') _ } : Ctx) = _
            rw [denShapes_set ρ _ _ _ _ _ (hpiece k hk)]; rfl
          rw [e]; exact this
        · cases h
      · cases h
    · cases h
  · cases h

/-- A narrower value in a register extended into another: exactly known
where the source is. -/
def extendReg (Γ : CtxS) (d r : Reg) (f : Op1) : Option (CtxS × List CondS) :=
  if d = .rsp then none
  else match exactly (Γ.regs.get r) with
    | some a =>
      if r = .rsp then some (Γ.setReg d .int, []) else some (Γ.setReg d (.eq (.mk1 f a)), [])
    | none => some (Γ.setReg d .int, [])

/-- What `extendReg` gives: the register and its exactly known value, or
that the result is a number. -/
theorem extendReg_spec {ρ : Env} {Γ : CtxS} {d r : Reg} {f : Op1} {x : CtxS × List CondS}
    (h : extendReg Γ d r f = some x) :
    d ≠ .rsp ∧ ((∃ a, r ≠ .rsp ∧ (Γ.den ρ).regs r = .eq a ∧
        x.1.den ρ = (Γ.den ρ).setReg d (.eq (f.den a))) ∨
      x.1.den ρ = (Γ.den ρ).setReg d .int) := by
  unfold extendReg at h
  split at h
  · cases h
  · next hd =>
    refine ⟨hd, ?_⟩
    split at h
    · next a ha =>
      split at h
      · cases h; exact .inr (CtxS.den_setReg ρ Γ d .int)
      · next hr =>
        cases h
        exact .inl ⟨a.den ρ, hr, by rw [CtxS.den_regs, exactly_den ha],
          CtxS.den_setReg_mk1 ρ Γ d f a⟩
    · cases h; exact .inr (CtxS.den_setReg ρ Γ d .int)

/-- Arithmetic with its first operand in memory. -/
def aluMem (Γ : CtxS) (op : AluOp) (w : Width) (m : Mem) : Option (CtxS × List CondS) :=
  if op.writesDst then
    (writes Γ w.bytes.toNat m).map fun x =>
      ({ x.1 with flags := .known }, x.2 ++ carryConds Γ.flags op)
  else (reads Γ w.bytes.toNat m).map fun cs => ({ Γ with flags := .known }, cs)

theorem aluMem_spec {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS} {op : AluOp} {w : Width}
    {m : Mem} {x : CtxS × List CondS} (h : aluMem Γ op w m = some x) (hn : CondS.all ρ x.2) :
    (op.writesDst = true ∧ ∃ Γ', x.1.den ρ = { Γ' with flags := Flags.Known } ∧
        ReadOk Ψ next (Γ.den ρ) w.bytes.toNat (.mem m) ∧
        WriteIntOk Ψ next (Γ.den ρ) w.bytes.toNat (.mem m) Γ' ∧
        (op.readsCarry = true → ∀ f, (Γ.den ρ).flags f → f.cf.isSome = true)) ∨
    (op.writesDst = false ∧ x.1.den ρ = { Γ.den ρ with flags := Flags.Known } ∧
        ReadOk Ψ next (Γ.den ρ) w.bytes.toNat (.mem m)) := by
  unfold aluMem at h
  split at h
  · next hwd =>
    cases hw : writes Γ w.bytes.toNat m with
    | none => rw [hw] at h; cases h
    | some y =>
      rw [hw] at h; cases h
      obtain ⟨h₁, h₂⟩ := CondS.all_append _ _ hn
      obtain ⟨hwr, hrd⟩ := writes_sound (Ψ := Ψ) (next := next) hw h₁
      exact .inl ⟨hwd, y.1.den ρ, rfl, hrd, hwr, carryConds_spec h₂⟩
  · next hwd =>
    cases hr : reads Γ w.bytes.toNat m with
    | none => rw [hr] at h; cases h
    | some cs =>
      rw [hr] at h; cases h
      exact .inr ⟨(Bool.not_eq_true _).mp hwd, rfl, reads_sound hr hn⟩

/-- A step that only reads `n` bytes of an operand: what it leaves to be
shown is that they may be read. -/
theorem reads_map {Γ : CtxS} {n : Nat} {m : Mem} {f : List CondS → CtxS × List CondS}
    {x : CtxS × List CondS} (h : (reads Γ n m).map f = some x) :
    ∃ cs, reads Γ n m = some cs ∧ x = f cs := by
  cases hr : reads Γ n m with
  | none => rw [hr] at h; cases h
  | some cs => rw [hr] at h; cases h; exact ⟨cs, rfl, rfl⟩

/-- The checker for `mov`. -/
def stepMov (next : BitVec 64) (Γ : CtxS) (w : Width) (ops : Operands) :
    Option (CtxS × List CondS) :=
  match w, ops with
  | .w64, (.rm_r (.reg d) s) =>
    if d = .rsp ∨ s = .rsp then none else some (Γ.setReg d (Γ.regs.get s), [])
  | .w32, (.rm_r (.reg d) s) =>
    if d = .rsp then none
    else match exactly (Γ.regs.get s) with
      | some a =>
        if s = .rsp then some (Γ.setReg d .int, [])
        else some (Γ.setReg d (.eq (.mk1 .low32 a)), [])
      | none => some (Γ.setReg d .int, [])
  | w, (.rm_i (.reg d) imm) =>
    if d = .rsp then none
    else some (Γ.setReg d (.eq (.lit ((imm.signExtend w.bits).setWidth 64))), [])
  | .w64, (.r_m r (.sib (some .rsp) none disp)) => loadStack Γ r disp
  | .w64, (.rm_r (.mem (.sib (some .rsp) none disp)) s) => storeStack Γ s disp
  | .w64, (.r_m d m) => load Γ d m
  | w, (.r_m d m) =>
    if d = .rsp then none else (reads Γ w.bytes.toNat m).map fun cs => (Γ.setReg d .int, cs)
  | .w32, (.rm_r (.mem m) _) => writes Γ 4 m
  | w, (.rm_i (.mem m) _) => writes Γ w.bytes.toNat m
  | _, _ => none

theorem stepMov_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    
    {x : CtxS × List CondS} (h : stepMov next Γ w ops = some x)
    (hn : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) (.mov w ops) (x.1.den ρ) := by
  unfold stepMov at h
  split at h
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
  · exact loadStack_sound h
  · exact storeStack_sound h
  · exact load_sound h hn
  · split at h
    · cases h
    · next hd =>
      cases hr : reads Γ _ _ with
      | none => rw [hr] at h; cases h
      | some cs =>
        rw [hr] at h; cases h
        rw [CtxS.den_setReg]
        exact .loadInt hd (reads_sound hr hn)
  · exact .storeInt (writes_sound h hn).1
  · exact .storeImm (writes_sound h hn).1
  · cases h

/-- The checker for `lea`. -/
def stepLea (next : BitVec 64) (Γ : CtxS) (w : Width) (d : Reg) (m : Mem) :
    Option (CtxS × List CondS) :=
  match w, d, m with
  | .w64, d, (.rip disp) =>
    if d = .rsp then none else some (Γ.setReg d (.eq (.lit (next + disp.signExtend 64))), [])
  | .w64, d, (.sib (some b) none disp) =>
    if d = .rsp then none
    else match exactly (Γ.regs.get b) with
      | some a => some (Γ.setReg d (.eq (.add a (.lit (disp.signExtend 64)))), [])
      | none => some (Γ.setReg d .int, [])
  | .w64, d, (.sib (some b) (some (x, sc)) disp) =>
    if d = .rsp then none
    else match exactly (Γ.regs.get b), exactly (Γ.regs.get x.toReg) with
      | some a, some c =>
        if b = .rsp then some (Γ.setReg d .int, [])
        else
          some (Γ.setReg d (.eq (.add (.add a (.shl c sc.shift)) (.lit (disp.signExtend 64)))), [])
      | _, _ => some (Γ.setReg d .int, [])
  | _, d, _ => if d = .rsp then none else some (Γ.setReg d .int, [])

theorem stepLea_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    
    {x : CtxS × List CondS} (h : stepLea next Γ w d m = some x)
    (hn : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) (.lea w d m) (x.1.den ρ) := by
  unfold stepLea at h
  split at h
  · split at h
    · cases h
    · next hd => cases h; rw [CtxS.den_setReg]; exact .leaRip hd
  · next b disp =>
    split at h
    · cases h
    · next hd =>
      split at h
      · next a ha =>
        cases h
        rw [CtxS.den_setReg]
        have hΓ : (Γ.den ρ).regs b = .eq (a.den ρ) := by rw [CtxS.den_regs, exactly_den ha]
        by_cases hb : b = .rsp
        · subst hb; exact .leaSp hd hΓ
        · exact .leaExactB hd hb hΓ
      · cases h; rw [CtxS.den_setReg]; exact .lea hd
  · next b x sc disp =>
    split at h
    · cases h
    · next hd =>
      split at h
      · next a c ha hc =>
        split at h
        · cases h; rw [CtxS.den_setReg]; exact .lea hd
        · next hb =>
          cases h
          rw [CtxS.den_setReg]
          exact .leaExactBI hd hb (by rw [CtxS.den_regs, exactly_den ha])
            (by rw [CtxS.den_regs, exactly_den hc])
      · cases h; rw [CtxS.den_setReg]; exact .lea hd
  · split at h
    · cases h
    · next hd => cases h; rw [CtxS.den_setReg]; exact .lea hd

/-- The checker for `alu`. -/
def stepAlu (next : BitVec 64) (Γ : CtxS) (op : AluOp) (w : Width) (ops : Operands) :
    Option (CtxS × List CondS) :=
  match op, w, ops with
  | .sub, .w64, (.rm_i (.reg .rsp) imm) => allocFrame Γ imm
  | .add, .w64, (.rm_i (.reg .rsp) imm) => freeFrame Γ imm
  | op, w, (.r_m d m) =>
    if d = .rsp then none
    else (reads Γ w.bytes.toNat m).map fun cs => (afterAlu Γ op d, cs ++ carryConds Γ.flags op)
  | op, w, (.rm_r (.mem m) _) => aluMem Γ op w m
  | op, w, (.rm_i (.mem m) _) => aluMem Γ op w m
  | op, w, (.rm_r (.reg d) s) =>
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
  | op, w, (.rm_i (.reg d) imm) =>
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

theorem stepAlu_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    
    {x : CtxS × List CondS} (h : stepAlu next Γ op w ops = some x)
    (hn : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) (.alu op w ops) (x.1.den ρ) := by
  unfold stepAlu at h
  split at h
  · exact allocFrame_sound h hn
  · exact freeFrame_sound h
  · split at h
    · cases h
    · next hd =>
      cases hr : reads Γ _ _ with
      | none => rw [hr] at h; cases h
      | some cs =>
        rw [hr] at h; cases h
        obtain ⟨h₁, h₂⟩ := CondS.all_append _ _ hn
        rw [den_afterAlu]
        exact .aluLoad hd (reads_sound hr h₁) (carryConds_spec h₂)
  · rcases aluMem_spec (Ψ := Ψ) (next := next) h hn with ⟨hwd, Γ', e, hr, hw, hcf⟩ | ⟨hwd, e, hr⟩
    · rw [e]; exact .aluStoreR hwd hr hw hcf
    · rw [e]; exact .cmpR hwd hr
  · rcases aluMem_spec (Ψ := Ψ) (next := next) h hn with ⟨hwd, Γ', e, hr, hw, hcf⟩ | ⟨hwd, e, hr⟩
    · rw [e]; exact .aluStoreI hwd hr hw hcf
    · rw [e]; exact .cmpI hwd hr
  · next d s =>
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
  · next d imm _ _ =>
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

/-- The checker for `test`. -/
def stepTest (next : BitVec 64) (Γ : CtxS) (w : Width) (dst : RM) (src : RI) :
    Option (CtxS × List CondS) :=
  match w, dst, src with
  | w, (.mem m), _ =>
    (reads Γ w.bytes.toNat m).map fun cs => ({ Γ with flags := .known }, cs)
  | .w64, (.reg r), (.reg r') =>
    match exactly (Γ.regs.get r), exactly (Γ.regs.get r') with
    | some a, some b =>
      if r = .rsp ∨ r' = .rsp then some ({ Γ with flags := .known }, [])
      else some ({ Γ with flags := .test a b }, [])
    | _, _ => some ({ Γ with flags := .known }, [])
  | _, (.reg _), _ => some ({ Γ with flags := .known }, [])

theorem stepTest_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    
    {x : CtxS × List CondS} (h : stepTest next Γ w dst src = some x)
    (hn : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) (.test w dst src) (x.1.den ρ) := by
  unfold stepTest at h
  split at h
  · obtain ⟨cs, hr, rfl⟩ := reads_map h
    exact .testRM (reads_sound hr hn)
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

/-- The checker for `imul2`. -/
def stepImul2 (next : BitVec 64) (Γ : CtxS) (w : Width) (d : Reg) (src : RM) :
    Option (CtxS × List CondS) :=
  match w, d, src with
  | w, d, (.mem m) =>
    if d = .rsp then none
    else (reads Γ w.bytes.toNat m).map fun cs =>
      ({ Γ.setReg d .int with flags := .defined true false false true }, cs)
  | _, _, _ => none

theorem stepImul2_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    
    {x : CtxS × List CondS} (h : stepImul2 next Γ w d src = some x)
    (hn : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) (.imul2 w d src) (x.1.den ρ) := by
  unfold stepImul2 at h
  split at h
  · split at h
    · cases h
    · next hd =>
      obtain ⟨cs, hr, rfl⟩ := reads_map h
      exact cast_ctx (.imul2RM hd (reads_sound hr hn)) (by rw [CtxS.den_setReg_flags]; rfl)
  · cases h

/-- The checker for `imul3`. -/
def stepImul3 (next : BitVec 64) (Γ : CtxS) (w : Width) (d : Reg) (src : RM) (imm : BitVec 32) :
    Option (CtxS × List CondS) :=
  match w, d, src, imm with
  | w, d, (.mem m), _ =>
    if d = .rsp then none
    else (reads Γ w.bytes.toNat m).map fun cs =>
      ({ Γ.setReg d .int with flags := .defined true false false true }, cs)
  | _, _, _, _ => none

theorem stepImul3_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    
    {x : CtxS × List CondS} (h : stepImul3 next Γ w d src imm = some x)
    (hn : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) (.imul3 w d src imm) (x.1.den ρ) := by
  unfold stepImul3 at h
  split at h
  · split at h
    · cases h
    · next hd =>
      obtain ⟨cs, hr, rfl⟩ := reads_map h
      exact cast_ctx (.imul3RM hd (reads_sound hr hn)) (by rw [CtxS.den_setReg_flags]; rfl)
  · cases h

/-- The checker for `popcnt`. -/
def stepPopcnt (next : BitVec 64) (Γ : CtxS) (w : Width) (d : Reg) (src : RM) :
    Option (CtxS × List CondS) :=
  match w, d, src with
  | w, d, (.mem m) =>
    if d = .rsp then none
    else (reads Γ w.bytes.toNat m).map fun cs => ({ Γ.setReg d .int with flags := .known }, cs)
  | w, d, (.reg r) =>
    if d = .rsp then none
    else match exactly (Γ.regs.get r) with
      | some a =>
        if r = .rsp then some ({ Γ.setReg d .int with flags := .known }, [])
        else some ({ Γ.setReg d (.eq (.mk1 (.popcnt w) a)) with flags := .popcnt w a }, [])
      | none => some ({ Γ.setReg d .int with flags := .known }, [])

theorem stepPopcnt_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    
    {x : CtxS × List CondS} (h : stepPopcnt next Γ w d src = some x)
    (hn : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) (.popcnt w d src) (x.1.den ρ) := by
  unfold stepPopcnt at h
  split at h
  · split at h
    · cases h
    · next hd =>
      obtain ⟨cs, hr, rfl⟩ := reads_map h
      exact cast_ctx (.popcntRM hd (reads_sound hr hn)) (by rw [CtxS.den_setReg_flags]; rfl)
  · next r =>
    split at h
    · cases h
    · next hd =>
      split at h
      · next a ha =>
        split at h
        · cases h
          exact cast_ctx (.popcntRM hd (.reg _)) (by rw [CtxS.den_setReg_flags]; rfl)
        · next hr =>
          cases h
          exact cast_ctx (.popcntExact hd hr (by rw [CtxS.den_regs, exactly_den ha]))
            (CtxS.den_setReg_mk1_flags ρ Γ d (.popcnt w) a (.popcnt w a))
      · cases h
        exact cast_ctx (.popcntRM hd (.reg _)) (by rw [CtxS.den_setReg_flags]; rfl)

/-- The checker for `movsxd`. -/
def stepMovsxd (next : BitVec 64) (Γ : CtxS) (d : Reg) (src : RM) :
    Option (CtxS × List CondS) :=
  match d, src with
  | d, (.mem m) =>
    if d = .rsp then none else (reads Γ 4 m).map fun cs => (Γ.setReg d .int, cs)
  | d, (.reg r) => extendReg Γ d r .sext32

theorem stepMovsxd_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    
    {x : CtxS × List CondS} (h : stepMovsxd next Γ d src = some x)
    (hn : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) (.movsxd d src) (x.1.den ρ) := by
  unfold stepMovsxd at h
  split at h
  · split at h
    · cases h
    · next hd =>
      obtain ⟨cs, hr, rfl⟩ := reads_map h
      rw [CtxS.den_setReg]; exact .movsxdRM hd (reads_sound hr hn)
  · obtain ⟨hd, ⟨a, hr, hΓ, e⟩ | e⟩ := extendReg_spec (ρ := ρ) h
    · rw [e]; exact .movsxdExact hd hr hΓ
    · rw [e]; exact .movsxdRM hd (.reg _)

/-- The checker for `movzx`. -/
def stepMovzx (next : BitVec 64) (Γ : CtxS) (w : Width) (d : Reg) (sw : NarrowW) (src : RM) :
    Option (CtxS × List CondS) :=
  match w, d, sw, src with
  | _, d, sw, (.mem m) =>
    if d = .rsp then none else (reads Γ sw.bytes m).map fun cs => (Γ.setReg d .int, cs)
  | w, d, sw, (.reg r) => extendReg Γ d r (.zx w sw)

theorem stepMovzx_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    
    {x : CtxS × List CondS} (h : stepMovzx next Γ w d sw src = some x)
    (hn : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) (.movzx w d sw src) (x.1.den ρ) := by
  unfold stepMovzx at h
  split at h
  · split at h
    · cases h
    · next hd =>
      obtain ⟨cs, hr, rfl⟩ := reads_map h
      rw [CtxS.den_setReg]; exact .movzxRM hd (reads_sound hr hn)
  · obtain ⟨hd, ⟨a, hr, hΓ, e⟩ | e⟩ := extendReg_spec (ρ := ρ) h
    · rw [e]; exact .movzxExact hd hr hΓ
    · rw [e]; exact .movzxRM hd (.reg _)

/-- The checker for `movsx`. -/
def stepMovsx (next : BitVec 64) (Γ : CtxS) (w : Width) (d : Reg) (sw : NarrowW) (src : RM) :
    Option (CtxS × List CondS) :=
  match w, d, sw, src with
  | _, d, sw, (.mem m) =>
    if d = .rsp then none else (reads Γ sw.bytes m).map fun cs => (Γ.setReg d .int, cs)
  | w, d, sw, (.reg r) => extendReg Γ d r (.sx w sw)

theorem stepMovsx_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    
    {x : CtxS × List CondS} (h : stepMovsx next Γ w d sw src = some x)
    (hn : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) (.movsx w d sw src) (x.1.den ρ) := by
  unfold stepMovsx at h
  split at h
  · split at h
    · cases h
    · next hd =>
      obtain ⟨cs, hr, rfl⟩ := reads_map h
      rw [CtxS.den_setReg]; exact .movsxRM hd (reads_sound hr hn)
  · obtain ⟨hd, ⟨a, hr, hΓ, e⟩ | e⟩ := extendReg_spec (ρ := ρ) h
    · rw [e]; exact .movsxExact hd hr hΓ
    · rw [e]; exact .movsxRM hd (.reg _)

/-- The checker for `unary`. -/
def stepUnary (next : BitVec 64) (Γ : CtxS) (op : UnOp) (w : Width) (dst : RM) :
    Option (CtxS × List CondS) :=
  match op, w, dst with
  | .neg, w, (.reg d) =>
    if d = .rsp then none
    else match exactly (Γ.regs.get d) with
      | some a => some ({ Γ.setReg d (.eq (.mk1 (.neg w) a)) with flags := .neg w a }, [])
      | none => some ({ Γ.setReg d .int with flags := .known }, [])
  | .not, w, (.reg d) =>
    if d = .rsp then none
    else match exactly (Γ.regs.get d) with
      | some a => some (Γ.setReg d (.eq (.mk1 (.not w) a)), [])
      | none => some (Γ.setReg d .int, [])
  | _, _, _ => none

theorem stepUnary_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    
    {x : CtxS × List CondS} (h : stepUnary next Γ op w dst = some x)
    (hn : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) (.unary op w dst) (x.1.den ρ) := by
  unfold stepUnary at h
  split at h
  · next d =>
    split at h
    · cases h
    · next hd =>
      split at h
      · next a ha =>
        cases h
        exact cast_ctx (.negExact hd (by rw [CtxS.den_regs, exactly_den ha]))
          (CtxS.den_setReg_mk1_flags ρ Γ d (.neg w) a (.neg w a))
      · cases h
        exact cast_ctx (.negRM (.reg _) (.reg hd)) (by rw [CtxS.den_setReg_flags]; rfl)
  · next d =>
    split at h
    · cases h
    · next hd =>
      split at h
      · next a ha =>
        cases h
        exact cast_ctx (.notExact hd (by rw [CtxS.den_regs, exactly_den ha]))
          (CtxS.den_setReg_mk1 ρ Γ d (.not w) a)
      · cases h
        exact cast_ctx (.notRM (.reg _) (.reg hd)) (CtxS.den_setReg ρ Γ d .int)
  · cases h

/-- **The checker** for an instruction that goes on to the next. It gives the
context afterwards and what is left to be shown. -/
def step (next : BitVec 64) (Γ : CtxS) : Instr → Option (CtxS × List CondS)
  | .nop => some (Γ, [])
  | .mov w ops => stepMov next Γ w ops
  | .movAbs d imm => if d = .rsp then none else some (Γ.setReg d (.eq (.lit imm)), [])
  | .lea w d m => stepLea next Γ w d m
  | .alu op w ops => stepAlu next Γ op w ops
  | .push r => push Γ r
  | .pop r => pop Γ r
  | .store8 m _ => writes Γ 1 m
  | .store16 m _ => writes Γ 2 m
  | .test w dst src => stepTest next Γ w dst src
  | .imul2 w d src => stepImul2 next Γ w d src
  | .imul3 w d src imm => stepImul3 next Γ w d src imm
  | .popcnt w d src => stepPopcnt next Γ w d src
  | .movsxd d src => stepMovsxd next Γ d src
  | .movzx w d sw src => stepMovzx next Γ w d sw src
  | .movsx w d sw src => stepMovsx next Γ w d sw src
  | .unary op w dst => stepUnary next Γ op w dst
  | .bswap w r =>
    if r = .rsp then none
    else match exactly (Γ.regs.get r) with
      | some a => some (Γ.setReg r (.eq (.mk1 (.bswap w) a)), [])
      | none => some (Γ.setReg r .int, [])
  | .cdq =>
    match exactly (Γ.regs.get .rax) with
    | some a => some (Γ.setReg .rdx (.eq (.mk1 .fill32 a)), [])
    | none => some (Γ.setReg .rdx .int, [])
  | .cqo =>
    match exactly (Γ.regs.get .rax) with
    | some a => some (Γ.setReg .rdx (.eq (.mk1 .fill64 a)), [])
    | none => some (Γ.setReg .rdx .int, [])
  | _ => none

/-- **What the checker works out is a typing step.** -/
theorem step_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS} {i : Instr}
    {x : CtxS × List CondS} (h : step next Γ i = some x) (hn : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) i (x.1.den ρ) := by
  unfold step at h
  split at h
  · cases h; exact .nop
  · exact stepMov_sound h hn
  · split at h
    · cases h
    · next hd => cases h; rw [CtxS.den_setReg]; exact .movAbs hd
  · exact stepLea_sound h hn
  · exact stepAlu_sound h hn
  · exact push_sound h hn
  · exact pop_sound h
  · exact .store8RM (writes_sound h hn).1
  · exact .store16RM (writes_sound h hn).1
  · exact stepTest_sound h hn
  · exact stepImul2_sound h hn
  · exact stepImul3_sound h hn
  · exact stepPopcnt_sound h hn
  · exact stepMovsxd_sound h hn
  · exact stepMovzx_sound h hn
  · exact stepMovsx_sound h hn
  · exact stepUnary_sound h hn
  · next w r =>
    split at h
    · cases h
    · next hr =>
      split at h
      · next a ha =>
        cases h
        exact cast_ctx (.bswapExact hr (by rw [CtxS.den_regs, exactly_den ha]))
          (CtxS.den_setReg_mk1 ρ Γ r (.bswap w) a)
      · cases h; exact cast_ctx (.bswap hr) (CtxS.den_setReg ρ Γ r .int)
  · split at h
    · next a ha =>
      cases h
      exact cast_ctx (.cdqExact (by rw [CtxS.den_regs, exactly_den ha]))
        (CtxS.den_setReg_mk1 ρ Γ .rdx .fill32 a)
    · cases h; exact cast_ctx .cdq (CtxS.den_setReg ρ Γ .rdx .int)
  · split at h
    · next a ha =>
      cases h
      exact cast_ctx (.cqoExact (by rw [CtxS.den_regs, exactly_den ha]))
        (CtxS.den_setReg_mk1 ρ Γ .rdx .fill64 a)
    · cases h; exact cast_ctx .cqo (CtxS.den_setReg ρ Γ .rdx .int)
  · cases h

end Sym

end TypedAsm
