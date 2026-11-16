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

/-- The memory operand of an instruction, if it has one. -/
def Instr.memOperand? : Instr → Option Mem
  | .alu _ _ (.rm_r (.mem m) _) | .alu _ _ (.r_m _ m) | .alu _ _ (.rm_i (.mem m) _)
  | .mov _ (.rm_r (.mem m) _) | .mov _ (.r_m _ m) | .mov _ (.rm_i (.mem m) _)
  | .test _ (.mem m) _ | .unary _ _ (.mem m) | .shift _ _ (.mem m) _ | .setcc _ (.mem m)
  | .mulDiv _ _ (.mem m) | .imul2 _ _ (.mem m) | .imul3 _ _ (.mem m) _ | .popcnt _ _ (.mem m)
  | .movzx _ _ _ (.mem m) | .movsx _ _ _ (.mem m) | .movsxd _ (.mem m) | .cmov _ _ _ (.mem m)
  | .store8 m _ | .store16 m _ | .jmp (.ind (.mem m)) | .call (.ind (.mem m)) => some m
  | _ => none

/-- The registers whose values an instruction's rules need to speak of. If
one of them is typed as an integer, the tactic gives its value a name first,
so that the rules for exactly known values apply. -/
def Instr.wantsNamed : Instr → List Reg
  | .mulDiv .div _ (.reg r) | .mulDiv .idiv _ (.reg r) => [.rax, .rdx, r]
  | .cqo | .cdq => [.rax]
  -- what is compared: so that the way a jump after it went says something
  -- of those values
  | .alu .cmp _ (.rm_r (.reg d) s) => [d, s]
  | .alu .cmp _ (.rm_i (.reg d) _) => [d]
  | .test _ (.reg r) (.reg r') => [r, r']
  -- the address of something on the stack is known when the stack pointer is
  | .lea .w64 _ (.sib (some .rsp) _ _) => [.rsp]
  | i =>
    -- an index into memory must be exactly known for the access to be placed
    match i.memOperand? with
    | some (.sib _ (some (x, _)) _) => [x.toReg]
    | _ => []

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
  /-- Shifted or rotated by a number of bits, at a width. -/
  | shift (op : ShiftOp) (w : Width) (c : Nat)
  /-- The low byte set from a condition that came out this way. -/
  | setcc (b : Bool)
  deriving DecidableEq, Repr

/-- An operation of two values, likewise. -/
inductive Op2
  /-- The result of an arithmetic or logic operation at a width. -/
  | alu (op : AluOp) (w : Width)
  /-- The low half of a signed product at a width. -/
  | imul (w : Width)
  /-- The second value if a condition came out true, else the first, at a width. -/
  | cmov (w : Width) (b : Bool)
  /-- Quotient and remainder at a width, unsigned and signed. -/
  | udiv (w : Width)
  | urem (w : Width)
  | sdiv (w : Width)
  | srem (w : Width)
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
  | .shift op w c, a => (op.apply (a.setWidth w.bits) c).setWidth 64
  | .setcc b, x => (x &&& ~~~0xff) ||| (if b then (1 : BitVec 8) else 0).setWidth 64

def Op2.den : Op2 → BitVec 64 → BitVec 64 → BitVec 64
  | .alu op .w64, a, b => (op.apply a b).1
  | .alu op .w32, a, b => (op.apply (a.setWidth 32) (b.setWidth 32)).1.setWidth 64
  | .imul w, a, b => (imulTrunc (a.setWidth w.bits) (b.setWidth w.bits)).1.setWidth 64
  | .cmov w b, x, a => (if b then a.setWidth w.bits else x.setWidth w.bits).setWidth 64
  | .udiv w, a, b => (a.setWidth w.bits / b.setWidth w.bits).setWidth 64
  | .urem w, a, b => (a.setWidth w.bits % b.setWidth w.bits).setWidth 64
  | .sdiv w, a, b => ((a.setWidth w.bits).sdiv (b.setWidth w.bits)).setWidth 64
  | .srem w, a, b => ((a.setWidth w.bits).srem (b.setWidth w.bits)).setWidth 64

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

deriving instance DecidableEq for TyS, ShapeS, ValsS

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
  /-- They are exactly what a signed multiply left. -/
  | imul (w : Width) (a b : Val)
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
  /-- The program's own blocks: where each is, its shape, and whether it
  may be written. They are no part of what the context says of the machine;
  they are what the memory typing says, kept at hand for finding an operand
  in one. -/
  blocks : List (BitVec 64 × ShapeS × Bool) := []

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
  | .imul w a b =>
    (· = (imulTrunc ((a.den ρ).setWidth w.bits) ((b.den ρ).setWidth w.bits)).2)
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

theorem den_setReg_mk2_flags (ρ : Env) (Γ : CtxS) (r : Reg) (f : Op2) (a b : Val) (fl : FlagsS) :
    CtxS.den ρ { Γ.setReg r (.eq (.mk2 f a b)) with flags := fl }
      = { (Γ.den ρ).setReg r (.eq (f.den (a.den ρ) (b.den ρ))) with flags := fl.den ρ } := by
  rw [den_setReg_flags]
  show ({ CtxOf.setReg _ _ (.eq ((Val.mk2 f a b).den ρ)) with flags := _ } : Ctx) = _
  rw [Val.den_mk2]

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
  /-- A value of one type is one of another. -/
  | sub (τ υ : TyS)
  /-- Flags of which this is known decide a condition. -/
  | decides (fl : FlagsS) (c : Cond)
  /-- Two numbers are the same. -/
  | eqN (a b : Num)
  /-- What is known of the flags one way is known the other. -/
  | flagsSub (fl fl' : FlagsS)
  /-- A value is zero, or is not, at a width. -/
  | zeroW (w : Width) (v : Val)
  | nonzeroW (w : Width) (v : Val)
  /-- One value is the sign of another in every bit, at a width. -/
  | sfill (w : Width) (d a : Val)
  /-- A signed divide of one value by another does not overflow, at a width. -/
  | noOvf (w : Width) (a b : Val)

def CondS.den (ρ : Env) : CondS → Prop
  | .le a b => a.den ρ ≤ b.den ρ
  | .lt a b => a.den ρ < b.den ρ
  | .cf fl => ∀ f, fl.den ρ f → f.cf.isSome = true
  | .sub τ υ => Sub (τ.den ρ) (υ.den ρ)
  | .decides fl c => ∀ f, fl.den ρ f → ∃ b, c.eval f = some b
  | .eqN a b => a.den ρ = b.den ρ
  | .flagsSub fl fl' => ∀ f, fl.den ρ f → fl'.den ρ f
  | .zeroW w v => (v.den ρ).setWidth w.bits = 0
  | .nonzeroW w v => (v.den ρ).setWidth w.bits ≠ 0
  | .sfill w d a => (d.den ρ).setWidth w.bits = signFill ((a.den ρ).setWidth w.bits)
  | .noOvf w a b =>
    (a.den ρ).setWidth w.bits ≠ BitVec.intMin w.bits ∨ (b.den ρ).setWidth w.bits ≠ -1#w.bits

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

/-- A constant operand as a value, extended with its sign to a width and
then with zeros. -/
def immW (w : Width) (imm : BitVec 32) : Val := .lit ((imm.signExtend w.bits).setWidth 64)

theorem low_high (w : Width) (x : BitVec w.bits) : (x.setWidth 64).setWidth w.bits = x := by
  cases w
  · exact BitVec.setWidth_setWidth_of_le x (by decide)
  · simp [Width.bits]

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
      exact Addr.index_bytes (c.den ρ) sc disp hlt
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
    | imul w => simp [Val.summands, sumV]
    | cmov w b => simp [Val.summands, sumV]
    | udiv w => simp [Val.summands, sumV]
    | urem w => simp [Val.summands, sumV]
    | sdiv w => simp [Val.summands, sumV]
    | srem w => simp [Val.summands, sumV]

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
          (by rw [CtxS.den_regs, exactly_den hc]) (Addr.index_bytes _ sc disp hlt)
          ⟨by rw [CtxS.den_stack]; exact denShapes_getElem? ρ _ _ _ _ hj, ?_⟩
        rw [CtxS.den_stack, Num.den_plus]
        show _ = _ + ((c.den ρ).toNat * 2 ^ sc.shift + R)
        omega
      · cases h
  · cases h

/-! ### The program's own blocks -/

/-- That the blocks a context term lists are blocks of the memory typing,
with those shapes. -/
def BlocksOk (Ψ : MemTy) (ρ : Env) : List (BitVec 64 × ShapeS × Bool) → Prop
  | [] => True
  | (base, S, w) :: rest =>
    (∃ l, Ψ base = some l ∧ l.shape = S.den ρ ∧ l.writable = w) ∧ BlocksOk Ψ ρ rest

theorem BlocksOk.nil {Ψ : MemTy} {ρ : Env} : BlocksOk Ψ ρ [] := trivial

theorem BlocksOk.cons {Ψ : MemTy} {ρ : Env} {base : BitVec 64} {S : ShapeS} {w : Bool}
    {rest : List (BitVec 64 × ShapeS × Bool)} (l : Layout) (h₁ : Ψ base = some l)
    (h₂ : l.shape = S.den ρ) (h₃ : l.writable = w) (h : BlocksOk Ψ ρ rest) :
    BlocksOk Ψ ρ ((base, S, w) :: rest) := ⟨⟨l, h₁, h₂, h₃⟩, h⟩

/-- The block of the program an address is in, and how far in: the first
whose length is a number greater than how far past its start the address is. -/
def blockAt : List (BitVec 64 × ShapeS × Bool) → BitVec 64 →
    Option (BitVec 64 × ShapeS × Bool × Nat)
  | [], _ => none
  | (base, S, w) :: rest, a =>
    match S.size.lit? with
    | some sz =>
      if (a - base).toNat < sz then some (base, S, w, (a - base).toNat) else blockAt rest a
    | none => blockAt rest a

theorem blockAt_spec {Ψ : MemTy} {ρ : Env} : (bs : List (BitVec 64 × ShapeS × Bool)) →
    {a base : BitVec 64} → {S : ShapeS} → {w : Bool} → {d : Nat} → BlocksOk Ψ ρ bs →
    blockAt bs a = some (base, S, w, d) →
    (∃ l, Ψ base = some l ∧ l.shape = S.den ρ ∧ l.writable = w) ∧ a = base + BitVec.ofNat 64 d
  | [], _, _, _, _, _, _, h => by cases h
  | (b, T, v) :: rest, a, base, S, w, d, hB, h => by
    unfold blockAt at h
    split at h
    · split at h
      · cases h
        refine ⟨hB.1, ?_⟩
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
        bv_omega
      · exact blockAt_spec rest hB.2 h
    · exact blockAt_spec rest hB.2 h

/-- Where an operand that is not reached through a register is: in one of
the program's blocks, at a fixed distance from the next instruction or at a
fixed address, with or without an index. -/
def locateBlock (next : BitVec 64) (Γ : CtxS) : Mem → Option (PlaceS × List CondS)
  | .rip disp =>
    match blockAt Γ.blocks (next + disp.signExtend 64) with
    | some (_, S, w, d) => some (⟨.block w, S, .lit d⟩, [])
    | none => none
  | .sib none none disp =>
    match blockAt Γ.blocks (disp.signExtend 64) with
    | some (_, S, w, d) => some (⟨.block w, S, .lit d⟩, [])
    | none => none
  | .sib none (some (x, sc)) disp =>
    match exactly (Γ.regs.get x.toReg), blockAt Γ.blocks (disp.signExtend 64) with
    | some c, some (_, S, w, d) =>
      some (⟨.block w, S, Num.plus (.mul (.toNat c) (.lit (2 ^ sc.shift))) (.lit d)⟩, [])
    | _, _ => none
  | _ => none

theorem locateBlock_spec {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS} {m : Mem}
    {x : PlaceS × List CondS} (hB : BlocksOk Ψ ρ Γ.blocks) (h : locateBlock next Γ m = some x) :
    Loc Ψ next (Γ.den ρ) m (x.1.kind.den ρ) (x.1.shape.den ρ) (x.1.off.den ρ) := by
  unfold locateBlock at h
  split at h
  · split at h
    · next base S w d hb =>
      cases h
      obtain ⟨⟨l, hl, hs, hw⟩, ha⟩ := blockAt_spec _ hB hb
      have := Loc.global (Γ := Γ.den ρ) hl ha
      rw [hs, hw] at this
      exact this
    · cases h
  · split at h
    · next base S w d hb =>
      cases h
      obtain ⟨⟨l, hl, hs, hw⟩, ha⟩ := blockAt_spec _ hB hb
      have := Loc.placed (Ψ := Ψ) (next := next) (Γ := Γ.den ρ) .abs hl ha
      rw [hs, hw] at this
      exact this
    · cases h
  · next xr sc disp =>
    split at h
    · next c base S w d hc hb =>
      cases h
      obtain ⟨⟨l, hl, hs, hw⟩, ha⟩ := blockAt_spec _ hB hb
      have := Loc.placed (Ψ := Ψ) (next := next) (Γ := Γ.den ρ)
        (.absIndexed (sc := sc) (disp := disp) (by rw [CtxS.den_regs, exactly_den hc])) hl
        (Addr.block_idx (c.den ρ) sc disp base d ha)
      rw [hs, hw] at this
      show Loc Ψ next _ _ (.block w) (S.den ρ) ((Num.plus _ (.lit d)).den ρ)
      rw [Num.den_plus]
      exact this
    · cases h
  · cases h

theorem locateBlock_listed {next : BitVec 64} {Γ : CtxS} {m : Mem} {pl : PlaceS}
    {cs : List CondS} (h : locateBlock next Γ m = some (pl, cs)) :
    (∀ k a, pl.kind = .owned k a → Γ.owned[k]? = some (a, pl.shape)) ∧
    (∀ k, pl.kind = .piece k → Γ.stack[k]? = some pl.shape) := by
  have hk : ∃ w, pl.kind = .block w := by
    unfold locateBlock at h
    split at h
    · split at h
      · cases h; exact ⟨_, rfl⟩
      · cases h
    · split at h
      · cases h; exact ⟨_, rfl⟩
      · cases h
    · split at h
      · cases h; exact ⟨_, rfl⟩
      · cases h
    · cases h
  obtain ⟨w, hw⟩ := hk
  exact ⟨fun _ _ e => (by rw [hw] at e; cases e), fun _ e => (by rw [hw] at e; cases e)⟩

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
def locate (next : BitVec 64) (Γ : CtxS) (m : Mem) : Option (PlaceS × List CondS) :=
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
  | m => locateBlock next Γ m

theorem CtxS.den_owned (ρ : Env) (Γ : CtxS) :
    (Γ.den ρ).owned = denOwned ρ Γ.owned (ownedTail ρ Γ.ownedRest) := rfl

theorem locate_spec {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    (hB : BlocksOk Ψ ρ Γ.blocks) {m : Mem}
    {x : PlaceS × List CondS} (h : locate next Γ m = some x) (hc : CondS.all ρ x.2) :
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
  · exact locateBlock_spec hB h

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

/-- What a product is so many times `es` of, where one side of it is `es`
written out. -/
def Num.timesOf (x y : Num) (es : Nat) : Option Num :=
  match y with
  | .lit a => if a = es then some x else none
  | _ =>
    match x with
    | .lit a => if a = es then some y else none
    | _ => none

theorem Num.timesOf_spec (ρ : Env) {x y q : Num} {es : Nat} (h : Num.timesOf x y es = some q) :
    x.den ρ * y.den ρ = q.den ρ * es := by
  unfold Num.timesOf at h
  split at h
  · split at h
    · next e => cases h; subst e; rfl
    · cases h
  · split at h
    · split at h
      · next e => cases h; subst e; exact Nat.mul_comm _ _
      · cases h
    · cases h

/-- A number as so many times `es` and something less than `es` over, where
its terms show that. -/
def Num.divMod : Num → Nat → Option (Num × Nat)
  | .lit m, es => some (.lit (m / es), m % es)
  | .mul x y, es => (Num.timesOf x y es).map (·, 0)
  | .add p q, es =>
    match p.divMod es, q.divMod es with
    | some (q1, r1), some (q2, r2) =>
      some (q1.plus' (q2.plus (.lit ((r1 + r2) / es))), (r1 + r2) % es)
    | _, _ => none
  | _, _ => none

theorem Num.divMod_spec (ρ : Env) {es : Nat} (hes : 0 < es) : (o : Num) → {q : Num} → {r : Nat} →
    o.divMod es = some (q, r) → o.den ρ = q.den ρ * es + r ∧ r < es := by
  intro o
  induction o with
  | lit m =>
    intro q r h
    simp only [Num.divMod, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, Nat.mod_lt _ hes⟩
    show m = m / es * es + m % es
    rw [Nat.mul_comm]; exact (Nat.div_add_mod m es).symm
  | mul x y ihx ihy =>
    intro q r h
    simp only [Num.divMod, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨q', hq, rfl, rfl⟩ := h
    exact ⟨Num.timesOf_spec ρ hq, hes⟩
  | add p q' ihp ihq =>
    intro q r h
    simp only [Num.divMod] at h
    split at h
    · next q1 r1 q2 r2 hp hq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨e1, _⟩ := ihp hp
      obtain ⟨e2, _⟩ := ihq hq
      refine ⟨?_, Nat.mod_lt _ hes⟩
      show p.den ρ + q'.den ρ = _
      rw [Num.den_plus', Num.den_plus, e1, e2]
      show _ = (q1.den ρ + (q2.den ρ + (r1 + r2) / es)) * es + (r1 + r2) % es
      have := Nat.div_add_mod (r1 + r2) es
      rw [Nat.mul_comm] at this
      simp only [Nat.add_mul]
      omega
    · cases h
  | var _ => intro q r h; cases h
  | sub _ _ _ _ => intro q r h; cases h
  | toNat _ => intro q r h; cases h
  | size _ => intro q r h; cases h

/-- Whether every typed value of a list ends within `es` bytes. -/
def ValsS.allFit : ValsS → Nat → Bool
  | .nil, _ => true
  | .cons p _ rest, es => decide (p + 8 ≤ es) && rest.allFit es

theorem ValsS.den_allFit (ρ : Env) : (vs : ValsS) → (es : Nat) →
    ((vs.den ρ).all fun p => decide (p.1 + 8 ≤ es)) = vs.allFit es
  | .nil, _ => rfl
  | .cons p τ rest, es => by
    show List.all ((p, τ.den ρ) :: rest.den ρ) _ = _
    rw [List.all_cons, ValsS.den_allFit ρ rest es]
    rfl

/-- The typed value at a byte of an array, where the terms show which
element the byte is in, and what is left to be shown: that there is such an
element. -/
def ShapeS.elem : ShapeS → Num → Option (TyS × List CondS)
  | .rep n (.mk (.lit es) vals), o =>
    if es = 0 ∨ vals.allFit es = false then none
    else match o.divMod es with
      | some (q, f) =>
        match vals.find f with
        | some τ => some (τ, [.lt q n])
        | none => none
      | none => none
  | _, _ => none

theorem ShapeS.elem_typed {ρ : Env} {S : ShapeS} {o : Num} {x : TyS × List CondS}
    (h : S.elem o = some x) (hc : CondS.all ρ x.2) :
    (S.den ρ).valAt (o.den ρ) = some (x.1.den ρ) := by
  unfold ShapeS.elem at h
  split at h
  · next n es vals =>
    split at h
    · cases h
    · next hne =>
      have hes : 0 < es := Nat.pos_of_ne_zero fun e => hne (.inl e)
      have hfit : vals.allFit es = true := by
        cases hf : vals.allFit es with
        | true => rfl
        | false => exact absurd (.inr hf) hne
      split at h
      · next q f hd =>
        split at h
        · next τ hτ =>
          cases h
          obtain ⟨ho, _⟩ := Num.divMod_spec ρ hes o hd
          have hf : ((ShapeS.mk (.lit es) vals).den ρ).fits = true := by
            show (vals.den ρ).all _ = true
            rw [ValsS.den_allFit]; exact hfit
          have hv : ((ShapeS.mk (.lit es) vals).den ρ).valAt f = some (τ.den ρ) :=
            ShapeS.den_valAt (S := .mk (.lit es) vals) hτ
          have := ShapeOf.valAt_rep hf (n := n.den ρ) (i := q.den ρ) hc.1 hv
          rw [ho]; exact this
        · cases h
      · cases h
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

/-- How many typed values reach into the eight bytes at a place. -/
def ValsS.hits : ValsS → Nat → Nat
  | .nil, _ => 0
  | .cons p _ rest, o => (if p + 8 ≤ o ∨ o + 8 ≤ p then 0 else 1) + rest.hits o

theorem ValsS.den_hits (ρ : Env) : (vs : ValsS) → (o : Nat) →
    ((vs.den ρ).filter fun p => !ShapeOf.clearOf o 8 p).length = vs.hits o
  | .nil, _ => rfl
  | .cons p τ rest, o => by
    show (List.filter _ ((p, τ.den ρ) :: rest.den ρ)).length = _
    unfold ValsS.hits
    by_cases h : p + 8 ≤ o ∨ o + 8 ≤ p
    · have hc : ShapeOf.clearOf o 8 (p, τ.den ρ) = true := by
        simp only [ShapeOf.clearOf, Bool.or_eq_true, decide_eq_true_eq]; exact h
      rw [List.filter_cons_of_neg (by simp [hc])]
      simp only [h, ↓reduceIte, Nat.zero_add]
      exact ValsS.den_hits ρ rest o
    · have hc : ShapeOf.clearOf o 8 (p, τ.den ρ) = false := by
        simp only [ShapeOf.clearOf, Bool.or_eq_false_iff, decide_eq_false_iff_not]
        exact ⟨fun h1 => h (.inl h1), fun h2 => h (.inr h2)⟩
      rw [List.filter_cons_of_pos (by simp [hc])]
      simp only [h, ↓reduceIte, List.length_cons]
      rw [ValsS.den_hits ρ rest o]; omega

/-- What is left to be shown for `k` bytes at a byte of an array to be
plain, where the terms show which element they are in and that they are
plain in it: that there is such an element. -/
def ShapeS.elemFree : ShapeS → Num → Nat → Option (List CondS)
  | .rep n (.mk (.lit es) vals), o, k =>
    if es = 0 ∨ vals.allFit es = false then none
    else match o.divMod es with
      | some (q, f) => if vals.allClear f k = true ∧ f + k ≤ es then some [.lt q n] else none
      | none => none
  | _, _, _ => none

theorem ShapeS.elemFree_spec {ρ : Env} {S : ShapeS} {o : Num} {k : Nat} {cs : List CondS}
    (h : S.elemFree o k = some cs) (hc : CondS.all ρ cs) :
    (S.den ρ).free (o.den ρ) k = true := by
  unfold ShapeS.elemFree at h
  split at h
  · next n es vals =>
    split at h
    · cases h
    · next hne =>
      have hes : 0 < es := Nat.pos_of_ne_zero fun e => hne (.inl e)
      have hfit : vals.allFit es = true := by
        cases hf : vals.allFit es with
        | true => rfl
        | false => exact absurd (.inr hf) hne
      split at h
      · next q f hd =>
        split at h
        · next hcl =>
          cases h
          obtain ⟨ho, _⟩ := Num.divMod_spec ρ hes o hd
          have hf : ((ShapeS.mk (.lit es) vals).den ρ).fits = true := by
            show (vals.den ρ).all _ = true
            rw [ValsS.den_allFit]; exact hfit
          have hfree : ((ShapeS.mk (.lit es) vals).den ρ).free f k = true := by
            show (vals.den ρ).all _ = true
            rw [ValsS.den_allClear]; exact hcl.1
          have := ShapeOf.free_rep hf (n := n.den ρ) (i := q.den ρ) hc.1 (m := k) hcl.2 hfree
          rw [ho]; exact this
        · cases h
      · cases h
  · cases h

/-- What a number is at least, as far as its terms show. -/
def Num.low : Num → Nat
  | .lit n => n
  | .add a b => a.low + b.low
  | .mul a b => a.low * b.low
  | _ => 0

theorem Num.low_le (ρ : Env) : (o : Num) → o.low ≤ o.den ρ
  | .lit _ => Nat.le_refl _
  | .add a b => Nat.add_le_add (Num.low_le ρ a) (Num.low_le ρ b)
  | .mul a b => Nat.mul_le_mul (Num.low_le ρ a) (Num.low_le ρ b)
  | .var _ => Nat.zero_le _
  | .sub _ _ => Nat.zero_le _
  | .toNat _ => Nat.zero_le _
  | .size _ => Nat.zero_le _

/-- Whether every typed value of a list ends at or before a byte. -/
def ValsS.allBelow : ValsS → Nat → Bool
  | .nil, _ => true
  | .cons p _ rest, b => decide (p + 8 ≤ b) && rest.allBelow b

theorem ValsS.den_allBelow (ρ : Env) : (vs : ValsS) → {b o n : Nat} → vs.allBelow b = true →
    b ≤ o → (vs.den ρ).all (ShapeOf.clearOf o n) = true
  | .nil, _, _, _, _, _ => rfl
  | .cons p τ rest, b, o, n, h, hb => by
    simp only [ValsS.allBelow, Bool.and_eq_true, decide_eq_true_eq] at h
    show List.all ((p, τ.den ρ) :: rest.den ρ) _ = true
    rw [List.all_cons, ValsS.den_allBelow ρ rest h.2 hb, Bool.and_true]
    show (decide (p + 8 ≤ o) || decide (o + n ≤ p)) = true
    have : p + 8 ≤ o := Nat.le_trans h.1 hb
    simp [this]

/-- Whether the bytes from a place on are seen to be past every typed value
of a shape, where the place is not a number written out but is at least one. -/
def ShapeS.freeAbove : ShapeS → Num → Bool
  | .mk _ vals, o => vals.allBelow o.low
  | _, _ => false

theorem ShapeS.den_freeAbove {ρ : Env} {S : ShapeS} {o : Num} {n : Nat}
    (h : S.freeAbove o = true) : (S.den ρ).free (o.den ρ) n = true := by
  unfold ShapeS.freeAbove at h
  split at h
  · next sz vals => exact ValsS.den_allBelow ρ vals h (Num.low_le ρ o)
  · cases h

/-- What is left to be shown for `n` bytes of a shape to be plain: nothing
where the terms show it outright. -/
def freeConds (S : ShapeS) (o : Num) (n : Nat) : Option (List CondS) :=
  if S.free o n then some [] else if S.freeAbove o then some [] else S.elemFree o n

theorem freeConds_spec {ρ : Env} {S : ShapeS} {o : Num} {n : Nat} {cs : List CondS}
    (h : freeConds S o n = some cs) (hc : CondS.all ρ cs) :
    (S.den ρ).free (o.den ρ) n = true := by
  unfold freeConds at h
  split at h
  · next hf => exact ShapeS.den_free hf
  · split at h
    · next hf => exact ShapeS.den_freeAbove hf
    · exact ShapeS.elemFree_spec h hc

/-- Whether the eight bytes at a byte of an array are seen to be one typed
value's alone within their element. -/
def ShapeS.elemSole : ShapeS → Num → Bool
  | .rep _ (.mk (.lit es) vals), o =>
    match o.divMod es with
    | some (_, f) => vals.hits f == 1 && decide (f + 8 ≤ es)
    | none => false
  | _, _ => false

theorem ShapeS.elemSole_spec {ρ : Env} {S : ShapeS} {o : Num} {x : TyS × List CondS}
    (he : S.elem o = some x) (hc : CondS.all ρ x.2) (hs : S.elemSole o = true) :
    (S.den ρ).sole (o.den ρ) = true := by
  unfold ShapeS.elem at he
  unfold ShapeS.elemSole at hs
  split at he
  · next n es vals =>
    split at he
    · cases he
    · next hne =>
      have hes : 0 < es := Nat.pos_of_ne_zero fun e => hne (.inl e)
      have hfit : vals.allFit es = true := by
        cases hf : vals.allFit es with
        | true => rfl
        | false => exact absurd (.inr hf) hne
      split at he
      · next q f hd =>
        split at he
        · next τ hτ =>
          cases he
          simp only [hd, Bool.and_eq_true, decide_eq_true_eq] at hs
          obtain ⟨ho, _⟩ := Num.divMod_spec ρ hes o hd
          have hf : ((ShapeS.mk (.lit es) vals).den ρ).fits = true := by
            show (vals.den ρ).all _ = true
            rw [ValsS.den_allFit]; exact hfit
          have hsole : ((ShapeS.mk (.lit es) vals).den ρ).sole f = true := by
            show ((vals.den ρ).filter _).length == 1
            rw [ValsS.den_hits]; exact hs.1
          have := ShapeOf.sole_rep hf (n := n.den ρ) (i := q.den ρ) hc.1 hs.2 hsole
          rw [ho]; exact this
        · cases he
      · cases he
  · cases he

/-- What is left to be shown for `n` bytes to be read from an operand. -/
def reads (next : BitVec 64) (Γ : CtxS) (n : Nat) (m : Mem) : Option (List CondS) :=
  match locate next Γ m with
  | some (pl, cs) => (within pl.off n pl.shape.size).map (cs ++ ·)
  | none => none

theorem CondS.all_append {ρ : Env} : (as bs : List CondS) →
    CondS.all ρ (as ++ bs) → CondS.all ρ as ∧ CondS.all ρ bs
  | [], _, h => ⟨trivial, h⟩
  | _ :: as, bs, h => ⟨⟨h.1, (CondS.all_append as bs h.2).1⟩, (CondS.all_append as bs h.2).2⟩

theorem reads_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    (hB : BlocksOk Ψ ρ Γ.blocks) {n : Nat} {m : Mem}
    {cs : List CondS} (h : reads next Γ n m = some cs) (hc : CondS.all ρ cs) :
    ReadOk Ψ next (Γ.den ρ) n (.mem m) := by
  unfold reads at h
  split at h
  · next pl cs₀ hl =>
    cases hw : within pl.off n pl.shape.size with
    | none => rw [hw] at h; cases h
    | some ws =>
      rw [hw] at h; cases h
      obtain ⟨h₁, h₂⟩ := CondS.all_append _ _ hc
      refine (locate_spec hB (Ψ := Ψ) (next := next) hl h₁).read ?_
      rw [ShapeS.den_size]
      exact within_spec hw h₂
  · cases h

/-- A 64-bit load from memory: the typed value there, or a number. -/
def load (next : BitVec 64) (Γ : CtxS) (d : Reg) (m : Mem) : Option (CtxS × List CondS) :=
  if d = .rsp then none
  else match locate next Γ m with
    | some (pl, cs) =>
      match pl.shape.look pl.off with
      | some (some τ) => some (Γ.setReg d τ, cs)
      -- plain bytes are a number
      | some none => (within pl.off 8 pl.shape.size).map fun ws => (Γ.setReg d .int, cs ++ ws)
      | none =>
        -- an element of an array
        match pl.shape.elem pl.off with
        | some (τ, es) => some (Γ.setReg d τ, cs ++ es)
        -- what is there cannot be read off the terms: the bytes are a number
        | none => (within pl.off 8 pl.shape.size).map fun ws => (Γ.setReg d .int, cs ++ ws)
    | none => none

theorem load_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    (hB : BlocksOk Ψ ρ Γ.blocks) {d : Reg} {m : Mem}
    {x : CtxS × List CondS} (h : load next Γ d m = some x) (hc : CondS.all ρ x.2) :
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
      exact (locate_spec hB (Ψ := Ψ) (next := next) hl hc).load hd (ShapeS.look_typed hτ)
    · cases hw : within pl.off 8 pl.shape.size with
      | none => rw [hw] at h; cases h
      | some ws =>
        rw [hw] at h; cases h
        obtain ⟨h₁, h₂⟩ := CondS.all_append _ _ hc
        rw [CtxS.den_setReg]
        refine .loadInt hd ((locate_spec hB (Ψ := Ψ) (next := next) hl h₁).read ?_)
        rw [ShapeS.den_size]
        exact within_spec hw h₂
    · split at h
      · next τ es he =>
        cases h
        obtain ⟨h₁, h₂⟩ := CondS.all_append _ _ hc
        rw [CtxS.den_setReg]
        exact (locate_spec hB (Ψ := Ψ) (next := next) hl h₁).load hd
          (ShapeS.elem_typed (x := (τ, es)) he h₂)
      · cases hw : within pl.off 8 pl.shape.size with
        | none => rw [hw] at h; cases h
        | some ws =>
          rw [hw] at h; cases h
          obtain ⟨h₁, h₂⟩ := CondS.all_append _ _ hc
          rw [CtxS.den_setReg]
          refine .loadInt hd ((locate_spec hB (Ψ := Ψ) (next := next) hl h₁).read ?_)
          rw [ShapeS.den_size]
          exact within_spec hw h₂
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
theorem locate_listed {next : BitVec 64} {Γ : CtxS} {m : Mem} {pl : PlaceS} {cs : List CondS}
    (h : locate next Γ m = some (pl, cs)) :
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
  · exact locateBlock_listed h

/-- The context after `n` plain bytes are stored to an operand, and what is
left to be shown. In a block others may point into the bytes must be plain
already; in a block the context owns or a piece of the stack, what typed
values reached into them are forgotten. -/
def writes (next : BitVec 64) (Γ : CtxS) (n : Nat) (m : Mem) : Option (CtxS × List CondS) :=
  match locate next Γ m with
  | some (pl, cs) =>
    match within pl.off n pl.shape.size with
    | some ws =>
      match pl.kind with
      | .ptr true =>
        match freeConds pl.shape pl.off n with
        | some fs => some (Γ, (cs ++ ws) ++ fs)
        | none => none
      | .block true =>
        match freeConds pl.shape pl.off n with
        | some fs => some (Γ, (cs ++ ws) ++ fs)
        | none => none
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

theorem writes_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    (hB : BlocksOk Ψ ρ Γ.blocks) {n : Nat} {m : Mem}
    {x : CtxS × List CondS} (h : writes next Γ n m = some x) (hc : CondS.all ρ x.2) :
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
        exact ⟨locate_spec hB hl h₁, by rw [ShapeS.den_size]; exact within_spec hw h₂⟩
      obtain ⟨hown, hpiece⟩ := locate_listed hl
      split at h
      · next hk =>
        split at h
        · next fs hfree =>
          cases h
          obtain ⟨h₁, h₂⟩ := CondS.all_append _ _ hc
          obtain ⟨hloc, hin⟩ := key (Γ' := Γ) h₁
          rw [hk] at hloc
          exact ⟨hloc.writeShared (w := true) (.inl rfl) rfl hin (freeConds_spec hfree h₂),
            hloc.read hin⟩
        · cases h
      · next hk =>
        split at h
        · next fs hfree =>
          cases h
          obtain ⟨h₁, h₂⟩ := CondS.all_append _ _ hc
          obtain ⟨hloc, hin⟩ := key (Γ' := Γ) h₁
          rw [hk] at hloc
          exact ⟨hloc.writeShared (w := true) (.inr rfl) rfl hin (freeConds_spec hfree h₂),
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

/-! ### Storing a register's eight bytes -/

/-- Whether the eight bytes at a place are seen from the terms to be one
typed value's alone. -/
def ShapeS.sole : ShapeS → Num → Bool
  | .mk _ vals, .lit i => vals.hits i == 1
  | _, _ => false

theorem ShapeS.den_sole {ρ : Env} {S : ShapeS} {o : Num} (h : S.sole o = true) :
    (S.den ρ).sole (o.den ρ) = true := by
  unfold ShapeS.sole at h
  split at h
  · next sz vals i =>
    show ((vals.den ρ).filter _).length == 1
    rw [ValsS.den_hits]; exact h
  · cases h

/-- A shape with a typed value put at a place, where the terms let that be
worked out. -/
def ShapeS.set : ShapeS → Num → TyS → Option ShapeS
  | .mk size vals, .lit i, τ => some (.mk size (vals.set i τ))
  | _, _, _ => none

theorem ShapeS.den_set {ρ : Env} {S S' : ShapeS} {o : Num} {τ : TyS}
    (h : S.set o τ = some S') : S'.den ρ = (S.den ρ).set (o.den ρ) (τ.den ρ) := by
  unfold ShapeS.set at h
  split at h
  · cases h
    show (⟨_, (_, _) :: (ValsS.clear _ _ 8).den ρ⟩ : Shape) = _
    rw [ValsS.den_clear]; rfl
  · cases h

/-- Whether a value of one type is seen from the terms to be one of another:
the same type, any type where a number is wanted, a type where it or nothing
is wanted. -/
def TyS.subB (τ υ : TyS) : Bool :=
  decide (τ = υ) ||
    match υ with
    | .int => true
    | .nullable υ' => decide (τ = υ')
    | .orErr υ' => decide (τ = υ')
    | _ => false

theorem TyS.subB_sound {ρ : Env} {τ υ : TyS} (h : τ.subB υ = true) : Sub (τ.den ρ) (υ.den ρ) := by
  unfold TyS.subB at h
  rcases Bool.or_eq_true _ _ |>.mp h with h | h
  · rw [of_decide_eq_true h]; exact .refl _
  · split at h
    · exact .int _
    · rw [of_decide_eq_true h]; exact .nullable (.refl _)
    · rw [of_decide_eq_true h]; exact .orErr (.refl _)
    · cases h

/-- What is left to be shown for a value of one type to be stored where
another is. -/
def subConds (τ υ : TyS) : List CondS := if τ.subB υ then [] else [.sub τ υ]

theorem subConds_spec {ρ : Env} {τ υ : TyS} (h : CondS.all ρ (subConds τ υ)) :
    Sub (τ.den ρ) (υ.den ρ) := by
  unfold subConds at h
  split at h
  · next hs => exact TyS.subB_sound hs
  · exact h.1

/-- A store into a block the context owns that changes what the bytes hold:
a number is stored as plain bytes, and anything else gives the bytes its type. -/
def storeOwnedNew (next : BitVec 64) (Γ : CtxS) (s : Reg) (m : Mem) (pl : PlaceS) (cs : List CondS) (k : Nat)
    (a : Val) : Option (CtxS × List CondS) :=
  match Γ.regs.get s with
  | .int => writes next Γ 8 m
  | τ =>
    match pl.shape.set pl.off τ, within pl.off 8 pl.shape.size with
    | some S', some ws => some ({ Γ with owned := Γ.owned.set k (a, S') }, cs ++ ws)
    | _, _ => none

/-- A 64-bit store of a register to memory. -/
def store (next : BitVec 64) (Γ : CtxS) (s : Reg) (m : Mem) : Option (CtxS × List CondS) :=
  if s = .rsp then none
  else match locate next Γ m with
    | some (pl, cs) =>
      match pl.kind with
      | .ptr true =>
        match pl.shape.look pl.off with
        | some (some τ) =>
          if pl.shape.sole pl.off then some (Γ, cs ++ subConds (Γ.regs.get s) τ) else none
        | some none => writes next Γ 8 m
        | none =>
          -- an element of an array: a value of the type its elements have there
          match pl.shape.elem pl.off with
          | some (τ, es) =>
            if pl.shape.elemSole pl.off then
              some (Γ, (cs ++ es) ++ subConds (Γ.regs.get s) τ)
            else none
          | none => writes next Γ 8 m
      | .owned k a =>
        match pl.shape.look pl.off with
        | some (some τ) =>
          -- the type that is there is kept where what is stored has it
          if pl.shape.sole pl.off ∧ (Γ.regs.get s).subB τ = true then some (Γ, cs)
          else storeOwnedNew next Γ s m pl cs k a
        | some none => storeOwnedNew next Γ s m pl cs k a
        | none =>
          -- an element of an array keeps its type: what is stored must have it
          match pl.shape.elem pl.off with
          | some (τ, es) =>
            if pl.shape.elemSole pl.off = true ∧ (Γ.regs.get s).subB τ = true then
              some (Γ, cs ++ es)
            else none
          | none => storeOwnedNew next Γ s m pl cs k a
      | .piece _ => writes next Γ 8 m
      | .block true =>
        match pl.shape.look pl.off with
        | some (some τ) =>
          if pl.shape.sole pl.off then some (Γ, cs ++ subConds (Γ.regs.get s) τ) else none
        | some none => writes next Γ 8 m
        | none => none
      | _ => none
    | none => none

theorem storeOwnedNew_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    (hB : BlocksOk Ψ ρ Γ.blocks) {s : Reg}
    {m : Mem} {pl : PlaceS} {cs : List CondS} {k : Nat} {a : Val} {x : CtxS × List CondS}
    (hs : s ≠ .rsp) (hl : locate next Γ m = some (pl, cs)) (hk : pl.kind = .owned k a)
    (h : storeOwnedNew next Γ s m pl cs k a = some x) (hc : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) (.mov .w64 (.rm_r (.mem m) s)) (x.1.den ρ) := by
  unfold storeOwnedNew at h
  split at h
  · exact .storeInt (writes_sound hB h hc).1
  · split at h
    · next S' ws hset hw =>
      cases h
      obtain ⟨h₁, h₂⟩ := CondS.all_append _ _ hc
      have hloc := locate_spec hB (Ψ := Ψ) (next := next) hl h₁
      rw [hk] at hloc
      have hin : pl.off.den ρ + 8 ≤ (pl.shape.den ρ).size := by
        rw [ShapeS.den_size]; exact within_spec hw h₂
      have := hloc.storeOwned hs hin
      rw [CtxS.den_regs, ← ShapeS.den_set hset] at this
      have e : CtxS.den ρ { Γ with owned := Γ.owned.set k (a, S') }
          = { Γ.den ρ with owned := (Γ.den ρ).owned.set k (a.den ρ, S'.den ρ) } := by
        show ({ Γ.den ρ with owned := denOwned ρ (Γ.owned.set k (a, S')) _ } : Ctx) = _
        rw [denOwned_set ρ _ _ _ _ _ ((locate_listed hl).1 k a hk)]; rfl
      rw [e]; exact this
    · cases h

theorem store_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    (hB : BlocksOk Ψ ρ Γ.blocks) {s : Reg} {m : Mem}
    {x : CtxS × List CondS} (h : store next Γ s m = some x) (hc : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) (.mov .w64 (.rm_r (.mem m) s)) (x.1.den ρ) := by
  unfold store at h
  split at h
  · cases h
  next hs =>
  split at h
  · next pl cs hl =>
    split at h
    · next hk =>
      split at h
      · next τ hτ =>
        split at h
        · next hso =>
          cases h
          obtain ⟨h₁, h₂⟩ := CondS.all_append _ _ hc
          have hloc := locate_spec hB (Ψ := Ψ) (next := next) hl h₁
          rw [hk] at hloc
          exact hloc.storePtr hs (ShapeS.look_typed hτ) (ShapeS.den_sole hso)
            (by rw [CtxS.den_regs]; exact subConds_spec h₂)
        · cases h
      · exact .storeInt (writes_sound hB h hc).1
      · split at h
        · next τ es he =>
          split at h
          · next hso =>
            cases h
            obtain ⟨h₁, h₂⟩ := CondS.all_append _ _ hc
            obtain ⟨h₁₁, h₁₂⟩ := CondS.all_append _ _ h₁
            have hloc := locate_spec hB (Ψ := Ψ) (next := next) hl h₁₁
            rw [hk] at hloc
            exact hloc.storePtr hs (ShapeS.elem_typed (x := (τ, es)) he h₁₂)
              (ShapeS.elemSole_spec (x := (τ, es)) he h₁₂ hso)
              (by rw [CtxS.den_regs]; exact subConds_spec h₂)
          · cases h
        · exact .storeInt (writes_sound hB h hc).1
    · next k a hk =>
      split at h
      · next τ hτ =>
        split at h
        · next hkeep =>
          cases h
          have hloc := locate_spec hB (Ψ := Ψ) (next := next) hl hc
          rw [hk] at hloc
          exact hloc.storeOwnedKeep hs (ShapeS.look_typed hτ) (ShapeS.den_sole hkeep.1)
            (by rw [CtxS.den_regs]; exact TyS.subB_sound hkeep.2)
        · exact storeOwnedNew_sound hB hs hl hk h hc
      · exact storeOwnedNew_sound hB hs hl hk h hc
      · split at h
        · next τ es he =>
          split at h
          · next hkeep =>
            cases h
            obtain ⟨h₁, h₂⟩ := CondS.all_append _ _ hc
            have hloc := locate_spec hB (Ψ := Ψ) (next := next) hl h₁
            rw [hk] at hloc
            exact hloc.storeOwnedKeep hs (ShapeS.elem_typed (x := (τ, es)) he h₂)
              (ShapeS.elemSole_spec (x := (τ, es)) he h₂ hkeep.1)
              (by rw [CtxS.den_regs]; exact TyS.subB_sound hkeep.2)
          · cases h
        · exact storeOwnedNew_sound hB hs hl hk h hc
    · exact .storeInt (writes_sound hB h hc).1
    · next hk =>
      split at h
      · next τ hτ =>
        split at h
        · next hso =>
          cases h
          obtain ⟨h₁, h₂⟩ := CondS.all_append _ _ hc
          have hloc := locate_spec hB (Ψ := Ψ) (next := next) hl h₁
          exact hloc.storeBlock (by rw [hk]; rfl) hs (ShapeS.look_typed hτ) (ShapeS.den_sole hso)
            (by rw [CtxS.den_regs]; exact subConds_spec h₂)
        · cases h
      · exact .storeInt (writes_sound hB h hc).1
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
def aluMem (next : BitVec 64) (Γ : CtxS) (op : AluOp) (w : Width) (m : Mem) : Option (CtxS × List CondS) :=
  if op.writesDst then
    (writes next Γ w.bytes.toNat m).map fun x =>
      ({ x.1 with flags := .known }, x.2 ++ carryConds Γ.flags op)
  else (reads next Γ w.bytes.toNat m).map fun cs => ({ Γ with flags := .known }, cs)

theorem aluMem_spec {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    (hB : BlocksOk Ψ ρ Γ.blocks) {op : AluOp} {w : Width}
    {m : Mem} {x : CtxS × List CondS} (h : aluMem next Γ op w m = some x) (hn : CondS.all ρ x.2) :
    (op.writesDst = true ∧ ∃ Γ', x.1.den ρ = { Γ' with flags := Flags.Known } ∧
        ReadOk Ψ next (Γ.den ρ) w.bytes.toNat (.mem m) ∧
        WriteIntOk Ψ next (Γ.den ρ) w.bytes.toNat (.mem m) Γ' ∧
        (op.readsCarry = true → ∀ f, (Γ.den ρ).flags f → f.cf.isSome = true)) ∨
    (op.writesDst = false ∧ x.1.den ρ = { Γ.den ρ with flags := Flags.Known } ∧
        ReadOk Ψ next (Γ.den ρ) w.bytes.toNat (.mem m)) := by
  unfold aluMem at h
  split at h
  · next hwd =>
    cases hw : writes next Γ w.bytes.toNat m with
    | none => rw [hw] at h; cases h
    | some y =>
      rw [hw] at h; cases h
      obtain ⟨h₁, h₂⟩ := CondS.all_append _ _ hn
      obtain ⟨hwr, hrd⟩ := writes_sound hB (Ψ := Ψ) (next := next) hw h₁
      exact .inl ⟨hwd, y.1.den ρ, rfl, hrd, hwr, carryConds_spec h₂⟩
  · next hwd =>
    cases hr : reads next Γ w.bytes.toNat m with
    | none => rw [hr] at h; cases h
    | some cs =>
      rw [hr] at h; cases h
      exact .inr ⟨(Bool.not_eq_true _).mp hwd, rfl, reads_sound hB hr hn⟩

/-- A step that only reads `n` bytes of an operand: what it leaves to be
shown is that they may be read. -/
theorem reads_map {next : BitVec 64} {Γ : CtxS} {n : Nat} {m : Mem} {f : List CondS → CtxS × List CondS}
    {x : CtxS × List CondS} (h : (reads next Γ n m).map f = some x) :
    ∃ cs, reads next Γ n m = some cs ∧ x = f cs := by
  cases hr : reads next Γ n m with
  | none => rw [hr] at h; cases h
  | some cs => rw [hr] at h; cases h; exact ⟨cs, rfl, rfl⟩

theorem writes_map {next : BitVec 64} {Γ : CtxS} {n : Nat} {m : Mem} {f : CtxS × List CondS → CtxS × List CondS}
    {x : CtxS × List CondS} (h : (writes next Γ n m).map f = some x) :
    ∃ y, writes next Γ n m = some y ∧ x = f y := by
  cases hw : writes next Γ n m with
  | none => rw [hw] at h; cases h
  | some y => rw [hw] at h; cases h; exact ⟨y, rfl, rfl⟩

/-! ### What the flags say of a condition -/

/-- Whether flags known this way have all four defined. -/
def FlagsS.allDefined : FlagsS → Bool
  | .known => true
  | .alu _ _ _ _ => true
  | .test _ _ => true
  | .neg _ _ => true
  | .popcnt _ _ => true
  | .lit f => f.defined
  | _ => false

theorem FlagsS.allDefined_spec {ρ : Env} {fl : FlagsS} (h : fl.allDefined = true) :
    ∀ f, fl.den ρ f → f.defined = true := by
  intro f hf
  cases fl with
  | known => exact hf
  | alu op w a b => cases w <;> (rw [show f = _ from hf]; exact AluOp.apply_defined _ _ _)
  | test a b => rw [show f = _ from hf]; exact Flags.ofResult_defined _ _ _
  | neg w a => rw [show f = _ from hf]; exact subBorrow_defined _ _ _
  | popcnt w a => rw [show f = _ from hf]; rfl
  | lit g => rw [show f = g from hf]; exact h
  | any => cases h
  | defined _ _ _ _ => cases h
  | imul _ _ _ => cases h
  | atom _ => cases h

/-- What is left to be shown for the flags to decide a condition: nothing
where they are all defined. -/
def decideConds (fl : FlagsS) (c : Cond) : List CondS :=
  if fl.allDefined then [] else [.decides fl c]

theorem decideConds_spec {ρ : Env} {fl : FlagsS} {c : Cond}
    (h : CondS.all ρ (decideConds fl c)) : ∀ f, fl.den ρ f → ∃ b, c.eval f = some b := by
  unfold decideConds at h
  split at h
  · next hd => exact fun f hf => Cond.eval_some (FlagsS.allDefined_spec hd f hf) c
  · exact h.1

/-- What the flags make of a condition, where they are exactly known from
values that are numbers. -/
def FlagsS.eval? : FlagsS → Cond → Option Bool
  | .lit f, c => c.eval f
  | .alu op .w64 (.lit a) (.lit b), c => c.eval (op.apply a b).2
  | .alu op .w32 (.lit a) (.lit b), c => c.eval (op.apply (a.setWidth 32) (b.setWidth 32)).2
  | .test (.lit a) (.lit b), c => c.eval (Flags.ofResult (a &&& b) false false)
  | _, _ => none

theorem FlagsS.eval?_spec {ρ : Env} {fl : FlagsS} {c : Cond} {b : Bool}
    (h : fl.eval? c = some b) : ∀ f, fl.den ρ f → c.eval f = some b := by
  intro f hf
  unfold FlagsS.eval? at h
  split at h
  · rw [show f = _ from hf]; exact h
  · rw [show f = _ from hf]; exact h
  · rw [show f = _ from hf]; exact h
  · rw [show f = _ from hf]; exact h
  · cases h

/-- The checker for `setcc`. -/
def stepSetcc (next : BitVec 64) (Γ : CtxS) (c : Cond) (dst : RM) : Option (CtxS × List CondS) :=
  match dst with
  | .mem m => (writes next Γ 1 m).map fun x => (x.1, x.2 ++ decideConds Γ.flags c)
  | .reg d =>
    if d = .rsp then none
    else match exactly (Γ.regs.get d), Γ.flags.eval? c with
      | some v, some b => some (Γ.setReg d (.eq (.mk1 (.setcc b) v)), [])
      | _, _ => some (Γ.setReg d .int, decideConds Γ.flags c)

theorem stepSetcc_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    (hB : BlocksOk Ψ ρ Γ.blocks) {c : Cond} {dst : RM}
    {x : CtxS × List CondS} (h : stepSetcc next Γ c dst = some x) (hn : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) (.setcc c dst) (x.1.den ρ) := by
  unfold stepSetcc at h
  split at h
  · next m =>
    obtain ⟨y, hw, rfl⟩ := writes_map h
    obtain ⟨h₁, h₂⟩ := CondS.all_append _ _ hn
    exact .setccRM (writes_sound hB hw h₁).1 (decideConds_spec h₂)
  · next d =>
    split at h
    · cases h
    · next hd =>
      split at h
      · next v b hv hb =>
        cases h
        exact cast_ctx (.setccExact hd (by rw [CtxS.den_regs, exactly_den hv])
          (FlagsS.eval?_spec hb)) (CtxS.den_setReg_mk1 ρ Γ d (.setcc b) v)
      · cases h
        rw [CtxS.den_setReg]
        exact .setccRM (.reg hd) (decideConds_spec hn)

/-- The checker for `cmov`. -/
def stepCmov (next : BitVec 64) (Γ : CtxS) (c : Cond) (w : Width) (d : Reg) (src : RM) :
    Option (CtxS × List CondS) :=
  if d = .rsp then none
  else match src with
    | .mem m =>
      (reads next Γ w.bytes.toNat m).map fun cs => (Γ.setReg d .int, cs ++ decideConds Γ.flags c)
    | .reg r =>
      match exactly (Γ.regs.get d), exactly (Γ.regs.get r), Γ.flags.eval? c with
      | some v, some a, some b =>
        if r = .rsp then some (Γ.setReg d .int, decideConds Γ.flags c)
        else some (Γ.setReg d (.eq (.mk2 (.cmov w b) v a)), [])
      | _, _, _ => some (Γ.setReg d .int, decideConds Γ.flags c)

theorem stepCmov_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    (hB : BlocksOk Ψ ρ Γ.blocks) {c : Cond} {w : Width}
    {d : Reg} {src : RM} {x : CtxS × List CondS} (h : stepCmov next Γ c w d src = some x)
    (hn : CondS.all ρ x.2) : Straight Ψ next (Γ.den ρ) (.cmov c w d src) (x.1.den ρ) := by
  unfold stepCmov at h
  split at h
  · cases h
  next hd =>
  split at h
  · next m =>
    obtain ⟨cs, hr, rfl⟩ := reads_map h
    obtain ⟨h₁, h₂⟩ := CondS.all_append _ _ hn
    rw [CtxS.den_setReg]
    exact .cmovRM hd (reads_sound hB hr h₁) (decideConds_spec h₂)
  · next r =>
    split at h
    · next v a b hv ha hb =>
      split at h
      · cases h
        rw [CtxS.den_setReg]
        exact .cmovRM hd (.reg _) (decideConds_spec hn)
      · next hr =>
        cases h
        refine cast_ctx (.cmovExact hd hr (by rw [CtxS.den_regs, exactly_den hv])
          (by rw [CtxS.den_regs, exactly_den ha]) (FlagsS.eval?_spec hb)) ?_
        rw [CtxS.den_setReg]
        show CtxOf.setReg _ _ (.eq ((Val.mk2 (.cmov w b) v a).den ρ)) = _
        rw [Val.den_mk2]; rfl
    · cases h
      rw [CtxS.den_setReg]
      exact .cmovRM hd (.reg _) (decideConds_spec hn)

/-- What is known of the flags after a shift or rotate by a number of bits. -/
def flagsAfterS (op : ShiftOp) (c : Nat) (fl : FlagsS) : FlagsS :=
  if c = 0 then fl
  else match op with
    | .shl | .shr | .sar => .defined true true true (c == 1)
    | .rol | .ror => .defined true false false (c == 1)

theorem den_flagsAfterS (ρ : Env) (op : ShiftOp) (c : Nat) (fl : FlagsS) :
    (flagsAfterS op c fl).den ρ = op.flagsAfter c (fl.den ρ) := by
  unfold flagsAfterS ShiftOp.flagsAfter
  split
  · rfl
  · cases op <;> rfl

/-- The checker for shifts and rotates. -/
def stepShift (next : BitVec 64) (Γ : CtxS) (op : ShiftOp) (w : Width) (dst : RM) (c : Count) :
    Option (CtxS × List CondS) :=
  match dst, c with
  | .reg d, .imm n =>
    if d = .rsp then none
    else match exactly (Γ.regs.get d) with
      | some a =>
        some ({ Γ.setReg d (.eq (.mk1 (.shift op w (n.toNat % w.bits)) a)) with
          flags := flagsAfterS op (n.toNat % w.bits) Γ.flags }, [])
      | none =>
        some ({ Γ.setReg d .int with flags := flagsAfterS op (n.toNat % w.bits) Γ.flags }, [])
  | .reg d, .cl =>
    if d = .rsp then none else some ({ Γ.setReg d .int with flags := .any }, [])
  | .mem m, .imm n =>
    (writes next Γ w.bytes.toNat m).map fun x =>
      ({ x.1 with flags := flagsAfterS op (n.toNat % w.bits) Γ.flags }, x.2)
  | .mem m, .cl => (writes next Γ w.bytes.toNat m).map fun x => ({ x.1 with flags := .any }, x.2)

theorem stepShift_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    (hB : BlocksOk Ψ ρ Γ.blocks) {op : ShiftOp}
    {w : Width} {dst : RM} {c : Count} {x : CtxS × List CondS}
    (h : stepShift next Γ op w dst c = some x) (hn : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) (.shift op w dst c) (x.1.den ρ) := by
  unfold stepShift at h
  split at h
  · next d n =>
    split at h
    · cases h
    · next hd =>
      split at h
      · next a ha =>
        cases h
        refine cast_ctx (.shiftExact hd (by rw [CtxS.den_regs, exactly_den ha])) ?_
        rw [CtxS.den_setReg_mk1_flags, den_flagsAfterS]; rfl
      · cases h
        refine cast_ctx (.shiftImm (.reg _) (.reg hd)) ?_
        rw [CtxS.den_setReg_flags, den_flagsAfterS]; rfl
  · next d =>
    split at h
    · cases h
    · next hd =>
      cases h
      exact cast_ctx (.shiftCl (.reg _) (.reg hd)) (by rw [CtxS.den_setReg_flags]; rfl)
  · next m n =>
    obtain ⟨y, hw, rfl⟩ := writes_map h
    obtain ⟨hwr, hrd⟩ := writes_sound hB (Ψ := Ψ) (next := next) hw hn
    refine cast_ctx (.shiftImm hrd hwr) ?_
    show ({ y.1.den ρ with flags := (flagsAfterS op _ Γ.flags).den ρ } : Ctx) = _
    rw [den_flagsAfterS]; rfl
  · next m =>
    obtain ⟨y, hw, rfl⟩ := writes_map h
    obtain ⟨hwr, hrd⟩ := writes_sound hB (Ψ := Ψ) (next := next) hw hn
    exact cast_ctx (.shiftCl hrd hwr) rfl

/-- The context after a multiply whose result is only known to be a number. -/
def afterMulS (Γ : CtxS) : CtxS :=
  { (Γ.setReg .rax .int).setReg .rdx .int with flags := .defined true false false true }

theorem den_afterMulS (ρ : Env) (Γ : CtxS) :
    (afterMulS Γ).den ρ = (Γ.den ρ).afterMulDiv Flags.AfterMul := by
  unfold afterMulS
  rw [CtxS.den_setReg_flags, CtxS.den_setReg]; rfl

/-- What is left to be shown for a value to be zero at a width: nothing
where it is a number that is. -/
def zeroConds (w : Width) (v : Val) : Option (List CondS) :=
  match v with
  | .lit n => if n.setWidth w.bits = 0 then some [] else none
  | v => some [.zeroW w v]

theorem zeroConds_spec {ρ : Env} {w : Width} {v : Val} {cs : List CondS}
    (h : zeroConds w v = some cs) (hc : CondS.all ρ cs) : (v.den ρ).setWidth w.bits = 0 := by
  unfold zeroConds at h
  split at h
  · split at h
    · next hz => exact hz
    · cases h
  · cases h; exact hc.1

/-- What is left to be shown for a value not to be zero at a width. -/
def nonzeroConds (w : Width) (v : Val) : Option (List CondS) :=
  match v with
  | .lit n => if n.setWidth w.bits = 0 then none else some []
  | v => some [.nonzeroW w v]

theorem nonzeroConds_spec {ρ : Env} {w : Width} {v : Val} {cs : List CondS}
    (h : nonzeroConds w v = some cs) (hc : CondS.all ρ cs) : (v.den ρ).setWidth w.bits ≠ 0 := by
  unfold nonzeroConds at h
  split at h
  · split at h
    · cases h
    · next hz => exact hz
  · cases h; exact hc.1

/-- A divide of exactly known values that are not all numbers: its results,
exactly known, and what is left to be shown for it not to fault. -/
def divideVals (Γ : CtxS) (op : MulDivOp) (w : Width) (a d b : Val) :
    Option (CtxS × List CondS) :=
  match op with
  | .div =>
    match zeroConds w d, nonzeroConds w b with
    | some c₁, some c₂ =>
      some ({ (Γ.setReg .rax (.eq (.mk2 (.udiv w) a b))).setReg .rdx
        (.eq (.mk2 (.urem w) a b)) with flags := .lit Flags.unknown }, c₁ ++ c₂)
    | _, _ => none
  | .idiv =>
    match nonzeroConds w b with
    | some c₂ =>
      some ({ (Γ.setReg .rax (.eq (.mk2 (.sdiv w) a b))).setReg .rdx
        (.eq (.mk2 (.srem w) a b)) with flags := .lit Flags.unknown },
        .sfill w d a :: .noOvf w a b :: c₂)
    | none => none
  | _ => none

theorem divideVals_spec {ρ : Env} {Γ : CtxS} {op : MulDivOp} {w : Width} {a d b : Val}
    {x : CtxS × List CondS} (h : divideVals Γ op w a d b = some x) (hn : CondS.all ρ x.2) :
    ∃ lo hi fl, op.eval ((d.den ρ).setWidth w.bits) ((a.den ρ).setWidth w.bits)
        ((b.den ρ).setWidth w.bits) = .next (lo, hi, fl) ∧
      x.1.den ρ = { ((Γ.den ρ).setReg .rax (.eq (lo.setWidth 64))).setReg .rdx
        (.eq (hi.setWidth 64)) with flags := (· = fl) } := by
  unfold divideVals at h
  have ctx : ∀ (f g : Op2),
      CtxS.den ρ { (Γ.setReg .rax (.eq (.mk2 f a b))).setReg .rdx (.eq (.mk2 g a b)) with
        flags := .lit Flags.unknown }
      = { ((Γ.den ρ).setReg .rax (.eq (f.den (a.den ρ) (b.den ρ)))).setReg .rdx
          (.eq (g.den (a.den ρ) (b.den ρ))) with flags := (· = Flags.unknown) } := by
    intro f g
    rw [CtxS.den_setReg_flags, CtxS.den_setReg]
    show ({ CtxOf.setReg (CtxOf.setReg _ _ (.eq ((Val.mk2 f a b).den ρ))) _
      (.eq ((Val.mk2 g a b).den ρ)) with flags := _ } : Ctx) = _
    rw [Val.den_mk2, Val.den_mk2]; rfl
  split at h
  · split at h
    · next c₁ c₂ h₁ h₂ =>
      cases h
      obtain ⟨hc₁, hc₂⟩ := CondS.all_append _ _ hn
      have hz := zeroConds_spec h₁ hc₁
      have hnz := nonzeroConds_spec h₂ hc₂
      exact ⟨_, _, _, by rw [hz]; exact MulDivOp.eval_div _ _ hnz, ctx (.udiv w) (.urem w)⟩
    · cases h
  · split at h
    · next c₂ h₂ =>
      cases h
      have hnz := nonzeroConds_spec h₂ hn.2.2
      exact ⟨_, _, _, by
        rw [show (d.den ρ).setWidth w.bits = _ from hn.1]
        exact MulDivOp.eval_idiv _ _ hnz hn.2.1, ctx (.sdiv w) (.srem w)⟩
    · cases h
  · cases h

/-- A divide by a register, of exactly known values. -/
def divide (Γ : CtxS) (op : MulDivOp) (w : Width) (r : Reg) (a d b : Val) :
    Option (CtxS × List CondS) :=
  if r = .rsp then none else divideVals Γ op w a d b

theorem divide_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS} {op : MulDivOp}
    {w : Width} {r : Reg} {a d b : Val} {x : CtxS × List CondS}
    (ha : (Γ.den ρ).regs .rax = .eq (a.den ρ)) (hd : (Γ.den ρ).regs .rdx = .eq (d.den ρ))
    (hb : (Γ.den ρ).regs r = .eq (b.den ρ))
    (h : divide Γ op w r a d b = some x) (hn : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) (.mulDiv op w (.reg r)) (x.1.den ρ) := by
  unfold divide at h
  split at h
  · cases h
  · next hr =>
    obtain ⟨lo, hi, fl, hev, e⟩ := divideVals_spec h hn
    rw [e]; exact .mulDivExact hr ha hd hb hev

/-- Whether the rules have a form for a typed value held at a place of this
kind, reached by this operand. -/
def holdable (κ : KindS) (m : Mem) : Bool :=
  match κ, m with
  | .owned _ _, _ => false
  | _, .sib (some .rsp) (some _) _ => false
  | _, _ => true

theorem holdable_spec {ρ : Env} {κ : KindS} {m : Mem} (h : holdable κ m = true) :
    (∀ k a, κ.den ρ ≠ .owned k a) ∧ (∀ x d, m ≠ .sib (some .rsp) (some x) d) := by
  unfold holdable at h
  split at h
  · cases h
  · cases h
  · next h₁ h₂ =>
    refine ⟨fun k a e => ?_, fun x d e => h₂ x d e⟩
    cases κ with
    | owned k' a' => exact h₁ k' a' rfl
    | ptr _ => cases e
    | piece _ => cases e
    | block _ => cases e

/-- A divide by an exactly known value held in memory. -/
def divideMem (next : BitVec 64) (Γ : CtxS) (op : MulDivOp) (w : Width) (m : Mem) :
    Option (CtxS × List CondS) :=
  match locate next Γ m, exactly (Γ.regs.get .rax), exactly (Γ.regs.get .rdx) with
  | some (pl, cs), some a, some d =>
    if holdable pl.kind m then
      match pl.shape.look pl.off with
      | some (some (.eq b)) => (divideVals Γ op w a d b).map fun x => (x.1, cs ++ x.2)
      | _ => none
    else none
  | _, _, _ => none

theorem divideMem_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    (hB : BlocksOk Ψ ρ Γ.blocks) {op : MulDivOp} {w : Width} {m : Mem} {x : CtxS × List CondS}
    (h : divideMem next Γ op w m = some x) (hn : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) (.mulDiv op w (.mem m)) (x.1.den ρ) := by
  unfold divideMem at h
  split at h
  · next pl cs a d hl ha hd =>
    split at h
    · next hh =>
      split at h
      · next b hτ =>
        cases hv : divideVals Γ op w a d b with
        | none => rw [hv] at h; cases h
        | some y =>
          rw [hv] at h; cases h
          obtain ⟨h₁, h₂⟩ := CondS.all_append _ _ hn
          obtain ⟨lo, hi, fl, hev, e⟩ := divideVals_spec hv h₂
          obtain ⟨hκ, hm⟩ := holdable_spec (ρ := ρ) hh
          have hloc := locate_spec hB (Ψ := Ψ) (next := next) hl h₁
          rw [e]
          exact .mulDivHeld (hloc.holds hκ hm (ShapeS.look_typed hτ))
            (by rw [CtxS.den_regs, exactly_den ha]) (by rw [CtxS.den_regs, exactly_den hd]) hev
      · cases h
    · cases h
  · cases h

/-- The checker for the widening multiplies and the divides. Values that are
numbers are multiplied or divided at once; a multiply of anything else gives
numbers; a divide of exactly known values is typed where it is shown not to
fault. -/
def stepMulDiv (next : BitVec 64) (Γ : CtxS) (op : MulDivOp) (w : Width) (src : RM) : Option (CtxS × List CondS) :=
  match src with
  | .reg r =>
    match Γ.regs.get .rax, Γ.regs.get .rdx, Γ.regs.get r with
    | .eq (.lit a), .eq (.lit d), .eq (.lit b) =>
      if r = .rsp then none
      else match op.eval (d.setWidth w.bits) (a.setWidth w.bits) (b.setWidth w.bits) with
        | .next (lo, hi, fl) =>
          some ({ (Γ.setReg .rax (.eq (.lit (lo.setWidth 64)))).setReg .rdx
            (.eq (.lit (hi.setWidth 64))) with flags := .lit fl }, [])
        | _ => none
    | _, _, _ =>
      match op with
      | .mul => some (afterMulS Γ, [])
      | .imul => some (afterMulS Γ, [])
      | op =>
        match exactly (Γ.regs.get .rax), exactly (Γ.regs.get .rdx), exactly (Γ.regs.get r) with
        | some a, some d, some b => divide Γ op w r a d b
        | _, _, _ => none
  | .mem m =>
    match op with
    | .mul => (reads next Γ w.bytes.toNat m).map fun cs => (afterMulS Γ, cs)
    | .imul => (reads next Γ w.bytes.toNat m).map fun cs => (afterMulS Γ, cs)
    | op => divideMem next Γ op w m

theorem stepMulDiv_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    (hB : BlocksOk Ψ ρ Γ.blocks) {op : MulDivOp}
    {w : Width} {src : RM} {x : CtxS × List CondS}
    (h : stepMulDiv next Γ op w src = some x) (hn : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) (.mulDiv op w src) (x.1.den ρ) := by
  unfold stepMulDiv at h
  split at h
  · next r =>
    split at h
    · next a d b ha hd hb =>
      split at h
      · cases h
      · next hr =>
        split at h
        · next lo hi fl hev =>
          cases h
          refine cast_ctx (.mulDivExact hr (a := a) (d := d) (b := b)
            (by rw [CtxS.den_regs, ha]; rfl) (by rw [CtxS.den_regs, hd]; rfl)
            (by rw [CtxS.den_regs, hb]; rfl) hev) ?_
          rw [CtxS.den_setReg_flags, CtxS.den_setReg]; rfl
        · cases h
    · split at h
      · cases h; rw [den_afterMulS]; exact .mulRM (.reg _)
      · cases h; rw [den_afterMulS]; exact .imulRM (.reg _)
      · split at h
        · next a d b ha hd hb =>
          exact divide_sound (by rw [CtxS.den_regs, exactly_den ha])
            (by rw [CtxS.den_regs, exactly_den hd]) (by rw [CtxS.den_regs, exactly_den hb]) h hn
        · cases h
  · next m =>
    split at h
    · obtain ⟨cs, hr, rfl⟩ := reads_map h
      rw [den_afterMulS]; exact .mulRM (reads_sound hB hr hn)
    · obtain ⟨cs, hr, rfl⟩ := reads_map h
      rw [den_afterMulS]; exact .imulRM (reads_sound hB hr hn)
    · exact divideMem_sound hB h hn

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
  | .w64, (.rm_r (.mem m) s) => store next Γ s m
  | .w64, (.r_m d m) => load next Γ d m
  | w, (.r_m d m) =>
    if d = .rsp then none else (reads next Γ w.bytes.toNat m).map fun cs => (Γ.setReg d .int, cs)
  | .w32, (.rm_r (.mem m) _) => writes next Γ 4 m
  | w, (.rm_i (.mem m) _) => writes next Γ w.bytes.toNat m

theorem stepMov_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    (hB : BlocksOk Ψ ρ Γ.blocks)
    
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
  · exact store_sound hB h hn
  · exact load_sound hB h hn
  · split at h
    · cases h
    · next hd =>
      cases hr : reads next Γ _ _ with
      | none => rw [hr] at h; cases h
      | some cs =>
        rw [hr] at h; cases h
        rw [CtxS.den_setReg]
        exact .loadInt hd (reads_sound hB hr hn)
  · exact .storeInt (writes_sound hB h hn).1
  · exact .storeImm (writes_sound hB h hn).1

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
    else (reads next Γ w.bytes.toNat m).map fun cs => (afterAlu Γ op d, cs ++ carryConds Γ.flags op)
  | op, w, (.rm_r (.mem m) _) => aluMem next Γ op w m
  | op, w, (.rm_i (.mem m) _) => aluMem next Γ op w m
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
          else some (afterAlu Γ op d, carryConds Γ.flags op)
        | _, _ => some (afterAlu Γ op d, carryConds Γ.flags op)
      | .str true =>
        match op, w with
        | .add, .w64 =>
          if imm = 1 then some ({ Γ.setReg d (.str false) with flags := .known }, [])
          else some (afterAlu Γ op d, carryConds Γ.flags op)
        | _, _ => some (afterAlu Γ op d, carryConds Γ.flags op)
      -- anything else is a number once arithmetic has been done on it
      | _ => some (afterAlu Γ op d, carryConds Γ.flags op)

theorem stepAlu_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    (hB : BlocksOk Ψ ρ Γ.blocks)
    
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
      cases hr : reads next Γ _ _ with
      | none => rw [hr] at h; cases h
      | some cs =>
        rw [hr] at h; cases h
        obtain ⟨h₁, h₂⟩ := CondS.all_append _ _ hn
        rw [den_afterAlu]
        exact .aluLoad hd (reads_sound hB hr h₁) (carryConds_spec h₂)
  · rcases aluMem_spec hB (Ψ := Ψ) (next := next) h hn with ⟨hwd, Γ', e, hr, hw, hcf⟩ | ⟨hwd, e, hr⟩
    · rw [e]; exact .aluStoreR hwd hr hw hcf
    · rw [e]; exact .cmpR hwd hr
  · rcases aluMem_spec hB (Ψ := Ψ) (next := next) h hn with ⟨hwd, Γ', e, hr, hw, hcf⟩ | ⟨hwd, e, hr⟩
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
        · cases h; rw [den_afterAlu]; exact .aluRI hd (carryConds_spec hn)
      · cases h; rw [den_afterAlu]; exact .aluRI hd (carryConds_spec hn)
    · next hΓ =>
      split at h
      · split at h
        · next hi =>
          cases h; subst hi
          have hΓd : (Γ.den ρ).regs d = .str true := by rw [CtxS.den_regs, hΓ]; rfl
          exact cast_ctx (.strNext hd hΓd) (by rw [CtxS.den_setReg_flags]; rfl)
        · cases h; rw [den_afterAlu]; exact .aluRI hd (carryConds_spec hn)
      · cases h; rw [den_afterAlu]; exact .aluRI hd (carryConds_spec hn)
    · cases h; rw [den_afterAlu]; exact .aluRI hd (carryConds_spec hn)

/-- The checker for `test`. -/
def stepTest (next : BitVec 64) (Γ : CtxS) (w : Width) (dst : RM) (src : RI) :
    Option (CtxS × List CondS) :=
  match w, dst, src with
  | w, (.mem m), _ =>
    (reads next Γ w.bytes.toNat m).map fun cs => ({ Γ with flags := .known }, cs)
  | .w64, (.reg r), (.reg r') =>
    match exactly (Γ.regs.get r), exactly (Γ.regs.get r') with
    | some a, some b =>
      if r = .rsp ∨ r' = .rsp then some ({ Γ with flags := .known }, [])
      else some ({ Γ with flags := .test a b }, [])
    | _, _ => some ({ Γ with flags := .known }, [])
  | _, (.reg _), _ => some ({ Γ with flags := .known }, [])

theorem stepTest_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    (hB : BlocksOk Ψ ρ Γ.blocks)
    
    {x : CtxS × List CondS} (h : stepTest next Γ w dst src = some x)
    (hn : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) (.test w dst src) (x.1.den ρ) := by
  unfold stepTest at h
  split at h
  · obtain ⟨cs, hr, rfl⟩ := reads_map h
    exact .testRM (reads_sound hB hr hn)
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
    else (reads next Γ w.bytes.toNat m).map fun cs =>
      ({ Γ.setReg d .int with flags := .defined true false false true }, cs)
  | w, d, .reg r =>
    if d = .rsp then none
    else match exactly (Γ.regs.get d), exactly (Γ.regs.get r) with
      | some a, some b =>
        if r = .rsp then some ({ Γ.setReg d .int with flags := .defined true false false true }, [])
        else some ({ Γ.setReg d (.eq (.mk2 (.imul w) a b)) with flags := .imul w a b }, [])
      | _, _ => some ({ Γ.setReg d .int with flags := .defined true false false true }, [])

theorem stepImul2_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    (hB : BlocksOk Ψ ρ Γ.blocks)
    
    {x : CtxS × List CondS} (h : stepImul2 next Γ w d src = some x)
    (hn : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) (.imul2 w d src) (x.1.den ρ) := by
  unfold stepImul2 at h
  split at h
  · split at h
    · cases h
    · next hd =>
      obtain ⟨cs, hr, rfl⟩ := reads_map h
      exact cast_ctx (.imul2RM hd (reads_sound hB hr hn)) (by rw [CtxS.den_setReg_flags]; rfl)
  · next r =>
    split at h
    · cases h
    · next hd =>
      split at h
      · next a b ha hb =>
        split at h
        · cases h; exact cast_ctx (.imul2RM hd (.reg _)) (by rw [CtxS.den_setReg_flags]; rfl)
        · next hr =>
          cases h
          exact cast_ctx (.imul2Exact hd hr (by rw [CtxS.den_regs, exactly_den ha])
            (by rw [CtxS.den_regs, exactly_den hb]))
            (CtxS.den_setReg_mk2_flags ρ Γ d (.imul w) a b (.imul w a b))
      · cases h; exact cast_ctx (.imul2RM hd (.reg _)) (by rw [CtxS.den_setReg_flags]; rfl)

/-- The checker for `imul3`. -/
def stepImul3 (next : BitVec 64) (Γ : CtxS) (w : Width) (d : Reg) (src : RM) (imm : BitVec 32) :
    Option (CtxS × List CondS) :=
  match w, d, src, imm with
  | w, d, (.mem m), _ =>
    if d = .rsp then none
    else (reads next Γ w.bytes.toNat m).map fun cs =>
      ({ Γ.setReg d .int with flags := .defined true false false true }, cs)
  | w, d, .reg r, imm =>
    if d = .rsp then none
    else match exactly (Γ.regs.get r) with
      | some b =>
        if r = .rsp then some ({ Γ.setReg d .int with flags := .defined true false false true }, [])
        else
          some ({ Γ.setReg d (.eq (.mk2 (.imul w) b (immW w imm))) with
            flags := .imul w b (immW w imm) }, [])
      | none => some ({ Γ.setReg d .int with flags := .defined true false false true }, [])

theorem stepImul3_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    (hB : BlocksOk Ψ ρ Γ.blocks)
    
    {x : CtxS × List CondS} (h : stepImul3 next Γ w d src imm = some x)
    (hn : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) (.imul3 w d src imm) (x.1.den ρ) := by
  unfold stepImul3 at h
  split at h
  · split at h
    · cases h
    · next hd =>
      obtain ⟨cs, hr, rfl⟩ := reads_map h
      exact cast_ctx (.imul3RM hd (reads_sound hB hr hn)) (by rw [CtxS.den_setReg_flags]; rfl)
  · next r =>
    split at h
    · cases h
    · next hd =>
      split at h
      · next b hb =>
        split at h
        · cases h; exact cast_ctx (.imul3RM hd (.reg _)) (by rw [CtxS.den_setReg_flags]; rfl)
        · next hr =>
          cases h
          refine cast_ctx (.imul3Exact (imm := imm) hd hr (by rw [CtxS.den_regs, exactly_den hb])) ?_
          rw [CtxS.den_setReg_mk2_flags]
          simp only [Op2.den, FlagsS.den, immW, Val.den, low_high]
      · cases h; exact cast_ctx (.imul3RM hd (.reg _)) (by rw [CtxS.den_setReg_flags]; rfl)

/-- The checker for `popcnt`. -/
def stepPopcnt (next : BitVec 64) (Γ : CtxS) (w : Width) (d : Reg) (src : RM) :
    Option (CtxS × List CondS) :=
  match w, d, src with
  | w, d, (.mem m) =>
    if d = .rsp then none
    else (reads next Γ w.bytes.toNat m).map fun cs => ({ Γ.setReg d .int with flags := .known }, cs)
  | w, d, (.reg r) =>
    if d = .rsp then none
    else match exactly (Γ.regs.get r) with
      | some a =>
        if r = .rsp then some ({ Γ.setReg d .int with flags := .known }, [])
        else some ({ Γ.setReg d (.eq (.mk1 (.popcnt w) a)) with flags := .popcnt w a }, [])
      | none => some ({ Γ.setReg d .int with flags := .known }, [])

theorem stepPopcnt_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    (hB : BlocksOk Ψ ρ Γ.blocks)
    
    {x : CtxS × List CondS} (h : stepPopcnt next Γ w d src = some x)
    (hn : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) (.popcnt w d src) (x.1.den ρ) := by
  unfold stepPopcnt at h
  split at h
  · split at h
    · cases h
    · next hd =>
      obtain ⟨cs, hr, rfl⟩ := reads_map h
      exact cast_ctx (.popcntRM hd (reads_sound hB hr hn)) (by rw [CtxS.den_setReg_flags]; rfl)
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
    if d = .rsp then none else (reads next Γ 4 m).map fun cs => (Γ.setReg d .int, cs)
  | d, (.reg r) => extendReg Γ d r .sext32

theorem stepMovsxd_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    (hB : BlocksOk Ψ ρ Γ.blocks)
    
    {x : CtxS × List CondS} (h : stepMovsxd next Γ d src = some x)
    (hn : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) (.movsxd d src) (x.1.den ρ) := by
  unfold stepMovsxd at h
  split at h
  · split at h
    · cases h
    · next hd =>
      obtain ⟨cs, hr, rfl⟩ := reads_map h
      rw [CtxS.den_setReg]; exact .movsxdRM hd (reads_sound hB hr hn)
  · obtain ⟨hd, ⟨a, hr, hΓ, e⟩ | e⟩ := extendReg_spec (ρ := ρ) h
    · rw [e]; exact .movsxdExact hd hr hΓ
    · rw [e]; exact .movsxdRM hd (.reg _)

/-- The checker for `movzx`. -/
def stepMovzx (next : BitVec 64) (Γ : CtxS) (w : Width) (d : Reg) (sw : NarrowW) (src : RM) :
    Option (CtxS × List CondS) :=
  match w, d, sw, src with
  | _, d, sw, (.mem m) =>
    if d = .rsp then none else (reads next Γ sw.bytes m).map fun cs => (Γ.setReg d .int, cs)
  | w, d, sw, (.reg r) => extendReg Γ d r (.zx w sw)

theorem stepMovzx_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    (hB : BlocksOk Ψ ρ Γ.blocks)
    
    {x : CtxS × List CondS} (h : stepMovzx next Γ w d sw src = some x)
    (hn : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) (.movzx w d sw src) (x.1.den ρ) := by
  unfold stepMovzx at h
  split at h
  · split at h
    · cases h
    · next hd =>
      obtain ⟨cs, hr, rfl⟩ := reads_map h
      rw [CtxS.den_setReg]; exact .movzxRM hd (reads_sound hB hr hn)
  · obtain ⟨hd, ⟨a, hr, hΓ, e⟩ | e⟩ := extendReg_spec (ρ := ρ) h
    · rw [e]; exact .movzxExact hd hr hΓ
    · rw [e]; exact .movzxRM hd (.reg _)

/-- The checker for `movsx`. -/
def stepMovsx (next : BitVec 64) (Γ : CtxS) (w : Width) (d : Reg) (sw : NarrowW) (src : RM) :
    Option (CtxS × List CondS) :=
  match w, d, sw, src with
  | _, d, sw, (.mem m) =>
    if d = .rsp then none else (reads next Γ sw.bytes m).map fun cs => (Γ.setReg d .int, cs)
  | w, d, sw, (.reg r) => extendReg Γ d r (.sx w sw)

theorem stepMovsx_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    (hB : BlocksOk Ψ ρ Γ.blocks)
    
    {x : CtxS × List CondS} (h : stepMovsx next Γ w d sw src = some x)
    (hn : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) (.movsx w d sw src) (x.1.den ρ) := by
  unfold stepMovsx at h
  split at h
  · split at h
    · cases h
    · next hd =>
      obtain ⟨cs, hr, rfl⟩ := reads_map h
      rw [CtxS.den_setReg]; exact .movsxRM hd (reads_sound hB hr hn)
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
  | .neg, w, .mem m =>
    (writes next Γ w.bytes.toNat m).map fun x => ({ x.1 with flags := .known }, x.2)
  | .not, w, .mem m => writes next Γ w.bytes.toNat m

theorem stepUnary_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    (hB : BlocksOk Ψ ρ Γ.blocks)
    
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
  · next m =>
    obtain ⟨y, hw, rfl⟩ := writes_map h
    obtain ⟨hwr, hrd⟩ := writes_sound hB (Ψ := Ψ) (next := next) hw hn
    exact cast_ctx (.negRM hrd hwr) rfl
  · next m =>
    obtain ⟨hwr, hrd⟩ := writes_sound hB (Ψ := Ψ) (next := next) h hn
    exact .notRM hrd hwr

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
  | .store8 m _ => writes next Γ 1 m
  | .store16 m _ => writes next Γ 2 m
  | .test w dst src => stepTest next Γ w dst src
  | .imul2 w d src => stepImul2 next Γ w d src
  | .imul3 w d src imm => stepImul3 next Γ w d src imm
  | .popcnt w d src => stepPopcnt next Γ w d src
  | .movsxd d src => stepMovsxd next Γ d src
  | .movzx w d sw src => stepMovzx next Γ w d sw src
  | .movsx w d sw src => stepMovsx next Γ w d sw src
  | .unary op w dst => stepUnary next Γ op w dst
  | .shift op w dst c => stepShift next Γ op w dst c
  | .setcc c dst => stepSetcc next Γ c dst
  | .cmov c w d src => stepCmov next Γ c w d src
  | .mulDiv op w src => stepMulDiv next Γ op w src
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
theorem step_sound {Ψ : MemTy} {next : BitVec 64} {ρ : Env} {Γ : CtxS}
    (hB : BlocksOk Ψ ρ Γ.blocks) {i : Instr}
    {x : CtxS × List CondS} (h : step next Γ i = some x) (hn : CondS.all ρ x.2) :
    Straight Ψ next (Γ.den ρ) i (x.1.den ρ) := by
  unfold step at h
  split at h
  · cases h; exact .nop
  · exact stepMov_sound hB h hn
  · split at h
    · cases h
    · next hd => cases h; rw [CtxS.den_setReg]; exact .movAbs hd
  · exact stepLea_sound h hn
  · exact stepAlu_sound hB h hn
  · exact push_sound h hn
  · exact pop_sound h
  · exact .store8RM (writes_sound hB h hn).1
  · exact .store16RM (writes_sound hB h hn).1
  · exact stepTest_sound hB h hn
  · exact stepImul2_sound hB h hn
  · exact stepImul3_sound hB h hn
  · exact stepPopcnt_sound hB h hn
  · exact stepMovsxd_sound hB h hn
  · exact stepMovzx_sound hB h hn
  · exact stepMovsx_sound hB h hn
  · exact stepUnary_sound hB h hn
  · exact stepShift_sound hB h hn
  · exact stepSetcc_sound hB h hn
  · exact stepCmov_sound hB h hn
  · exact stepMulDiv_sound hB h hn
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

/-! ## A run of instructions

The checker taken through one instruction after another, for as long as it
has an answer: the context at the end, and all that the steps left to be
shown. One evaluation gives the whole run. -/

/-- The instruction listed at an address. -/
def lookup : List (BitVec 64 × Instr × BitVec 64) → BitVec 64 → Option (Instr × BitVec 64)
  | [], _ => none
  | (a, x) :: rest, b => if a = b then some x else lookup rest b

/-- That the instructions listed are the ones the program has there. -/
def Agrees (fetch : Fetch) : List (BitVec 64 × Instr × BitVec 64) → Prop
  | [] => True
  | (a, x) :: rest => fetch a = some x ∧ Agrees fetch rest

theorem Agrees.lookup {fetch : Fetch} : (code : List (BitVec 64 × Instr × BitVec 64)) →
    Agrees fetch code → {a : BitVec 64} → {x : Instr × BitVec 64} → lookup code a = some x →
    fetch a = some x
  | [], _, _, _, h => by cases h
  | (b, y) :: rest, hc, a, x, h => by
    unfold Sym.lookup at h
    split at h
    · next e => cases h; subst e; exact hc.1
    · exact Agrees.lookup rest hc.2 h

/-- The checker run from an address for at most so many instructions, with
the program's blocks at hand: where it stops, the context there, and what is
left to be shown. It stops where no instruction is listed or it has no answer. -/
def run (B : List (BitVec 64 × ShapeS × Bool)) (code : List (BitVec 64 × Instr × BitVec 64)) :
    Nat → BitVec 64 → CtxS → BitVec 64 × CtxS × List CondS
  | 0, a, Γ => (a, Γ, [])
  | fuel + 1, a, Γ =>
    match lookup code a with
    | some (i, len) =>
      match step (a + len) { Γ with blocks := B } i with
      | some (Γ', cs) =>
        ((run B code fuel (a + len) Γ').1, (run B code fuel (a + len) Γ').2.1,
          cs ++ (run B code fuel (a + len) Γ').2.2)
      | none => (a, Γ, [])
    | none => (a, Γ, [])

/-- **A run the checker has an answer for is typed**: the block at the
start is well typed if the block where the run stops is. -/
theorem run_sound {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {Ψ : MemTy} {ρ : Env}
    {B : List (BitVec 64 × ShapeS × Bool)} {code : List (BitVec 64 × Instr × BitVec 64)}
    (hB : BlocksOk Ψ ρ B) (hcode : Agrees fetch code) : (fuel : Nat) → (a : BitVec 64) →
    (Γ : CtxS) → CondS.all ρ (run B code fuel a Γ).2.2 →
    BlockOk Φ fetch sys Ψ (run B code fuel a Γ).1 ((run B code fuel a Γ).2.1.den ρ) →
    BlockOk Φ fetch sys Ψ a (Γ.den ρ)
  | 0, _, _, _, h => h
  | fuel + 1, a, Γ, hc, h => by
    unfold run at hc h
    split at hc
    · next i len hl =>
      split at hc
      · next Γ' cs hs =>
        rw [hl] at h
        simp only [hs] at h
        obtain ⟨h₁, h₂⟩ := CondS.all_append _ _ hc
        exact .step (Agrees.lookup code hcode hl)
          (step_sound (Γ := { Γ with blocks := B }) hB hs h₁)
          (run_sound hB hcode fuel (a + len) Γ' h₂ h)
      · rw [hl] at h
        simp only [*] at h
        exact h
    · simp only [*] at h
      exact h

/-- The same, from the checker's answer written out: one evaluation shows the
answer is that, and the rest speaks of it as written. -/
theorem run_sound' {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {Ψ : MemTy} {ρ : Env}
    {B : List (BitVec 64 × ShapeS × Bool)} {code : List (BitVec 64 × Instr × BitVec 64)}
    (hB : BlocksOk Ψ ρ B) (hcode : Agrees fetch code) {fuel : Nat} {a a' : BitVec 64}
    {Γ Γ' : CtxS} {cs : List CondS} (h : run B code fuel a Γ = (a', Γ', cs))
    (hc : CondS.all ρ cs) (hrest : BlockOk Φ fetch sys Ψ a' (Γ'.den ρ)) :
    BlockOk Φ fetch sys Ψ a (Γ.den ρ) :=
  run_sound hB hcode fuel a Γ (by rw [h]; exact hc) (by rw [h]; exact hrest)

/-! ## Values given a name

A register of which only that it holds a number is known may have that
number given a name: the rest of the block is then typed for every value it
may be. On terms the name is a variable the context does not yet mention,
and "for every value" is every way of saying what that variable stands for. -/

/-- A list with a value put at a place, the list made long enough with a
filler if it is too short. -/
def padSet {α : Type} (fill : α) : List α → Nat → α → List α
  | [], 0, x => [x]
  | [], k + 1, x => fill :: padSet fill [] k x
  | _ :: l, 0, x => x :: l
  | y :: l, k + 1, x => y :: padSet fill l k x

theorem getD_padSet {α : Type} (fill : α) : (l : List α) → (k : Nat) → (x : α) → (i : Nat) →
    (padSet fill l k x).getD i fill = if i = k then x else l.getD i fill
  | [], 0, x, i => by cases i <;> simp [padSet]
  | [], k + 1, x, i => by
    cases i with
    | zero => simp [padSet]
    | succ i => simpa [padSet] using getD_padSet fill [] k x i
  | y :: l, 0, x, i => by cases i <;> simp [padSet]
  | y :: l, k + 1, x, i => by
    cases i with
    | zero => simp [padSet]
    | succ i => simpa [padSet] using getD_padSet fill l k x i

/-- The environment with a value variable standing for something else. -/
def Env.setVal (ρ : Env) (k : Nat) (x : BitVec 64) : Env := { ρ with val := padSet 0 ρ.val k x }

/-- Whether a value term mentions no variable from `k` on. -/
def Val.under (k : Nat) : Val → Bool
  | .lit _ => true
  | .var i => decide (i < k)
  | .add a b => a.under k && b.under k
  | .shl a _ => a.under k
  | .app1 _ a => a.under k
  | .app2 _ a b => a.under k && b.under k

theorem Val.den_setVal {ρ : Env} {k : Nat} {x : BitVec 64} : (t : Val) → t.under k = true →
    t.den (ρ.setVal k x) = t.den ρ
  | .lit _, _ => rfl
  | .var i, h => by
    have hi : i < k := of_decide_eq_true h
    show (padSet 0 ρ.val k x).getD i 0 = ρ.val.getD i 0
    rw [getD_padSet]
    simp only [show i ≠ k by omega, ↓reduceIte]
  | .add a b, h => by
    simp only [Val.under, Bool.and_eq_true] at h
    show a.den _ + b.den _ = _
    rw [Val.den_setVal a h.1, Val.den_setVal b h.2]; rfl
  | .shl a s, h => by
    show a.den _ <<< s = _
    rw [Val.den_setVal a h]; rfl
  | .app1 f a, h => by
    show f.den (a.den _) = _
    rw [Val.den_setVal a h]; rfl
  | .app2 f a b, h => by
    simp only [Val.under, Bool.and_eq_true] at h
    show f.den (a.den _) (b.den _) = _
    rw [Val.den_setVal a h.1, Val.den_setVal b h.2]; rfl

/-- Whether a number term mentions no value variable from `k` on. -/
def Num.under (k : Nat) : Num → Bool
  | .lit _ => true
  | .var _ => true
  | .add a b => a.under k && b.under k
  | .mul a b => a.under k && b.under k
  | .sub a b => a.under k && b.under k
  | .toNat v => v.under k
  | .size _ => true

theorem Num.den_setVal {ρ : Env} {k : Nat} {x : BitVec 64} : (t : Num) → t.under k = true →
    t.den (ρ.setVal k x) = t.den ρ
  | .lit _, _ => rfl
  | .var _, _ => rfl
  | .add a b, h => by
    simp only [Num.under, Bool.and_eq_true] at h
    show a.den _ + b.den _ = _
    rw [Num.den_setVal a h.1, Num.den_setVal b h.2]; rfl
  | .mul a b, h => by
    simp only [Num.under, Bool.and_eq_true] at h
    show a.den _ * b.den _ = _
    rw [Num.den_setVal a h.1, Num.den_setVal b h.2]; rfl
  | .sub a b, h => by
    simp only [Num.under, Bool.and_eq_true] at h
    show a.den _ - b.den _ = _
    rw [Num.den_setVal a h.1, Num.den_setVal b h.2]; rfl
  | .toNat v, h => by
    show (v.den _).toNat = _
    rw [Val.den_setVal v h]; rfl
  | .size _, _ => rfl

mutual

/-- Whether a type term mentions no value variable from `k` on. -/
def TyS.under (k : Nat) : TyS → Bool
  | .int => true
  | .eq v => v.under k
  | .ptr S _ off => S.under k && off.under k
  | .ref _ _ off => off.under k
  | .nullable τ => τ.under k
  | .orErr τ => τ.under k
  | .str _ => true
  | .atom _ => true

def ShapeS.under (k : Nat) : ShapeS → Bool
  | .mk size vals => size.under k && vals.under k
  | .rep n E => n.under k && E.under k
  | .atom _ => true

def ValsS.under (k : Nat) : ValsS → Bool
  | .nil => true
  | .cons _ τ rest => τ.under k && rest.under k

end

mutual

theorem TyS.den_setVal {ρ : Env} {k : Nat} {x : BitVec 64} : (t : TyS) → t.under k = true →
    t.den (ρ.setVal k x) = t.den ρ
  | .int, _ => rfl
  | .eq v, h => by
    show Ty.eq (v.den _) = _
    rw [Val.den_setVal v h]; rfl
  | .ptr S w off, h => by
    simp only [TyS.under, Bool.and_eq_true] at h
    show Ty.ptr (S.den _) w (off.den _) = _
    rw [ShapeS.den_setVal S h.1, Num.den_setVal off h.2]; rfl
  | .ref tag w off, h => by
    show Ty.ref tag w (off.den _) = _
    rw [Num.den_setVal off h]; rfl
  | .nullable τ, h => by
    show Ty.nullable (τ.den _) = _
    rw [TyS.den_setVal τ h]; rfl
  | .orErr τ, h => by
    show Ty.orErr (τ.den _) = _
    rw [TyS.den_setVal τ h]; rfl
  | .str _, _ => rfl
  | .atom _, _ => rfl

theorem ShapeS.den_setVal {ρ : Env} {k : Nat} {x : BitVec 64} : (t : ShapeS) →
    t.under k = true → t.den (ρ.setVal k x) = t.den ρ
  | .mk size vals, h => by
    simp only [ShapeS.under, Bool.and_eq_true] at h
    show (⟨size.den _, vals.den _⟩ : Shape) = _
    rw [Num.den_setVal size h.1, ValsS.den_setVal vals h.2]; rfl
  | .rep n E, h => by
    simp only [ShapeS.under, Bool.and_eq_true] at h
    show (E.den _).rep (n.den _) = _
    rw [Num.den_setVal n h.1, ShapeS.den_setVal E h.2]; rfl
  | .atom _, _ => rfl

theorem ValsS.den_setVal {ρ : Env} {k : Nat} {x : BitVec 64} : (t : ValsS) →
    t.under k = true → t.den (ρ.setVal k x) = t.den ρ
  | .nil, _ => rfl
  | .cons o τ rest, h => by
    simp only [ValsS.under, Bool.and_eq_true] at h
    show (o, τ.den _) :: rest.den _ = _
    rw [TyS.den_setVal τ h.1, ValsS.den_setVal rest h.2]; rfl

end

/-- Whether what a term says of the flags mentions no value variable from `k` on. -/
def FlagsS.under (k : Nat) : FlagsS → Bool
  | .alu _ _ a b => a.under k && b.under k
  | .test a b => a.under k && b.under k
  | .neg _ a => a.under k
  | .popcnt _ a => a.under k
  | .imul _ a b => a.under k && b.under k
  | _ => true

theorem FlagsS.den_setVal {ρ : Env} {k : Nat} {x : BitVec 64} : (t : FlagsS) →
    t.under k = true → t.den (ρ.setVal k x) = t.den ρ
  | .any, _ => rfl
  | .known, _ => rfl
  | .defined _ _ _ _, _ => rfl
  | .lit _, _ => rfl
  | .atom _, _ => rfl
  | .alu op w a b, h => by
    simp only [FlagsS.under, Bool.and_eq_true] at h
    cases w <;> simp only [FlagsS.den, Val.den_setVal a h.1, Val.den_setVal b h.2]
  | .test a b, h => by
    simp only [FlagsS.under, Bool.and_eq_true] at h
    simp only [FlagsS.den, Val.den_setVal a h.1, Val.den_setVal b h.2]
  | .neg w a, h => by simp only [FlagsS.den, Val.den_setVal a h]
  | .popcnt w a, h => by simp only [FlagsS.den, Val.den_setVal a h]
  | .imul w a b, h => by
    simp only [FlagsS.under, Bool.and_eq_true] at h
    simp only [FlagsS.den, Val.den_setVal a h.1, Val.den_setVal b h.2]

end Sym

/-- Whether something holds of every value of a table. -/
def RegMap.all {α : Type} (p : α → Bool) (m : RegMap α) : Bool :=
  p m.rax && p m.rcx && p m.rdx && p m.rbx && p m.rsp && p m.rbp && p m.rsi && p m.rdi &&
    p m.r8 && p m.r9 && p m.r10 && p m.r11 && p m.r12 && p m.r13 && p m.r14 && p m.r15

theorem RegMap.all_get {α : Type} {p : α → Bool} {m : RegMap α} (h : m.all p = true) (r : Reg) :
    p (m.get r) = true := by
  simp only [RegMap.all, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩,
    h15⟩ := h
  cases r <;> assumption

namespace Sym

def shapesUnder (k : Nat) : List ShapeS → Bool
  | [] => true
  | S :: σ => S.under k && shapesUnder k σ

theorem denShapes_setVal {ρ : Env} {k : Nat} {x : BitVec 64} (rest : List Shape) :
    (σ : List ShapeS) → shapesUnder k σ = true →
    denShapes (ρ.setVal k x) σ rest = denShapes ρ σ rest
  | [], _ => rfl
  | S :: σ, h => by
    simp only [shapesUnder, Bool.and_eq_true] at h
    show S.den _ :: denShapes _ σ rest = _
    rw [ShapeS.den_setVal S h.1, denShapes_setVal rest σ h.2]; rfl

def ownedUnder (k : Nat) : List (Val × ShapeS) → Bool
  | [] => true
  | (a, S) :: l => a.under k && S.under k && ownedUnder k l

theorem denOwned_setVal {ρ : Env} {k : Nat} {x : BitVec 64} (rest : List (BitVec 64 × Shape)) :
    (l : List (Val × ShapeS)) → ownedUnder k l = true →
    denOwned (ρ.setVal k x) l rest = denOwned ρ l rest
  | [], _ => rfl
  | (a, S) :: l, h => by
    simp only [ownedUnder, Bool.and_eq_true] at h
    show (a.den _, S.den _) :: denOwned _ l rest = _
    rw [Val.den_setVal a h.1.1, ShapeS.den_setVal S h.1.2, denOwned_setVal rest l h.2]; rfl

/-- Whether a context term mentions no value variable from `k` on. -/
def CtxS.under (k : Nat) (Γ : CtxS) : Bool :=
  Γ.regs.all (TyS.under k) && shapesUnder k Γ.stack && Γ.room.under k && Γ.flags.under k &&
    ownedUnder k Γ.owned && Γ.above.under k

theorem CtxS.den_setVal {ρ : Env} {k : Nat} {x : BitVec 64} {Γ : CtxS} (h : Γ.under k = true) :
    Γ.den (ρ.setVal k x) = Γ.den ρ := by
  simp only [CtxS.under, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hr, hs⟩, hroom⟩, hfl⟩, ho⟩, ha⟩ := h
  have e₁ : (Γ.den (ρ.setVal k x)).regs = (Γ.den ρ).regs := by
    funext r
    exact (CtxS.den_regs _ Γ r).trans
      ((TyS.den_setVal _ (RegMap.all_get hr r)).trans (CtxS.den_regs ρ Γ r).symm)
  have e₂ : (Γ.den (ρ.setVal k x)).stack = (Γ.den ρ).stack := denShapes_setVal _ _ hs
  have e₃ : (Γ.den (ρ.setVal k x)).room = (Γ.den ρ).room := Num.den_setVal _ hroom
  have e₄ : (Γ.den (ρ.setVal k x)).flags = (Γ.den ρ).flags := FlagsS.den_setVal _ hfl
  have e₅ : (Γ.den (ρ.setVal k x)).owned = (Γ.den ρ).owned := denOwned_setVal _ _ ho
  have e₆ : (Γ.den (ρ.setVal k x)).above = (Γ.den ρ).above := Num.den_setVal _ ha
  cases hd : Γ.den (ρ.setVal k x)
  cases hd' : Γ.den ρ
  rw [hd, hd'] at e₁ e₂ e₃ e₄ e₅ e₆
  simp only at e₁ e₂ e₃ e₄ e₅ e₆
  rw [e₁, e₂, e₃, e₄, e₅, e₆]

/-! ## A walk through a block

The checker taken through one instruction after another as in a run, and
where an instruction needs to speak of a value a register is only known to
hold a number for, that value is given a name first. What comes of it is a
tree: what each step leaves to be shown, under the names given before it,
and at the end the block where the walk stopped. -/

/-- What a walk comes to. -/
inductive Walk
  /-- It stopped at an address, in a context. -/
  | stop (a : BitVec 64) (Γ : CtxS)
  /-- Steps left these to be shown; then the rest. -/
  | conds (cs : List CondS) (rest : Walk)
  /-- A value was given the name `k`; then the rest, for every value. -/
  | name (k : Nat) (rest : Walk)
  /-- A value that may be null: the rest with it null, and with it not. -/
  | both (l r : Walk)
  /-- What a system call handed back: the rest with it an error number,
  named `k`, and with it a value. -/
  | err (k : Nat) (l r : Walk)
  /-- A byte of text was loaded: the rest with it zero, and with it some
  other byte, named `k`. -/
  | byte (k : Nat) (zero more : Walk)
  /-- A conditional jump both sides of which are typed where they are: the
  rest where the condition held, and where it did not, each with that known
  of the flags. -/
  | branch (fl : FlagsS) (c : Cond) (taken fall : Walk)

/-- That a walk's conditions hold, and that `P` holds of where it stopped:
for every value each name may stand for. -/
def Walk.holds (P : BitVec 64 → Ctx → Prop) : Walk → Env → Prop
  | .stop a Γ, ρ => P a (Γ.den ρ)
  | .conds cs rest, ρ => CondS.all ρ cs ∧ rest.holds P ρ
  | .name k rest, ρ => ∀ x, rest.holds P (ρ.setVal k x)
  | .both l r, ρ => l.holds P ρ ∧ r.holds P ρ
  | .err k l r, ρ => (∀ e, SysErr e → l.holds P (ρ.setVal k e)) ∧ r.holds P ρ
  | .byte k zero more, ρ =>
    zero.holds P ρ ∧ ∀ b : BitVec 64, b ≠ 0 → b < 256 → more.holds P (ρ.setVal k b)
  | .branch fl c taken fall, ρ =>
    (∀ f, fl.den ρ f → c.eval f = some true → taken.holds P ρ) ∧
      (∀ f, fl.den ρ f → c.eval f = some false → fall.holds P ρ)

/-- The first register an instruction needs the value of that the context
only knows to hold a number. -/
def toName (Γ : CtxS) (i : Instr) : Option Reg :=
  i.wantsNamed.find? fun r =>
    match Γ.regs.get r with
    | .int => true
    | _ => false

def blocksUnder (k : Nat) : List (BitVec 64 × ShapeS × Bool) → Bool
  | [] => true
  | (_, S, _) :: rest => S.under k && blocksUnder k rest

theorem BlocksOk.setVal {Ψ : MemTy} {ρ : Env} {k : Nat} {x : BitVec 64} :
    (B : List (BitVec 64 × ShapeS × Bool)) → blocksUnder k B = true → BlocksOk Ψ ρ B →
    BlocksOk Ψ (ρ.setVal k x) B
  | [], _, _ => trivial
  | (base, S, w) :: rest, hu, hB => by
    simp only [blocksUnder, Bool.and_eq_true] at hu
    obtain ⟨⟨l, hl, hs, hw⟩, hrest⟩ := hB
    exact ⟨⟨l, hl, by rw [ShapeS.den_setVal S hu.1]; exact hs, hw⟩,
      BlocksOk.setVal rest hu.2 hrest⟩

/-- What the checker is given of the program besides its instructions: its
blocks, which of them are of a declared kind, and the shape each kind has. -/
structure Prog where
  blocks : List (BitVec 64 × ShapeS × Bool) := []
  tags : List (BitVec 64 × Nat) := []
  kinds : List (Nat × ShapeS) := []
  /-- The addresses that have contexts of their own: a jump to one of them
  is not followed by the walk. -/
  labels : List (BitVec 64) := []

/-- That the blocks said to be of a kind are. -/
def TagsOk (Ψ : MemTy) : List (BitVec 64 × Nat) → Prop
  | [] => True
  | (base, tag) :: rest => (∃ l, Ψ base = some l ∧ l.tag = some tag) ∧ TagsOk Ψ rest

/-- That the kinds have the shapes they are said to. -/
def KindsOk (Ψ : MemTy) (ρ : Env) : List (Nat × ShapeS) → Prop
  | [] => True
  | (tag, S) :: rest => Ψ.kinds tag = some (S.den ρ) ∧ KindsOk Ψ ρ rest

theorem TagsOk.cons {Ψ : MemTy} {base : BitVec 64} {tag : Nat} {rest : List (BitVec 64 × Nat)}
    (l : Layout) (h₁ : Ψ base = some l) (h₂ : l.tag = some tag) (h : TagsOk Ψ rest) :
    TagsOk Ψ ((base, tag) :: rest) := ⟨⟨l, h₁, h₂⟩, h⟩

/-- That what the checker is given of the program is so. -/
structure Prog.Ok (Ψ : MemTy) (ρ : Env) (P : Prog) : Prop where
  blocks : BlocksOk Ψ ρ P.blocks
  tags : TagsOk Ψ P.tags
  kinds : KindsOk Ψ ρ P.kinds

def lookupNat {α : Type} : List (Nat × α) → Nat → Option α
  | [], _ => none
  | (k, x) :: rest, n => if k = n then some x else lookupNat rest n

def lookupTag : List (BitVec 64 × Nat) → BitVec 64 → Option Nat
  | [], _ => none
  | (b, t) :: rest, a => if b = a then some t else lookupTag rest a

theorem KindsOk.lookup {Ψ : MemTy} {ρ : Env} : (K : List (Nat × ShapeS)) → KindsOk Ψ ρ K →
    {tag : Nat} → {S : ShapeS} → lookupNat K tag = some S → Ψ.kinds tag = some (S.den ρ)
  | [], _, _, _, h => by cases h
  | (t, T) :: rest, hK, tag, S, h => by
    unfold lookupNat at h
    split at h
    · next e => cases h; subst e; exact hK.1
    · exact KindsOk.lookup rest hK.2 h

theorem TagsOk.lookup {Ψ : MemTy} : (T : List (BitVec 64 × Nat)) → TagsOk Ψ T →
    {base : BitVec 64} → {tag : Nat} → lookupTag T base = some tag →
    ∃ l, Ψ base = some l ∧ l.tag = some tag
  | [], _, _, _, h => by cases h
  | (b, t) :: rest, hT, base, tag, h => by
    unfold lookupTag at h
    split at h
    · next e => cases h; subst e; exact hT.1
    · exact TagsOk.lookup rest hT.2 h

def kindsUnder (k : Nat) : List (Nat × ShapeS) → Bool
  | [] => true
  | (_, S) :: rest => S.under k && kindsUnder k rest

theorem KindsOk.setVal {Ψ : MemTy} {ρ : Env} {k : Nat} {x : BitVec 64} :
    (K : List (Nat × ShapeS)) → kindsUnder k K = true → KindsOk Ψ ρ K →
    KindsOk Ψ (ρ.setVal k x) K
  | [], _, _ => trivial
  | (tag, S) :: rest, hu, hK => by
    simp only [kindsUnder, Bool.and_eq_true] at hu
    exact ⟨by rw [ShapeS.den_setVal S hu.1]; exact hK.1, KindsOk.setVal rest hu.2 hK.2⟩

theorem Prog.Ok.setVal {Ψ : MemTy} {ρ : Env} {k : Nat} {x : BitVec 64} {P : Prog}
    (hb : blocksUnder k P.blocks = true) (hk : kindsUnder k P.kinds = true) (h : P.Ok Ψ ρ) :
    P.Ok Ψ (ρ.setVal k x) :=
  ⟨BlocksOk.setVal _ hb h.blocks, h.tags, KindsOk.setVal _ hk h.kinds⟩

/-- The register an instruction reaches memory through, or moves on by a
constant. -/
def baseOf : Instr → Option Reg
  | .alu .add .w64 (.rm_i (.reg d) _) => some d
  | i =>
    match i.memOperand? with
    | some (.sib (some b) _ _) => some b
    | _ => none

/-- The register an instruction reaches memory through, or moves on, that
holds a pointer to a block of a kind: it is opened first, to a pointer to a
block of the shape that kind has. -/
def toOpen (Γ : CtxS) (i : Instr) : Option (Reg × Nat × Bool × Num) :=
  match baseOf i with
  | some r =>
    match Γ.regs.get r with
    | .ref tag w off => some (r, tag, w, off)
    | _ => none
  | none => none

theorem toOpen_spec {Γ : CtxS} {i : Instr} {r : Reg} {tag : Nat} {w : Bool} {off : Num}
    (h : toOpen Γ i = some (r, tag, w, off)) : Γ.regs.get r = .ref tag w off := by
  unfold toOpen at h
  split at h
  · split at h
    · next hΓ => cases h; exact hΓ
    · cases h
  · cases h

/-- A register just loaded with the address of a byte of one of the
program's blocks is a pointer into that block, or to a block of its kind. -/
def castData (P : Prog) (Γ : CtxS) (i : Instr) : CtxS :=
  match i with
  | .lea .w64 d (.rip _) =>
    if d = .rsp then Γ
    else match Γ.regs.get d with
      | .eq (.lit v) =>
        match blockAt P.blocks v with
        | some (base, S, w, off) =>
          match lookupTag P.tags base with
          | some tag => Γ.setReg d (.ref tag w (.lit off))
          | none => Γ.setReg d (.ptr S w (.lit off))
        | none => Γ
      | _ => Γ
  | _ => Γ

theorem castData_sound {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {Ψ : MemTy} {ρ : Env}
    {P : Prog} (hP : P.Ok Ψ ρ) {a : BitVec 64} {Γ : CtxS} {i : Instr}
    (h : BlockOk Φ fetch sys Ψ a ((castData P Γ i).den ρ)) :
    BlockOk Φ fetch sys Ψ a (Γ.den ρ) := by
  unfold castData at h
  split at h
  · next d disp =>
    split at h
    · exact h
    · next hd =>
      split at h
      · next v hΓ =>
        split at h
        · next base S w off hb =>
          obtain ⟨⟨l, hl, hs, hw⟩, hv⟩ := blockAt_spec _ hP.blocks hb
          have hΓ' : (Γ.den ρ).regs d = .eq v := by rw [CtxS.den_regs, hΓ]; rfl
          split at h
          · next tag ht =>
            obtain ⟨l', hl', htag⟩ := TagsOk.lookup _ hP.tags ht
            rw [hl] at hl'; cases hl'
            rw [CtxS.den_setReg] at h
            exact .castRef hd hΓ' hl htag hv (fun _ => by rw [hw]; assumption) h
          · rw [CtxS.den_setReg] at h
            have h' : BlockOk Φ fetch sys Ψ a ((Γ.den ρ).setReg d (.ptr l.shape w off)) := by
              rw [hs]; exact h
            exact .castPtr hd hΓ' hl hv (fun e => by rw [hw]; exact e) h'
        · exact h
      · exact h
  · exact h

/-- The register a `test` of itself is about to look at that holds a value
which may be null, or what a system call handed back: the type the value has
otherwise, and whether it is the second. The block goes on once for each of
the two things it may be. -/
def toSplit (Γ : CtxS) : Instr → Option (Reg × TyS × Bool)
  | .test _ (.reg r) (.reg r') =>
    if r = r' ∧ r ≠ .rsp then
      match Γ.regs.get r with
      | .nullable τ => some (r, τ, false)
      | .orErr τ => some (r, τ, true)
      | _ => none
    else none
  | _ => none

theorem toSplit_spec {Γ : CtxS} {i : Instr} {r : Reg} {τ : TyS} {e : Bool}
    (h : toSplit Γ i = some (r, τ, e)) :
    r ≠ .rsp ∧ Γ.regs.get r = (if e then .orErr τ else .nullable τ) := by
  unfold toSplit at h
  split at h
  · split at h
    · next hc =>
      split at h
      · next hΓ => cases h; exact ⟨hc.2, hΓ⟩
      · next hΓ => cases h; exact ⟨hc.2, hΓ⟩
      · cases h
    · cases h
  · cases h

/-- The registers of a load of the byte of text a pointer points at: where
the byte goes, and the pointer. -/
def toByte (Γ : CtxS) : Instr → Option (Reg × Reg)
  | .movzx _ d .w8 (.mem (.sib (some r) none disp)) =>
    if disp = 0 ∧ d ≠ .rsp ∧ r ≠ .rsp ∧ d ≠ r then
      match Γ.regs.get r with
      | .str _ => some (d, r)
      | _ => none
    else none
  | _ => none

theorem toByte_spec {Γ : CtxS} {i : Instr} {d r : Reg} (h : toByte Γ i = some (d, r)) :
    (∃ w, i = .movzx w d .w8 (.mem (.sib (some r) none 0))) ∧ d ≠ .rsp ∧ r ≠ .rsp ∧ d ≠ r ∧
      ∃ more, Γ.regs.get r = .str more := by
  unfold toByte at h
  split at h
  · next w d' r' disp =>
    split at h
    · next hc =>
      split at h
      · next more hΓ =>
        cases h
        obtain ⟨rfl, hd, hr, hdr⟩ := hc
        exact ⟨⟨w, rfl⟩, hd, hr, hdr, more, hΓ⟩
      · cases h
    · cases h
  · cases h

/-- Where a jump goes that the walk follows: forward, to an address with no
context of its own. What is jumped to is then typed in the context the jump
is made in. -/
def jumpTo (P : Prog) (a len : BitVec 64) : Instr → Option (BitVec 64)
  | .jmp (.rel d) =>
    if a.toNat < (a + len + d.signExtend 64).toNat ∧
        P.labels.contains (a + len + d.signExtend 64) = false then
      some (a + len + d.signExtend 64)
    else none
  | _ => none

theorem jumpTo_spec {P : Prog} {a len t : BitVec 64} {i : Instr} (h : jumpTo P a len i = some t) :
    ∃ d, i = .jmp (.rel d) ∧ t = a + len + d.signExtend 64 := by
  unfold jumpTo at h
  split at h
  · next d =>
    split at h
    · cases h; exact ⟨d, rfl, rfl⟩
    · cases h
  · cases h

/-- Where a conditional jump goes that is typed where it is: forward, to an
address with no context of its own. -/
def branchTo (P : Prog) (a len : BitVec 64) : Instr → Option (Cond × BitVec 64)
  | .jcc c d =>
    if a.toNat < (a + len + d.signExtend 64).toNat ∧
        P.labels.contains (a + len + d.signExtend 64) = false then
      some (c, a + len + d.signExtend 64)
    else none
  | _ => none

theorem branchTo_spec {P : Prog} {a len t : BitVec 64} {c : Cond} {i : Instr}
    (h : branchTo P a len i = some (c, t)) :
    ∃ d, i = .jcc c d ∧ t = a + len + d.signExtend 64 := by
  unfold branchTo at h
  split at h
  · next c' d =>
    split at h
    · cases h; exact ⟨d, rfl, rfl⟩
    · cases h
  · cases h

/-- The checker walked from an address for at most so many moves, `k` being
a variable no term yet mentions. Before an instruction, a pointer to a block
of a kind that it reaches through is opened, and a value it needs to speak
of is named; after it, an address of data just loaded is made a pointer. -/
def walk (P : Prog) (code : List (BitVec 64 × Instr × BitVec 64)) :
    Nat → Nat → BitVec 64 → CtxS → Walk
  | 0, _, a, Γ => .stop a Γ
  | fuel + 1, k, a, Γ =>
    match lookup code a with
    | none => .stop a Γ
    | some (i, len) =>
      match jumpTo P a len i with
      | some t => walk P code fuel k t Γ
      | none =>
      match branchTo P a len i with
      | some (c, t) =>
        .conds (decideConds Γ.flags c) (.branch Γ.flags c (.stop t Γ) (.stop (a + len) Γ))
      | none =>
      match toSplit Γ i with
      | some (r, τ, false) =>
        .both (.stop a (Γ.setReg r (.eq (.lit 0)))) (.stop a (Γ.setReg r τ))
      | some (r, τ, true) =>
        if Γ.under k then
          .err k (.stop a (Γ.setReg r (.eq (.var k)))) (.stop a (Γ.setReg r τ))
        else .stop a Γ
      | none =>
      match toByte Γ i with
      | some (d, r) =>
        if Γ.under k then
          .byte k (.stop (a + len) (Γ.setReg d (.eq (.lit 0))))
            (.stop (a + len) ((Γ.setReg d (.eq (.var k))).setReg r (.str true)))
        else .stop a Γ
      | none =>
      match toOpen Γ i with
      | some (r, tag, w, off) =>
        match lookupNat P.kinds tag with
        | some S =>
          if r = .rsp then .stop a Γ
          else walk P code fuel k a (Γ.setReg r (.ptr S w off))
        | none => .stop a Γ
      | none =>
        match toName Γ i with
        | some r =>
          if Γ.under k && blocksUnder k P.blocks && kindsUnder k P.kinds then
            .name k (walk P code fuel (k + 1) a (Γ.setReg r (.eq (.var k))))
          else .stop a Γ
        | none =>
          match step (a + len) { Γ with blocks := P.blocks } i with
          | some (Γ', cs) => .conds cs (walk P code fuel k (a + len) (castData P Γ' i))
          | none => .stop a Γ

/-- **A walk whose conditions hold types the block it started at**, if the
block where it stopped is typed. -/
theorem walk_sound {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {Ψ : MemTy} {P : Prog}
    {code : List (BitVec 64 × Instr × BitVec 64)} (hcode : Agrees fetch code) :
    (fuel k : Nat) → (a : BitVec 64) → (Γ : CtxS) → (ρ : Env) → P.Ok Ψ ρ →
    (walk P code fuel k a Γ).holds (BlockOk Φ fetch sys Ψ) ρ →
    BlockOk Φ fetch sys Ψ a (Γ.den ρ)
  | 0, _, _, _, _, _, h => h
  | fuel + 1, k, a, Γ, ρ, hP, h => by
    unfold walk at h
    split at h
    · exact h
    · next i len hl =>
      split at h
      · next t hj =>
        obtain ⟨d, rfl, rfl⟩ := jumpTo_spec hj
        exact .jump (Agrees.lookup code hcode hl) (walk_sound hcode fuel k _ Γ ρ hP h)
      next =>
      split at h
      · next c t hb =>
        obtain ⟨d, rfl, rfl⟩ := branchTo_spec hb
        obtain ⟨hdec, htaken, hfall⟩ := h
        exact .branchIn (Agrees.lookup code hcode hl) (decideConds_spec hdec)
          (fun f hf hc => htaken f hf hc) (fun f hf hc => hfall f hf hc)
      next =>
      split at h
      · next r τ hsp =>
        obtain ⟨hr, hΓ⟩ := toSplit_spec hsp
        have h₀ := h.1
        have h₁ := h.2
        simp only [Walk.holds] at h₀ h₁
        rw [CtxS.den_setReg] at h₀ h₁
        exact .splitNull hr (by rw [CtxS.den_regs, hΓ]; rfl) h₀ h₁
      · next r τ hsp =>
        obtain ⟨hr, hΓ⟩ := toSplit_spec hsp
        split at h
        · next hu =>
          have h₁ := h.2
          simp only [Walk.holds] at h₁
          rw [CtxS.den_setReg] at h₁
          refine .splitErr hr (by rw [CtxS.den_regs, hΓ]; rfl) (fun e he => ?_) h₁
          have h₀ := h.1 e he
          simp only [Walk.holds] at h₀
          rw [CtxS.den_setReg, CtxS.den_setVal hu] at h₀
          have e' : (TyS.eq (.var k)).den (ρ.setVal k e) = .eq e := by
            show Ty.eq ((padSet 0 ρ.val k e).getD k 0) = _
            rw [getD_padSet]; simp
          rw [e'] at h₀
          exact h₀
        · exact h
      next =>
      split at h
      · next d r hb =>
        obtain ⟨⟨w, rfl⟩, hd, hr, hdr, more, hΓ⟩ := toByte_spec hb
        split at h
        · next hu =>
          have h₀ := h.1
          simp only [Walk.holds] at h₀
          rw [CtxS.den_setReg] at h₀
          refine .strByte (Agrees.lookup code hcode hl) hd hr hdr
            (by rw [CtxS.den_regs, hΓ]; rfl) h₀ (fun b hb0 hb256 => ?_)
          have h₁ := h.2 b hb0 hb256
          simp only [Walk.holds] at h₁
          rw [CtxS.den_setReg, CtxS.den_setReg, CtxS.den_setVal hu] at h₁
          have e' : (TyS.eq (.var k)).den (ρ.setVal k b) = .eq b := by
            show Ty.eq ((padSet 0 ρ.val k b).getD k 0) = _
            rw [getD_padSet]; simp
          rw [e'] at h₁
          exact h₁
        · exact h
      next =>
      split at h
      · next r tag w off ho =>
        split at h
        · next S hk =>
          split at h
          · exact h
          · next hr =>
            have := walk_sound hcode fuel k a (Γ.setReg r (.ptr S w off)) ρ hP h
            rw [CtxS.den_setReg] at this
            exact .openRef hr (by rw [CtxS.den_regs, toOpen_spec ho]; rfl)
              (KindsOk.lookup _ hP.kinds hk) this
        · exact h
      · split at h
        · next r hr =>
          split at h
          · next hu =>
            simp only [Bool.and_eq_true] at hu
            have key : ∀ x, BlockOk Φ fetch sys Ψ a ((Γ.den ρ).setReg r (.eq x)) := fun x => by
              have := walk_sound hcode fuel (k + 1) a (Γ.setReg r (.eq (.var k)))
                (ρ.setVal k x) (hP.setVal hu.1.2 hu.2) (h x)
              rw [CtxS.den_setReg, CtxS.den_setVal hu.1.1] at this
              have e : (TyS.eq (.var k)).den (ρ.setVal k x) = .eq x := by
                show Ty.eq ((padSet 0 ρ.val k x).getD k 0) = _
                rw [getD_padSet]; simp
              rw [e] at this
              exact this
            by_cases hsp : r = .rsp
            · subst hsp; exact .nameSp key
            · exact .name hsp key
          · exact h
        · split at h
          · next Γ' cs hs =>
            exact .step (Agrees.lookup code hcode hl)
              (step_sound (Γ := { Γ with blocks := P.blocks }) hP.blocks hs h.1)
              (castData_sound hP (walk_sound hcode fuel k (a + len) _ ρ hP h.2))
          · exact h

/-- The same, from the walk written out. -/
theorem walk_sound' {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {Ψ : MemTy} {ρ : Env}
    {P : Prog} {code : List (BitVec 64 × Instr × BitVec 64)}
    (hP : P.Ok Ψ ρ) (hcode : Agrees fetch code) {fuel k : Nat} {a : BitVec 64} {Γ : CtxS}
    {W : Walk} (h : walk P code fuel k a Γ = W) (hW : W.holds (BlockOk Φ fetch sys Ψ) ρ) :
    BlockOk Φ fetch sys Ψ a (Γ.den ρ) :=
  walk_sound hcode fuel k a Γ ρ hP (by rw [h]; exact hW)

/-! ## One context standing for another

A block hands over to another, returns, or calls, where the context it has
reached may stand for the one wanted there: every register's type is one of
the type wanted, the stack is cut the same way with each piece standing for
its counterpart, and the rest agrees. On terms this is worked out part by
part, and what the terms do not show is left to be shown. -/

/-- What is left to be shown for two numbers to be the same. -/
def eqConds (a b : Num) : List CondS := if a = b then [] else [.eqN a b]

theorem eqConds_spec {ρ : Env} {a b : Num} (h : CondS.all ρ (eqConds a b)) :
    a.den ρ = b.den ρ := by
  unfold eqConds at h
  split at h
  · next e => rw [e]
  · exact h.1

/-- What is left to be shown for what is known of the flags one way to be
known the other. -/
def flagsConds (fl fl' : FlagsS) : List CondS :=
  if fl = fl' then []
  else match fl' with
    | .any => []
    | .known => if fl.allDefined then [] else [.flagsSub fl fl']
    | _ => [.flagsSub fl fl']

theorem flagsConds_spec {ρ : Env} {fl fl' : FlagsS} (h : CondS.all ρ (flagsConds fl fl')) :
    ∀ f, fl.den ρ f → fl'.den ρ f := by
  unfold flagsConds at h
  split at h
  · next e => rw [e]; exact fun _ hf => hf
  · split at h
    · exact fun _ _ => trivial
    · split at h
      · next hd => exact fun f hf => FlagsS.allDefined_spec hd f hf
      · exact h.1
    · exact h.1

/-- What is left to be shown for every typed value of one list to be found
in another at the same place, at a type it may stand for. -/
def valsConds (have' : ValsS) : ValsS → Option (List CondS)
  | .nil => some []
  | .cons o τ rest =>
    match have'.find o, valsConds have' rest with
    | some υ, some cs => some (subConds υ τ ++ cs)
    | _, _ => none

theorem ValsS.mem_of_find {ρ : Env} : (vs : ValsS) → {o : Nat} → {τ : TyS} →
    vs.find o = some τ → (o, τ.den ρ) ∈ vs.den ρ
  | .nil, _, _, h => by cases h
  | .cons p υ rest, o, τ, h => by
    unfold ValsS.find at h
    show (o, τ.den ρ) ∈ (p, υ.den ρ) :: rest.den ρ
    by_cases e : (p == o) = true
    · simp only [e, ↓reduceIte, Option.some.injEq] at h
      subst h
      rw [show p = o from by simpa using e]; exact List.mem_cons_self
    · simp only [e, Bool.false_eq_true, ↓reduceIte] at h
      exact List.mem_cons_of_mem _ (ValsS.mem_of_find rest h)

theorem valsConds_spec {ρ : Env} {have' : ValsS} : (want : ValsS) → {cs : List CondS} →
    valsConds have' want = some cs → CondS.all ρ cs →
    ∀ q ∈ want.den ρ, ∃ p ∈ have'.den ρ, p.1 = q.1 ∧ Sub p.2 q.2
  | .nil, _, _, _ => fun q hq => by cases hq
  | .cons o τ rest, cs, h, hc => by
    unfold valsConds at h
    split at h
    · next υ cs' hf hr =>
      cases h
      obtain ⟨h₁, h₂⟩ := CondS.all_append _ _ hc
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨(o, υ.den ρ), ValsS.mem_of_find _ hf, rfl, subConds_spec h₁⟩
      · exact valsConds_spec rest hr h₂ q hq
    · cases h

/-- What is left to be shown for one shape to stand for another. -/
def shapeConds (S T : ShapeS) : Option (List CondS) :=
  if S = T then some []
  else match S, T with
    | .mk size vals, .mk size' vals' =>
      (valsConds vals vals').map (eqConds size size' ++ ·)
    | _, _ => none

theorem shapeConds_spec {ρ : Env} {S T : ShapeS} {cs : List CondS}
    (h : shapeConds S T = some cs) (hc : CondS.all ρ cs) : SubShape (S.den ρ) (T.den ρ) := by
  unfold shapeConds at h
  split at h
  · next e => rw [e]; exact SubShape.refl _
  · split at h
    · obtain ⟨vs, hv, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨h₁, h₂⟩ := CondS.all_append _ _ hc
      exact ⟨eqConds_spec h₁, valsConds_spec _ hv h₂⟩
    · cases h

/-- What is left to be shown for one stack to stand for another, piece by piece. -/
def stackConds : List ShapeS → List ShapeS → Option (List CondS)
  | [], [] => some []
  | S :: σ, T :: τ =>
    match shapeConds S T, stackConds σ τ with
    | some cs, some ds => some (cs ++ ds)
    | _, _ => none
  | _, _ => none

theorem stackConds_spec {ρ : Env} (tail : List Shape) : (σ τ : List ShapeS) →
    {cs : List CondS} → stackConds σ τ = some cs → CondS.all ρ cs →
    SubList (denShapes ρ σ tail) (denShapes ρ τ tail)
  | [], [], _, _, _ => SubList.refl _
  | S :: σ, T :: τ, cs, h, hc => by
    unfold stackConds at h
    split at h
    · next cs' ds hs hr =>
      cases h
      obtain ⟨h₁, h₂⟩ := CondS.all_append _ _ hc
      exact .cons (shapeConds_spec hs h₁) (stackConds_spec tail σ τ hr h₂)
    · cases h
  | [], _ :: _, _, h, _ => by cases h
  | _ :: _, [], _, h, _ => by cases h

/-- Every register. -/
def regList : List Reg :=
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

theorem mem_regList (r : Reg) : r ∈ regList := by cases r <;> decide

theorem CondS.all_flatMap {ρ : Env} {α : Type} (f : α → List CondS) : (l : List α) →
    CondS.all ρ (l.flatMap f) → ∀ x ∈ l, CondS.all ρ (f x)
  | [], _, _, hx => by cases hx
  | y :: l, h, x, hx => by
    rw [List.flatMap_cons] at h
    obtain ⟨h₁, h₂⟩ := CondS.all_append _ _ h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h₁
    · exact CondS.all_flatMap f l h₂ x hx

/-- What is left to be shown for every register's type in one table to stand
for its counterpart in another. -/
def regsConds (m m' : RegMap TyS) : List CondS :=
  regList.flatMap fun r => subConds (m.get r) (m'.get r)

theorem regsConds_spec {ρ : Env} {m m' : RegMap TyS} (h : CondS.all ρ (regsConds m m'))
    (r : Reg) : Sub ((m.get r).den ρ) ((m'.get r).den ρ) :=
  subConds_spec (CondS.all_flatMap _ _ h r (mem_regList r))

/-- **What is left to be shown for one context to stand for another.** The
stacks must go on as the same thing, and the owned blocks be written the
same. -/
def subCtx (Γ Δ : CtxS) : Option (List CondS) :=
  if Γ.stackRest = Δ.stackRest ∧ Γ.owned = Δ.owned ∧ Γ.ownedRest = Δ.ownedRest then
    (stackConds Γ.stack Δ.stack).map fun ss =>
      regsConds Γ.regs Δ.regs ++ (ss ++ (eqConds Γ.room Δ.room ++
        (flagsConds Γ.flags Δ.flags ++ eqConds Γ.above Δ.above)))
  else none

theorem subCtx_sound {ρ : Env} {Γ Δ : CtxS} {cs : List CondS} (h : subCtx Γ Δ = some cs)
    (hc : CondS.all ρ cs) : CtxSub (Γ.den ρ) (Δ.den ρ) := by
  unfold subCtx at h
  split at h
  · next he =>
    cases hs : stackConds Γ.stack Δ.stack with
    | none => rw [hs] at h; cases h
    | some ss =>
      rw [hs] at h; cases h
      obtain ⟨hr, hc⟩ := CondS.all_append _ _ hc
      obtain ⟨hst, hc⟩ := CondS.all_append _ _ hc
      obtain ⟨hroom, hc⟩ := CondS.all_append _ _ hc
      obtain ⟨hfl, habove⟩ := CondS.all_append _ _ hc
      refine ⟨fun r _ => ?_, ?_, eqConds_spec hroom, flagsConds_spec hfl, ?_, ?_,
        eqConds_spec habove⟩
      · rw [CtxS.den_regs, CtxS.den_regs]; exact regsConds_spec hr r
      · rw [CtxS.den_stack, CtxS.den_stack, ← he.1]
        exact stackConds_spec _ _ _ hs hst
      · rw [CtxS.den_regs, CtxS.den_regs]; exact regsConds_spec hr .rsp
      · rw [CtxS.den_owned, CtxS.den_owned, he.2.1, he.2.2]
  · cases h

/-! ## Why the checker has no answer

Where the checker refuses an instruction, the reason is found by going
through what it does with the same parts it is made of: where the operand
is, whether the bytes are inside the block, whether they may be written.
The reason is for the one who wrote the program, so it is said of the
program; it is no part of what makes a typing sound. -/

/-- Why an instruction is refused. -/
inductive Reject
  /-- The stack pointer is an operand that may not be it. -/
  | spOperand
  /-- A register an address is taken from does not hold a pointer. -/
  | notPointer (r : Reg) (τ : TyS) (writing : Bool)
  /-- An index register does not hold an exactly known value. -/
  | indexUnknown (r : Reg) (τ : TyS)
  /-- A store through a pointer that may only be read through. -/
  | readOnly (r : Reg) (τ : TyS)
  /-- An exactly known address that is in no block the context owns. -/
  | notOwned
  /-- A fixed address that is in none of the program's blocks. -/
  | noBlock
  /-- Bytes not inside one piece of the stack. -/
  | noPiece
  /-- An access that reaches past the end of its block, or of its piece. -/
  | pastBlock
  | pastPiece
  /-- Plain bytes stored over a typed value others may read, or over bytes
  not known to be clear of one. -/
  | typedThere
  | notClear
  /-- Another typed value reaches into the eight bytes stored to. -/
  | notSole
  /-- Not enough room on the stack: what there is. -/
  | roomShort (room : Num)
  /-- The pieces at the top of the stack do not come to the bytes given back. -/
  | framePieces
  /-- Nothing to pop, or a piece that is not eight bytes. -/
  | popPiece
  /-- A divide whose values are not exactly known: the register and its type. -/
  | divUnknown (r : Reg) (τ : TyS)
  /-- A divide by zero, or one whose quotient does not fit. -/
  | divFault
  /-- A divide by a value in memory that is not exactly known: what is there. -/
  | divThere (τ : Option TyS)
  /-- A form the checker has no case for. -/
  | noForm

/-- How many bytes of its memory operand an instruction reads or writes,
and whether it writes them. -/
def access? : Instr → Option (Nat × Bool)
  | .mov w (.r_m _ _) => some (w.bytes.toNat, false)
  | .mov w (.rm_r (.mem _) _) => some (w.bytes.toNat, true)
  | .mov w (.rm_i (.mem _) _) => some (w.bytes.toNat, true)
  | .store8 _ _ => some (1, true)
  | .store16 _ _ => some (2, true)
  | .alu _ w (.r_m _ _) => some (w.bytes.toNat, false)
  | .alu op w (.rm_r (.mem _) _) => some (w.bytes.toNat, op.writesDst)
  | .alu op w (.rm_i (.mem _) _) => some (w.bytes.toNat, op.writesDst)
  | .test w (.mem _) _ => some (w.bytes.toNat, false)
  | .unary _ w (.mem _) => some (w.bytes.toNat, true)
  | .shift _ w (.mem _) _ => some (w.bytes.toNat, true)
  | .mulDiv _ w (.mem _) => some (w.bytes.toNat, false)
  | .imul2 w _ (.mem _) => some (w.bytes.toNat, false)
  | .imul3 w _ (.mem _) _ => some (w.bytes.toNat, false)
  | .popcnt w _ (.mem _) => some (w.bytes.toNat, false)
  | .movsxd _ (.mem _) => some (4, false)
  | .movzx _ _ sw (.mem _) => some (sw.bytes, false)
  | .movsx _ _ sw (.mem _) => some (sw.bytes, false)
  | .cmov _ w _ (.mem _) => some (w.bytes.toNat, false)
  | .setcc _ (.mem _) => some (1, true)
  | _ => none

/-- The register an instruction writes, where it writes one. -/
def dst? : Instr → Option Reg
  | .mov _ (.r_m d _) | .mov _ (.rm_r (.reg d) _) | .mov _ (.rm_i (.reg d) _) => some d
  | .alu _ _ (.r_m d _) | .alu _ _ (.rm_r (.reg d) _) | .alu _ _ (.rm_i (.reg d) _) => some d
  | .unary _ _ (.reg d) | .shift _ _ (.reg d) _ => some d
  | .imul2 _ d _ | .imul3 _ d _ _ | .popcnt _ d _ | .movsxd d _ => some d
  | .movzx _ d _ _ | .movsx _ d _ _ | .cmov _ _ d _ | .setcc _ (.reg d) => some d
  | .lea _ d _ => some d
  | _ => none

/-- Why an access of `n` bytes to a memory operand is refused. `typed` is
whether what is stored is a whole value with a type of its own. -/
def whyMem (next : BitVec 64) (Γ : CtxS) (m : Mem) (n : Nat) (writing typed : Bool) : Reject :=
  match locate next Γ m with
  | some (pl, _) =>
    match within pl.off n pl.shape.size with
    | none =>
      match pl.kind with
      | .piece _ => .pastPiece
      | _ => .pastBlock
    | some _ =>
      if writing then
        match pl.kind, m with
        | .ptr false, .sib (some b) _ _ => .readOnly b (Γ.regs.get b)
        | .block false, _ => .typedThere
        | .ptr true, _ | .block true, _ =>
          match pl.shape.look pl.off with
          | some _ => if typed then .notSole else .typedThere
          | none => .notClear
        | _, _ => .noForm
      else .noForm
  | none =>
    match m with
    | .sib (some .rsp) _ _ => .noPiece
    | .sib (some b) ix _ =>
      match Γ.regs.get b, ix with
      | .ptr _ _ _, some (x, _) => .indexUnknown x.toReg (Γ.regs.get x.toReg)
      | .eq _, some (x, _) =>
        match Γ.regs.get x.toReg with
        | .eq _ => .notOwned
        | τ => .indexUnknown x.toReg τ
      | .eq _, none => .notOwned
      | τ, _ => .notPointer b τ writing
    | _ => .noBlock

/-- **Why the checker refuses an instruction**, where it does. -/
def why (next : BitVec 64) (Γ : CtxS) (i : Instr) : Reject :=
  match i.memOperand?, access? i with
  | some m, some (n, writing) =>
    match whyMem next Γ m n writing
        (match i with | .mov .w64 (.rm_r (.mem _) _) => true | _ => false), i with
    -- a divide by what is in memory, which is there to be read
    | .noForm, .mulDiv .div _ _ | .noForm, .mulDiv .idiv _ _ =>
      match exactly (Γ.regs.get .rax), exactly (Γ.regs.get .rdx), locate next Γ m with
      | none, _, _ => .divUnknown .rax (Γ.regs.get .rax)
      | _, none, _ => .divUnknown .rdx (Γ.regs.get .rdx)
      | _, _, some (pl, _) =>
        match pl.shape.look pl.off with
        | some (some (.eq _)) => .divFault
        | some (some τ) => .divThere (some τ)
        | _ => .divThere none
      | _, _, none => .noForm
    | r, _ => r
  | _, _ =>
    match i with
    | .push _ => .spOperand
    | .pop r => if r = .rsp then .spOperand else .popPiece
    | .alu .add .w64 (.rm_i (.reg .rsp) _) => .framePieces
    | .mulDiv _ _ (.reg r) =>
      if r = .rsp then .spOperand
      else match Γ.regs.get .rax, Γ.regs.get .rdx, Γ.regs.get r with
        | .eq _, .eq _, .eq _ => .divFault
        | .eq _, .eq _, τ => .divUnknown r τ
        | .eq _, τ, _ => .divUnknown .rdx τ
        | τ, _, _ => .divUnknown .rax τ
    | i => if dst? i = some .rsp then .spOperand else .noForm

end Sym

end TypedAsm
