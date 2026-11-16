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

namespace CtxS

/-- The context a term stands for. -/
def den (ρ : Env) (Γ : CtxS) : Ctx where
  regs := RegMap.get
    ⟨Γ.regs.rax.den ρ, Γ.regs.rcx.den ρ, Γ.regs.rdx.den ρ, Γ.regs.rbx.den ρ, Γ.regs.rsp.den ρ,
     Γ.regs.rbp.den ρ, Γ.regs.rsi.den ρ, Γ.regs.rdi.den ρ, Γ.regs.r8.den ρ, Γ.regs.r9.den ρ,
     Γ.regs.r10.den ρ, Γ.regs.r11.den ρ, Γ.regs.r12.den ρ, Γ.regs.r13.den ρ, Γ.regs.r14.den ρ,
     Γ.regs.r15.den ρ⟩
  stack := denShapes ρ Γ.stack (match Γ.stackRest with
    | some i => ρ.stack.getD i []
    | none => [])
  room := Γ.room.den ρ
  flags := Γ.flags.den ρ
  owned := denOwned ρ Γ.owned (match Γ.ownedRest with
    | some i => ρ.owned.getD i []
    | none => [])
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

/-- **The checker**, for the forms that work on registers alone. It gives the
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
  · next op w d imm =>
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
