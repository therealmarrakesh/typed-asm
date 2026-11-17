import TypedAsm.U.Term
import TypedAsm.U.Regs

/-!
# What is known of a value, as data

The forms of knowledge a checker looks into, written as data: that a value
points into a block of a shape, or of a kind; that it may be null, or an
error number; that it is an address in a text. Anything else known of a
value, is a name the checker does not look into.

That a value is code wanting a family of contexts is written as data too:
the contexts, as terms, in which the values the family ranges over have
names of their own.
-/

namespace TypedAsm.U

/-- A region held alone, as terms: its size, and the values in it. -/
structure HeldS where
  size : Nat
  slots : List (Nat × Val)
  deriving DecidableEq

def HeldS.den (ρ : Env) (S : HeldS) : Held := ⟨S.size, S.slots.map fun p => (p.1, p.2.den ρ)⟩

/-- The regions a name for the rest stands for. -/
def restDen (ρ : Env) : Option Nat → List Region
  | some j => ρ.frame j
  | none => []

mutual

/-- What is known of a value, as data. -/
inductive TyS
  | any
  | ptr (shape : ShapeS) (writable : Bool) (off : Nat)
  | ref (tag : Nat) (writable : Bool) (off : Nat)
  | nullable (τ : TyS)
  | orErr (τ : TyS)
  | str (more : Bool)
  /-- Knowledge not written out: the `i`th the names stand for. -/
  | atom (i : Nat)
  /-- It is code, safe to enter in the context these terms stand for,
  whatever the values the family ranges over are. -/
  | code (regs : Regs Val) (flags : FlagsT) (held : List (Val × HeldS)) (known : FactsS)
      (rest : Option Nat)

/-- The shape of a block others may point into, as data. -/
inductive ShapeS
  | mk (size : Nat) (vals : ValsS)

/-- The typed values of a shape: where each is, and what is known of it. -/
inductive ValsS
  | nil
  | cons (o : Nat) (τ : TyS) (rest : ValsS)

/-- Things known of values, one after another. -/
inductive FactsS
  | nil
  | cons (v : Val) (τ : TyS) (rest : FactsS)

end

deriving instance DecidableEq for TyS, ShapeS, ValsS, FactsS

mutual

def TyS.den (ρ : Env) : TyS → Ty
  | .any => .any
  | .ptr S w off => .ptr (S.den ρ) w off
  | .ref tag w off => .ref tag w off
  | .nullable τ => .nullable (τ.den ρ)
  | .orErr τ => .orErr (τ.den ρ)
  | .str more => .str more
  | .atom i => ρ.ty i
  | .code regs flags held known rest => .code fun z =>
    { val := fun r => (regs.get r).den { ρ with bound := z :: ρ.bound }
      flags := flags.den { ρ with bound := z :: ρ.bound }
      held := (held.map fun b => (b.1.den { ρ with bound := z :: ρ.bound },
          b.2.den { ρ with bound := z :: ρ.bound }))
        ++ restDen { ρ with bound := z :: ρ.bound } rest
      known := known.den { ρ with bound := z :: ρ.bound } }

def ShapeS.den (ρ : Env) : ShapeS → Shape
  | .mk size vals => ⟨size, vals.den ρ⟩

def ValsS.den (ρ : Env) : ValsS → List (Nat × Ty)
  | .nil => []
  | .cons o τ rest => (o, τ.den ρ) :: rest.den ρ

def FactsS.den (ρ : Env) : FactsS → List (BitVec 64 × Ty)
  | .nil => []
  | .cons v τ rest => (v.den ρ, τ.den ρ) :: rest.den ρ

end

def ShapeS.size : ShapeS → Nat
  | .mk size _ => size

def ShapeS.vals : ShapeS → ValsS
  | .mk _ vals => vals

theorem ShapeS.den_size (ρ : Env) (S : ShapeS) : (S.den ρ).size = S.size := by
  cases S; rfl

theorem ShapeS.den_vals (ρ : Env) (S : ShapeS) : (S.den ρ).vals = S.vals.den ρ := by
  cases S; rfl

end TypedAsm.U
