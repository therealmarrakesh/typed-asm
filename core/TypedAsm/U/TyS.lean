import TypedAsm.U.Term

/-!
# What is known of a value, as data

The forms of knowledge a checker looks into, written as data: that a value
points into a block of a shape, or of a kind; that it may be null, or an
error number; that it is an address in a text. Anything else known of a
value, that it is code wanting certain contexts, is a name the checker does
not look into.
-/

namespace TypedAsm.U

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

/-- The shape of a block others may point into, as data. -/
inductive ShapeS
  | mk (size : Nat) (vals : ValsS)

/-- The typed values of a shape: where each is, and what is known of it. -/
inductive ValsS
  | nil
  | cons (o : Nat) (τ : TyS) (rest : ValsS)

end

deriving instance DecidableEq for TyS, ShapeS, ValsS

mutual

def TyS.den (ρ : Env) : TyS → Ty
  | .any => .any
  | .ptr S w off => .ptr (S.den ρ) w off
  | .ref tag w off => .ref tag w off
  | .nullable τ => .nullable (τ.den ρ)
  | .orErr τ => .orErr (τ.den ρ)
  | .str more => .str more
  | .atom i => ρ.ty i

def ShapeS.den (ρ : Env) : ShapeS → Shape
  | .mk size vals => ⟨size, vals.den ρ⟩

def ValsS.den (ρ : Env) : ValsS → List (Nat × Ty)
  | .nil => []
  | .cons o τ rest => (o, τ.den ρ) :: rest.den ρ

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
