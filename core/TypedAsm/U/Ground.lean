import TypedAsm.U.TyS

/-!
# What is known that mentions nothing

Knowledge written with no name, no value of a family and nothing left
unwritten in it stands for the same thing whatever names stand for. The
shapes of a program's kinds, and of the blocks it says its segments are,
are to be so.
-/

namespace TypedAsm.U

open TypedAsm

mutual

/-- Whether what is known mentions nothing: no name, no value of a family,
no knowledge left unwritten, no code. -/
def TyS.ground : TyS → Bool
  | .any => true
  | .ptr S _ _ => S.ground
  | .ref _ _ _ => true
  | .nullable τ => τ.ground
  | .orErr τ => τ.ground
  | .str (.lit _) => true
  | .range _ _ => true
  | _ => false

def ShapeS.ground : ShapeS → Bool
  | .mk _ vals => vals.ground

def ValsS.ground : ValsS → Bool
  | .nil => true
  | .cons _ τ rest => τ.ground && rest.ground

end

mutual

theorem TyS.den_ground (ρ₁ ρ₂ : Env) : (τ : TyS) → τ.ground = true → τ.den ρ₁ = τ.den ρ₂
  | .any, _ => rfl
  | .ptr S w off, h => by
    simp only [TyS.den, ShapeS.den_ground ρ₁ ρ₂ S (by simpa only [TyS.ground] using h)]
  | .ref _ _ _, _ => rfl
  | .nullable τ, h => by
    simp only [TyS.den, TyS.den_ground ρ₁ ρ₂ τ (by simpa only [TyS.ground] using h)]
  | .orErr τ, h => by
    simp only [TyS.den, TyS.den_ground ρ₁ ρ₂ τ (by simpa only [TyS.ground] using h)]
  | .str (.lit _), _ => rfl
  | .range _ _, _ => rfl
  | .str (.var _), h => nomatch h
  | .str (.bvar _ _), h => nomatch h
  | .str (.slot _), h => nomatch h
  | .str (.un _ _), h => nomatch h
  | .str (.bin _ _ _), h => nomatch h
  | .str (.tri _ _ _ _), h => nomatch h
  | .str (.fop _ _ _ _), h => nomatch h
  | .atom _, h => nomatch h
  | .code .., h => nomatch h

theorem ShapeS.den_ground (ρ₁ ρ₂ : Env) : (S : ShapeS) → S.ground = true → S.den ρ₁ = S.den ρ₂
  | .mk size vals, h => by
    simp only [ShapeS.den, ValsS.den_ground ρ₁ ρ₂ vals (by simpa only [ShapeS.ground] using h)]

theorem ValsS.den_ground (ρ₁ ρ₂ : Env) : (vs : ValsS) → vs.ground = true → vs.den ρ₁ = vs.den ρ₂
  | .nil, _ => rfl
  | .cons o τ rest, h => by
    simp only [ValsS.ground, Bool.and_eq_true] at h
    simp only [ValsS.den, TyS.den_ground ρ₁ ρ₂ τ h.1, ValsS.den_ground ρ₁ ρ₂ rest h.2]

end

end TypedAsm.U
