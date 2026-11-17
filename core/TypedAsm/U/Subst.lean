import TypedAsm.U.Check

/-!
# Terms with their names given terms

A context written for any values of its names is used at particular ones:
each name is given a term, and the context with the terms put in stands,
in one setting of the names, for what the context stood for in the setting
the terms give.
-/

namespace TypedAsm.U

open TypedAsm

/-- A term for each name: of values, of flags, and of knowledge not written
out. -/
structure Inst where
  val : Nat → Val
  flags : Nat → FlagsT
  ty : Nat → TyS
  /-- The name each name for a rest of what is held is given, if any. -/
  rest : Nat → Option Nat := fun _ => none

/-- The setting of the names that the terms give. -/
def Env.inst (ρ : Env) (σ : Inst) : Env where
  val j := (σ.val j).den ρ
  flags j := (σ.flags j).den ρ
  ty j := (σ.ty j).den ρ
  frame j := restDen ρ (σ.rest j)

mutual

def Val.subst (σ : Inst) : Val → Val
  | .lit v => .lit v
  | .var i => σ.val i
  | .add a b => .add (a.subst σ) (b.subst σ)
  | .shl a k => .shl (a.subst σ) k
  | .out i k a b c fl next ea cell =>
    .out i k (a.subst σ) (b.subst σ) (c.subst σ) (fl.subst σ) next (ea.subst σ) (cell.subst σ)
  | .stored i a b c fl next ea cell =>
    .stored i (a.subst σ) (b.subst σ) (c.subst σ) (fl.subst σ) next (ea.subst σ) (cell.subst σ)
  | .goes i a b c fl next ea cell =>
    .goes i (a.subst σ) (b.subst σ) (c.subst σ) (fl.subst σ) next (ea.subst σ) (cell.subst σ)

def FlagsT.subst (σ : Inst) : FlagsT → FlagsT
  | .lit f => .lit f
  | .var i => σ.flags i
  | .out i a b c fl next ea cell =>
    .out i (a.subst σ) (b.subst σ) (c.subst σ) (fl.subst σ) next (ea.subst σ) (cell.subst σ)

end

mutual

theorem Val.den_subst (ρ : Env) (σ : Inst) : (a : Val) → (a.subst σ).den ρ = a.den (ρ.inst σ)
  | .lit _ => rfl
  | .var _ => rfl
  | .add a b => by
    simp only [Val.subst, Val.den, Val.den_subst ρ σ a, Val.den_subst ρ σ b]
  | .shl a s => by simp only [Val.subst, Val.den, Val.den_subst ρ σ a]
  | .out i j a b c fl next ea cell => by
    simp only [Val.subst, Val.den, Val.den_subst ρ σ a, Val.den_subst ρ σ b,
      Val.den_subst ρ σ c, FlagsT.den_subst ρ σ fl, Val.den_subst ρ σ ea,
      Val.den_subst ρ σ cell]
  | .stored i a b c fl next ea cell => by
    simp only [Val.subst, Val.den, Val.den_subst ρ σ a, Val.den_subst ρ σ b,
      Val.den_subst ρ σ c, FlagsT.den_subst ρ σ fl, Val.den_subst ρ σ ea,
      Val.den_subst ρ σ cell]
  | .goes i a b c fl next ea cell => by
    simp only [Val.subst, Val.den, Val.den_subst ρ σ a, Val.den_subst ρ σ b,
      Val.den_subst ρ σ c, FlagsT.den_subst ρ σ fl, Val.den_subst ρ σ ea,
      Val.den_subst ρ σ cell]

theorem FlagsT.den_subst (ρ : Env) (σ : Inst) :
    (f : FlagsT) → (f.subst σ).den ρ = f.den (ρ.inst σ)
  | .lit _ => rfl
  | .var _ => rfl
  | .out i a b c fl next ea cell => by
    simp only [FlagsT.subst, FlagsT.den, Val.den_subst ρ σ a, Val.den_subst ρ σ b,
      Val.den_subst ρ σ c, FlagsT.den_subst ρ σ fl, Val.den_subst ρ σ ea,
      Val.den_subst ρ σ cell]

end

mutual

def TyS.subst (σ : Inst) : TyS → TyS
  | .any => .any
  | .ptr S w off => .ptr (S.subst σ) w off
  | .ref tag w off => .ref tag w off
  | .nullable τ => .nullable (τ.subst σ)
  | .orErr τ => .orErr (τ.subst σ)
  | .str more => .str more
  | .atom i => σ.ty i

def ShapeS.subst (σ : Inst) : ShapeS → ShapeS
  | .mk size vals => .mk size (vals.subst σ)

def ValsS.subst (σ : Inst) : ValsS → ValsS
  | .nil => .nil
  | .cons o τ rest => .cons o (τ.subst σ) (rest.subst σ)

end

mutual

theorem TyS.den_subst (ρ : Env) (σ : Inst) : (τ : TyS) → (τ.subst σ).den ρ = τ.den (ρ.inst σ)
  | .any => rfl
  | .ptr S w off => by simp only [TyS.subst, TyS.den, ShapeS.den_subst ρ σ S]
  | .ref _ _ _ => rfl
  | .nullable τ => by simp only [TyS.subst, TyS.den, TyS.den_subst ρ σ τ]
  | .orErr τ => by simp only [TyS.subst, TyS.den, TyS.den_subst ρ σ τ]
  | .str _ => rfl
  | .atom _ => rfl

theorem ShapeS.den_subst (ρ : Env) (σ : Inst) :
    (S : ShapeS) → (S.subst σ).den ρ = S.den (ρ.inst σ)
  | .mk size vals => by simp only [ShapeS.subst, ShapeS.den, ValsS.den_subst ρ σ vals]

theorem ValsS.den_subst (ρ : Env) (σ : Inst) :
    (vs : ValsS) → (vs.subst σ).den ρ = vs.den (ρ.inst σ)
  | .nil => rfl
  | .cons o τ rest => by
    simp only [ValsS.subst, ValsS.den, TyS.den_subst ρ σ τ, ValsS.den_subst ρ σ rest]

end

def HeldS.subst (σ : Inst) (S : HeldS) : HeldS :=
  ⟨S.size, S.slots.map fun p => (p.1, p.2.subst σ)⟩

theorem HeldS.den_subst (ρ : Env) (σ : Inst) (S : HeldS) :
    (S.subst σ).den ρ = S.den (ρ.inst σ) := by
  show (⟨S.size, (S.slots.map fun p => (p.1, p.2.subst σ)).map fun p => (p.1, p.2.den ρ)⟩ : Held)
    = ⟨S.size, S.slots.map fun p => (p.1, p.2.den (ρ.inst σ))⟩
  rw [List.map_map]
  congr 1
  exact List.map_congr_left fun p _ => by
    show (p.1, (p.2.subst σ).den ρ) = _
    rw [Val.den_subst]

/-- A context with its names given terms. -/
def CtxS.subst (σ : Inst) (Γ : CtxS) : CtxS where
  regs := Γ.regs.map (Val.subst σ)
  flags := Γ.flags.subst σ
  held := Γ.held.map fun b => (b.1.subst σ, b.2.subst σ)
  known := Γ.known.map fun f => (f.1.subst σ, f.2.subst σ)
  rest := Γ.rest.bind σ.rest

/-- **It stands for what the context stood for in the setting the terms
give.** -/
theorem CtxS.den_subst (ρ : Env) (σ : Inst) (Γ : CtxS) :
    (Γ.subst σ).den ρ = Γ.den (ρ.inst σ) := by
  refine ctx_ext ?_ ?_ ?_ ?_
  · funext r
    show ((Γ.regs.map (Val.subst σ)).get r).den ρ = _
    rw [Regs.get_map]
    exact Val.den_subst ρ σ _
  · exact FlagsT.den_subst ρ σ _
  · show (Γ.held.map _).map _ ++ restDen ρ (Γ.rest.bind σ.rest)
      = Γ.held.map _ ++ restDen (ρ.inst σ) Γ.rest
    have hrest : restDen ρ (Γ.rest.bind σ.rest) = restDen (ρ.inst σ) Γ.rest := by
      cases Γ.rest <;> rfl
    rw [hrest, List.map_map]
    congr 1
    exact List.map_congr_left fun b _ => by
      show ((b.1.subst σ).den ρ, (b.2.subst σ).den ρ) = _
      rw [Val.den_subst, HeldS.den_subst]
  · show (Γ.known.map _).map _ = Γ.known.map _
    rw [List.map_map]
    exact List.map_congr_left fun f _ => by
      show ((f.1.subst σ).den ρ, (f.2.subst σ).den ρ) = _
      rw [Val.den_subst, TyS.den_subst]

end TypedAsm.U
