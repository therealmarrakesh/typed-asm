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
  bound := ρ.bound

mutual

def Val.subst (σ : Inst) : Val → Val
  | .lit v => .lit v
  | .var i => σ.val i
  | .bvar i => .bvar i
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
  | .bvar => .bvar
  | .out i a b c fl next ea cell =>
    .out i (a.subst σ) (b.subst σ) (c.subst σ) (fl.subst σ) next (ea.subst σ) (cell.subst σ)

end

mutual

theorem Val.den_subst (ρ : Env) (σ : Inst) : (a : Val) → (a.subst σ).den ρ = a.den (ρ.inst σ)
  | .lit _ => rfl
  | .var _ => rfl
  | .bvar _ => rfl
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
  | .bvar => rfl
  | .out i a b c fl next ea cell => by
    simp only [FlagsT.subst, FlagsT.den, Val.den_subst ρ σ a, Val.den_subst ρ σ b,
      Val.den_subst ρ σ c, FlagsT.den_subst ρ σ fl, Val.den_subst ρ σ ea,
      Val.den_subst ρ σ cell]

end

/-! ## Terms that mention none of a family's values -/

mutual

/-- Whether a term mentions none of the values a family ranges over. -/
def Val.closed : Val → Bool
  | .lit _ => true
  | .var _ => true
  | .bvar _ => false
  | .add a b => a.closed && b.closed
  | .shl a _ => a.closed
  | .out _ _ a b c fl _ ea cell =>
    a.closed && b.closed && c.closed && fl.closed && ea.closed && cell.closed
  | .stored _ a b c fl _ ea cell =>
    a.closed && b.closed && c.closed && fl.closed && ea.closed && cell.closed
  | .goes _ a b c fl _ ea cell =>
    a.closed && b.closed && c.closed && fl.closed && ea.closed && cell.closed

def FlagsT.closed : FlagsT → Bool
  | .lit _ => true
  | .var _ => true
  | .bvar => false
  | .out _ a b c fl _ ea cell =>
    a.closed && b.closed && c.closed && fl.closed && ea.closed && cell.closed

end

mutual

/-- Such a term stands for the same whatever those values are. -/
theorem Val.den_bound (ρ : Env) (z : Seq) :
    (a : Val) → a.closed = true → a.den { ρ with bound := z } = a.den ρ
  | .lit _, _ => rfl
  | .var _, _ => rfl
  | .bvar _, h => nomatch h
  | .add a b, h => by
    simp only [Val.closed, Bool.and_eq_true] at h
    simp only [Val.den, Val.den_bound ρ z a h.1, Val.den_bound ρ z b h.2]
  | .shl a s, h => by
    simp only [Val.closed] at h
    simp only [Val.den, Val.den_bound ρ z a h]
  | .out i j a b c fl next ea cell, h => by
    simp only [Val.closed, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hf⟩, he⟩, hcell⟩ := h
    simp only [Val.den, Val.den_bound ρ z a ha, Val.den_bound ρ z b hb,
      Val.den_bound ρ z c hc, FlagsT.den_bound ρ z fl hf, Val.den_bound ρ z ea he,
      Val.den_bound ρ z cell hcell]
  | .stored i a b c fl next ea cell, h => by
    simp only [Val.closed, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hf⟩, he⟩, hcell⟩ := h
    simp only [Val.den, Val.den_bound ρ z a ha, Val.den_bound ρ z b hb,
      Val.den_bound ρ z c hc, FlagsT.den_bound ρ z fl hf, Val.den_bound ρ z ea he,
      Val.den_bound ρ z cell hcell]
  | .goes i a b c fl next ea cell, h => by
    simp only [Val.closed, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hf⟩, he⟩, hcell⟩ := h
    simp only [Val.den, Val.den_bound ρ z a ha, Val.den_bound ρ z b hb,
      Val.den_bound ρ z c hc, FlagsT.den_bound ρ z fl hf, Val.den_bound ρ z ea he,
      Val.den_bound ρ z cell hcell]

theorem FlagsT.den_bound (ρ : Env) (z : Seq) :
    (f : FlagsT) → f.closed = true → f.den { ρ with bound := z } = f.den ρ
  | .lit _, _ => rfl
  | .var _, _ => rfl
  | .bvar, h => nomatch h
  | .out i a b c fl next ea cell, h => by
    simp only [FlagsT.closed, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hf⟩, he⟩, hcell⟩ := h
    simp only [FlagsT.den, Val.den_bound ρ z a ha, Val.den_bound ρ z b hb,
      Val.den_bound ρ z c hc, FlagsT.den_bound ρ z fl hf, Val.den_bound ρ z ea he,
      Val.den_bound ρ z cell hcell]

end

mutual

/-- What is known of a value stands for the same whatever a family's values
are outside it: code wanting a family gives the family its own. -/
theorem TyS.den_bound (ρ : Env) (z : Seq) : (τ : TyS) → τ.den { ρ with bound := z } = τ.den ρ
  | .any => rfl
  | .ptr S w off => by simp only [TyS.den, ShapeS.den_bound ρ z S]
  | .ref _ _ _ => rfl
  | .nullable τ => by simp only [TyS.den, TyS.den_bound ρ z τ]
  | .orErr τ => by simp only [TyS.den, TyS.den_bound ρ z τ]
  | .str _ => rfl
  | .atom _ => rfl
  | .code _ _ _ _ _ => rfl

theorem ShapeS.den_bound (ρ : Env) (z : Seq) : (S : ShapeS) → S.den { ρ with bound := z } = S.den ρ
  | .mk size vals => by simp only [ShapeS.den, ValsS.den_bound ρ z vals]

theorem ValsS.den_bound (ρ : Env) (z : Seq) :
    (vs : ValsS) → vs.den { ρ with bound := z } = vs.den ρ
  | .nil => rfl
  | .cons o τ rest => by
    simp only [ValsS.den, TyS.den_bound ρ z τ, ValsS.den_bound ρ z rest]

end

/-- The terms given to names mention none of a family's values. -/
structure Inst.Closed (σ : Inst) : Prop where
  val : ∀ j, (σ.val j).closed = true
  flags : ∀ j, (σ.flags j).closed = true

/-- Then the setting they give, inside a family, is the setting they give
outside it with the family's values. -/
theorem Env.inst_bound (ρ : Env) (σ : Inst) (hσ : σ.Closed) (z : Seq) :
    ({ ρ with bound := z } : Env).inst σ = { ρ.inst σ with bound := z } := by
  have h1 : (fun j => (σ.val j).den { ρ with bound := z }) = fun j => (σ.val j).den ρ :=
    funext fun j => Val.den_bound ρ z _ (hσ.val j)
  have h2 : (fun j => (σ.flags j).den { ρ with bound := z }) = fun j => (σ.flags j).den ρ :=
    funext fun j => FlagsT.den_bound ρ z _ (hσ.flags j)
  have h3 : (fun j => (σ.ty j).den { ρ with bound := z }) = fun j => (σ.ty j).den ρ :=
    funext fun j => TyS.den_bound ρ z _
  have h4 : (fun j => restDen { ρ with bound := z } (σ.rest j)) = fun j => restDen ρ (σ.rest j) :=
    funext fun j => by cases σ.rest j <;> rfl
  show Env.mk (fun j => (σ.val j).den { ρ with bound := z }) (fun j => (σ.flags j).den { ρ with bound := z })
      (fun j => (σ.ty j).den { ρ with bound := z }) (fun j => restDen { ρ with bound := z } (σ.rest j)) z
    = _
  rw [h1, h2, h3, h4]
  rfl

/-! ## What is known, and contexts -/

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

theorem heldDen_subst (ρ : Env) (σ : Inst) (held : List (Val × HeldS)) :
    ((held.map fun b => (b.1.subst σ, b.2.subst σ)).map fun b => (b.1.den ρ, b.2.den ρ))
      = held.map fun b => (b.1.den (ρ.inst σ), b.2.den (ρ.inst σ)) := by
  rw [List.map_map]
  exact List.map_congr_left fun b _ => by
    show ((b.1.subst σ).den ρ, (b.2.subst σ).den ρ) = _
    rw [Val.den_subst, HeldS.den_subst]

theorem restDen_subst (ρ : Env) (σ : Inst) (rest : Option Nat) :
    restDen ρ (rest.bind σ.rest) = restDen (ρ.inst σ) rest := by
  cases rest <;> rfl

mutual

def TyS.subst (σ : Inst) : TyS → TyS
  | .any => .any
  | .ptr S w off => .ptr (S.subst σ) w off
  | .ref tag w off => .ref tag w off
  | .nullable τ => .nullable (τ.subst σ)
  | .orErr τ => .orErr (τ.subst σ)
  | .str more => .str more
  | .atom i => σ.ty i
  | .code regs flags held known rest =>
    .code (regs.map (Val.subst σ)) (flags.subst σ)
      (held.map fun b => (b.1.subst σ, b.2.subst σ)) (known.subst σ) (rest.bind σ.rest)

def ShapeS.subst (σ : Inst) : ShapeS → ShapeS
  | .mk size vals => .mk size (vals.subst σ)

def ValsS.subst (σ : Inst) : ValsS → ValsS
  | .nil => .nil
  | .cons o τ rest => .cons o (τ.subst σ) (rest.subst σ)

def FactsS.subst (σ : Inst) : FactsS → FactsS
  | .nil => .nil
  | .cons v τ rest => .cons (v.subst σ) (τ.subst σ) (rest.subst σ)

end

mutual

theorem TyS.den_subst (ρ : Env) (σ : Inst) (hσ : σ.Closed) :
    (τ : TyS) → (τ.subst σ).den ρ = τ.den (ρ.inst σ)
  | .any => rfl
  | .ptr S w off => by simp only [TyS.subst, TyS.den, ShapeS.den_subst ρ σ hσ S]
  | .ref _ _ _ => rfl
  | .nullable τ => by simp only [TyS.subst, TyS.den, TyS.den_subst ρ σ hσ τ]
  | .orErr τ => by simp only [TyS.subst, TyS.den, TyS.den_subst ρ σ hσ τ]
  | .str _ => rfl
  | .atom _ => rfl
  | .code regs flags held known rest => by
    show Ty.code _ = Ty.code _
    congr 1
    funext z
    have e := Env.inst_bound ρ σ hσ z
    refine ctx_ext ?_ ?_ ?_ ?_
    · funext r
      show ((regs.map (Val.subst σ)).get r).den { ρ with bound := z }
        = (regs.get r).den { ρ.inst σ with bound := z }
      rw [Regs.get_map, Val.den_subst, e]
    · show (flags.subst σ).den { ρ with bound := z } = flags.den { ρ.inst σ with bound := z }
      rw [FlagsT.den_subst, e]
    · show ((held.map fun b => (b.1.subst σ, b.2.subst σ)).map fun b =>
          (b.1.den { ρ with bound := z }, b.2.den { ρ with bound := z }))
          ++ restDen { ρ with bound := z } (rest.bind σ.rest)
        = (held.map fun b => (b.1.den { ρ.inst σ with bound := z },
            b.2.den { ρ.inst σ with bound := z })) ++ restDen { ρ.inst σ with bound := z } rest
      rw [heldDen_subst, restDen_subst, e]
    · show (known.subst σ).den { ρ with bound := z } = known.den { ρ.inst σ with bound := z }
      rw [FactsS.den_subst _ σ hσ known, e]

theorem ShapeS.den_subst (ρ : Env) (σ : Inst) (hσ : σ.Closed) :
    (S : ShapeS) → (S.subst σ).den ρ = S.den (ρ.inst σ)
  | .mk size vals => by simp only [ShapeS.subst, ShapeS.den, ValsS.den_subst ρ σ hσ vals]

theorem ValsS.den_subst (ρ : Env) (σ : Inst) (hσ : σ.Closed) :
    (vs : ValsS) → (vs.subst σ).den ρ = vs.den (ρ.inst σ)
  | .nil => rfl
  | .cons o τ rest => by
    simp only [ValsS.subst, ValsS.den, TyS.den_subst ρ σ hσ τ, ValsS.den_subst ρ σ hσ rest]

theorem FactsS.den_subst (ρ : Env) (σ : Inst) (hσ : σ.Closed) :
    (fs : FactsS) → (fs.subst σ).den ρ = fs.den (ρ.inst σ)
  | .nil => rfl
  | .cons v τ rest => by
    simp only [FactsS.subst, FactsS.den, Val.den_subst ρ σ v, TyS.den_subst ρ σ hσ τ,
      FactsS.den_subst ρ σ hσ rest]

end

/-- A context with its names given terms. -/
def CtxS.subst (σ : Inst) (Γ : CtxS) : CtxS where
  regs := Γ.regs.map (Val.subst σ)
  flags := Γ.flags.subst σ
  held := Γ.held.map fun b => (b.1.subst σ, b.2.subst σ)
  known := Γ.known.map fun f => (f.1.subst σ, f.2.subst σ)
  rest := Γ.rest.bind σ.rest

/-- **It stands for what the context stood for in the setting the terms
give.** -/
theorem CtxS.den_subst (ρ : Env) (σ : Inst) (hσ : σ.Closed) (Γ : CtxS) :
    (Γ.subst σ).den ρ = Γ.den (ρ.inst σ) := by
  refine ctx_ext ?_ ?_ ?_ ?_
  · funext r
    show ((Γ.regs.map (Val.subst σ)).get r).den ρ = _
    rw [Regs.get_map]
    exact Val.den_subst ρ σ _
  · exact FlagsT.den_subst ρ σ _
  · show (Γ.held.map _).map _ ++ restDen ρ (Γ.rest.bind σ.rest)
      = Γ.held.map _ ++ restDen (ρ.inst σ) Γ.rest
    rw [heldDen_subst, restDen_subst]
  · show (Γ.known.map _).map _ = Γ.known.map _
    rw [List.map_map]
    exact List.map_congr_left fun f _ => by
      show ((f.1.subst σ).den ρ, (f.2.subst σ).den ρ) = _
      rw [Val.den_subst, TyS.den_subst ρ σ hσ]

end TypedAsm.U
