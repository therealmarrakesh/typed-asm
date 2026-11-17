import TypedAsm.U.Fresh

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
  | .bvar d i => .bvar d i
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
  | .bvar d => .bvar d
  | .out i a b c fl next ea cell =>
    .out i (a.subst σ) (b.subst σ) (c.subst σ) (fl.subst σ) next (ea.subst σ) (cell.subst σ)

end

mutual

theorem Val.den_subst (ρ : Env) (σ : Inst) : (a : Val) → (a.subst σ).den ρ = a.den (ρ.inst σ)
  | .lit _ => rfl
  | .var _ => rfl
  | .bvar _ _ => rfl
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
  | .bvar _ => rfl
  | .out i a b c fl next ea cell => by
    simp only [FlagsT.subst, FlagsT.den, Val.den_subst ρ σ a, Val.den_subst ρ σ b,
      Val.den_subst ρ σ c, FlagsT.den_subst ρ σ fl, Val.den_subst ρ σ ea,
      Val.den_subst ρ σ cell]

end

/-! ## Terms that mention only so many enclosing families -/

mutual

/-- Whether a term mentions the values of only the `n` families nearest
it. With none, it mentions no family's values. -/
def Val.closedAt (n : Nat) : Val → Bool
  | .lit _ => true
  | .var _ => true
  | .bvar d _ => decide (d < n)
  | .add a b => a.closedAt n && b.closedAt n
  | .shl a _ => a.closedAt n
  | .out _ _ a b c fl _ ea cell =>
    a.closedAt n && b.closedAt n && c.closedAt n && fl.closedAt n && ea.closedAt n &&
      cell.closedAt n
  | .stored _ a b c fl _ ea cell =>
    a.closedAt n && b.closedAt n && c.closedAt n && fl.closedAt n && ea.closedAt n &&
      cell.closedAt n
  | .goes _ a b c fl _ ea cell =>
    a.closedAt n && b.closedAt n && c.closedAt n && fl.closedAt n && ea.closedAt n &&
      cell.closedAt n

def FlagsT.closedAt (n : Nat) : FlagsT → Bool
  | .lit _ => true
  | .var _ => true
  | .bvar d => decide (d < n)
  | .out _ a b c fl _ ea cell =>
    a.closedAt n && b.closedAt n && c.closedAt n && fl.closedAt n && ea.closedAt n &&
      cell.closedAt n

end

/-- Two stacks of families' values that agree on the `n` nearest. -/
def Agree (n : Nat) (zs zs' : List Seq) : Prop :=
  ∀ d, d < n → zs.getD d (fun _ => 0) = zs'.getD d (fun _ => 0)

theorem Agree.cons {n : Nat} {zs zs' : List Seq} (h : Agree n zs zs') (z : Seq) :
    Agree (n + 1) (z :: zs) (z :: zs') := by
  intro d hd
  cases d with
  | zero => rfl
  | succ d => exact h d (by omega)

mutual

/-- Such a term stands for the same under any two stacks that agree on
those families. -/
theorem Val.den_agree (ρ : Env) (n : Nat) (zs zs' : List Seq) (hz : Agree n zs zs') :
    (a : Val) → a.closedAt n = true → a.den { ρ with bound := zs } = a.den { ρ with bound := zs' }
  | .lit _, _ => rfl
  | .var _, _ => rfl
  | .bvar d i, h => by
    simp only [Val.closedAt, decide_eq_true_eq] at h
    show (zs.getD d fun _ => 0) (i + 1) = (zs'.getD d fun _ => 0) (i + 1)
    rw [hz d h]
  | .add a b, h => by
    simp only [Val.closedAt, Bool.and_eq_true] at h
    simp only [Val.den, Val.den_agree ρ n zs zs' hz a h.1, Val.den_agree ρ n zs zs' hz b h.2]
  | .shl a s, h => by
    simp only [Val.closedAt] at h
    simp only [Val.den, Val.den_agree ρ n zs zs' hz a h]
  | .out i j a b c fl next ea cell, h => by
    simp only [Val.closedAt, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hf⟩, he⟩, hcell⟩ := h
    simp only [Val.den, Val.den_agree ρ n zs zs' hz a ha, Val.den_agree ρ n zs zs' hz b hb,
      Val.den_agree ρ n zs zs' hz c hc, FlagsT.den_agree ρ n zs zs' hz fl hf,
      Val.den_agree ρ n zs zs' hz ea he, Val.den_agree ρ n zs zs' hz cell hcell]
  | .stored i a b c fl next ea cell, h => by
    simp only [Val.closedAt, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hf⟩, he⟩, hcell⟩ := h
    simp only [Val.den, Val.den_agree ρ n zs zs' hz a ha, Val.den_agree ρ n zs zs' hz b hb,
      Val.den_agree ρ n zs zs' hz c hc, FlagsT.den_agree ρ n zs zs' hz fl hf,
      Val.den_agree ρ n zs zs' hz ea he, Val.den_agree ρ n zs zs' hz cell hcell]
  | .goes i a b c fl next ea cell, h => by
    simp only [Val.closedAt, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hf⟩, he⟩, hcell⟩ := h
    simp only [Val.den, Val.den_agree ρ n zs zs' hz a ha, Val.den_agree ρ n zs zs' hz b hb,
      Val.den_agree ρ n zs zs' hz c hc, FlagsT.den_agree ρ n zs zs' hz fl hf,
      Val.den_agree ρ n zs zs' hz ea he, Val.den_agree ρ n zs zs' hz cell hcell]

theorem FlagsT.den_agree (ρ : Env) (n : Nat) (zs zs' : List Seq) (hz : Agree n zs zs') :
    (f : FlagsT) → f.closedAt n = true →
    f.den { ρ with bound := zs } = f.den { ρ with bound := zs' }
  | .lit _, _ => rfl
  | .var _, _ => rfl
  | .bvar d, h => by
    simp only [FlagsT.closedAt, decide_eq_true_eq] at h
    show flagsOf ((zs.getD d fun _ => 0) 0) = flagsOf ((zs'.getD d fun _ => 0) 0)
    rw [hz d h]
  | .out i a b c fl next ea cell, h => by
    simp only [FlagsT.closedAt, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hf⟩, he⟩, hcell⟩ := h
    simp only [FlagsT.den, Val.den_agree ρ n zs zs' hz a ha, Val.den_agree ρ n zs zs' hz b hb,
      Val.den_agree ρ n zs zs' hz c hc, FlagsT.den_agree ρ n zs zs' hz fl hf,
      Val.den_agree ρ n zs zs' hz ea he, Val.den_agree ρ n zs zs' hz cell hcell]

end

/-- Whether the regions of a list mention only so many families. -/
def heldClosedAt (n : Nat) (held : List (Val × HeldS)) : Bool :=
  held.all fun b => b.1.closedAt n && b.2.slots.all fun p => p.2.closedAt n

theorem heldDen_agree (ρ : Env) (n : Nat) (zs zs' : List Seq) (hz : Agree n zs zs')
    (held : List (Val × HeldS)) (h : heldClosedAt n held = true) :
    (held.map fun b => (b.1.den { ρ with bound := zs }, b.2.den { ρ with bound := zs }))
      = held.map fun b => (b.1.den { ρ with bound := zs' }, b.2.den { ρ with bound := zs' }) := by
  refine List.map_congr_left fun b hb => ?_
  have hbk := List.all_eq_true.mp h b hb
  rw [Bool.and_eq_true] at hbk
  show (b.1.den _, (⟨b.2.size, b.2.slots.map fun p => (p.1, p.2.den { ρ with bound := zs })⟩ : Held))
    = (b.1.den _, ⟨b.2.size, b.2.slots.map fun p => (p.1, p.2.den { ρ with bound := zs' })⟩)
  rw [Val.den_agree ρ n zs zs' hz _ hbk.1]
  congr 2
  exact List.map_congr_left fun p hp => by
    rw [Val.den_agree ρ n zs zs' hz _ (List.all_eq_true.mp hbk.2 p hp)]

theorem Regs.all_of_map {f : Val → Bool} (regs : Regs Val) (h : (regs.map f == allTrue) = true)
    (r : Reg) : f (regs.get r) = true := by
  have h1 : (regs.map f).get r = f (regs.get r) := Regs.get_map _ _ r
  rw [← h1, beq_iff_eq.mp h]
  cases r <;> rfl

mutual

/-- Whether what is known mentions only so many enclosing families. Code
wanting a family is one family further in. -/
def TyS.closedAt (n : Nat) : TyS → Bool
  | .ptr S _ _ => S.closedAt n
  | .nullable τ => τ.closedAt n
  | .orErr τ => τ.closedAt n
  | .code regs flags held known _ =>
    (regs.map (Val.closedAt (n + 1)) == allTrue) && flags.closedAt (n + 1) &&
      heldClosedAt (n + 1) held && known.closedAt (n + 1)
  | _ => true

def ShapeS.closedAt (n : Nat) : ShapeS → Bool
  | .mk _ vals => vals.closedAt n

def ValsS.closedAt (n : Nat) : ValsS → Bool
  | .nil => true
  | .cons _ τ rest => τ.closedAt n && rest.closedAt n

def FactsS.closedAt (n : Nat) : FactsS → Bool
  | .nil => true
  | .cons v τ rest => v.closedAt n && τ.closedAt n && rest.closedAt n

end

mutual

theorem TyS.den_agree (ρ : Env) (n : Nat) (zs zs' : List Seq) (hz : Agree n zs zs') :
    (τ : TyS) → τ.closedAt n = true → τ.den { ρ with bound := zs } = τ.den { ρ with bound := zs' }
  | .any, _ => rfl
  | .ptr S w off, h => by
    simp only [TyS.den, ShapeS.den_agree ρ n zs zs' hz S (by simpa only [TyS.closedAt] using h)]
  | .ref _ _ _, _ => rfl
  | .nullable τ, h => by
    simp only [TyS.den, TyS.den_agree ρ n zs zs' hz τ (by simpa only [TyS.closedAt] using h)]
  | .orErr τ, h => by
    simp only [TyS.den, TyS.den_agree ρ n zs zs' hz τ (by simpa only [TyS.closedAt] using h)]
  | .str _, _ => rfl
  | .atom _, _ => rfl
  | .code regs flags held known rest, h => by
    simp only [TyS.closedAt, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hr, hf⟩, hh⟩, hkn⟩ := h
    show Ty.code _ = Ty.code _
    congr 1
    funext z
    have hz' := hz.cons z
    refine ctx_ext ?_ ?_ ?_ ?_
    · funext r
      exact Val.den_agree ρ (n + 1) (z :: zs) (z :: zs') hz' _ (Regs.all_of_map regs hr r)
    · exact FlagsT.den_agree ρ (n + 1) (z :: zs) (z :: zs') hz' _ hf
    · show (held.map fun b => (b.1.den { ρ with bound := z :: zs }, b.2.den { ρ with bound := z :: zs }))
          ++ restDen { ρ with bound := z :: zs } rest
        = (held.map fun b => (b.1.den { ρ with bound := z :: zs' },
            b.2.den { ρ with bound := z :: zs' })) ++ restDen { ρ with bound := z :: zs' } rest
      rw [heldDen_agree ρ (n + 1) (z :: zs) (z :: zs') hz' held hh]
      congr 1
    · exact FactsS.den_agree ρ (n + 1) (z :: zs) (z :: zs') hz' known hkn

theorem ShapeS.den_agree (ρ : Env) (n : Nat) (zs zs' : List Seq) (hz : Agree n zs zs') :
    (S : ShapeS) → S.closedAt n = true → S.den { ρ with bound := zs } = S.den { ρ with bound := zs' }
  | .mk size vals, h => by
    simp only [ShapeS.den,
      ValsS.den_agree ρ n zs zs' hz vals (by simpa only [ShapeS.closedAt] using h)]

theorem ValsS.den_agree (ρ : Env) (n : Nat) (zs zs' : List Seq) (hz : Agree n zs zs') :
    (vs : ValsS) → vs.closedAt n = true →
    vs.den { ρ with bound := zs } = vs.den { ρ with bound := zs' }
  | .nil, _ => rfl
  | .cons o τ rest, h => by
    simp only [ValsS.closedAt, Bool.and_eq_true] at h
    simp only [ValsS.den, TyS.den_agree ρ n zs zs' hz τ h.1, ValsS.den_agree ρ n zs zs' hz rest h.2]

theorem FactsS.den_agree (ρ : Env) (n : Nat) (zs zs' : List Seq) (hz : Agree n zs zs') :
    (fs : FactsS) → fs.closedAt n = true →
    fs.den { ρ with bound := zs } = fs.den { ρ with bound := zs' }
  | .nil, _ => rfl
  | .cons v τ rest, h => by
    simp only [FactsS.closedAt, Bool.and_eq_true] at h
    simp only [FactsS.den, Val.den_agree ρ n zs zs' hz v h.1.1, TyS.den_agree ρ n zs zs' hz τ h.1.2,
      FactsS.den_agree ρ n zs zs' hz rest h.2]

end

/-- What mentions no family's values stands for the same under any stack. -/
theorem Val.den_bound (ρ : Env) (zs : List Seq) (a : Val) (h : a.closedAt 0 = true) :
    a.den { ρ with bound := zs } = a.den ρ :=
  Val.den_agree ρ 0 zs ρ.bound (fun _ hd => absurd hd (Nat.not_lt_zero _)) a h

theorem FlagsT.den_bound (ρ : Env) (zs : List Seq) (f : FlagsT) (h : f.closedAt 0 = true) :
    f.den { ρ with bound := zs } = f.den ρ :=
  FlagsT.den_agree ρ 0 zs ρ.bound (fun _ hd => absurd hd (Nat.not_lt_zero _)) f h

theorem TyS.den_bound (ρ : Env) (zs : List Seq) (τ : TyS) (h : τ.closedAt 0 = true) :
    τ.den { ρ with bound := zs } = τ.den ρ :=
  TyS.den_agree ρ 0 zs ρ.bound (fun _ hd => absurd hd (Nat.not_lt_zero _)) τ h

/-- The terms given to names mention no family's values. -/
structure Inst.Closed (σ : Inst) : Prop where
  val : ∀ j, (σ.val j).closedAt 0 = true
  flags : ∀ j, (σ.flags j).closedAt 0 = true
  ty : ∀ j, (σ.ty j).closedAt 0 = true

/-- Then the setting they give, inside families, is the setting they give
outside them with the families' values. -/
theorem Env.inst_bound (ρ : Env) (σ : Inst) (hσ : σ.Closed) (zs : List Seq) :
    ({ ρ with bound := zs } : Env).inst σ = { ρ.inst σ with bound := zs } := by
  have h1 : (fun j => (σ.val j).den { ρ with bound := zs }) = fun j => (σ.val j).den ρ :=
    funext fun j => Val.den_bound ρ zs _ (hσ.val j)
  have h2 : (fun j => (σ.flags j).den { ρ with bound := zs }) = fun j => (σ.flags j).den ρ :=
    funext fun j => FlagsT.den_bound ρ zs _ (hσ.flags j)
  have h3 : (fun j => (σ.ty j).den { ρ with bound := zs }) = fun j => (σ.ty j).den ρ :=
    funext fun j => TyS.den_bound ρ zs _ (hσ.ty j)
  have h4 : (fun j => restDen { ρ with bound := zs } (σ.rest j)) = fun j => restDen ρ (σ.rest j) :=
    funext fun j => by cases σ.rest j <;> rfl
  show Env.mk (fun j => (σ.val j).den { ρ with bound := zs })
      (fun j => (σ.flags j).den { ρ with bound := zs })
      (fun j => (σ.ty j).den { ρ with bound := zs })
      (fun j => restDen { ρ with bound := zs } (σ.rest j)) zs
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
    have e := Env.inst_bound ρ σ hσ (z :: ρ.bound)
    refine ctx_ext ?_ ?_ ?_ ?_
    · funext r
      show ((regs.map (Val.subst σ)).get r).den { ρ with bound := z :: ρ.bound }
        = (regs.get r).den { ρ.inst σ with bound := z :: ρ.bound }
      rw [Regs.get_map, Val.den_subst, e]
    · show (flags.subst σ).den { ρ with bound := z :: ρ.bound }
        = flags.den { ρ.inst σ with bound := z :: ρ.bound }
      rw [FlagsT.den_subst, e]
    · show ((held.map fun b => (b.1.subst σ, b.2.subst σ)).map fun b =>
          (b.1.den { ρ with bound := z :: ρ.bound }, b.2.den { ρ with bound := z :: ρ.bound }))
          ++ restDen { ρ with bound := z :: ρ.bound } (rest.bind σ.rest)
        = (held.map fun b => (b.1.den { ρ.inst σ with bound := z :: ρ.bound },
            b.2.den { ρ.inst σ with bound := z :: ρ.bound }))
          ++ restDen { ρ.inst σ with bound := z :: ρ.bound } rest
      rw [heldDen_subst, restDen_subst, e]
    · show (known.subst σ).den { ρ with bound := z :: ρ.bound }
        = known.den { ρ.inst σ with bound := z :: ρ.bound }
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
