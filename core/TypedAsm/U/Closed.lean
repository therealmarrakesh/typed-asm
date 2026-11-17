import TypedAsm.U.Fresh

/-!
# What mentions only so many enclosing families

Knowledge that a value is code wanting a family of contexts names the
values the family ranges over by how many families out they belong to. A
term that mentions the values of only the families nearest it stands for
the same whatever the families further out are; one that mentions none
stands for the same under any.
-/

namespace TypedAsm.U

open TypedAsm

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
def Agree (n : Nat) (zs zs' : List Fam) : Prop :=
  ∀ d, d < n → zs.getD d {} = zs'.getD d {}

theorem Agree.cons {n : Nat} {zs zs' : List Fam} (h : Agree n zs zs') (z : Fam) :
    Agree (n + 1) (z :: zs) (z :: zs') := by
  intro d hd
  cases d with
  | zero => rfl
  | succ d => exact h d (by omega)

mutual

/-- Such a term stands for the same under any two stacks that agree on
those families. -/
theorem Val.den_agree (ρ : Env) (n : Nat) (zs zs' : List Fam) (hz : Agree n zs zs') :
    (a : Val) → a.closedAt n = true → a.den { ρ with bound := zs } = a.den { ρ with bound := zs' }
  | .lit _, _ => rfl
  | .var _, _ => rfl
  | .bvar d i, h => by
    simp only [Val.closedAt, decide_eq_true_eq] at h
    show (zs.getD d {}).vals i = (zs'.getD d {}).vals i
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

theorem FlagsT.den_agree (ρ : Env) (n : Nat) (zs zs' : List Fam) (hz : Agree n zs zs') :
    (f : FlagsT) → f.closedAt n = true →
    f.den { ρ with bound := zs } = f.den { ρ with bound := zs' }
  | .lit _, _ => rfl
  | .var _, _ => rfl
  | .bvar d, h => by
    simp only [FlagsT.closedAt, decide_eq_true_eq] at h
    show (zs.getD d {}).flags = (zs'.getD d {}).flags
    rw [hz d h]
  | .out i a b c fl next ea cell, h => by
    simp only [FlagsT.closedAt, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hf⟩, he⟩, hcell⟩ := h
    simp only [FlagsT.den, Val.den_agree ρ n zs zs' hz a ha, Val.den_agree ρ n zs zs' hz b hb,
      Val.den_agree ρ n zs zs' hz c hc, FlagsT.den_agree ρ n zs zs' hz fl hf,
      Val.den_agree ρ n zs zs' hz ea he, Val.den_agree ρ n zs zs' hz cell hcell]

end

/-- Whether whatever else is held is that of one of the `n` families
nearest, or of none. -/
def RestS.closedAt (n : Nat) : RestS → Bool
  | .bvar d => decide (d < n)
  | _ => true

theorem RestS.den_agree (ρ : Env) (n : Nat) (zs zs' : List Fam) (hz : Agree n zs zs')
    (r : RestS) (h : r.closedAt n = true) :
    restDen { ρ with bound := zs } r = restDen { ρ with bound := zs' } r := by
  cases r with
  | none => rfl
  | name j => rfl
  | bvar d =>
    simp only [RestS.closedAt, decide_eq_true_eq] at h
    show (zs.getD d {}).rest = (zs'.getD d {}).rest
    rw [hz d h]

/-- Whether the regions of a list mention only so many families. -/
def heldClosedAt (n : Nat) (held : List (Val × HeldS)) : Bool :=
  held.all fun b => b.1.closedAt n && b.2.slots.all fun p => p.2.closedAt n

theorem heldDen_agree (ρ : Env) (n : Nat) (zs zs' : List Fam) (hz : Agree n zs zs')
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

mutual

/-- Whether what is known mentions only so many enclosing families. Code
wanting a family is one family further in. -/
def TyS.closedAt (n : Nat) : TyS → Bool
  | .ptr S _ _ => S.closedAt n
  | .nullable τ => τ.closedAt n
  | .orErr τ => τ.closedAt n
  | .code regs flags held known rest =>
    (regs.map (Val.closedAt (n + 1)) == allTrue) && flags.closedAt (n + 1) &&
      heldClosedAt (n + 1) held && known.closedAt (n + 1) && rest.closedAt (n + 1)
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

theorem TyS.den_agree (ρ : Env) (n : Nat) (zs zs' : List Fam) (hz : Agree n zs zs') :
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
  | .range _ _, _ => rfl
  | .code regs flags held known rest, h => by
    simp only [TyS.closedAt, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hr, hf⟩, hh⟩, hkn⟩, hrest⟩ := h
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
      rw [heldDen_agree ρ (n + 1) (z :: zs) (z :: zs') hz' held hh,
        RestS.den_agree ρ (n + 1) (z :: zs) (z :: zs') hz' rest hrest]
    · exact FactsS.den_agree ρ (n + 1) (z :: zs) (z :: zs') hz' known hkn

theorem ShapeS.den_agree (ρ : Env) (n : Nat) (zs zs' : List Fam) (hz : Agree n zs zs') :
    (S : ShapeS) → S.closedAt n = true → S.den { ρ with bound := zs } = S.den { ρ with bound := zs' }
  | .mk size vals, h => by
    simp only [ShapeS.den,
      ValsS.den_agree ρ n zs zs' hz vals (by simpa only [ShapeS.closedAt] using h)]

theorem ValsS.den_agree (ρ : Env) (n : Nat) (zs zs' : List Fam) (hz : Agree n zs zs') :
    (vs : ValsS) → vs.closedAt n = true →
    vs.den { ρ with bound := zs } = vs.den { ρ with bound := zs' }
  | .nil, _ => rfl
  | .cons o τ rest, h => by
    simp only [ValsS.closedAt, Bool.and_eq_true] at h
    simp only [ValsS.den, TyS.den_agree ρ n zs zs' hz τ h.1, ValsS.den_agree ρ n zs zs' hz rest h.2]

theorem FactsS.den_agree (ρ : Env) (n : Nat) (zs zs' : List Fam) (hz : Agree n zs zs') :
    (fs : FactsS) → fs.closedAt n = true →
    fs.den { ρ with bound := zs } = fs.den { ρ with bound := zs' }
  | .nil, _ => rfl
  | .cons v τ rest, h => by
    simp only [FactsS.closedAt, Bool.and_eq_true] at h
    simp only [FactsS.den, Val.den_agree ρ n zs zs' hz v h.1.1, TyS.den_agree ρ n zs zs' hz τ h.1.2,
      FactsS.den_agree ρ n zs zs' hz rest h.2]

end

/-- What mentions no family's values stands for the same under any stack. -/
theorem Val.den_bound (ρ : Env) (zs : List Fam) (a : Val) (h : a.closedAt 0 = true) :
    a.den { ρ with bound := zs } = a.den ρ :=
  Val.den_agree ρ 0 zs ρ.bound (fun _ hd => absurd hd (Nat.not_lt_zero _)) a h

theorem FlagsT.den_bound (ρ : Env) (zs : List Fam) (f : FlagsT) (h : f.closedAt 0 = true) :
    f.den { ρ with bound := zs } = f.den ρ :=
  FlagsT.den_agree ρ 0 zs ρ.bound (fun _ hd => absurd hd (Nat.not_lt_zero _)) f h

theorem TyS.den_bound (ρ : Env) (zs : List Fam) (τ : TyS) (h : τ.closedAt 0 = true) :
    τ.den { ρ with bound := zs } = τ.den ρ :=
  TyS.den_agree ρ 0 zs ρ.bound (fun _ hd => absurd hd (Nat.not_lt_zero _)) τ h

theorem RestS.den_bound (ρ : Env) (zs : List Fam) (r : RestS) (h : r.closedAt 0 = true) :
    restDen { ρ with bound := zs } r = restDen ρ r :=
  RestS.den_agree ρ 0 zs ρ.bound (fun _ hd => absurd hd (Nat.not_lt_zero _)) r h

theorem heldDen_bound (ρ : Env) (zs : List Fam) (held : List (Val × HeldS))
    (h : heldClosedAt 0 held = true) :
    (held.map fun b => (b.1.den { ρ with bound := zs }, b.2.den { ρ with bound := zs }))
      = held.map fun b => (b.1.den ρ, b.2.den ρ) :=
  heldDen_agree ρ 0 zs ρ.bound (fun _ hd => absurd hd (Nat.not_lt_zero _)) held h

end TypedAsm.U
