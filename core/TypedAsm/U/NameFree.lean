import TypedAsm.U.Open

/-!
# What mentions no names

A family of contexts written for use anywhere mentions no names of any one
context: only the values, flags and rest the family ranges over. Such a
thing stands for the same in any two settings of the names, so long as the
families' values are the same and what is not written out as data is.
-/

namespace TypedAsm.U

open TypedAsm

mutual

/-- Whether a term mentions no name. -/
def Val.nameFree : Val → Bool
  | .lit _ => true
  | .var _ => false
  | .bvar _ _ => true
  | .add a b => a.nameFree && b.nameFree
  | .shl a _ => a.nameFree
  | .out _ _ a b c fl _ ea cell =>
    a.nameFree && b.nameFree && c.nameFree && fl.nameFree && ea.nameFree && cell.nameFree
  | .stored _ a b c fl _ ea cell =>
    a.nameFree && b.nameFree && c.nameFree && fl.nameFree && ea.nameFree && cell.nameFree
  | .goes _ a b c fl _ ea cell =>
    a.nameFree && b.nameFree && c.nameFree && fl.nameFree && ea.nameFree && cell.nameFree

def FlagsT.nameFree : FlagsT → Bool
  | .lit _ => true
  | .var _ => false
  | .bvar _ => true
  | .out _ a b c fl _ ea cell =>
    a.nameFree && b.nameFree && c.nameFree && fl.nameFree && ea.nameFree && cell.nameFree

end

/-- Two settings with the same families' values and the same knowledge not
written out. -/
structure Env.Same (ρ₁ ρ₂ : Env) : Prop where
  ty : ρ₁.ty = ρ₂.ty
  bound : ρ₁.bound = ρ₂.bound

theorem Env.Same.push {ρ₁ ρ₂ : Env} (h : ρ₁.Same ρ₂) (z : Fam) :
    Env.Same { ρ₁ with bound := z :: ρ₁.bound } { ρ₂ with bound := z :: ρ₂.bound } :=
  ⟨h.ty, by show z :: ρ₁.bound = z :: ρ₂.bound; rw [h.bound]⟩

mutual

theorem Val.den_nameFree {ρ₁ ρ₂ : Env} (hs : ρ₁.Same ρ₂) :
    (a : Val) → a.nameFree = true → a.den ρ₁ = a.den ρ₂
  | .lit _, _ => rfl
  | .var _, h => nomatch h
  | .bvar d i, _ => by
    show (ρ₁.bound.getD d {}).vals i = (ρ₂.bound.getD d {}).vals i
    rw [hs.bound]
  | .add a b, h => by
    simp only [Val.nameFree, Bool.and_eq_true] at h
    simp only [Val.den, Val.den_nameFree hs a h.1, Val.den_nameFree hs b h.2]
  | .shl a s, h => by
    simp only [Val.nameFree] at h
    simp only [Val.den, Val.den_nameFree hs a h]
  | .out i j a b c fl next ea cell, h => by
    simp only [Val.nameFree, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hf⟩, he⟩, hcell⟩ := h
    simp only [Val.den, Val.den_nameFree hs a ha, Val.den_nameFree hs b hb,
      Val.den_nameFree hs c hc, FlagsT.den_nameFree hs fl hf, Val.den_nameFree hs ea he,
      Val.den_nameFree hs cell hcell]
  | .stored i a b c fl next ea cell, h => by
    simp only [Val.nameFree, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hf⟩, he⟩, hcell⟩ := h
    simp only [Val.den, Val.den_nameFree hs a ha, Val.den_nameFree hs b hb,
      Val.den_nameFree hs c hc, FlagsT.den_nameFree hs fl hf, Val.den_nameFree hs ea he,
      Val.den_nameFree hs cell hcell]
  | .goes i a b c fl next ea cell, h => by
    simp only [Val.nameFree, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hf⟩, he⟩, hcell⟩ := h
    simp only [Val.den, Val.den_nameFree hs a ha, Val.den_nameFree hs b hb,
      Val.den_nameFree hs c hc, FlagsT.den_nameFree hs fl hf, Val.den_nameFree hs ea he,
      Val.den_nameFree hs cell hcell]

theorem FlagsT.den_nameFree {ρ₁ ρ₂ : Env} (hs : ρ₁.Same ρ₂) :
    (f : FlagsT) → f.nameFree = true → f.den ρ₁ = f.den ρ₂
  | .lit _, _ => rfl
  | .var _, h => nomatch h
  | .bvar d, _ => by
    show (ρ₁.bound.getD d {}).flags = (ρ₂.bound.getD d {}).flags
    rw [hs.bound]
  | .out i a b c fl next ea cell, h => by
    simp only [FlagsT.nameFree, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hf⟩, he⟩, hcell⟩ := h
    simp only [FlagsT.den, Val.den_nameFree hs a ha, Val.den_nameFree hs b hb,
      Val.den_nameFree hs c hc, FlagsT.den_nameFree hs fl hf, Val.den_nameFree hs ea he,
      Val.den_nameFree hs cell hcell]

end

/-- Whether whatever else is held is said without a name. -/
def RestS.nameFree : RestS → Bool
  | .name _ => false
  | _ => true

theorem RestS.den_nameFree {ρ₁ ρ₂ : Env} (hs : ρ₁.Same ρ₂) (r : RestS) (h : r.nameFree = true) :
    restDen ρ₁ r = restDen ρ₂ r := by
  cases r with
  | none => rfl
  | name j => cases h
  | bvar d =>
    show (ρ₁.bound.getD d {}).rest = (ρ₂.bound.getD d {}).rest
    rw [hs.bound]

def heldNameFree (held : List (Val × HeldS)) : Bool :=
  held.all fun b => b.1.nameFree && b.2.slots.all fun p => p.2.nameFree

theorem heldDen_nameFree {ρ₁ ρ₂ : Env} (hs : ρ₁.Same ρ₂) (held : List (Val × HeldS))
    (h : heldNameFree held = true) :
    (held.map fun b => (b.1.den ρ₁, b.2.den ρ₁)) = held.map fun b => (b.1.den ρ₂, b.2.den ρ₂) := by
  refine List.map_congr_left fun b hb => ?_
  have hbk := List.all_eq_true.mp h b hb
  rw [Bool.and_eq_true] at hbk
  show (b.1.den ρ₁, (⟨b.2.size, b.2.slots.map fun p => (p.1, p.2.den ρ₁)⟩ : Held))
    = (b.1.den ρ₂, ⟨b.2.size, b.2.slots.map fun p => (p.1, p.2.den ρ₂)⟩)
  rw [Val.den_nameFree hs _ hbk.1]
  congr 2
  exact List.map_congr_left fun p hp => by
    rw [Val.den_nameFree hs _ (List.all_eq_true.mp hbk.2 p hp)]

mutual

/-- Whether what is known mentions no name. Knowledge not written out is
none: it is the same in both settings. -/
def TyS.nameFree : TyS → Bool
  | .ptr S _ _ => S.nameFree
  | .nullable τ => τ.nameFree
  | .orErr τ => τ.nameFree
  | .code regs flags held known rest =>
    (regs.map Val.nameFree == allTrue) && flags.nameFree && heldNameFree held &&
      known.nameFree && rest.nameFree
  | _ => true

def ShapeS.nameFree : ShapeS → Bool
  | .mk _ vals => vals.nameFree

def ValsS.nameFree : ValsS → Bool
  | .nil => true
  | .cons _ τ rest => τ.nameFree && rest.nameFree

def FactsS.nameFree : FactsS → Bool
  | .nil => true
  | .cons v τ rest => v.nameFree && τ.nameFree && rest.nameFree

end

mutual

theorem TyS.den_nameFree {ρ₁ ρ₂ : Env} (hs : ρ₁.Same ρ₂) :
    (τ : TyS) → τ.nameFree = true → τ.den ρ₁ = τ.den ρ₂
  | .any, _ => rfl
  | .ptr S w off, h => by
    simp only [TyS.den, ShapeS.den_nameFree hs S (by simpa only [TyS.nameFree] using h)]
  | .ref _ _ _, _ => rfl
  | .nullable τ, h => by
    simp only [TyS.den, TyS.den_nameFree hs τ (by simpa only [TyS.nameFree] using h)]
  | .orErr τ, h => by
    simp only [TyS.den, TyS.den_nameFree hs τ (by simpa only [TyS.nameFree] using h)]
  | .str _, _ => rfl
  | .atom i, _ => by
    show ρ₁.ty i = ρ₂.ty i
    rw [hs.ty]
  | .code regs flags held known rest, h => by
    simp only [TyS.nameFree, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hr, hf⟩, hh⟩, hkn⟩, hrest⟩ := h
    show Ty.code _ = Ty.code _
    congr 1
    funext z
    have hs' := hs.push z
    refine ctx_ext ?_ ?_ ?_ ?_
    · funext r
      exact Val.den_nameFree hs' _ (Regs.all_of_map regs hr r)
    · exact FlagsT.den_nameFree hs' _ hf
    · show (held.map fun b => (b.1.den { ρ₁ with bound := z :: ρ₁.bound },
            b.2.den { ρ₁ with bound := z :: ρ₁.bound }))
          ++ restDen { ρ₁ with bound := z :: ρ₁.bound } rest
        = (held.map fun b => (b.1.den { ρ₂ with bound := z :: ρ₂.bound },
            b.2.den { ρ₂ with bound := z :: ρ₂.bound }))
          ++ restDen { ρ₂ with bound := z :: ρ₂.bound } rest
      rw [heldDen_nameFree hs' held hh, RestS.den_nameFree hs' rest hrest]
    · exact FactsS.den_nameFree hs' known hkn

theorem ShapeS.den_nameFree {ρ₁ ρ₂ : Env} (hs : ρ₁.Same ρ₂) :
    (S : ShapeS) → S.nameFree = true → S.den ρ₁ = S.den ρ₂
  | .mk size vals, h => by
    simp only [ShapeS.den, ValsS.den_nameFree hs vals (by simpa only [ShapeS.nameFree] using h)]

theorem ValsS.den_nameFree {ρ₁ ρ₂ : Env} (hs : ρ₁.Same ρ₂) :
    (vs : ValsS) → vs.nameFree = true → vs.den ρ₁ = vs.den ρ₂
  | .nil, _ => rfl
  | .cons o τ rest, h => by
    simp only [ValsS.nameFree, Bool.and_eq_true] at h
    simp only [ValsS.den, TyS.den_nameFree hs τ h.1, ValsS.den_nameFree hs rest h.2]

theorem FactsS.den_nameFree {ρ₁ ρ₂ : Env} (hs : ρ₁.Same ρ₂) :
    (fs : FactsS) → fs.nameFree = true → fs.den ρ₁ = fs.den ρ₂
  | .nil, _ => rfl
  | .cons v τ rest, h => by
    simp only [FactsS.nameFree, Bool.and_eq_true] at h
    simp only [FactsS.den, Val.den_nameFree hs v h.1.1, TyS.den_nameFree hs τ h.1.2,
      FactsS.den_nameFree hs rest h.2]

end

/-- Whether a context mentions no name. -/
def CtxS.nameFree (Γ : CtxS) : Bool :=
  (Γ.regs.map Val.nameFree == allTrue) && Γ.flags.nameFree && heldNameFree Γ.held &&
    (Γ.known.all fun f => f.1.nameFree && f.2.nameFree) && Γ.rest.nameFree

/-- **A context that mentions no name stands for the same in any two
settings with the same families' values.** -/
theorem CtxS.den_nameFree {ρ₁ ρ₂ : Env} (hs : ρ₁.Same ρ₂) (Γ : CtxS) (h : Γ.nameFree = true) :
    Γ.den ρ₁ = Γ.den ρ₂ := by
  simp only [CtxS.nameFree, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hr, hf⟩, hh⟩, hkn⟩, hrest⟩ := h
  refine ctx_ext ?_ ?_ ?_ ?_
  · funext r
    exact Val.den_nameFree hs _ (Regs.all_of_map Γ.regs hr r)
  · exact FlagsT.den_nameFree hs _ hf
  · show Γ.held.map _ ++ restDen ρ₁ Γ.rest = Γ.held.map _ ++ restDen ρ₂ Γ.rest
    rw [heldDen_nameFree hs Γ.held hh, RestS.den_nameFree hs Γ.rest hrest]
  · show Γ.known.map _ = Γ.known.map _
    refine List.map_congr_left fun f hf' => ?_
    show (f.1.den ρ₁, f.2.den ρ₁) = (f.1.den ρ₂, f.2.den ρ₂)
    rw [Val.den_nameFree hs _ (hkn f hf').1, TyS.den_nameFree hs _ (hkn f hf').2]

end TypedAsm.U
