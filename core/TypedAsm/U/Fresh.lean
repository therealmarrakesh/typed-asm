import TypedAsm.U.Find

/-!
# What a term stands for turns only on the names it mentions

Terms mention names: of values, of flags, and of whatever else is held.
What a term stands for is the same in any two settings of the names that
agree on those it mentions. That is one statement, `den_under`, of terms,
of what is known, and of contexts; and two things much used are cases of
it. Where a step learns of a value it cannot write as a term of what it
has, the value is given a name no term yet mentions: what the terms there
were stand for does not turn on what the new name stands for. And a family
of contexts written for use anywhere mentions no names at all: it stands
for the same in every setting.
-/

namespace TypedAsm.U

open TypedAsm

/-- The names with the `k`th given a value. -/
def Env.setVal (ρ : Env) (k : Nat) (x : BitVec 64) : Env :=
  { ρ with val := fun i => if i = k then x else ρ.val i }

theorem Env.setVal_get_lt (ρ : Env) (k : Nat) (x : BitVec 64) {i : Nat} (h : i < k) :
    (ρ.setVal k x).val i = ρ.val i := by
  show (if i = k then x else ρ.val i) = ρ.val i
  simp only [show i ≠ k by omega, ↓reduceIte]

theorem Env.setVal_get_self (ρ : Env) (k : Nat) (x : BitVec 64) : (ρ.setVal k x).val k = x := by
  show (if k = k then x else ρ.val k) = x
  simp only [↓reduceIte]

/-- Two settings that agree on every name below `k`, and on what is not a
name: the families' values, and knowledge not written out. -/
structure Env.SameBelow (k : Nat) (ρ₁ ρ₂ : Env) : Prop where
  val : ∀ i, i < k → ρ₁.val i = ρ₂.val i
  flags : ∀ i, i < k → ρ₁.flags i = ρ₂.flags i
  frame : ∀ i, i < k → ρ₁.frame i = ρ₂.frame i
  ty : ρ₁.ty = ρ₂.ty
  bound : ρ₁.bound = ρ₂.bound
  slot : ρ₁.slot = ρ₂.slot
  old : ρ₁.old = ρ₂.old

theorem Env.SameBelow.refl (k : Nat) (ρ : Env) : Env.SameBelow k ρ ρ :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Env.SameBelow.trans {k : Nat} {ρ₁ ρ₂ ρ₃ : Env} (h₁ : Env.SameBelow k ρ₁ ρ₂)
    (h₂ : Env.SameBelow k ρ₂ ρ₃) : Env.SameBelow k ρ₁ ρ₃ :=
  ⟨fun i hi => (h₁.val i hi).trans (h₂.val i hi), fun i hi => (h₁.flags i hi).trans (h₂.flags i hi),
    fun i hi => (h₁.frame i hi).trans (h₂.frame i hi), h₁.ty.trans h₂.ty, h₁.bound.trans h₂.bound,
    h₁.slot.trans h₂.slot, h₁.old.trans h₂.old⟩

theorem Env.SameBelow.mono {k j : Nat} {ρ₁ ρ₂ : Env} (h : Env.SameBelow k ρ₁ ρ₂) (hjk : j ≤ k) :
    Env.SameBelow j ρ₁ ρ₂ :=
  ⟨fun i hi => h.val i (Nat.lt_of_lt_of_le hi hjk), fun i hi => h.flags i (Nat.lt_of_lt_of_le hi hjk),
    fun i hi => h.frame i (Nat.lt_of_lt_of_le hi hjk), h.ty, h.bound, h.slot, h.old⟩

theorem Env.SameBelow.push {k : Nat} {ρ₁ ρ₂ : Env} (h : Env.SameBelow k ρ₁ ρ₂) (z : Fam) :
    Env.SameBelow k { ρ₁ with bound := z :: ρ₁.bound } { ρ₂ with bound := z :: ρ₂.bound } :=
  ⟨h.val, h.flags, h.frame, h.ty, by show z :: ρ₁.bound = z :: ρ₂.bound; rw [h.bound], h.slot,
    h.old⟩

theorem Env.SameBelow.setVal (ρ : Env) (k : Nat) (x : BitVec 64) :
    Env.SameBelow k (ρ.setVal k x) ρ :=
  ⟨fun _ hi => Env.setVal_get_lt ρ k x hi, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

mutual

/-- Whether a term mentions only names below `k`. -/
def Val.under (k : Nat) : Val → Bool
  | .lit _ => true
  | .var i => decide (i < k)
  | .bvar _ _ => true
  | .slot _ => true
  | .un _ a => a.under k
  | .bin _ a b => a.under k && b.under k
  | .tri _ a b c => a.under k && b.under k && c.under k
  | .fop _ fl a b => fl.under k && a.under k && b.under k

def FlagsT.under (k : Nat) : FlagsT → Bool
  | .lit _ => true
  | .var i => decide (i < k)
  | .bvar _ => true
  | .old => true
  | .src _ fl a b c => fl.under k && a.under k && b.under k && c.under k

end

mutual

/-- A term that mentions only names below `k` mentions only names below
any larger number. -/
theorem Val.under_mono {k k' : Nat} (hk : k ≤ k') : (a : Val) → a.under k = true → a.under k' = true
  | .lit _, _ => rfl
  | .var i, h => by
    simp only [Val.under, decide_eq_true_eq] at h ⊢
    omega
  | .bvar _ _, _ => rfl
  | .slot _, _ => rfl
  | .un _ a, h => by
    simp only [Val.under] at h ⊢
    exact Val.under_mono hk a h
  | .bin _ a b, h => by
    simp only [Val.under, Bool.and_eq_true] at h ⊢
    exact ⟨Val.under_mono hk a h.1, Val.under_mono hk b h.2⟩
  | .tri _ a b c, h => by
    simp only [Val.under, Bool.and_eq_true] at h ⊢
    exact ⟨⟨Val.under_mono hk a h.1.1, Val.under_mono hk b h.1.2⟩, Val.under_mono hk c h.2⟩
  | .fop _ fl a b, h => by
    simp only [Val.under, Bool.and_eq_true] at h ⊢
    exact ⟨⟨FlagsT.under_mono hk fl h.1.1, Val.under_mono hk a h.1.2⟩, Val.under_mono hk b h.2⟩

theorem FlagsT.under_mono {k k' : Nat} (hk : k ≤ k') :
    (f : FlagsT) → f.under k = true → f.under k' = true
  | .lit _, _ => rfl
  | .var i, h => by
    simp only [FlagsT.under, decide_eq_true_eq] at h ⊢
    omega
  | .bvar _, _ => rfl
  | .old, _ => rfl
  | .src _ fl a b c, h => by
    simp only [FlagsT.under, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨FlagsT.under_mono hk fl h.1.1.1, Val.under_mono hk a h.1.1.2⟩,
      Val.under_mono hk b h.1.2⟩, Val.under_mono hk c h.2⟩

end

mutual

/-- **A term that mentions only names below `k` stands for the same in any
two settings that agree below `k`.** -/
theorem Val.den_under {k : Nat} {ρ₁ ρ₂ : Env} (hs : Env.SameBelow k ρ₁ ρ₂) :
    (a : Val) → a.under k = true → a.den ρ₁ = a.den ρ₂
  | .lit _, _ => rfl
  | .var i, h => by
    simp only [Val.under, decide_eq_true_eq] at h
    exact hs.val i h
  | .bvar d i, _ => by
    show (ρ₁.bound.getD d {}).vals i = (ρ₂.bound.getD d {}).vals i
    rw [hs.bound]
  | .slot s, _ => by
    show ρ₁.slot s = ρ₂.slot s
    rw [hs.slot]
  | .un o a, h => by
    simp only [Val.under] at h
    simp only [Val.den, Val.den_under hs a h]
  | .bin o a b, h => by
    simp only [Val.under, Bool.and_eq_true] at h
    simp only [Val.den, Val.den_under hs a h.1, Val.den_under hs b h.2]
  | .tri o a b c, h => by
    simp only [Val.under, Bool.and_eq_true] at h
    simp only [Val.den, Val.den_under hs a h.1.1, Val.den_under hs b h.1.2, Val.den_under hs c h.2]
  | .fop o fl a b, h => by
    simp only [Val.under, Bool.and_eq_true] at h
    simp only [Val.den, FlagsT.den_under hs fl h.1.1, Val.den_under hs a h.1.2,
      Val.den_under hs b h.2]

theorem FlagsT.den_under {k : Nat} {ρ₁ ρ₂ : Env} (hs : Env.SameBelow k ρ₁ ρ₂) :
    (f : FlagsT) → f.under k = true → f.den ρ₁ = f.den ρ₂
  | .lit _, _ => rfl
  | .var i, h => by
    simp only [FlagsT.under, decide_eq_true_eq] at h
    exact hs.flags i h
  | .bvar d, _ => by
    show (ρ₁.bound.getD d {}).flags = (ρ₂.bound.getD d {}).flags
    rw [hs.bound]
  | .old, _ => by
    show ρ₁.old = ρ₂.old
    rw [hs.old]
  | .src o fl a b c, h => by
    simp only [FlagsT.under, Bool.and_eq_true] at h
    simp only [FlagsT.den, FlagsT.den_under hs fl h.1.1.1, Val.den_under hs a h.1.1.2,
      Val.den_under hs b h.1.2, Val.den_under hs c h.2]

end

/-- Every entry of a table of sixteen. -/
def allTrue : Regs Bool :=
  ⟨true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true⟩

theorem Regs.all_of_map {f : Val → Bool} (regs : Regs Val) (h : (regs.map f == allTrue) = true)
    (r : Reg) : f (regs.get r) = true := by
  have h1 : (regs.map f).get r = f (regs.get r) := Regs.get_map _ _ r
  rw [← h1, beq_iff_eq.mp h]
  cases r <;> rfl

theorem Regs.all_get {k : Nat} (regs : Regs Val)
    (h : (regs.map (·.under k) == allTrue) = true) (r : Reg) : (regs.get r).under k = true :=
  Regs.all_of_map regs h r

/-- Whether the regions of a list mention only names below `k`. -/
def heldUnder (k : Nat) (held : List (Val × HeldS)) : Bool :=
  held.all fun b => b.1.under k && b.2.size.under k &&
    b.2.slots.all fun p => p.1.under k && p.2.under k

theorem heldDen_under {k : Nat} {ρ₁ ρ₂ : Env} (hs : Env.SameBelow k ρ₁ ρ₂)
    (held : List (Val × HeldS)) (h : heldUnder k held = true) :
    (held.map fun b => (b.1.den ρ₁, b.2.den ρ₁)) = held.map fun b => (b.1.den ρ₂, b.2.den ρ₂) := by
  refine List.map_congr_left fun b hb => ?_
  have hbk := List.all_eq_true.mp h b hb
  simp only [Bool.and_eq_true] at hbk
  show (b.1.den ρ₁, (⟨(b.2.size.den ρ₁).toNat, b.2.slots.map (slotDen ρ₁)⟩ : Held))
    = (b.1.den ρ₂, ⟨(b.2.size.den ρ₂).toNat, b.2.slots.map (slotDen ρ₂)⟩)
  rw [Val.den_under hs _ hbk.1.1, Val.den_under hs _ hbk.1.2]
  congr 2
  exact List.map_congr_left fun p hp => by
    have hp' := List.all_eq_true.mp hbk.2 p hp
    rw [Bool.and_eq_true] at hp'
    show ((p.1.den ρ₁).toNat, p.2.den ρ₁) = ((p.1.den ρ₂).toNat, p.2.den ρ₂)
    rw [Val.den_under hs _ hp'.1, Val.den_under hs _ hp'.2]

/-- Whether whatever else is held is said with a name below `k`, or none. -/
def RestS.under (k : Nat) : RestS → Bool
  | .name j => decide (j < k)
  | _ => true

theorem restDen_under {k : Nat} {ρ₁ ρ₂ : Env} (hs : Env.SameBelow k ρ₁ ρ₂) (r : RestS)
    (h : r.under k = true) : restDen ρ₁ r = restDen ρ₂ r := by
  cases r with
  | none => rfl
  | name j =>
    simp only [RestS.under, decide_eq_true_eq] at h
    exact hs.frame j h
  | bvar d =>
    show (ρ₁.bound.getD d {}).rest = (ρ₂.bound.getD d {}).rest
    rw [hs.bound]

mutual

/-- Whether what is known mentions only names below `k`. Knowledge not
written out is none of them. -/
def TyS.under (k : Nat) : TyS → Bool
  | .ptr S _ _ => S.under k
  | .nullable τ => τ.under k
  | .orErr τ => τ.under k
  | .str c => c.under k
  | .arr c τ => c.under k && τ.under k
  | .upTo t _ => t.under k
  | .code regs flags held known rest =>
    (regs.map (·.under k) == allTrue) && flags.under k && heldUnder k held && known.under k &&
      rest.under k
  | _ => true

def ShapeS.under (k : Nat) : ShapeS → Bool
  | .mk _ vals => vals.under k

def ValsS.under (k : Nat) : ValsS → Bool
  | .nil => true
  | .cons _ τ rest => τ.under k && rest.under k

def FactsS.under (k : Nat) : FactsS → Bool
  | .nil => true
  | .cons v τ rest => v.under k && τ.under k && rest.under k

end

mutual

theorem TyS.den_under {k : Nat} {ρ₁ ρ₂ : Env} (hs : Env.SameBelow k ρ₁ ρ₂) :
    (τ : TyS) → τ.under k = true → τ.den ρ₁ = τ.den ρ₂
  | .any, _ => rfl
  | .ptr S w off, h => by
    simp only [TyS.den, ShapeS.den_under hs S (by simpa only [TyS.under] using h)]
  | .ref _ _ _, _ => rfl
  | .nullable τ, h => by
    simp only [TyS.den, TyS.den_under hs τ (by simpa only [TyS.under] using h)]
  | .orErr τ, h => by
    simp only [TyS.den, TyS.den_under hs τ (by simpa only [TyS.under] using h)]
  | .str c, h => by
    simp only [TyS.den, Val.den_under hs c (by simpa only [TyS.under] using h)]
  | .atom i, _ => by
    show ρ₁.ty i = ρ₂.ty i
    rw [hs.ty]
  | .range _ _, _ => rfl
  | .arr c τ, h => by
    simp only [TyS.under, Bool.and_eq_true] at h
    simp only [TyS.den, Val.den_under hs c h.1, TyS.den_under hs τ h.2]
  | .upTo t _, h => by
    simp only [TyS.den, Val.den_under hs t (by simpa only [TyS.under] using h)]
  | .code regs flags held known rest, h => by
    simp only [TyS.under, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hr, hf⟩, hh⟩, hkn⟩, hrest⟩ := h
    show Ty.code _ = Ty.code _
    congr 1
    funext z
    have hs' := hs.push z
    refine ctx_ext ?_ ?_ ?_ ?_
    · funext r
      exact Val.den_under hs' _ (Regs.all_get regs hr r)
    · exact FlagsT.den_under hs' _ hf
    · show (held.map fun b => (b.1.den { ρ₁ with bound := z :: ρ₁.bound },
            b.2.den { ρ₁ with bound := z :: ρ₁.bound }))
          ++ restDen { ρ₁ with bound := z :: ρ₁.bound } rest
        = (held.map fun b => (b.1.den { ρ₂ with bound := z :: ρ₂.bound },
            b.2.den { ρ₂ with bound := z :: ρ₂.bound }))
          ++ restDen { ρ₂ with bound := z :: ρ₂.bound } rest
      rw [heldDen_under hs' held hh, restDen_under hs' rest hrest]
    · exact FactsS.den_under hs' known hkn

theorem ShapeS.den_under {k : Nat} {ρ₁ ρ₂ : Env} (hs : Env.SameBelow k ρ₁ ρ₂) :
    (S : ShapeS) → S.under k = true → S.den ρ₁ = S.den ρ₂
  | .mk size vals, h => by
    simp only [ShapeS.den, ValsS.den_under hs vals (by simpa only [ShapeS.under] using h)]

theorem ValsS.den_under {k : Nat} {ρ₁ ρ₂ : Env} (hs : Env.SameBelow k ρ₁ ρ₂) :
    (vs : ValsS) → vs.under k = true → vs.den ρ₁ = vs.den ρ₂
  | .nil, _ => rfl
  | .cons o τ rest, h => by
    simp only [ValsS.under, Bool.and_eq_true] at h
    simp only [ValsS.den, TyS.den_under hs τ h.1, ValsS.den_under hs rest h.2]

theorem FactsS.den_under {k : Nat} {ρ₁ ρ₂ : Env} (hs : Env.SameBelow k ρ₁ ρ₂) :
    (fs : FactsS) → fs.under k = true → fs.den ρ₁ = fs.den ρ₂
  | .nil, _ => rfl
  | .cons v τ rest, h => by
    simp only [FactsS.under, Bool.and_eq_true] at h
    simp only [FactsS.den, Val.den_under hs v h.1.1, TyS.den_under hs τ h.1.2,
      FactsS.den_under hs rest h.2]

end

/-- Whether a context mentions only names below `k`. -/
def CtxS.under (k : Nat) (Γ : CtxS) : Bool :=
  (Γ.regs.map (·.under k) == allTrue) && Γ.flags.under k && heldUnder k Γ.held &&
  (Γ.known.all fun f => f.1.under k && f.2.under k) && Γ.rest.under k

/-- **A context that mentions only names below `k` stands for the same in
any two settings that agree below `k`.** -/
theorem CtxS.den_under {k : Nat} {ρ₁ ρ₂ : Env} (hs : Env.SameBelow k ρ₁ ρ₂) (Γ : CtxS)
    (h : Γ.under k = true) : Γ.den ρ₁ = Γ.den ρ₂ := by
  simp only [CtxS.under, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hr, hf⟩, hh⟩, hkn⟩, hrest⟩ := h
  refine ctx_ext ?_ ?_ ?_ ?_
  · funext r
    exact Val.den_under hs _ (Regs.all_get Γ.regs hr r)
  · exact FlagsT.den_under hs _ hf
  · show Γ.held.map _ ++ restDen ρ₁ Γ.rest = Γ.held.map _ ++ restDen ρ₂ Γ.rest
    rw [heldDen_under hs Γ.held hh, restDen_under hs Γ.rest hrest]
  · show Γ.known.map _ = Γ.known.map _
    refine List.map_congr_left fun f hf' => ?_
    show (f.1.den ρ₁, f.2.den ρ₁) = (f.1.den ρ₂, f.2.den ρ₂)
    rw [Val.den_under hs _ (hkn f hf').1, TyS.den_under hs _ (hkn f hf').2]

/-! ## The case of one name more -/

theorem Val.den_setVal (ρ : Env) (k : Nat) (x : BitVec 64) (a : Val) (h : a.under k = true) :
    a.den (ρ.setVal k x) = a.den ρ :=
  Val.den_under (Env.SameBelow.setVal ρ k x) a h

theorem FlagsT.den_setVal (ρ : Env) (k : Nat) (x : BitVec 64) (f : FlagsT)
    (h : f.under k = true) : f.den (ρ.setVal k x) = f.den ρ :=
  FlagsT.den_under (Env.SameBelow.setVal ρ k x) f h

theorem TyS.den_setVal (ρ : Env) (k : Nat) (x : BitVec 64) (τ : TyS) (h : τ.under k = true) :
    τ.den (ρ.setVal k x) = τ.den ρ :=
  TyS.den_under (Env.SameBelow.setVal ρ k x) τ h

theorem ShapeS.den_setVal (ρ : Env) (k : Nat) (x : BitVec 64) (S : ShapeS)
    (h : S.under k = true) : S.den (ρ.setVal k x) = S.den ρ :=
  ShapeS.den_under (Env.SameBelow.setVal ρ k x) S h

theorem CtxS.den_setVal (ρ : Env) (k : Nat) (x : BitVec 64) (Γ : CtxS) (h : Γ.under k = true) :
    Γ.den (ρ.setVal k x) = Γ.den ρ :=
  CtxS.den_under (Env.SameBelow.setVal ρ k x) Γ h

end TypedAsm.U
