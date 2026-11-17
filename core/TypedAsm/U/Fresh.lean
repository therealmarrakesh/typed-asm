import TypedAsm.U.Find

/-!
# Names not yet used

Where a step learns of a value it cannot write as a term of what it has,
bytes read whose value the context does not say, the value is given a name
no term yet mentions. What the terms there were stand for does not turn on
what the new name stands for; that is what "not yet mentioned" buys.
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

mutual

/-- Whether a term mentions only names below `k`. -/
def Val.under (k : Nat) : Val → Bool
  | .lit _ => true
  | .var i => decide (i < k)
  | .bvar _ _ => true
  | .add a b => a.under k && b.under k
  | .shl a _ => a.under k
  | .out _ _ a b c fl _ ea cell =>
    a.under k && b.under k && c.under k && fl.under k && ea.under k && cell.under k
  | .stored _ a b c fl _ ea cell =>
    a.under k && b.under k && c.under k && fl.under k && ea.under k && cell.under k
  | .goes _ a b c fl _ ea cell =>
    a.under k && b.under k && c.under k && fl.under k && ea.under k && cell.under k

def FlagsT.under (k : Nat) : FlagsT → Bool
  | .lit _ => true
  | .var _ => true
  | .bvar _ => true
  | .out _ a b c fl _ ea cell =>
    a.under k && b.under k && c.under k && fl.under k && ea.under k && cell.under k

end

mutual

/-- A term that mentions only names below `k` stands for what it did,
whatever the `k`th is given. -/
theorem Val.den_setVal (ρ : Env) (k : Nat) (x : BitVec 64) :
    (a : Val) → a.under k = true → a.den (ρ.setVal k x) = a.den ρ
  | .lit _, _ => rfl
  | .bvar _ _, _ => rfl
  | .var i, h => by
    simp only [Val.under, decide_eq_true_eq] at h
    exact Env.setVal_get_lt ρ k x h
  | .add a b, h => by
    simp only [Val.under, Bool.and_eq_true] at h
    simp only [Val.den, Val.den_setVal ρ k x a h.1, Val.den_setVal ρ k x b h.2]
  | .shl a s, h => by
    simp only [Val.under] at h
    simp only [Val.den, Val.den_setVal ρ k x a h]
  | .out i j a b c fl next ea cell, h => by
    simp only [Val.under, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hf⟩, he⟩, hcell⟩ := h
    simp only [Val.den, Val.den_setVal ρ k x a ha, Val.den_setVal ρ k x b hb,
      Val.den_setVal ρ k x c hc, FlagsT.den_setVal ρ k x fl hf, Val.den_setVal ρ k x ea he,
      Val.den_setVal ρ k x cell hcell]
  | .stored i a b c fl next ea cell, h => by
    simp only [Val.under, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hf⟩, he⟩, hcell⟩ := h
    simp only [Val.den, Val.den_setVal ρ k x a ha, Val.den_setVal ρ k x b hb,
      Val.den_setVal ρ k x c hc, FlagsT.den_setVal ρ k x fl hf, Val.den_setVal ρ k x ea he,
      Val.den_setVal ρ k x cell hcell]
  | .goes i a b c fl next ea cell, h => by
    simp only [Val.under, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hf⟩, he⟩, hcell⟩ := h
    simp only [Val.den, Val.den_setVal ρ k x a ha, Val.den_setVal ρ k x b hb,
      Val.den_setVal ρ k x c hc, FlagsT.den_setVal ρ k x fl hf, Val.den_setVal ρ k x ea he,
      Val.den_setVal ρ k x cell hcell]

theorem FlagsT.den_setVal (ρ : Env) (k : Nat) (x : BitVec 64) :
    (f : FlagsT) → f.under k = true → f.den (ρ.setVal k x) = f.den ρ
  | .lit _, _ => rfl
  | .var _, _ => rfl
  | .bvar _, _ => rfl
  | .out i a b c fl next ea cell, h => by
    simp only [FlagsT.under, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hf⟩, he⟩, hcell⟩ := h
    simp only [FlagsT.den, Val.den_setVal ρ k x a ha, Val.den_setVal ρ k x b hb,
      Val.den_setVal ρ k x c hc, FlagsT.den_setVal ρ k x fl hf, Val.den_setVal ρ k x ea he,
      Val.den_setVal ρ k x cell hcell]

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
  | .add a b, h => by
    simp only [Val.under, Bool.and_eq_true] at h ⊢
    exact ⟨Val.under_mono hk a h.1, Val.under_mono hk b h.2⟩
  | .shl a _, h => by
    simp only [Val.under] at h ⊢
    exact Val.under_mono hk a h
  | .out _ _ a b c fl _ ea cell, h => by
    simp only [Val.under, Bool.and_eq_true] at h ⊢
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hf⟩, he⟩, hcell⟩ := h
    exact ⟨⟨⟨⟨⟨Val.under_mono hk a ha, Val.under_mono hk b hb⟩, Val.under_mono hk c hc⟩,
      FlagsT.under_mono hk fl hf⟩, Val.under_mono hk ea he⟩, Val.under_mono hk cell hcell⟩
  | .stored _ a b c fl _ ea cell, h => by
    simp only [Val.under, Bool.and_eq_true] at h ⊢
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hf⟩, he⟩, hcell⟩ := h
    exact ⟨⟨⟨⟨⟨Val.under_mono hk a ha, Val.under_mono hk b hb⟩, Val.under_mono hk c hc⟩,
      FlagsT.under_mono hk fl hf⟩, Val.under_mono hk ea he⟩, Val.under_mono hk cell hcell⟩
  | .goes _ a b c fl _ ea cell, h => by
    simp only [Val.under, Bool.and_eq_true] at h ⊢
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hf⟩, he⟩, hcell⟩ := h
    exact ⟨⟨⟨⟨⟨Val.under_mono hk a ha, Val.under_mono hk b hb⟩, Val.under_mono hk c hc⟩,
      FlagsT.under_mono hk fl hf⟩, Val.under_mono hk ea he⟩, Val.under_mono hk cell hcell⟩

theorem FlagsT.under_mono {k k' : Nat} (hk : k ≤ k') :
    (f : FlagsT) → f.under k = true → f.under k' = true
  | .lit _, _ => rfl
  | .var _, _ => rfl
  | .bvar _, _ => rfl
  | .out _ a b c fl _ ea cell, h => by
    simp only [FlagsT.under, Bool.and_eq_true] at h ⊢
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hf⟩, he⟩, hcell⟩ := h
    exact ⟨⟨⟨⟨⟨Val.under_mono hk a ha, Val.under_mono hk b hb⟩, Val.under_mono hk c hc⟩,
      FlagsT.under_mono hk fl hf⟩, Val.under_mono hk ea he⟩, Val.under_mono hk cell hcell⟩

end

/-- Every entry of a table of sixteen. -/
def allTrue : Regs Bool :=
  ⟨true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true⟩

theorem Regs.all_get {k : Nat} (regs : Regs Val)
    (h : (regs.map (·.under k) == allTrue) = true) (r : Reg) : (regs.get r).under k = true := by
  have h1 : (regs.map (·.under k)).get r = (regs.get r).under k := Regs.get_map _ _ r
  rw [← h1, beq_iff_eq.mp h]
  cases r <;> rfl

/-- Whether the regions of a list mention only names below `k`. -/
def heldUnder (k : Nat) (held : List (Val × HeldS)) : Bool :=
  held.all fun b => b.1.under k && b.2.slots.all fun p => p.2.under k

theorem heldDen_setVal (ρ : Env) (k : Nat) (x : BitVec 64) (held : List (Val × HeldS))
    (h : heldUnder k held = true) :
    (held.map fun b => (b.1.den (ρ.setVal k x), b.2.den (ρ.setVal k x)))
      = held.map fun b => (b.1.den ρ, b.2.den ρ) := by
  refine List.map_congr_left fun b hb => ?_
  have hbk := List.all_eq_true.mp h b hb
  rw [Bool.and_eq_true] at hbk
  show (b.1.den _, (⟨b.2.size, b.2.slots.map fun p => (p.1, p.2.den (ρ.setVal k x))⟩ : Held))
    = (b.1.den ρ, ⟨b.2.size, b.2.slots.map fun p => (p.1, p.2.den ρ)⟩)
  rw [Val.den_setVal ρ k x _ hbk.1]
  congr 2
  exact List.map_congr_left fun p hp => by
    rw [Val.den_setVal ρ k x _ (List.all_eq_true.mp hbk.2 p hp)]

theorem restDen_setVal (ρ : Env) (k : Nat) (x : BitVec 64) (rest : RestS) :
    restDen (ρ.setVal k x) rest = restDen ρ rest := by
  cases rest <;> rfl

mutual

/-- Whether what is known mentions only names below `k`. -/
def TyS.under (k : Nat) : TyS → Bool
  | .ptr S _ _ => S.under k
  | .nullable τ => τ.under k
  | .orErr τ => τ.under k
  | .code regs flags held known _ =>
    (regs.map (·.under k) == allTrue) && flags.under k && heldUnder k held && known.under k
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

/-- What is known, mentioning only names below `k`, stands for the same
whatever the `k`th is given. -/
theorem TyS.den_setVal (ρ : Env) (k : Nat) (x : BitVec 64) :
    (τ : TyS) → τ.under k = true → τ.den (ρ.setVal k x) = τ.den ρ
  | .any, _ => rfl
  | .ptr S w off, h => by
    simp only [TyS.den, ShapeS.den_setVal ρ k x S (by simpa only [TyS.under] using h)]
  | .ref _ _ _, _ => rfl
  | .nullable τ, h => by
    simp only [TyS.den, TyS.den_setVal ρ k x τ (by simpa only [TyS.under] using h)]
  | .orErr τ, h => by
    simp only [TyS.den, TyS.den_setVal ρ k x τ (by simpa only [TyS.under] using h)]
  | .str _, _ => rfl
  | .atom _, _ => rfl
  | .code regs flags held known rest, h => by
    simp only [TyS.under, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hr, hf⟩, hh⟩, hkn⟩ := h
    show Ty.code _ = Ty.code _
    congr 1
    funext z
    have e : ({ ρ.setVal k x with bound := z :: (ρ.setVal k x).bound } : Env) = ({ ρ with bound := z :: ρ.bound } : Env).setVal k x :=
      rfl
    have h1 : (fun r => (regs.get r).den { ρ.setVal k x with bound := z :: (ρ.setVal k x).bound })
        = fun r => (regs.get r).den { ρ with bound := z :: ρ.bound } := by
      funext r
      rw [e]
      exact Val.den_setVal _ k x _ (Regs.all_get regs hr r)
    have h2 : flags.den { ρ.setVal k x with bound := z :: (ρ.setVal k x).bound } = flags.den { ρ with bound := z :: ρ.bound } := by
      rw [e]
      exact FlagsT.den_setVal _ k x _ hf
    have h3 : (held.map fun b => (b.1.den { ρ.setVal k x with bound := z :: (ρ.setVal k x).bound },
          b.2.den { ρ.setVal k x with bound := z :: (ρ.setVal k x).bound })) ++ restDen { ρ.setVal k x with bound := z :: (ρ.setVal k x).bound } rest
        = (held.map fun b => (b.1.den { ρ with bound := z :: ρ.bound }, b.2.den { ρ with bound := z :: ρ.bound }))
          ++ restDen { ρ with bound := z :: ρ.bound } rest := by
      rw [e, heldDen_setVal _ k x held hh, restDen_setVal]
    have h4 : known.den { ρ.setVal k x with bound := z :: (ρ.setVal k x).bound } = known.den { ρ with bound := z :: ρ.bound } := by
      rw [e]
      exact FactsS.den_setVal _ k x known hkn
    show CtxOf.mk _ _ _ _ = CtxOf.mk _ _ _ _
    rw [h1, h2, h3, h4]

theorem ShapeS.den_setVal (ρ : Env) (k : Nat) (x : BitVec 64) :
    (S : ShapeS) → S.under k = true → S.den (ρ.setVal k x) = S.den ρ
  | .mk size vals, h => by
    simp only [ShapeS.den, ValsS.den_setVal ρ k x vals (by simpa only [ShapeS.under] using h)]

theorem ValsS.den_setVal (ρ : Env) (k : Nat) (x : BitVec 64) :
    (vs : ValsS) → vs.under k = true → vs.den (ρ.setVal k x) = vs.den ρ
  | .nil, _ => rfl
  | .cons o τ rest, h => by
    simp only [ValsS.under, Bool.and_eq_true] at h
    simp only [ValsS.den, TyS.den_setVal ρ k x τ h.1, ValsS.den_setVal ρ k x rest h.2]

theorem FactsS.den_setVal (ρ : Env) (k : Nat) (x : BitVec 64) :
    (fs : FactsS) → fs.under k = true → fs.den (ρ.setVal k x) = fs.den ρ
  | .nil, _ => rfl
  | .cons v τ rest, h => by
    simp only [FactsS.under, Bool.and_eq_true] at h
    simp only [FactsS.den, Val.den_setVal ρ k x v h.1.1, TyS.den_setVal ρ k x τ h.1.2,
      FactsS.den_setVal ρ k x rest h.2]

end

/-- Whether a context mentions only names below `k`. -/
def CtxS.under (k : Nat) (Γ : CtxS) : Bool :=
  (Γ.regs.map (·.under k) == allTrue) && Γ.flags.under k && heldUnder k Γ.held &&
  Γ.known.all fun f => f.1.under k && f.2.under k

theorem CtxS.den_setVal (ρ : Env) (k : Nat) (x : BitVec 64) (Γ : CtxS) (h : Γ.under k = true) :
    Γ.den (ρ.setVal k x) = Γ.den ρ := by
  simp only [CtxS.under, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨hr, hf⟩, hh⟩, hkn⟩ := h
  refine ctx_ext ?_ ?_ ?_ ?_
  · funext r
    exact Val.den_setVal ρ k x _ (Regs.all_get Γ.regs hr r)
  · exact FlagsT.den_setVal ρ k x _ hf
  · show Γ.held.map _ ++ restDen (ρ.setVal k x) Γ.rest = Γ.held.map _ ++ restDen ρ Γ.rest
    rw [heldDen_setVal ρ k x Γ.held hh, restDen_setVal]
  · show Γ.known.map _ = Γ.known.map _
    refine List.map_congr_left fun f hf' => ?_
    show (f.1.den _, f.2.den _) = (f.1.den ρ, f.2.den ρ)
    rw [Val.den_setVal ρ k x _ (hkn f hf').1, TyS.den_setVal ρ k x _ (hkn f hf').2]

end TypedAsm.U
