import TypedAsm.U.Find
import TypedAsm.U.Regard

/-!
# Whether one context may be regarded as another, computed

Two contexts over the same names: the second asks no more than the first
gives if each register holds the same value, the flags are the same, the
regions held are the same in some order, and each thing the second knows
follows from something the first knows of the same value. This is decided
on the terms; that it is right is proved once.
-/

namespace TypedAsm.U

open TypedAsm

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

/-- Whether two terms stand for the same value, as far as their being the
same term, or sums of the same terms and the same number, shows. -/
def Val.same (a b : Val) : Bool :=
  a == b || (a.summands.1 == b.summands.1 && a.summands.2 == b.summands.2)

theorem Val.same_den (ρ : Env) {a b : Val} (h : a.same b = true) : a.den ρ = b.den ρ := by
  unfold Val.same at h
  rcases Bool.or_eq_true _ _ |>.mp h with h | h
  · rw [beq_iff_eq.mp h]
  · rw [Bool.and_eq_true] at h
    rw [Val.summands_den ρ a, Val.summands_den ρ b, beq_iff_eq.mp h.1, beq_iff_eq.mp h.2]

def allRegs : List Reg :=
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

theorem mem_allRegs (r : Reg) : r ∈ allRegs := by
  cases r <;> decide

def slotsSame : List (Nat × Val) → List (Nat × Val) → Bool
  | [], [] => true
  | p :: ps, q :: qs => p.1 == q.1 && p.2.same q.2 && slotsSame ps qs
  | _, _ => false

theorem slotsSame_den (ρ : Env) : (ps qs : List (Nat × Val)) → slotsSame ps qs = true →
    (ps.map fun p => (p.1, p.2.den ρ)) = qs.map fun p => (p.1, p.2.den ρ)
  | [], [], _ => rfl
  | p :: ps, q :: qs, h => by
    simp only [slotsSame, Bool.and_eq_true, beq_iff_eq] at h
    simp only [List.map_cons, h.1.1, Val.same_den ρ h.1.2, slotsSame_den ρ ps qs h.2]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

/-- Whether two regions are the same: at the same address, of the same
size, holding the same values. -/
def regionSame (g d : Val × HeldS) : Bool :=
  g.1.same d.1 && g.2.size == d.2.size && slotsSame g.2.slots d.2.slots

def regionDen (ρ : Env) (b : Val × HeldS) : Region := (b.1.den ρ, b.2.den ρ)

theorem regionSame_den (ρ : Env) {g d : Val × HeldS} (h : regionSame g d = true) :
    regionDen ρ g = regionDen ρ d := by
  simp only [regionSame, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  show (g.1.den ρ, (⟨g.2.size, g.2.slots.map fun p => (p.1, p.2.den ρ)⟩ : Held))
    = (d.1.den ρ, ⟨d.2.size, d.2.slots.map fun p => (p.1, p.2.den ρ)⟩)
  rw [Val.same_den ρ h1, h2, slotsSame_den ρ _ _ h3]

/-- A list of regions less one that is the same as a given one. -/
def takeRegion (d : Val × HeldS) : List (Val × HeldS) → Option (List (Val × HeldS))
  | [] => none
  | g :: gs => if regionSame g d then some gs else (takeRegion d gs).map (g :: ·)

theorem takeRegion_perm (ρ : Env) (d : Val × HeldS) :
    (G G' : List (Val × HeldS)) → takeRegion d G = some G' →
    (regionDen ρ d :: G'.map (regionDen ρ)).Perm (G.map (regionDen ρ))
  | [], _, h => nomatch h
  | g :: gs, G', h => by
    unfold takeRegion at h
    split at h
    · next hs =>
      cases h
      rw [List.map_cons, regionSame_den ρ hs]
    · cases ht : takeRegion d gs with
      | none => rw [ht] at h; cases h
      | some G'' =>
        rw [ht] at h
        cases h
        have ih := takeRegion_perm ρ d gs G'' ht
        rw [List.map_cons, List.map_cons]
        exact (List.Perm.swap _ _ _).trans (ih.cons _)

/-- Whether two lists of regions are the same in some order. -/
def heldPerm : List (Val × HeldS) → List (Val × HeldS) → Bool
  | [], G => G.isEmpty
  | d :: ds, G =>
    match takeRegion d G with
    | some G' => heldPerm ds G'
    | none => false

theorem heldPerm_den (ρ : Env) : (D G : List (Val × HeldS)) → heldPerm D G = true →
    (D.map (regionDen ρ)).Perm (G.map (regionDen ρ))
  | [], G, h => by
    cases G with
    | nil => exact .nil
    | cons _ _ => cases h
  | d :: ds, G, h => by
    unfold heldPerm at h
    cases ht : takeRegion d G with
    | none => rw [ht] at h; cases h
    | some G' =>
      rw [ht] at h
      rw [List.map_cons]
      exact ((heldPerm_den ρ ds G' h).cons _).trans (takeRegion_perm ρ d G G' ht)

/-- Whether what is known one way is known another, read off the two. -/
def followsS (τ : TyS) : TyS → Bool
  | .any => true
  | .ptr S w off => τ == .ptr S w off || τ == .ptr S true off
  | .ref tag w off => τ == .ref tag w off || τ == .ref tag true off
  | .nullable υ =>
    τ == .nullable υ || followsS τ υ ||
      (match τ with
       | .nullable τ' => followsS τ' υ
       | _ => false)
  | .orErr υ =>
    τ == .orErr υ || followsS τ υ ||
      (match τ with
       | .orErr τ' => followsS τ' υ
       | _ => false)
  | .str more => τ == .str more || τ == .str true
  | .atom i => τ == .atom i

theorem followsS_sub (ρ : Env) (v : BitVec 64) :
    (υ τ : TyS) → followsS τ υ = true → Sub v (τ.den ρ) (υ.den ρ)
  | .any, τ, _ => .any _ _
  | .ptr S w off, τ, h => by
    simp only [followsS, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | rfl
    · exact .refl _ _
    · exact .readOnly _ _ _ _
  | .ref tag w off, τ, h => by
    simp only [followsS, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | rfl
    · exact .refl _ _
    · exact .refReadOnly _ _ _ _
  | .nullable υ, τ, h => by
    simp only [followsS, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with (rfl | h) | h
    · exact .refl _ _
    · exact .nullable (followsS_sub ρ v υ τ h)
    · cases τ with
      | nullable τ' => exact .nullableMono (followsS_sub ρ v υ τ' h)
      | _ => cases h
  | .orErr υ, τ, h => by
    simp only [followsS, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with (rfl | h) | h
    · exact .refl _ _
    · exact .orErr (followsS_sub ρ v υ τ h)
    · cases τ with
      | orErr τ' => exact .orErrMono (followsS_sub ρ v υ τ' h)
      | _ => cases h
  | .str more, τ, h => by
    simp only [followsS, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | rfl
    · exact .refl _ _
    · exact .strLess _ _
  | .atom i, τ, h => by
    simp only [followsS, beq_iff_eq] at h
    subst h
    exact .refl _ _

/-- Whether a thing known follows from one of a list, of the same value. -/
def factFrom (G : List (Val × TyS)) (f : Val × TyS) : Bool :=
  G.any fun g => g.1.same f.1 && followsS g.2 f.2

/-- **Whether the first context may be regarded as the second.** -/
def regardS (Γ Δ : CtxS) : Bool :=
  (allRegs.all fun r => (Γ.regs.get r).same (Δ.regs.get r)) && Γ.flags == Δ.flags &&
    heldPerm Δ.held Γ.held && Δ.known.all (factFrom Γ.known)

theorem regardS_sound (ρ : Env) {Γ Δ : CtxS} (h : regardS Γ Δ = true) :
    Regards fetch sys Ψ (Γ.den ρ) (Δ.den ρ) := by
  simp only [regardS, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hr, hf⟩, hh⟩, hk⟩ := h
  have e : Δ.den ρ
      = { ({ Γ.den ρ with known := (Δ.den ρ).known } : Ctx) with held := (Δ.den ρ).held } := by
    refine ctx_ext ?_ ?_ rfl rfl
    · funext r
      exact (Val.same_den ρ (hr r (mem_allRegs r))).symm
    · show Δ.flags.den ρ = Γ.flags.den ρ
      rw [hf]
  rw [e]
  refine (Regards.follows _ ?_).trans (Regards.perm ?_)
  · intro f hf'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf'
    have := hk g hg
    simp only [factFrom, List.any_eq_true, Bool.and_eq_true] at this
    obtain ⟨g₀, hg₀, hs, hfo⟩ := this
    refine ⟨g₀.2.den ρ, ?_, (followsS_sub ρ _ _ _ hfo).follows⟩
    show (g.1.den ρ, g₀.2.den ρ) ∈ Γ.known.map fun f => (f.1.den ρ, f.2.den ρ)
    rw [← Val.same_den ρ hs]
    exact List.mem_map.mpr ⟨g₀, hg₀, rfl⟩
  · exact heldPerm_den ρ Δ.held Γ.held hh

end TypedAsm.U
