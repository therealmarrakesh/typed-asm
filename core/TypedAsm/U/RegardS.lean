import TypedAsm.U.Find
import TypedAsm.U.Regard

/-!
# Whether one context may be regarded as another, computed

Two contexts over the same names: the second asks no more than the first
gives if each register holds the same value, the flags are the same, the
regions held are the same in some order, each saying no more of what it
holds, and each thing the second knows
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

/-- Whether each value the second list says is there, the first says too. -/
def slotsLess (gs ds : List (Nat × Val)) : Bool :=
  ds.all fun d => gs.any fun g => g.1 == d.1 && g.2.same d.2

/-- Whether the second region says no more than the first: at the same
address, of the same size, each value it says is there said by the first. -/
def regionLess (g d : Val × HeldS) : Bool :=
  g.1.same d.1 && g.2.size == d.2.size && slotsLess g.2.slots d.2.slots

def regionDen (ρ : Env) (b : Val × HeldS) : Region := (b.1.den ρ, b.2.den ρ)

theorem regionLess_den (ρ : Env) {g d : Val × HeldS} (h : regionLess g d = true) :
    Region.Less (regionDen ρ d) (regionDen ρ g) := by
  simp only [regionLess, slotsLess, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.any_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨(Val.same_den ρ h1).symm, h2.symm, ?_⟩
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  obtain ⟨q', hq', ho, hv⟩ := h3 q hq
  refine List.mem_map.mpr ⟨q', hq', ?_⟩
  show (q'.1, q'.2.den ρ) = (q.1, q.2.den ρ)
  rw [ho, Val.same_den ρ hv]

/-- A list of regions less one that says no less than a given one. -/
def takeRegion (d : Val × HeldS) : List (Val × HeldS) → Option (List (Val × HeldS))
  | [] => none
  | g :: gs => if regionLess g d then some gs else (takeRegion d gs).map (g :: ·)

theorem takeRegion_perm (ρ : Env) (d : Val × HeldS) :
    (G G' : List (Val × HeldS)) → takeRegion d G = some G' →
    ∃ g, Region.Less (regionDen ρ d) g ∧ (g :: G'.map (regionDen ρ)).Perm (G.map (regionDen ρ))
  | [], _, h => nomatch h
  | g :: gs, G', h => by
    unfold takeRegion at h
    split at h
    · next hs =>
      cases h
      exact ⟨_, regionLess_den ρ hs, .refl _⟩
    · cases ht : takeRegion d gs with
      | none => rw [ht] at h; cases h
      | some G'' =>
        rw [ht] at h
        cases h
        obtain ⟨g', hl, ih⟩ := takeRegion_perm ρ d gs G'' ht
        refine ⟨g', hl, ?_⟩
        rw [List.map_cons, List.map_cons]
        exact (List.Perm.swap _ _ _).trans (ih.cons _)

/-- Whether the first list of regions is the second in some order, each
saying no more. -/
def heldPerm : List (Val × HeldS) → List (Val × HeldS) → Bool
  | [], G => G.isEmpty
  | d :: ds, G =>
    match takeRegion d G with
    | some G' => heldPerm ds G'
    | none => false

theorem heldPerm_den (ρ : Env) : (D G : List (Val × HeldS)) → heldPerm D G = true →
    ∃ M, M.Perm (G.map (regionDen ρ)) ∧ LessAll (D.map (regionDen ρ)) M
  | [], G, h => by
    cases G with
    | nil => exact ⟨[], .nil, .nil⟩
    | cons _ _ => cases h
  | d :: ds, G, h => by
    unfold heldPerm at h
    cases ht : takeRegion d G with
    | none => rw [ht] at h; cases h
    | some G' =>
      rw [ht] at h
      obtain ⟨g, hl, hp⟩ := takeRegion_perm ρ d G G' ht
      obtain ⟨M, hM, hF⟩ := heldPerm_den ρ ds G' h
      exact ⟨g :: M, (hM.cons g).trans hp, .cons hl hF⟩

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
  obtain ⟨M, hM, hF⟩ := heldPerm_den ρ Δ.held Γ.held hh
  have e : Δ.den ρ
      = { ({ ({ Γ.den ρ with known := (Δ.den ρ).known } : Ctx) with held := M } : Ctx)
          with held := (Δ.den ρ).held } := by
    refine ctx_ext ?_ ?_ rfl rfl
    · funext r
      exact (Val.same_den ρ (hr r (mem_allRegs r))).symm
    · show Δ.flags.den ρ = Γ.flags.den ρ
      rw [hf]
  rw [e]
  refine ((Regards.follows _ ?_).trans (Regards.perm hM)).trans (Regards.forget hF)
  intro f hf'
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf'
  have := hk g hg
  simp only [factFrom, List.any_eq_true, Bool.and_eq_true] at this
  obtain ⟨g₀, hg₀, hs, hfo⟩ := this
  refine ⟨g₀.2.den ρ, ?_, (followsS_sub ρ _ _ _ hfo).follows⟩
  show (g.1.den ρ, g₀.2.den ρ) ∈ Γ.known.map fun f => (f.1.den ρ, f.2.den ρ)
  rw [← Val.same_den ρ hs]
  exact List.mem_map.mpr ⟨g₀, hg₀, rfl⟩

end TypedAsm.U
