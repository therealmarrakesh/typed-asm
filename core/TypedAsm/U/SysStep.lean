import TypedAsm.U.Step
import TypedAsm.U.RegardS
import TypedAsm.U.Unmap

/-!
# System calls, as steps on terms

Where the call number is a number written out, what the call does is read
from the system's description, and the context it returns in is given: one
function for each of the few things a call may do, none for any one call.
-/

namespace TypedAsm.U

open TypedAsm

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

/-- The context a call returns in, as terms: `rax` holds the term for what
was handed back, `rcx` the address after the call, `r11` zero; and the flags
are undefined. -/
def CtxS.afterSys (Γ : CtxS) (v : Val) (next : BitVec 64) : CtxS :=
  { Γ with
    regs := ((Γ.regs.set .rax v).set .rcx (.lit next)).set .r11 (.lit 0)
    flags := .lit Flags.unknown }

theorem CtxS.afterSys_den (ρ : Env) (Γ : CtxS) (v : Val) (next : BitVec 64) :
    (Γ.afterSys v next).den ρ = (Γ.den ρ).afterSys (v.den ρ) next := by
  refine ctx_ext ?_ rfl rfl rfl
  funext r
  cases r <;> rfl

/-- **A call that does nothing to the program, as a step on terms**: where
the call number is written out and is such a call's, the context it returns
in, with the name `k` for what it hands back. -/
def sysWorld (Γ : CtxS) (k : Nat) (next : BitVec 64) : Option CtxS :=
  match Γ.regs.rax.lit? with
  | some nr =>
    match linuxKind nr with
    | some .world => some (Γ.afterSys (.var k) next)
    | _ => none
  | none => none

theorem sysWorld_sound {D : SysDesc} (hD : Describes sys D) (hkind : D.kind = linuxKind)
    (hpre : ∀ s, D.pre s) {ρ : Env} {Γ Γ' : CtxS} {k : Nat} {next : BitVec 64}
    (h : sysWorld Γ k next = some Γ') (hu : Γ.under k = true) :
    Steps fetch sys Ψ .syscall next (Γ.den ρ) fun t Δ =>
      ∃ x, t = next ∧ Δ = Γ'.den (ρ.setVal k x) := by
  unfold sysWorld at h
  split at h
  · next nr hnr =>
    split at h
    · next hk =>
      cases h
      have hrax : (Γ.den ρ).val .rax = nr := Val.lit?_den hnr
      refine Steps.mono (Steps.world hD (by rw [hkind, hrax]; exact hk)
        (fun _ _ _ _ s _ _ => hpre s)) ?_
      rintro t Δ ⟨rfl, x, rfl⟩
      refine ⟨x, rfl, ?_⟩
      rw [CtxS.afterSys_den, CtxS.den_setVal ρ k x Γ hu]
      show _ = CtxOf.afterSys (Γ.den ρ) ((ρ.setVal k x).val k) t
      rw [Env.setVal_get_self]
    · cases h
  · cases h

/-- Whether the call is one that ends the program: its number written out,
and such a call's. -/
def sysEnds (Γ : CtxS) : Bool :=
  match Γ.regs.rax.lit? with
  | some nr =>
    match linuxKind nr with
    | some .ends => true
    | _ => false
  | none => false

theorem sysEnds_sound {D : SysDesc} (hD : Describes sys D) (hkind : D.kind = linuxKind)
    (hpre : ∀ s, D.pre s) {ρ : Env} {Γ : CtxS} (h : sysEnds Γ = true) {a len : BitVec 64}
    (hf : fetch a = some (.syscall, len)) (n : Nat) : Ok fetch sys Ψ n a (Γ.den ρ) := by
  unfold sysEnds at h
  split at h
  · next nr hnr =>
    split at h
    · next hk =>
      have hrax : (Γ.den ρ).val .rax = nr := Val.lit?_den hnr
      exact Ok.ends hD hf (by rw [hkind, hrax]; exact hk) (fun _ _ _ _ s _ _ => hpre s)
    · cases h
  · cases h

/-! ## Calls with two outcomes -/

/-- **A call for fresh memory, as a step on terms**: where the call number
and the length are written out and no address is asked for, the two
contexts it may return in, with the name `k` for what it hands back: one in
which that is an error number and nothing more is held, and one in which it
is the address of so many bytes, now held. With them, the size. -/
def sysMap (Γ : CtxS) (k : Nat) (next : BitVec 64) : Option (CtxS × CtxS × Nat) :=
  match Γ.regs.rax.lit?, Γ.regs.rdi.lit?, Γ.regs.rsi.lit? with
  | some nr, some di, some len =>
    match linuxKind nr with
    | some .map =>
      if di = 0 then
        some (Γ.afterSys (.var k) next,
          CtxS.afterSys { Γ with held := (.var k, ⟨pages len, []⟩) :: Γ.held } (.var k) next,
          pages len)
      else none
    | _ => none
  | _, _, _ => none

theorem sysMap_sound {D : SysDesc} (hD : Describes sys D) (hkind : D.kind = linuxKind)
    (hpre : ∀ s, D.pre s) {ρ : Env} {Γ Γe Γo : CtxS} {sz k : Nat} {next : BitVec 64}
    (h : sysMap Γ k next = some (Γe, Γo, sz)) (hu : Γ.under k = true) :
    Steps fetch sys Ψ .syscall next (Γ.den ρ) fun t Δ =>
      ∃ x, t = next ∧ ((SysErr x ∧ Δ = Γe.den (ρ.setVal k x)) ∨
        (x.toNat + sz ≤ addrTop ∧ Δ = Γo.den (ρ.setVal k x))) := by
  unfold sysMap at h
  split at h
  · next nr di len hnr hdi hlen =>
    split at h
    · next hk =>
      split at h
      · next hd0 =>
        cases h
        have hrax : (Γ.den ρ).val .rax = nr := Val.lit?_den hnr
        have hrdi : (Γ.den ρ).val .rdi = 0 := by rw [← hd0]; exact Val.lit?_den hdi
        have hrsi : (Γ.den ρ).val .rsi = len := Val.lit?_den hlen
        refine Steps.mono (Steps.map hD (by rw [hkind, hrax]; exact hk) hrdi
          (fun _ _ _ _ s _ _ => hpre s)) ?_
        rintro t Δ ⟨rfl, x, hcase⟩
        have hΓ : Γ.den (ρ.setVal k x) = Γ.den ρ := CtxS.den_setVal ρ k x Γ hu
        refine ⟨x, rfl, ?_⟩
        rcases hcase with ⟨hx, rfl⟩ | ⟨_, hfit, rfl⟩
        · refine .inl ⟨hx, ?_⟩
          rw [CtxS.afterSys_den, hΓ]
          show _ = CtxOf.afterSys (Γ.den ρ) ((ρ.setVal k x).val k) t
          rw [Env.setVal_get_self]
        · rw [hrsi] at hfit
          refine .inr ⟨hfit, ?_⟩
          rw [CtxS.afterSys_den, hrsi]
          have e : CtxS.den (ρ.setVal k x) { Γ with held := (.var k, ⟨pages len, []⟩) :: Γ.held }
              = { Γ.den ρ with held := (x, ⟨pages len, []⟩) :: (Γ.den ρ).held } := by
            refine ctx_ext
              (congrArg CtxOf.val hΓ : (Γ.den (ρ.setVal k x)).val = (Γ.den ρ).val)
              (congrArg CtxOf.flags hΓ : (Γ.den (ρ.setVal k x)).flags = (Γ.den ρ).flags) ?_
              (congrArg CtxOf.known hΓ : (Γ.den (ρ.setVal k x)).known = (Γ.den ρ).known)
            show ((ρ.setVal k x).val k, (⟨pages len, []⟩ : Held)) :: (Γ.den (ρ.setVal k x)).held = _
            rw [Env.setVal_get_self, hΓ]
          rw [e]
          show _ = CtxOf.afterSys _ ((ρ.setVal k x).val k) t
          rw [Env.setVal_get_self]
      · cases h
    · cases h
  · cases h

theorem map_eraseIdx {α β : Type} (f : α → β) : (l : List α) → (i : Nat) →
    (l.eraseIdx i).map f = (l.map f).eraseIdx i
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | a :: l, i + 1 => by
    show f a :: (l.eraseIdx i).map f = f a :: (l.map f).eraseIdx i
    rw [map_eraseIdx f l i]

/-- The place among the regions held of one at an address, of a size. -/
def findRegion (base : Val) (size : Nat) : List (Val × HeldS) → Nat → Option Nat
  | [], _ => none
  | g :: gs, i => if g.1.same base && g.2.size == size then some i else findRegion base size gs (i + 1)

theorem findRegion_spec {base : Val} {size : Nat} : (G : List (Val × HeldS)) → (i₀ j : Nat) →
    findRegion base size G i₀ = some j →
    ∃ g, G[j - i₀]? = some g ∧ i₀ ≤ j ∧ g.1.same base = true ∧ g.2.size = size
  | [], _, _, h => nomatch h
  | g :: gs, i₀, j, h => by
    unfold findRegion at h
    split at h
    · next hc =>
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨g, by simp, Nat.le_refl _, hc.1, hc.2⟩
    · obtain ⟨g', hg', hle, rest⟩ := findRegion_spec gs (i₀ + 1) j h
      refine ⟨g', ?_, by omega, rest⟩
      have e : j - i₀ = (j - (i₀ + 1)) + 1 := by omega
      rw [e, List.getElem?_cons_succ]
      exact hg'

/-- **A call that takes memory back, as a step on terms**: where the call
number and the length are written out and a region of that size is held at
the address given, the two contexts it may return in: one in which what it
hands back, named `k`, is an error number and the region is held still; and
one in which it hands back zero and the region is held no longer. -/
def sysUnmap (Γ : CtxS) (k : Nat) (next : BitVec 64) : Option (CtxS × CtxS) :=
  match Γ.regs.rax.lit?, Γ.regs.rsi.lit? with
  | some nr, some len =>
    match linuxKind nr with
    | some .unmap =>
      match findRegion Γ.regs.rdi (pages len) Γ.held 0 with
      | some j =>
        some (Γ.afterSys (.var k) next,
          CtxS.afterSys { Γ with held := Γ.held.eraseIdx j } (.lit 0) next)
      | none => none
    | _ => none
  | _, _ => none

theorem sysUnmap_sound {D : SysDesc} (hD : Describes sys D) (hkind : D.kind = linuxKind)
    (hpre : ∀ s, D.pre s) {ρ : Env} {Γ Γe Γo : CtxS} {k : Nat} {next : BitVec 64}
    (h : sysUnmap Γ k next = some (Γe, Γo)) (hu : Γ.under k = true) :
    Steps fetch sys Ψ .syscall next (Γ.den ρ) fun t Δ =>
      t = next ∧ ((∃ x, SysErr x ∧ Δ = Γe.den (ρ.setVal k x)) ∨ Δ = Γo.den ρ) := by
  unfold sysUnmap at h
  split at h
  · next nr len hnr hlen =>
    split at h
    · next hk =>
      split at h
      · next j hfind =>
        cases h
        obtain ⟨g, hg, _, hsame, hsize⟩ := findRegion_spec Γ.held 0 j hfind
        rw [Nat.sub_zero] at hg
        have hrax : (Γ.den ρ).val .rax = nr := Val.lit?_den hnr
        have hrsi : (Γ.den ρ).val .rsi = len := Val.lit?_den hlen
        have hheld : (Γ.den ρ).held[j]? = some ((Γ.den ρ).val .rdi, g.2.den ρ) := by
          rw [CtxS.held_den ρ Γ (b := g.1) (S := g.2) hg]
          show some (g.1.den ρ, _) = some ((Γ.regs.get .rdi).den ρ, _)
          rw [Val.same_den ρ hsame]
          rfl
        refine Steps.mono (Steps.unmap hD (by rw [hkind, hrax]; exact hk) hheld
          (by rw [hrsi]; exact hsize) (fun _ _ _ _ s _ _ => hpre s)) ?_
        rintro t Δ ⟨rfl, hcase⟩
        refine ⟨rfl, ?_⟩
        rcases hcase with ⟨x, hx, rfl⟩ | rfl
        · refine .inl ⟨x, hx, ?_⟩
          rw [CtxS.afterSys_den, CtxS.den_setVal ρ k x Γ hu]
          show _ = CtxOf.afterSys (Γ.den ρ) ((ρ.setVal k x).val k) t
          rw [Env.setVal_get_self]
        · refine .inr ?_
          rw [CtxS.afterSys_den]
          have hj : j < (Γ.held.map fun b => (b.1.den ρ, b.2.den ρ)).length := by
            rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hg).1
          have e : CtxS.den ρ { Γ with held := Γ.held.eraseIdx j }
              = { Γ.den ρ with held := (Γ.den ρ).held.eraseIdx j } := by
            refine ctx_ext rfl rfl ?_ rfl
            show (Γ.held.eraseIdx j).map (fun b => (b.1.den ρ, b.2.den ρ)) ++ restDen ρ Γ.rest
              = ((Γ.held.map fun b => (b.1.den ρ, b.2.den ρ)) ++ restDen ρ Γ.rest).eraseIdx j
            rw [List.eraseIdx_append_of_lt_length hj, map_eraseIdx]
          rw [e]
          rfl
      · cases h
    · cases h
  · cases h

end TypedAsm.U
