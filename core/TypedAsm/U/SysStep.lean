import TypedAsm.U.Step
import TypedAsm.U.RegardS
import TypedAsm.U.Unmap
import TypedAsm.U.SysMem

/-!
# System calls, as steps on terms

Where the call number is a number written out, what the call does is read
from the system's description, and the context it returns in is given: one
function for each of the few things a call may do, none for any one call.
-/

namespace TypedAsm.U

open TypedAsm

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

/-- What the system asks for a call to be let through holds in every state
that matches a context. -/
def PreAt (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (D : SysDesc) (Γ : Ctx) : Prop :=
  ∀ n, ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → ∀ s : State, WellTyped fetch sys Ψ' n Γ s → D.pre s

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
    {ρ : Env} {Γ Γ' : CtxS} {k : Nat} {next : BitVec 64}
    (h : sysWorld Γ k next = some Γ') (hu : Γ.under k = true)
    (hpre : PreAt fetch sys Ψ D (Γ.den ρ)) :
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
        (fun n Ψ' he hwf s _ hw => hpre n Ψ' he hwf s hw)) ?_
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
    {ρ : Env} {Γ : CtxS} (h : sysEnds Γ = true) {a len : BitVec 64}
    (hf : fetch a = some (.syscall, len)) (hpre : PreAt fetch sys Ψ D (Γ.den ρ)) (n : Nat) : Ok fetch sys Ψ n a (Γ.den ρ) := by
  unfold sysEnds at h
  split at h
  · next nr hnr =>
    split at h
    · next hk =>
      have hrax : (Γ.den ρ).val .rax = nr := Val.lit?_den hnr
      exact Ok.ends hD hf (by rw [hkind, hrax]; exact hk) (fun n Ψ' he hwf s _ hw => hpre n Ψ' he hwf s hw)
    · cases h
  · cases h

/-! ## Calls that store bytes -/

/-- The most bytes a call may store: written out, or the most the register
that says so can hold. -/
def roomTop (Γ : CtxS) : Reg ⊕ Nat → Option Nat
  | .inl r => Γ.upper (Γ.regs.get r)
  | .inr n => some n

theorem roomTop_le {ρ : Env} {Γ : CtxS} {room : Reg ⊕ Nat} {M : Nat} (h : roomTop Γ room = some M)
    {Ψ' : MemTy} {n : Nat} (hg : ∀ g ∈ (Γ.den ρ).known, HasTy fetch sys Ψ' n g.2 g.1) :
    roomVal (Γ.den ρ).val room ≤ M := by
  cases room with
  | inr m => cases h; exact Nat.le_refl _
  | inl r => exact CtxS.upper_le hg _ h

/-- How many bytes a call may store, as terms and a number: what the
register that says so holds, or the number written out. -/
def roomLs (Γ : CtxS) : Reg ⊕ Nat → List Val × Nat
  | .inl r => ([Γ.regs.get r], 0)
  | .inr n => ([], n)

theorem roomLs_den (ρ : Env) (Γ : CtxS) (room : Reg ⊕ Nat) :
    sumNat ρ (roomLs Γ room).1 + (roomLs Γ room).2 = roomVal (Γ.den ρ).val room := by
  cases room with
  | inl r => show ((Γ.regs.get r).den ρ).toNat + 0 + 0 = ((Γ.regs.get r).den ρ).toNat; omega
  | inr n => show 0 + n = n; omega

/-- A region with fewer of its values, in a list of regions that mention
only names below `k`, mentions only those. -/
theorem heldUnder_set {k : Nat} {held : List (Val × HeldS)} {j : Nat} {b : Val} {S S' : HeldS}
    (h : heldUnder k held = true) (hl : held[j]? = some (b, S)) (hsz : S'.size = S.size)
    (hsub : ∀ p ∈ S'.slots, p ∈ S.slots) : heldUnder k (held.set j (b, S')) = true := by
  simp only [heldUnder, List.all_eq_true, Bool.and_eq_true] at h ⊢
  intro x hx
  rcases List.mem_or_eq_of_mem_set hx with hx | rfl
  · exact h x hx
  · have := h (b, S) (List.mem_of_getElem? hl)
    exact ⟨⟨this.1.1, by rw [hsz]; exact this.1.2⟩, fun p hp => this.2 p (hsub p hp)⟩

/-- A call that stores bytes in a region the context holds, of those the
address is a number into (`plain`) or of the others: the two contexts it may
return in. -/
def fillsHeld (plain : Bool) (Γ : CtxS) (k : Nat) (next : BitVec 64) (b : Reg) (room : Reg ⊕ Nat) :
    Option (CtxS × CtxS) :=
  let ls := (roomLs Γ room).1
  let n := (roomLs Γ room).2
  match findHeldP plain Γ.known (Γ.regs.get b) ls n Γ.held 0 with
  | some (j, base, S, o) =>
    some (Γ.afterSys (.var k) next,
      CtxS.afterSys { Γ with held := Γ.held.set j (base, S.clearT Γ.known o ls n) } (.var k) next)
  | none => none

theorem fillsHeld_sound {D : SysDesc} (hD : Describes sys D) {ρ : Env} {plain : Bool}
    {Γ Γe Γh : CtxS} {k : Nat} {next : BitVec 64} {b : Reg} {room : Reg ⊕ Nat}
    (hk : D.kind ((Γ.den ρ).val .rax) = some (.fills b room))
    (h : fillsHeld plain Γ k next b room = some (Γe, Γh)) (hu : Γ.under k = true)
    (hpre : PreAt fetch sys Ψ D (Γ.den ρ)) :
    Steps fetch sys Ψ .syscall next (Γ.den ρ) fun t Δ =>
      ∃ x, t = next ∧ (Δ = Γe.den (ρ.setVal k x) ∨ Δ = Γh.den (ρ.setVal k x)) := by
  simp only [fillsHeld] at h
  split at h
  · next j base S o hfind =>
    cases h
    obtain ⟨i, hi, hl, hraw, ho⟩ := findHeldP_raw Γ.held 0 hfind
    have hji : j = i := by omega
    subst hji
    generalize hls : (roomLs Γ room).1 = ls at hraw
    generalize hn : (roomLs Γ room).2 = n at hraw
    have hroom : sumNat ρ ls + n = roomVal (Γ.den ρ).val room := by
      rw [← hls, ← hn]; exact roomLs_den ρ Γ room
    have hjlt : j < (Γ.held.map fun b => (b.1.den ρ, b.2.den ρ)).length := by
      rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hl).1
    have hH : Havoc fetch sys Ψ (Γ.den ρ) ((Γ.den ρ).val b) (roomVal (Γ.den ρ).val room)
        { Γ.den ρ with
          held := (Γ.den ρ).held.set j (base.den ρ, (S.clearT Γ.known o ls n).den ρ) } := by
      refine ⟨rfl, rfl, fun k' Ψ' he hwf s hw data hlen hcw => ?_⟩
      have hg := knownS hw.known
      have hin := sumLe_den hraw hg
      simp only [sumNat, Nat.add_zero] at hin
      have H := Havoc.heldTo (fetch := fetch) (sys := sys) (Ψ := Ψ)
        (S' := (S.clearT Γ.known o ls n).den ρ) (CtxS.held_den ρ Γ hl)
        (o := o.nat ρ) (n := roomVal (Γ.den ρ).val room)
        (by show o.nat ρ + _ ≤ S.size.nat ρ; omega) rfl
        (fun p hp => by
          have := HeldS.clearT_mem hg hp
          exact ⟨this.1, by omega⟩)
      have ha' : (Γ.den ρ).val b = base.den ρ + BitVec.ofNat 64 (o.nat ρ) := by
        show (Γ.regs.get b).den ρ = _
        rw [ho, Val.nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        exact offTerm_den ρ _ _
      rw [ha'] at hcw ⊢
      exact H.2.2 k' Ψ' he hwf s hw data hlen hcw
    refine Steps.mono (Steps.fills hD hk
      (fun n Ψ' he hwf s _ hw => hpre n Ψ' he hwf s hw) hH) ?_
    rintro t Δ ⟨rfl, x, hcase⟩
    have hΓ : Γ.den (ρ.setVal k x) = Γ.den ρ := CtxS.den_setVal ρ k x Γ hu
    refine ⟨x, rfl, ?_⟩
    rcases hcase with rfl | rfl
    · refine .inl ?_
      rw [CtxS.afterSys_den, hΓ]
      show _ = CtxOf.afterSys (Γ.den ρ) ((ρ.setVal k x).val k) t
      rw [Env.setVal_get_self]
    · refine .inr ?_
      rw [CtxS.afterSys_den]
      have hu' : CtxS.under k
          { Γ with held := Γ.held.set j (base, S.clearT Γ.known o ls n) } = true := by
        simp only [CtxS.under, Bool.and_eq_true] at hu ⊢
        exact ⟨⟨⟨hu.1.1.1, heldUnder_set hu.1.1.2 hl rfl
          (fun p hp => (List.mem_filter.mp hp).1)⟩, hu.1.2⟩, hu.2⟩
      have e : CtxS.den (ρ.setVal k x)
            { Γ with held := Γ.held.set j (base, S.clearT Γ.known o ls n) }
          = { Γ.den ρ with
              held := (Γ.den ρ).held.set j (base.den ρ, (S.clearT Γ.known o ls n).den ρ) } := by
        rw [CtxS.den_setVal ρ k x _ hu']
        refine ctx_ext rfl rfl ?_ rfl
        show (Γ.held.set j (base, S.clearT Γ.known o ls n)).map (fun b => (b.1.den ρ, b.2.den ρ))
            ++ restDen ρ Γ.rest
          = ((Γ.held.map fun b => (b.1.den ρ, b.2.den ρ)) ++ restDen ρ Γ.rest).set j _
        rw [List.set_append_left _ _ hjlt, List.map_set]
      rw [e]
      show _ = CtxOf.afterSys _ ((ρ.setVal k x).val k) t
      rw [Env.setVal_get_self]
  · cases h

/-- **A call that stores bytes at an address the program gives, as a step
on terms**: where the call number is written out and the bytes, as many as
the call may store, lie in a region held, the two contexts it may return
in, with the name `k` for what it hands back: the context as it was, and
the context saying nothing of those bytes. Or the bytes lie, wherever in
its stretch the address is, in a block a value is known to point into, that
may be written through it, where the block has no typed value: the context
is then as it was either way. -/
def sysFills (kinds : Nat → Option ShapeS) (Γ : CtxS) (k : Nat) (next : BitVec 64) :
    Option (CtxS × CtxS) :=
  match Γ.regs.rax.lit? with
  | some nr =>
    match linuxKind nr with
    | some (.fills b room) =>
      match fillsHeld true Γ k next b room with
      | some r => some r
      | none =>
        match roomTop Γ room with
        | some M =>
          match findFactR kinds Γ (Γ.regs.get b) M Γ.known with
          | some (_, _, Sh, w, off, d, Ma) =>
            if w && Sh.vals.free (d + off) (Ma + M) then
              some (Γ.afterSys (.var k) next, Γ.afterSys (.var k) next)
            else fillsHeld false Γ k next b room
          | none => fillsHeld false Γ k next b room
        | none => fillsHeld false Γ k next b room
    | _ => none
  | none => none

theorem sysFills_sound {D : SysDesc} (hD : Describes sys D) (hkind : D.kind = linuxKind)
    {ρ : Env} {kinds : Nat → Option ShapeS} (hkd : KindsOk Ψ kinds)
    {Γ Γe Γh : CtxS} {k : Nat} {next : BitVec 64}
    (h : sysFills kinds Γ k next = some (Γe, Γh)) (hu : Γ.under k = true)
    (hpre : PreAt fetch sys Ψ D (Γ.den ρ)) :
    Steps fetch sys Ψ .syscall next (Γ.den ρ) fun t Δ =>
      ∃ x, t = next ∧ (Δ = Γe.den (ρ.setVal k x) ∨ Δ = Γh.den (ρ.setVal k x)) := by
  unfold sysFills at h
  split at h
  · next nr hnr =>
    have hrax : (Γ.den ρ).val .rax = nr := Val.lit?_den hnr
    split at h
    · next b room hk =>
      have hk' : D.kind ((Γ.den ρ).val .rax) = some (.fills b room) := by
        rw [hkind, hrax]; exact hk
      split at h
      · next r hr => cases h; exact fillsHeld_sound hD hk' hr hu hpre
      · split at h
        · next M hM =>
          split at h
          · next p τ Sh w off d Ma hfind =>
            split at h
            · next hc =>
              cases h
              rw [Bool.and_eq_true] at hc
              obtain ⟨hw', hfree⟩ := hc
              subst hw'
              obtain ⟨hmem, hpt, hin, hsp⟩ := findFactR_spec Γ.known hfind
              have hfm : (p.den ρ, τ.den ρ) ∈ (Γ.den ρ).known :=
                List.mem_map.mpr ⟨(p, τ), hmem, rfl⟩
              have hH : Havoc fetch sys Ψ (Γ.den ρ) ((Γ.den ρ).val b)
                  (roomVal (Γ.den ρ).val room) (Γ.den ρ) := by
                refine ⟨rfl, rfl, fun k' Ψ' he hwf s hw data hlen hcw => ?_⟩
                obtain ⟨o', ha, h1, h2⟩ := CtxS.spanFrom_den hsp hw.known
                have hroom := roomTop_le hM hw.known
                have hall : ∀ q ∈ (Sh.den ρ).vals,
                    ShapeOf.clearOf (d + off) (Ma + M) q = true := by
                  have := ValsS.free_den ρ (d + off) (Ma + M) Sh.vals
                  rw [hfree, ← ShapeS.den_vals, List.all_eq_true] at this
                  exact this
                have ha' : (Γ.den ρ).val b = p.den ρ + BitVec.ofNat 64 o' := ha
                have H := Havoc.shared (fetch := fetch) (sys := sys) (Ψ := Ψ)
                  (a := (Γ.den ρ).val b) (o := o' + off) (n := M) hfm (TyS.pointee_den hkd ρ hpt)
                  (by rw [ha', BitVec.ofNat_add, BitVec.add_assoc])
                  (by rw [ShapeS.den_size]; omega)
                  (by
                    show (Sh.den ρ).vals.all _ = true
                    rw [List.all_eq_true]
                    intro q hq
                    have := hall q hq
                    simp only [ShapeOf.clearOf, Bool.or_eq_true, decide_eq_true_eq] at this ⊢
                    omega)
                exact H.2.2 k' Ψ' he hwf s hw data (by omega) hcw
              refine Steps.mono (Steps.fills hD (by rw [hkind, hrax]; exact hk)
                (fun n Ψ' he hwf s _ hw => hpre n Ψ' he hwf s hw) hH) ?_
              rintro t Δ ⟨rfl, x, hcase⟩
              have hΓ : Γ.den (ρ.setVal k x) = Γ.den ρ := CtxS.den_setVal ρ k x Γ hu
              have e : (Γ.afterSys (.var k) t).den (ρ.setVal k x) = (Γ.den ρ).afterSys x t := by
                rw [CtxS.afterSys_den, hΓ]
                show CtxOf.afterSys (Γ.den ρ) ((ρ.setVal k x).val k) t = _
                rw [Env.setVal_get_self]
              refine ⟨x, rfl, .inl ?_⟩
              rcases hcase with rfl | rfl <;> exact e.symm
            · exact fillsHeld_sound hD hk' h hu hpre
          · exact fillsHeld_sound hD hk' h hu hpre
        · exact fillsHeld_sound hD hk' h hu hpre
    · cases h
  · cases h

/-! ## Calls with two outcomes -/

/-- **A call for fresh memory, as a step on terms**: where the call number
and the length are written out, no address is asked for, and the memory
asked for is to be read and written, private and of no file (`rdx` three,
`r10` 0x22: the one form of the call the kernel is modelled in), the two
contexts it may return in, with the name `k` for what it hands back: one in
which that is an error number and nothing more is held, and one in which it
is the address of so many bytes, now held. With them, the size. -/
def sysMap (Γ : CtxS) (k : Nat) (next : BitVec 64) : Option (CtxS × CtxS × Nat) :=
  match Γ.regs.rax.lit?, Γ.regs.rdi.lit?, Γ.regs.rsi.lit? with
  | some nr, some di, some len =>
    match linuxKind nr with
    | some .map =>
      if di = 0 then
        if Γ.regs.rdx.lit? = some 3 ∧ Γ.regs.r10.lit? = some 0x22 then
          some (Γ.afterSys (.var k) next,
            CtxS.afterSys { Γ with held := (.var k, ⟨litNat (pages len), []⟩) :: Γ.held } (.var k) next,
            pages len)
        else none
      else none
    | _ => none
  | _, _, _ => none

theorem sysMap_sound {D : SysDesc} (hD : Describes sys D) (hkind : D.kind = linuxKind)
    {ρ : Env} {Γ Γe Γo : CtxS} {sz k : Nat} {next : BitVec 64}
    (h : sysMap Γ k next = some (Γe, Γo, sz)) (hu : Γ.under k = true)
    (hpre : PreAt fetch sys Ψ D (Γ.den ρ)) :
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
        split at h
        rotate_left
        · cases h
        cases h
        have hrax : (Γ.den ρ).val .rax = nr := Val.lit?_den hnr
        have hrdi : (Γ.den ρ).val .rdi = 0 := by rw [← hd0]; exact Val.lit?_den hdi
        have hrsi : (Γ.den ρ).val .rsi = len := Val.lit?_den hlen
        refine Steps.mono (Steps.map hD (by rw [hkind, hrax]; exact hk) hrdi
          (fun n Ψ' he hwf s _ hw => hpre n Ψ' he hwf s hw)) ?_
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
          have hlt : pages len < 2 ^ 64 := by
            have : addrTop < 2 ^ 64 := by decide
            omega
          have e : CtxS.den (ρ.setVal k x)
                { Γ with held := (.var k, ⟨litNat (pages len), []⟩) :: Γ.held }
              = { Γ.den ρ with held := (x, ⟨pages len, []⟩) :: (Γ.den ρ).held } := by
            refine ctx_ext
              (congrArg CtxOf.val hΓ : (Γ.den (ρ.setVal k x)).val = (Γ.den ρ).val)
              (congrArg CtxOf.flags hΓ : (Γ.den (ρ.setVal k x)).flags = (Γ.den ρ).flags) ?_
              (congrArg CtxOf.known hΓ : (Γ.den (ρ.setVal k x)).known = (Γ.den ρ).known)
            show ((ρ.setVal k x).val k,
              (⟨(litNat (pages len)).nat (ρ.setVal k x), []⟩ : Held)) ::
                (Γ.den (ρ.setVal k x)).held = _
            rw [Env.setVal_get_self, hΓ, litNat_nat _ hlt]
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
    {ρ : Env} {Γ Γe Γo : CtxS} {k : Nat} {next : BitVec 64}
    (h : sysUnmap Γ k next = some (Γe, Γo)) (hu : Γ.under k = true)
    (hpre : PreAt fetch sys Ψ D (Γ.den ρ)) :
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
        obtain ⟨g, hg, _, hsame, hsize⟩ := findRegion_spec ρ Γ.held 0 j hfind
        rw [Nat.sub_zero] at hg
        have hrax : (Γ.den ρ).val .rax = nr := Val.lit?_den hnr
        have hrsi : (Γ.den ρ).val .rsi = len := Val.lit?_den hlen
        have hheld : (Γ.den ρ).held[j]? = some ((Γ.den ρ).val .rdi, g.2.den ρ) := by
          rw [CtxS.held_den ρ Γ (b := g.1) (S := g.2) hg]
          show some (g.1.den ρ, _) = some ((Γ.regs.get .rdi).den ρ, _)
          rw [Val.same_den ρ hsame]
          rfl
        refine Steps.mono (Steps.unmap hD (by rw [hkind, hrax]; exact hk) hheld
          (by rw [hrsi]; exact hsize) (fun n Ψ' he hwf s _ hw => hpre n Ψ' he hwf s hw)) ?_
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
