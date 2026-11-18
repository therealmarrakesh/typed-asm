import TypedAsm.U.Entry

/-!
# How a program ends

A program is seen to end only with a status as wanted by typing it against
the system that lets an exit through only with such a status. What that
system asks at a call, the checker sees of the context there: the call
number is written out, and where it is an exit, so is the status, which is
as wanted. One check gives both that the program is safe and how it ends.
-/

namespace TypedAsm.U

open TypedAsm

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

theorem ite_ne_exit {α : Type} {p : Prop} [Decidable p] {a b : Result α} {c : BitVec 32}
    (ha : a ≠ .exit c) (hb : b ≠ .exit c) : (if p then a else b) ≠ .exit c := by
  split <;> assumption

/-- Linux ends a program only at an `exit` or an `exit_group`. -/
theorem linux_exit_only {s : State} {c : BitVec 32} (h : linux s = .exit c) :
    s.getReg .rax = 60 ∨ s.getReg .rax = 231 := by
  by_cases h60 : s.getReg .rax = 60
  · exact .inl h60
  · by_cases h231 : s.getReg .rax = 231
    · exact .inr h231
    · have hne : linux s ≠ .exit c := by
        unfold linux
        simp only [h60, h231, ↓reduceIte]
        repeat (first | refine ite_ne_exit ?_ ?_ | (intro h; cases h))
      exact absurd h hne

/-- Linux, described, asking besides that any exit be with a status as
wanted. -/
def exitsDesc (Q : BitVec 32 → Prop) : SysDesc :=
  { linuxDesc with pre := fun s => linuxDesc.pre s ∧ ∀ c, linux s = .exit c → Q c }

/-- **Whether a context at a system call is seen to end the program only
with a status as wanted**: the call number is written out; and where it is
an exit, the status is written out and is as wanted, or is seen by what is
known to lie among a few numbers each of which is as wanted. -/
def preExits (q : BitVec 32 → Bool) (Γ : CtxS) : Bool :=
  match Γ.regs.rax.lit? with
  | some nr =>
    if nr = 60 ∨ nr = 231 then
      match Γ.regs.rdi.lit? with
      | some v => q (v.setWidth 32)
      | none =>
        match Γ.within Γ.regs.rdi with
        | some (lo, hi) =>
          decide (hi < 4294967296) && decide (hi - lo < 4096) &&
            (List.range (hi - lo + 1)).all fun i => q (BitVec.ofNat 32 (lo + i))
        | none => false
    else true
  | none => false

theorem preExits_sound {Q : BitVec 32 → Prop} {q : BitVec 32 → Bool} (hq : ∀ c, q c = true → Q c) :
    PreSound fetch sys Ψ (exitsDesc Q) (preExits q) := by
  intro Γ ρ h n Ψ' _ _ s hw
  refine ⟨trivial, fun c hc => ?_⟩
  unfold preExits at h
  split at h
  · next nr hnr =>
    have hrax : s.getReg .rax = nr := (hw.val .rax).trans (Val.lit?_den hnr)
    split at h
    · next hex =>
      split at h
      · next v hv =>
        have hrdi : s.getReg .rdi = v := (hw.val .rdi).trans (Val.lit?_den hv)
        have hc' := linux_exit_status (by rw [hrax]; exact hex) hc
        rw [hc']
        show Q ((s.getReg .rdi).setWidth 32)
        rw [hrdi]
        exact hq _ h
      · split at h
        · next lo hi hwi =>
          simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
          obtain ⟨⟨hhi, _⟩, hall⟩ := h
          have hb := CtxS.within_den (ρ := ρ) hwi hw.known
          have hv : (Γ.regs.rdi.den ρ) = s.getReg .rdi := (hw.val .rdi).symm
          rw [hv] at hb
          have hc' := linux_exit_status (by rw [hrax]; exact hex) hc
          rw [hc']
          show Q ((s.getReg .rdi).setWidth 32)
          have e : (s.getReg .rdi).setWidth 32
              = BitVec.ofNat 32 (lo + ((s.getReg .rdi).toNat - lo)) := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
            congr 1
            omega
          rw [e]
          exact hq _ (hall _ (by omega))
        · cases h
    · next hne =>
      have := linux_exit_only hc
      rw [hrax] at this
      exact absurd this hne
  · cases h

/-- **A program that checks against that requirement is safe under Linux,
and ends only with a status as wanted.** The state may match under a memory
typing that has more blocks than the one the program is checked under. -/
theorem exits_of_checked_ext {Q : BitVec 32 → Prop} {q : BitVec 32 → Bool}
    (hq : ∀ c, q c = true → Q c) {pg : Prog} {labels : List Label} {fuel k : Nat}
    (hpg : pg.pre = preExits q)
    (hcode : ∀ e ∈ pg.code, fetch e.1 = some (e.2.1, e.2.2)) (hk : KindsOk Ψ pg.kinds)
    (hst : StaticsOk fetch (linux.exitsOnly Q) Ψ pg.statics) {Ψ₂ : MemTy} (hext : Ψ.Ext Ψ₂)
    (hwf : Ψ₂.WF)
    (h : checkProgram pg labels fuel k = true)
    {l : Label} (hl : l ∈ labels) {s : State} (hrip : s.rip = l.addr) (ρ : Env) (fam : Fam)
    (hfn : ρ.fn = pg.fns) (hlaws : LawsHold pg.fns pg.laws)
    (hw : ∀ n, (∀ l' ∈ labels, ∀ (ρ' : Env) (fam' : Fam), ρ'.fn = pg.fns →
        Ok fetch (linux.exitsOnly Q) Ψ n l'.addr
          (l'.pat.den { ρ' with bound := fam' :: ρ'.bound })) →
      WellTyped fetch (linux.exitsOnly Q) Ψ₂ n
        (l.pat.den { ρ with bound := fam :: ρ.bound }) s) :
    Safe fetch linux s ∧
      ∀ s', TypedAsm.Steps fetch linux s s' → ∀ len c, fetch s'.rip = some (.syscall, len) →
        linux { s' with rip := s'.rip + len } = .exit c → Q c :=
  Safe.of_exitsOnly
    (safe_of_checked_ext (D := exitsDesc Q) (linux_describes.exitsOnly Q) rfl
      (by rw [hpg]; exact preExits_sound hq) hcode hk hst hext hwf hlaws h hl hrip ρ fam hfn hw)

/-- The same, the state matching under the memory typing the program is
checked under. -/
theorem exits_of_checked {Q : BitVec 32 → Prop} {q : BitVec 32 → Bool}
    (hq : ∀ c, q c = true → Q c) {pg : Prog} {labels : List Label} {fuel k : Nat}
    (hpg : pg.pre = preExits q)
    (hcode : ∀ e ∈ pg.code, fetch e.1 = some (e.2.1, e.2.2)) (hk : KindsOk Ψ pg.kinds)
    (hst : StaticsOk fetch (linux.exitsOnly Q) Ψ pg.statics) (hwf : Ψ.WF)
    (h : checkProgram pg labels fuel k = true)
    {l : Label} (hl : l ∈ labels) {s : State} (hrip : s.rip = l.addr) (ρ : Env) (fam : Fam)
    (hfn : ρ.fn = pg.fns) (hlaws : LawsHold pg.fns pg.laws)
    (hw : ∀ n, (∀ l' ∈ labels, ∀ (ρ' : Env) (fam' : Fam), ρ'.fn = pg.fns →
        Ok fetch (linux.exitsOnly Q) Ψ n l'.addr
          (l'.pat.den { ρ' with bound := fam' :: ρ'.bound })) →
      WellTyped fetch (linux.exitsOnly Q) Ψ n
        (l.pat.den { ρ with bound := fam :: ρ.bound }) s) :
    Safe fetch linux s ∧
      ∀ s', TypedAsm.Steps fetch linux s s' → ∀ len c, fetch s'.rip = some (.syscall, len) →
        linux { s' with rip := s'.rip + len } = .exit c → Q c :=
  exits_of_checked_ext hq hpg hcode hk hst (MemTy.Ext.refl Ψ) hwf h hl hrip ρ fam hfn hlaws hw

end TypedAsm.U
