import TypedAsm.U.Exits

/-!
# What a program writes

A program is seen to offer the kernel, at every `write`, a descriptor and
bytes as wanted, by typing it against the system that lets a `write`
through only with such. What that system asks at a call, the checker sees
of the context there: the descriptor, the address and the length are
written out, and the bytes lie in a block that says its bytes, which are
therefore the bytes offered.
-/

namespace TypedAsm.U

open TypedAsm

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

/-- The bytes of a block that says them are the bytes there, in any state
that matches a context. -/
theorem WellTyped.loadBytes_said {n : Nat} {Γ : Ctx} {s : State} {base : BitVec 64} {l : Layout}
    {bs : List (BitVec 8)} {off cnt : Nat} (h : WellTyped fetch sys Ψ n Γ s)
    (hl : Ψ base = some l) (hs : l.said = some bs) (hin : off + cnt ≤ bs.length) :
    s.loadBytes (base + BitVec.ofNat 64 off) cnt = (bs.drop off).take cnt := by
  apply List.ext_getElem
  · simp only [State.loadBytes, List.length_map, List.length_range, List.length_take,
      List.length_drop]
    omega
  · intro k hk₁ hk₂
    simp only [State.loadBytes, List.length_map, List.length_range] at hk₁
    simp only [State.loadBytes, List.getElem_map, List.getElem_range, List.getElem_take,
      List.getElem_drop]
    have := h.said base l bs hl hs (off + k) (by omega)
    rw [← this, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The blocks a program says the bytes of are blocks of the memory typing
that say those bytes. -/
def SaidOk (Ψ : MemTy) (said : List (BitVec 64 × List (BitVec 8))) : Prop :=
  ∀ x ∈ said, ∃ l, Ψ x.1 = some l ∧ l.said = some x.2

/-- **Whether a context at a system call is seen to offer, if the call is a
`write`, a descriptor and bytes as wanted**: the call number is written
out; and where it is a `write`, so are the descriptor, the address and the
length, and the bytes lie in a block that says its bytes. -/
def preWrites (said : List (BitVec 64 × List (BitVec 8))) (r : BitVec 64 → List (BitVec 8) → Bool)
    (Γ : CtxS) : Bool :=
  match Γ.regs.rax.lit? with
  | some nr =>
    if nr = 1 then
      match Γ.regs.rdi.lit?, Γ.regs.rsi.lit?, Γ.regs.rdx.lit? with
      | some fd, some buf, some len =>
        said.any fun x =>
          decide ((buf - x.1).toNat + len.toNat ≤ x.2.length) &&
            r fd ((x.2.drop (buf - x.1).toNat).take len.toNat)
      | _, _, _ => false
    else true
  | none => false

/-- **What that check shows**: in every state matching the context, if the
call is a `write`, the descriptor and the bytes offered are as wanted. -/
theorem preWrites_holds {R : BitVec 64 → List (BitVec 8) → Prop}
    {r : BitVec 64 → List (BitVec 8) → Bool} (hr : ∀ fd bs, r fd bs = true → R fd bs)
    {said : List (BitVec 64 × List (BitVec 8))} (hsaid : SaidOk Ψ said) {Γ : CtxS} {ρ : Env}
    (h : preWrites said r Γ = true) {n : Nat} {Ψ' : MemTy} (he : Ψ.Ext Ψ') {s : State}
    (hw : WellTyped fetch sys Ψ' n (Γ.den ρ) s) :
    s.getReg .rax = 1 → R (s.getReg .rdi) s.offered := by
  intro h1
  unfold preWrites at h
  split at h
  · next nr hnr =>
    have hrax : s.getReg .rax = nr := (hw.val .rax).trans (Val.lit?_den hnr)
    split at h
    · split at h
      · next fd buf len hfd hbuf hlen =>
        have hrdi : s.getReg .rdi = fd := (hw.val .rdi).trans (Val.lit?_den hfd)
        have hrsi : s.getReg .rsi = buf := (hw.val .rsi).trans (Val.lit?_den hbuf)
        have hrdx : s.getReg .rdx = len := (hw.val .rdx).trans (Val.lit?_den hlen)
        simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨x, hx, hin, hrx⟩ := h
        obtain ⟨l, hl, hs⟩ := hsaid x hx
        have hbytes := hw.loadBytes_said (he.blocks _ _ hl) hs hin
        have hb : x.1 + BitVec.ofNat 64 (buf - x.1).toNat = buf := by
          rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
        rw [hb] at hbytes
        show R (s.getReg .rdi) (s.loadBytes (s.getReg .rsi) (s.getReg .rdx).toNat)
        rw [hrdi, hrsi, hrdx, hbytes]
        exact hr _ _ hrx
      · cases h
    · next hne =>
      rw [hrax] at h1
      exact absurd h1 hne
  · cases h

/-- Linux, described, asking besides that any exit be with a status as
wanted and any `write` offer a descriptor and bytes as wanted. -/
def outDesc (Q : BitVec 32 → Prop) (R : BitVec 64 → List (BitVec 8) → Prop) : SysDesc :=
  { exitsDesc Q with
    pre := fun s => (exitsDesc Q).pre s ∧ (s.getReg .rax = 1 → R (s.getReg .rdi) s.offered) }

/-- Both asked of a context at a system call. -/
def preOut (said : List (BitVec 64 × List (BitVec 8))) (q : BitVec 32 → Bool)
    (r : BitVec 64 → List (BitVec 8) → Bool) (Γ : CtxS) : Bool :=
  preExits q Γ && preWrites said r Γ

theorem preOut_sound {Q : BitVec 32 → Prop} {q : BitVec 32 → Bool} (hq : ∀ c, q c = true → Q c)
    {R : BitVec 64 → List (BitVec 8) → Prop} {r : BitVec 64 → List (BitVec 8) → Bool}
    (hr : ∀ fd bs, r fd bs = true → R fd bs) {said : List (BitVec 64 × List (BitVec 8))}
    (hsaid : SaidOk Ψ said) : PreSound fetch sys Ψ (outDesc Q R) (preOut said q r) := by
  intro Γ ρ h n Ψ' he hwf s hw
  simp only [preOut, Bool.and_eq_true] at h
  exact ⟨preExits_sound hq Γ ρ h.1 n Ψ' he hwf s hw, preWrites_holds hr hsaid h.2 he hw⟩

/-- **A program that checks against both is safe under Linux, ends only
with a status as wanted, and offers at every `write` it reaches a
descriptor and bytes as wanted.** -/
theorem outputs_of_checked {Q : BitVec 32 → Prop} {q : BitVec 32 → Bool}
    (hq : ∀ c, q c = true → Q c) {R : BitVec 64 → List (BitVec 8) → Prop}
    {r : BitVec 64 → List (BitVec 8) → Bool} (hr : ∀ fd bs, r fd bs = true → R fd bs)
    {said : List (BitVec 64 × List (BitVec 8))} (hsaid : SaidOk Ψ said)
    {pg : Prog} {labels : List Label} {fuel k : Nat} (hpg : pg.pre = preOut said q r)
    (hcode : ∀ e ∈ pg.code, fetch e.1 = some (e.2.1, e.2.2)) (hk : KindsOk Ψ pg.kinds)
    (hst : StaticsOk fetch ((linux.exitsOnly Q).writesOnly R) Ψ pg.statics) (hwf : Ψ.WF)
    (h : checkProgram pg labels fuel k = true)
    {l : Label} (hl : l ∈ labels) {s : State} (hrip : s.rip = l.addr) (ρ : Env) (fam : Fam)
    (hfn : ρ.fn = pg.fns) (hlaws : LawsHold pg.fns pg.laws)
    (hw : ∀ n, (∀ l' ∈ labels, ∀ (ρ' : Env) (fam' : Fam), ρ'.fn = pg.fns →
        Ok fetch ((linux.exitsOnly Q).writesOnly R) Ψ n l'.addr
          (l'.pat.den { ρ' with bound := fam' :: ρ'.bound })) →
      WellTyped fetch ((linux.exitsOnly Q).writesOnly R) Ψ n
        (l.pat.den { ρ with bound := fam :: ρ.bound }) s) :
    Safe fetch linux s ∧
      (∀ s', TypedAsm.Steps fetch linux s s' → ∀ len c, fetch s'.rip = some (.syscall, len) →
        linux { s' with rip := s'.rip + len } = .exit c → Q c) ∧
      (∀ s', TypedAsm.Steps fetch linux s s' → ∀ len, fetch s'.rip = some (.syscall, len) →
        s'.getReg .rax = 1 → R (s'.getReg .rdi) s'.offered) :=
  have hW := Safe.of_writesOnly
    (safe_of_checked (D := outDesc Q R) ((linux_describes.exitsOnly Q).writesOnly R) rfl
      (by rw [hpg]; exact preOut_sound hq hr hsaid) hcode hk hst hwf hlaws h hl hrip ρ fam hfn hw)
  have hE := Safe.of_exitsOnly hW.1
  ⟨hE.1, hE.2, fun s' hs' len hf hax => hW.2 s' hs'.exitsOnly len hf hax⟩

end TypedAsm.U
