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

/-! ## Bytes the program made

A value the context says a region held holds, where it is a number written
out, is its eight bytes, the least significant first. So the bytes at an
address in such a region are known where each lies in such a value. -/

/-- The byte at a place in a region, where the region is said to hold a
number written out that the place lies in. -/
def cellByte (S : HeldS) (place : Val) : Option (BitVec 8) :=
  S.slots.findSome? fun p =>
    match place.minus p.1, p.2 with
    | some d, .lit v => if d.toNat < 8 then (le64 v)[d.toNat]? else none
    | _, _ => none

/-- So many bytes of a region from a place on, counted from the `j`th. -/
def cellBytes (S : HeldS) (o : Val) : Nat → Nat → Option (List (BitVec 8))
  | _, 0 => some []
  | j, n + 1 =>
    match cellByte S (o.plus (litNat j)), cellBytes S o (j + 1) n with
    | some b, some bs => some (b :: bs)
    | _, _ => none

/-- **So many bytes at an address, where they lie in numbers a region held
is said to hold.** -/
def heldBytes (Γ : CtxS) (buf : Val) (len : Nat) : Option (List (BitVec 8)) :=
  Γ.held.findSome? fun g => cellBytes g.2 (offTerm buf g.1) 0 len

theorem loadBytes_getElem (s : State) (a : BitVec 64) {n i : Nat} (hi : i < n) :
    (s.loadBytes a n)[i]'(by simp [State.loadBytes, hi]) = s.mem (a + BitVec.ofNat 64 i) := by
  simp [State.loadBytes]

theorem cellByte_mem {ρ : Env} {s : State} {b : BitVec 64} {S : HeldS}
    (hv : ∀ p ∈ (S.den ρ).vals, s.load64 (b + BitVec.ofNat 64 p.1) = p.2) {place : Val}
    {x : BitVec 8} (h : cellByte S place = some x) : s.mem (b + place.den ρ) = x := by
  obtain ⟨p, hp, hx⟩ := List.exists_of_findSome?_eq_some h
  split at hx
  · next d v hd hlit =>
    split at hx
    · next hlt =>
      have hload := hv (slotDen ρ p) (List.mem_map.mpr ⟨p, hp, rfl⟩)
      have hp2 : (slotDen ρ p).2 = v := by show p.2.den ρ = v; rw [hlit]; rfl
      have h8 := s.loadBytes_eight (b + BitVec.ofNat 64 (slotDen ρ p).1)
      rw [hload, hp2] at h8
      have hget := List.getElem?_eq_some_iff.mp hx
      obtain ⟨hlen, hval⟩ := hget
      have hm := loadBytes_getElem s (b + BitVec.ofNat 64 (slotDen ρ p).1) hlt
      have e : (s.loadBytes (b + BitVec.ofNat 64 (slotDen ρ p).1) 8)[d.toNat]'(by
          simp [State.loadBytes, hlt]) = (le64 v)[d.toNat] := by
        simp only [h8]
      rw [hm] at e
      rw [← hval, ← e, Val.minus_den ρ hd]
      show _ = s.mem (b + BitVec.ofNat 64 (p.1.den ρ).toNat + BitVec.ofNat 64 d.toNat)
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq,
        BitVec.add_assoc]
    · cases hx
  · cases hx

theorem cellBytes_mem {ρ : Env} {s : State} {b : BitVec 64} {S : HeldS}
    (hv : ∀ p ∈ (S.den ρ).vals, s.load64 (b + BitVec.ofNat 64 p.1) = p.2) (o : Val) :
    (n j : Nat) → {bs : List (BitVec 8)} → cellBytes S o j n = some bs →
    bs = (List.range n).map fun i => s.mem (b + o.den ρ + BitVec.ofNat 64 (j + i))
  | 0, _, _, h => by cases h; rfl
  | n + 1, j, bs, h => by
    simp only [cellBytes] at h
    split at h
    · next x xs hx hxs =>
      cases h
      have h1 := cellByte_mem hv hx
      rw [Val.plus_den] at h1
      have h2 := cellBytes_mem hv o n (j + 1) hxs
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, h2]
      congr 1
      · rw [← h1, BitVec.add_assoc]
        rfl
      · refine List.map_congr_left fun i _ => ?_
        show s.mem (b + o.den ρ + BitVec.ofNat 64 (j + 1 + i))
          = s.mem (b + o.den ρ + BitVec.ofNat 64 (j + (i + 1)))
        rw [show j + 1 + i = j + (i + 1) from by omega]
    · cases h

/-- **The bytes found so are the bytes there**, in any state that matches
the context. -/
theorem heldBytes_load {n : Nat} {Γ : CtxS} {ρ : Env} {s : State} {Ψ' : MemTy}
    (hw : WellTyped fetch sys Ψ' n (Γ.den ρ) s) {buf : Val} {len : Nat} {bs : List (BitVec 8)}
    (h : heldBytes Γ buf len = some bs) : s.loadBytes (buf.den ρ) len = bs := by
  obtain ⟨g, hg, hc⟩ := List.exists_of_findSome?_eq_some h
  have hmem : (g.1.den ρ, g.2.den ρ) ∈ (Γ.den ρ).held :=
    List.mem_append_left _ (List.mem_map.mpr ⟨g, hg, rfl⟩)
  have := cellBytes_mem (ρ := ρ) (s := s) (b := g.1.den ρ)
    (fun p hp => hw.held.vals _ hmem p hp) (offTerm buf g.1) len 0 hc
  rw [this, ← offTerm_den]
  simp [State.loadBytes]

/-! ## Bytes of a kind

Where the bytes a `write` offers are rows of bytes the context says are
each of a range, they are each of that range: so a number written out digit
by digit is offered as digits, whatever the number. -/

/-- Whether two terms are the same value: as written, or by what is known. -/
def sameAt (K : List (Val × TyS)) (a b : Val) : Bool := a.same b || sameKnown K a b

theorem sameAt_den {ρ : Env} {Ψ' : MemTy} {n : Nat} {K : List (Val × TyS)}
    (hg : ∀ g ∈ K, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ)) {a b : Val}
    (h : sameAt K a b = true) : a.den ρ = b.den ρ := by
  rcases Bool.or_eq_true _ _ |>.mp h with h | h
  · exact Val.same_den ρ h
  · exact sameKnown_den hg h

/-- **Rows of bytes one after another from an address**: one that starts
there, then one that starts where it ends, and so on, so far. -/
def rowChain (K : List (Val × TyS)) (rows : List RowS) : Nat → Val → List RowS
  | 0, _ => []
  | f + 1, cur =>
    match rows.find? fun g => g.byte && g.stride == 1 && sameAt K g.addr cur with
    | some g => g :: rowChain K rows f (.add cur g.count)
    | none => []

/-- Each byte so far from where a run of rows starts, within all they come
to, is a value of one of them. -/
theorem rowChain_cover {ρ : Env} {Ψ' : MemTy} {n : Nat} {K : List (Val × TyS)}
    (hg : ∀ g ∈ K, HasTy fetch sys Ψ' n (g.2.den ρ) (g.1.den ρ)) (rows : List RowS) :
    (f : Nat) → (cur : Val) → ∀ i, i < sumNat ρ ((rowChain K rows f cur).map (·.count)) →
      ∃ g ∈ rowChain K rows f cur, g ∈ rows ∧ g.byte = true ∧ g.stride = 1 ∧
        ∃ i', i' < (g.count.den ρ).toNat ∧
        cur.den ρ + BitVec.ofNat 64 i = g.addr.den ρ + BitVec.ofNat 64 (1 * i')
  | 0, _, i, hi => by simp [rowChain, sumNat] at hi
  | f + 1, cur, i, hi => by
    unfold rowChain at hi
    split at hi
    · next g hfind =>
      have hmem := List.mem_of_find?_eq_some hfind
      have hp := List.find?_some hfind
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      obtain ⟨⟨hb, hst⟩, hsame⟩ := hp
      have ha := sameAt_den hg hsame
      simp only [List.map_cons, sumNat] at hi
      by_cases hlt : i < (g.count.den ρ).toNat
      · refine ⟨g, ?_, hmem, hb, hst, i, hlt, by rw [ha, Nat.one_mul]⟩
        unfold rowChain
        rw [hfind]
        exact List.mem_cons_self
      · obtain ⟨g', hch', hm', hb', hst', i', hi', he⟩ :=
          rowChain_cover hg rows f (.add cur g.count) (i - (g.count.den ρ).toNat)
            (by simp only [Val.nat] at hi; omega)
        refine ⟨g', ?_, hm', hb', hst', i', hi', ?_⟩
        · unfold rowChain
          rw [hfind]
          exact List.mem_cons_of_mem _ hch'
        rw [← he]
        show cur.den ρ + BitVec.ofNat 64 i
          = cur.den ρ + g.count.den ρ + BitVec.ofNat 64 (i - (g.count.den ρ).toNat)
        have hc : g.count.den ρ = BitVec.ofNat 64 (g.count.den ρ).toNat := by simp
        rw [BitVec.add_assoc, hc, ← BitVec.ofNat_add]
        congr 2
        simp only [BitVec.toNat_ofNat]
        have := (g.count.den ρ).isLt
        rw [Nat.mod_eq_of_lt this]
        omega
    · simp [sumNat] at hi

/-- Whether every byte a type of a value says it may be, is one `p` takes:
of a range, each number from nought to 255 in it. -/
def byteKind (p : BitVec 8 → Bool) : TyS → Bool
  | .range lo hi => (List.range 256).all fun b =>
      !decide (BitVec.ofNat 64 b - lo ≤ hi - lo) || p (BitVec.ofNat 8 b)
  | _ => false

theorem byteKind_mem {p : BitVec 8 → Bool} {τ : TyS} (h : byteKind p τ = true) {ρ : Env}
    {Ψ' : MemTy} {n : Nat} {b : BitVec 8} (hb : HasTy fetch sys Ψ' n (τ.den ρ) (b.setWidth 64)) :
    p b = true := by
  cases τ with
  | range lo hi =>
    have hr := hasTy_range.mp hb
    simp only [byteKind, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at h
    have hlt := b.isLt
    rcases h b.toNat hlt with h | h
    · exact absurd (by
        have e : BitVec.ofNat 64 b.toNat = b.setWidth 64 := by
          apply BitVec.eq_of_toNat_eq; simp
        rw [e]; exact hr) h
    · have e : BitVec.ofNat 8 b.toNat = b := by simp
      rw [e] at h; exact h
  | _ => simp [byteKind] at h

/-- **Whether a `write` is seen to offer bytes each of a kind**: rows of
bytes from the address offered, one after another, are as many as are
offered or more, and each is of a range all of whose bytes `p` takes. -/
def rowsOffer (Γ : CtxS) (p : BitVec 8 → Bool) : Bool :=
  let ch := rowChain Γ.known Γ.rows Γ.rows.length Γ.regs.rsi
  sumLe Γ.known [Γ.regs.rdx] 0 (ch.map (·.count)) 0 && ch.all fun g => byteKind p g.ty

theorem rowsOffer_holds {Γ : CtxS} {p : BitVec 8 → Bool} (h : rowsOffer Γ p = true) {ρ : Env}
    {n : Nat} {Ψ' : MemTy} {s : State} (hw : WellTyped fetch sys Ψ' n (Γ.den ρ) s) :
    s.offered.all p = true := by
  have hg := knownS hw.known
  simp only [rowsOffer, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hle, hkind⟩ := h
  have hle' := sumLe_den hle hg
  simp only [sumNat, Nat.add_zero] at hle'
  rw [List.all_eq_true]
  intro b hb
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
  have hjn : j < (s.getReg .rdx).toNat := by
    simpa [State.offered, State.loadBytes] using hj
  have hrdx : s.getReg .rdx = Γ.regs.rdx.den ρ := hw.val .rdx
  have hrsi : s.getReg .rsi = Γ.regs.rsi.den ρ := hw.val .rsi
  obtain ⟨g, hgch, hgm, hbyte, hst, i', hi', he⟩ :=
    rowChain_cover hg Γ.rows Γ.rows.length Γ.regs.rsi j (by
      rw [hrdx] at hjn
      simp only [Val.nat] at hle'
      omega)
  have hrow := hw.rows (g.den ρ) (List.mem_map.mpr ⟨g, hgm, rfl⟩) i' hi'
  show p (s.offered[j]) = true
  have eb : s.offered[j] = s.mem (Γ.regs.rsi.den ρ + BitVec.ofNat 64 j) := by
    simp only [State.offered, State.loadBytes, List.getElem_map, List.getElem_range, hrsi]
  rw [eb, he]
  show p (s.mem _) = true
  have hcell : cellAt s (g.den ρ).byte ((g.den ρ).addr + BitVec.ofNat 64 ((g.den ρ).stride * i'))
      = (s.mem (g.addr.den ρ + BitVec.ofNat 64 (1 * i'))).setWidth 64 := by
    show cellAt s g.byte (g.addr.den ρ + BitVec.ofNat 64 (g.stride * i')) = _
    rw [hbyte, hst]
    rfl
  rw [hcell] at hrow
  exact byteKind_mem (hkind g hgch) hrow

/-- **Whether a context at a system call is seen to offer, if the call is a
`write`, a descriptor and bytes as wanted**: the call number is written
out; and where it is a `write`, so are the descriptor and the length, and
the bytes lie in a block that says its bytes, at an address written out,
or in numbers a region held is said to hold; or, where bytes of a kind may
be written anywhere (`each`), they lie in rows of bytes each of that kind. -/
def preWrites (said : List (BitVec 64 × List (BitVec 8))) (r : BitVec 64 → List (BitVec 8) → Bool)
    (each : Option (BitVec 64 → BitVec 8 → Bool)) (Γ : CtxS) : Bool :=
  match Γ.regs.rax.lit? with
  | some nr =>
    if nr = 1 then
      (match each, Γ.regs.rdi.lit? with
       | some e, some fd => rowsOffer Γ (e fd)
       | _, _ => false) ||
      match Γ.regs.rdi.lit?, Γ.regs.rdx.lit? with
      | some fd, some len =>
        (match Γ.regs.rsi.lit? with
         | some buf =>
           said.any fun x =>
             decide ((buf - x.1).toNat + len.toNat ≤ x.2.length) &&
               r fd ((x.2.drop (buf - x.1).toNat).take len.toNat)
         | none => false) ||
        (match heldBytes Γ Γ.regs.rsi len.toNat with
         | some bs => r fd bs
         | none => false)
      | _, _ => false
    else true
  | none => false

/-- **What that check shows**: in every state matching the context, if the
call is a `write`, the descriptor and the bytes offered are as wanted. -/
theorem preWrites_holds {R : BitVec 64 → List (BitVec 8) → Prop}
    {r : BitVec 64 → List (BitVec 8) → Bool} (hr : ∀ fd bs, r fd bs = true → R fd bs)
    {each : Option (BitVec 64 → BitVec 8 → Bool)}
    (heach : ∀ e, each = some e → ∀ fd bs, bs.all (e fd) = true → R fd bs)
    {said : List (BitVec 64 × List (BitVec 8))} (hsaid : SaidOk Ψ said) {Γ : CtxS} {ρ : Env}
    (h : preWrites said r each Γ = true) {n : Nat} {Ψ' : MemTy} (he : Ψ.Ext Ψ') {s : State}
    (hw : WellTyped fetch sys Ψ' n (Γ.den ρ) s) :
    s.getReg .rax = 1 → R (s.getReg .rdi) s.offered := by
  intro h1
  unfold preWrites at h
  split at h
  · next nr hnr =>
    have hrax : s.getReg .rax = nr := (hw.val .rax).trans (Val.lit?_den hnr)
    split at h
    · rcases Bool.or_eq_true _ _ |>.mp h with hrow | h
      · split at hrow
        · next e fd hfd =>
          have hrdi : s.getReg .rdi = fd := (hw.val .rdi).trans (Val.lit?_den hfd)
          rw [hrdi]
          exact heach e rfl fd _ (rowsOffer_holds hrow hw)
        · cases hrow
      split at h
      · next fd len hfd hlen =>
        have hrdi : s.getReg .rdi = fd := (hw.val .rdi).trans (Val.lit?_den hfd)
        have hrdx : s.getReg .rdx = len := (hw.val .rdx).trans (Val.lit?_den hlen)
        show R (s.getReg .rdi) (s.loadBytes (s.getReg .rsi) (s.getReg .rdx).toNat)
        rw [hrdi, hrdx]
        rcases Bool.or_eq_true _ _ |>.mp h with h | h
        · split at h
          · next buf hbuf =>
            have hrsi : s.getReg .rsi = buf := (hw.val .rsi).trans (Val.lit?_den hbuf)
            simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨x, hx, hin, hrx⟩ := h
            obtain ⟨l, hl, hs⟩ := hsaid x hx
            have hbytes := hw.loadBytes_said (he.blocks _ _ hl) hs hin
            have hb : x.1 + BitVec.ofNat 64 (buf - x.1).toNat = buf := by
              rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
            rw [hb] at hbytes
            rw [hrsi, hbytes]
            exact hr _ _ hrx
          · cases h
        · split at h
          · next bs hbs =>
            have hrsi : s.getReg .rsi = Γ.regs.rsi.den ρ := hw.val .rsi
            rw [hrsi, heldBytes_load hw hbs]
            exact hr _ _ h
          · cases h
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
    (r : BitVec 64 → List (BitVec 8) → Bool) (each : Option (BitVec 64 → BitVec 8 → Bool) := none)
    (Γ : CtxS) : Bool :=
  preExits q Γ && preWrites said r each Γ

theorem preOut_sound {Q : BitVec 32 → Prop} {q : BitVec 32 → Bool} (hq : ∀ c, q c = true → Q c)
    {R : BitVec 64 → List (BitVec 8) → Prop} {r : BitVec 64 → List (BitVec 8) → Bool}
    (hr : ∀ fd bs, r fd bs = true → R fd bs) {each : Option (BitVec 64 → BitVec 8 → Bool)}
    (heach : ∀ e, each = some e → ∀ fd bs, bs.all (e fd) = true → R fd bs)
    {said : List (BitVec 64 × List (BitVec 8))}
    (hsaid : SaidOk Ψ said) : PreSound fetch sys Ψ (outDesc Q R) (preOut said q r each) := by
  intro Γ ρ h n Ψ' he hwf s hw
  simp only [preOut, Bool.and_eq_true] at h
  exact ⟨preExits_sound hq Γ ρ h.1 n Ψ' he hwf s hw, preWrites_holds hr heach hsaid h.2 he hw⟩

/-- **A program that checks against both is safe under Linux, ends only
with a status as wanted, and offers at every `write` it reaches a
descriptor and bytes as wanted**: started in a state that matches under a
memory typing with the blocks it is typed under and maybe more. -/
theorem outputs_of_checked {Q : BitVec 32 → Prop} {q : BitVec 32 → Bool}
    (hq : ∀ c, q c = true → Q c) {R : BitVec 64 → List (BitVec 8) → Prop}
    {r : BitVec 64 → List (BitVec 8) → Bool} (hr : ∀ fd bs, r fd bs = true → R fd bs)
    {each : Option (BitVec 64 → BitVec 8 → Bool)}
    (heach : ∀ e, each = some e → ∀ fd bs, bs.all (e fd) = true → R fd bs)
    {said : List (BitVec 64 × List (BitVec 8))} (hsaid : SaidOk Ψ said)
    {pg : Prog} {labels : List Label} {fuel k : Nat} (hpg : pg.pre = preOut said q r each)
    (hcode : ∀ e ∈ pg.code, fetch e.1 = some (e.2.1, e.2.2)) (hk : KindsOk Ψ pg.kinds)
    (hst : StaticsOk fetch ((linux.exitsOnly Q).writesOnly R) Ψ pg.statics) {Ψ₂ : MemTy}
    (hext : Ψ.Ext Ψ₂) (hwf : Ψ₂.WF)
    (h : checkProgram pg labels fuel k = true)
    {l : Label} (hl : l ∈ labels) {s : State} (hrip : s.rip = l.addr) (ρ : Env) (fam : Fam)
    (hfn : ρ.fn = pg.fns) (hlaws : LawsHold pg.fns pg.laws)
    (hw : ∀ n, (∀ l' ∈ labels, ∀ (ρ' : Env) (fam' : Fam), ρ'.fn = pg.fns →
        Ok fetch ((linux.exitsOnly Q).writesOnly R) Ψ n l'.addr
          (l'.pat.den { ρ' with bound := fam' :: ρ'.bound })) →
      WellTyped fetch ((linux.exitsOnly Q).writesOnly R) Ψ₂ n
        (l.pat.den { ρ with bound := fam :: ρ.bound }) s) :
    Safe fetch linux s ∧
      (∀ s', TypedAsm.Steps fetch linux s s' → ∀ len c, fetch s'.rip = some (.syscall, len) →
        linux { s' with rip := s'.rip + len } = .exit c → Q c) ∧
      (∀ s', TypedAsm.Steps fetch linux s s' → ∀ len, fetch s'.rip = some (.syscall, len) →
        s'.getReg .rax = 1 → R (s'.getReg .rdi) s'.offered) :=
  have hW := Safe.of_writesOnly
    (safe_of_checked_ext (D := outDesc Q R) ((linux_describes.exitsOnly Q).writesOnly R) rfl
      (by rw [hpg]; exact preOut_sound hq hr heach hsaid) hcode hk hst hext hwf hlaws h hl hrip ρ fam hfn
      hw)
  have hE := Safe.of_exitsOnly hW.1
  ⟨hE.1, hE.2, fun s' hs' len hf hax => hW.2 s' hs'.exitsOnly len hf hax⟩

end TypedAsm.U
