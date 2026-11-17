import TypedAsm.U.FindFact
import TypedAsm.U.FlagsS
import TypedAsm.U.RegardS
import TypedAsm.U.Bridge
import TypedAsm.U.Guard

/-!
# The checker's step

One function, for every instruction that is described. It reads the
description: the registers used, the bytes read and written, and where they
are. The bytes are found among the regions the context holds, by the
address as a term. What is read is the value the region holds there, or a
value the context does not say, which is given a name. Each register
written holds the term for what the instruction gives it. What is written
is put where it goes. And the address control goes to is given, as a term.

It is proved to be what the one statement that types every instruction
gives, for the machine.
-/

namespace TypedAsm.U

open TypedAsm

/-- The value a region holds at a byte, if it holds one there. -/
def HeldS.slotAt (S : HeldS) (o : Nat) : Option Val :=
  match S.slots.find? fun p => p.1 = o with
  | some p => some p.2
  | none => none

theorem HeldS.slotAt_mem {S : HeldS} {o : Nat} {v : Val} (h : S.slotAt o = some v) :
    (o, v) ∈ S.slots := by
  unfold HeldS.slotAt at h
  split at h
  · next p hp =>
    cases h
    have hm := List.mem_of_find?_eq_some hp
    have ho := List.find?_some hp
    simp only [decide_eq_true_eq] at ho
    rw [← ho]
    exact hm
  · cases h

/-- A region with `n` of its bytes, from `o`, given a value: as `heldPut`. -/
def HeldS.put (S : HeldS) (o n : Nat) (v : Val) : HeldS :=
  if n = 8 then ⟨S.size, (o, v) :: S.slots.filter (ShapeOf.clearOf o 8)⟩
  else ⟨S.size, S.slots.filter (ShapeOf.clearOf o n)⟩

theorem HeldS.put_den (ρ : Env) (S : HeldS) (o n : Nat) (v : Val) :
    (S.put o n v).den ρ = heldPut (S.den ρ) o n (v.den ρ) := by
  have key : ∀ m, (S.slots.filter (ShapeOf.clearOf o m)).map (fun p => (p.1, p.2.den ρ))
      = (S.slots.map fun p => (p.1, p.2.den ρ)).filter (ShapeOf.clearOf o m) := by
    intro m
    rw [List.filter_map]
    rfl
  unfold HeldS.put heldPut
  split
  · show (⟨S.size, _⟩ : Held) = ShapeOf.set (S.den ρ) o (v.den ρ)
    simp only [ShapeOf.set, ShapeOf.clear, HeldS.den, List.map_cons, key]
  · show (⟨S.size, _⟩ : Held) = ShapeOf.clear (S.den ρ) o n
    simp only [ShapeOf.clear, HeldS.den, key]

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

theorem Reads.mono {Γ : Ctx} {a : BitVec 64} {n : Nat} {P P' : BitVec 64 → Ctx → Prop}
    (h : Reads fetch sys Ψ Γ a n P) (hP : ∀ x Δ, P x Δ → P' x Δ) : Reads fetch sys Ψ Γ a n P' := by
  intro k Ψ' he hwf s hw
  obtain ⟨hr, Γr, hp, hv, hf, hw'⟩ := h k Ψ' he hwf s hw
  exact ⟨hr, Γr, hP _ _ hp, hv, hf, hw'⟩

/-- A region the context holds, as terms, is one it holds. -/
theorem CtxS.held_den (ρ : Env) (Γ : CtxS) {j : Nat} {b : Val} {S : HeldS}
    (h : Γ.held[j]? = some (b, S)) : (Γ.den ρ).held[j]? = some (b.den ρ, S.den ρ) := by
  show ((Γ.held.map fun b => (b.1.den ρ, b.2.den ρ)) ++ restDen ρ Γ.rest)[j]? = _
  have hj : j < (Γ.held.map fun b => (b.1.den ρ, b.2.den ρ)).length := by
    rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp h).1
  rw [List.getElem?_append_left hj, List.getElem?_map, h]
  rfl

/-- The term for the bytes an instruction reads, and what reading them
tells. Nothing where it reads none. In a region the context holds: the value
held there, where one is held at those eight bytes, and otherwise the name
`k`, for a value the context does not say. In a block a value is known to
point into: the name `k`, of which is then known what the block's shape
says is at those bytes. -/
def readCell (Γ : CtxS) (k : Nat) (next : BitVec 64) :
    Option (Mem × Nat) → Option (Val × List (Val × TyS))
  | none => some (.lit 0, [])
  | some (m, n) =>
    match findHeld (eaS Γ.regs next m) n Γ.held 0 with
    | some (_, _, S, o) =>
      if n = 8 then
        match S.slotAt o with
        | some v => some (v, [])
        | none => some (.var k, [])
      else some (.var k, [])
    | none =>
      match findFact (eaS Γ.regs next m) n Γ.known with
      | some (_, Sh, _, _, o) => some (.var k, readFactsS Sh o n (.var k))
      | none => none

theorem readCell_sound {ρ : Env} {Γ : CtxS} {k : Nat} {next : BitVec 64} {cell : Val}
    {extra : List (Val × TyS)} (hu : Γ.under k = true) :
    (rd : Option (Mem × Nat)) → readCell Γ k next rd = some (cell, extra) →
    match rd with
    | some (m, n) => Reads fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) n
        (fun x Γr => Γr = CtxS.den (ρ.setVal k x) { Γ with known := extra ++ Γ.known } ∧
          cell.den (ρ.setVal k x) = x)
    | none => extra = [] ∧ cell.den (ρ.setVal k 0) = 0
  | none, h => by cases h; exact ⟨rfl, rfl⟩
  | some (m, n), h => by
    simp only [readCell] at h
    split at h
    · next j b S o hfind =>
      obtain ⟨i, hi, hl, hin, ha⟩ := findHeld_spec (ρ := ρ) Γ.held 0 hfind
      have haddr : eaOf (Γ.den ρ).val next m = b.den ρ + BitVec.ofNat 64 o := by
        rw [← eaS_den]; exact ha
      show Reads fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) n _
      rw [haddr]
      refine (Reads.held (CtxS.held_den ρ Γ hl) hin).mono ?_
      rintro x Γr ⟨rfl, hslot⟩
      -- nothing is learnt, and the context is as it was
      have key : ∀ c : Val, c.den (ρ.setVal k x) = x → (some (c, ([] : List (Val × TyS))) = some (cell, extra)) →
          Γ.den ρ = CtxS.den (ρ.setVal k x) { Γ with known := extra ++ Γ.known } ∧
            cell.den (ρ.setVal k x) = x := by
        intro c hc he
        cases he
        exact ⟨(CtxS.den_setVal ρ k x Γ hu).symm, hc⟩
      split at h
      · next h8 =>
        split at h
        · next v hv =>
          have hm := HeldS.slotAt_mem hv
          have hx := hslot h8 (v.den ρ) (by
            show (o, v.den ρ) ∈ S.slots.map _
            exact List.mem_map.mpr ⟨(o, v), hm, rfl⟩)
          -- the slot's term mentions no name from `k` on
          have hcu : v.under k = true := by
            simp only [CtxS.under, heldUnder, Bool.and_eq_true, List.all_eq_true] at hu
            exact (hu.1.1.2 (b, S) (List.mem_of_getElem? hl)).2 (o, v) hm
          exact key v (by rw [Val.den_setVal ρ k x _ hcu]; exact hx.symm) h
        · exact key (.var k) (Env.setVal_get_self ρ k x) h
      · exact key (.var k) (Env.setVal_get_self ρ k x) h
    · split at h
      · next p Sh w off o hfind =>
        cases h
        obtain ⟨hmem, hin, ha⟩ := findFact_spec (ρ := ρ) Γ.known hfind
        have hf : (p.den ρ, Ty.ptr (Sh.den ρ) w off) ∈ (Γ.den ρ).known :=
          List.mem_map.mpr ⟨(p, .ptr Sh w off), hmem, rfl⟩
        have haddr : eaOf (Γ.den ρ).val next m + BitVec.ofNat 64 off
            = p.den ρ + BitVec.ofNat 64 o := by
          rw [← eaS_den]; exact ha
        refine (Reads.shared hf haddr (by rw [ShapeS.den_size]; exact hin)).mono ?_
        rintro x Γr rfl
        refine ⟨?_, Env.setVal_get_self ρ k x⟩
        have hΓ := CtxS.den_setVal ρ k x Γ hu
        refine ctx_ext (congrArg CtxOf.val hΓ).symm (congrArg CtxOf.flags hΓ).symm
          (congrArg CtxOf.held hΓ).symm ?_
        show readFacts (Sh.den ρ) o n x ++ (Γ.den ρ).known
          = (readFactsS Sh o n (.var k) ++ Γ.known).map _
        have hSh : Sh.under k = true := by
          have hu' := hu
          simp only [CtxS.under, Bool.and_eq_true, List.all_eq_true] at hu'
          simpa only [TyS.under] using (hu'.1.2 _ hmem).2
        rw [List.map_append, readFactsS_den, ShapeS.den_setVal ρ k x Sh hSh]
        congr 1
        · show _ = readFacts (Sh.den ρ) o n ((Val.var k).den (ρ.setVal k x))
          rw [show (Val.var k).den (ρ.setVal k x) = x from Env.setVal_get_self ρ k x]
        · exact (congrArg CtxOf.known hΓ).symm
      · cases h

/-- Whether each typed value of a block keeps clear of the `n` bytes written
at `o`, or is the eight bytes written, with a value that is of its type:
of itself, or by something known of it. -/
def valsOkS (Γ : CtxS) (v : Val) (o n : Nat) : ValsS → Bool
  | .nil => true
  | .cons q τ rest =>
    (decide (q + 8 ≤ o) || decide (o + n ≤ q) ||
      (n == 8 && q == o &&
        (outright v τ || Γ.known.any fun g => g.1.same v && followsS g.2 τ))) &&
    valsOkS Γ v o n rest

theorem valsOkS_sound (ρ : Env) {Γ : CtxS} {v : Val} {o n : Nat} :
    (vs : ValsS) → valsOkS Γ v o n vs = true → ∀ q ∈ vs.den ρ,
    (q.1 + 8 ≤ o ∨ o + n ≤ q.1) ∨
      (n = 8 ∧ q.1 = o ∧ ∀ (Ψ' : MemTy) (k : Nat),
        (∀ g ∈ (Γ.den ρ).known, HasTy fetch sys Ψ' k g.2 g.1) →
        HasTy fetch sys Ψ' k q.2 (v.den ρ))
  | .nil, _, q, hq => nomatch hq
  | .cons q₀ τ rest, h, q, hq => by
    simp only [valsOkS, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hq with rfl | hq
    · have h1 := h.1
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
        List.any_eq_true] at h1
      rcases h1 with (h1 | h1) | ⟨⟨h8, hqo⟩, hty⟩
      · exact .inl (.inl h1)
      · exact .inl (.inr h1)
      · refine .inr ⟨h8, hqo, fun Ψ' k hg => ?_⟩
        rcases hty with hout | ⟨g, hgm, hsame, hfol⟩
        · exact outright_hasTy ρ Ψ' k v τ hout
        · have hsrc := hg (g.1.den ρ, g.2.den ρ) (List.mem_map.mpr ⟨g, hgm, rfl⟩)
          show HasTy fetch sys Ψ' k (τ.den ρ) (v.den ρ)
          rw [← Val.same_den ρ hsame]
          exact hsrc.sub (followsS_sub ρ _ _ _ hfol)
    · exact valsOkS_sound ρ rest h.2 q hq

/-- What the context holds once an instruction has written its bytes. In a
region held: the region holds the value written there. In a block a value
is known to point into, through a pointer that may be written through: what
is held is as it was, the block still holding what its shape says. -/
def writeCell (Γ : CtxS) (next : BitVec 64) (v : Val) :
    Option (Mem × Nat) → Option (List (Val × HeldS))
  | none => some Γ.held
  | some (m, n) =>
    match findHeld (eaS Γ.regs next m) n Γ.held 0 with
    | some (j, b, S, o) => if n ≤ 8 then some (Γ.held.set j (b, S.put o n v)) else none
    | none =>
      match findFact (eaS Γ.regs next m) n Γ.known with
      | some (_, Sh, w, _, o) =>
        if w && decide (n ≤ 8) && valsOkS Γ v o n Sh.vals then some Γ.held else none
      | none => none

theorem writeCell_sound {ρ : Env} {Γ : CtxS} {next : BitVec 64} {v : Val}
    {held' : List (Val × HeldS)} :
    (wr : Option (Mem × Nat)) → writeCell Γ next v wr = some held' →
    match wr with
    | some (m, n) => Writes fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) n (v.den ρ)
        (CtxS.den ρ { Γ with held := held' })
    | none => held' = Γ.held
  | none, h => by cases h; rfl
  | some (m, n), h => by
    simp only [writeCell] at h
    split at h
    · next j b S o hfind =>
      split at h
      · next hn =>
        cases h
        obtain ⟨i, hi, hl, hin, ha⟩ := findHeld_spec (ρ := ρ) Γ.held 0 hfind
        have hji : j = i := by omega
        subst hji
        have haddr : eaOf (Γ.den ρ).val next m = b.den ρ + BitVec.ofNat 64 o := by
          rw [← eaS_den]; exact ha
        show Writes fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) n (v.den ρ) _
        rw [haddr]
        have hW := Writes.held (fetch := fetch) (sys := sys) (Ψ := Ψ) (v.den ρ)
          (CtxS.held_den ρ Γ hl) hin hn
        have e : CtxS.den ρ { Γ with held := Γ.held.set j (b, S.put o n v) }
            = { Γ.den ρ with
                held := (Γ.den ρ).held.set j (b.den ρ, heldPut (S.den ρ) o n (v.den ρ)) } := by
          refine ctx_ext rfl rfl ?_ rfl
          show (Γ.held.set j (b, S.put o n v)).map (fun b => (b.1.den ρ, b.2.den ρ))
              ++ restDen ρ Γ.rest
            = ((Γ.held.map fun b => (b.1.den ρ, b.2.den ρ)) ++ restDen ρ Γ.rest).set j _
          have hj : j < (Γ.held.map fun b => (b.1.den ρ, b.2.den ρ)).length := by
            rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hl).1
          rw [List.set_append_left _ _ hj, List.map_set, HeldS.put_den]
        rw [e]
        exact hW
      · cases h
    · split at h
      · next p Sh w off o hfind =>
        split at h
        · next hc =>
          cases h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          obtain ⟨⟨hw, hn⟩, hvals⟩ := hc
          subst hw
          obtain ⟨hmem, hin, ha⟩ := findFact_spec (ρ := ρ) Γ.known hfind
          have hf : (p.den ρ, Ty.ptr (Sh.den ρ) true off) ∈ (Γ.den ρ).known :=
            List.mem_map.mpr ⟨(p, .ptr Sh true off), hmem, rfl⟩
          have haddr : eaOf (Γ.den ρ).val next m + BitVec.ofNat 64 off
              = p.den ρ + BitVec.ofNat 64 o := by
            rw [← eaS_den]; exact ha
          show Writes fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) n (v.den ρ) (Γ.den ρ)
          exact Writes.shared (v.den ρ) hf haddr (by rw [ShapeS.den_size]; exact hin) hn
            (by rw [ShapeS.den_vals]; exact valsOkS_sound ρ Sh.vals hvals)
        · cases h
      · cases h

/-- The term for the address an instruction uses as a number. -/
def eaTerm (Γ : CtxS) (next : BitVec 64) : Option Mem → Val
  | some m => eaS Γ.regs next m
  | none => .lit 0

theorem eaTerm_den (ρ : Env) (Γ : CtxS) (next : BitVec 64) (ea : Option Mem) :
    (eaTerm Γ next ea).den ρ = (ea.map (eaOf (Γ.den ρ).val next)).getD 0 := by
  cases ea with
  | none => rfl
  | some m => exact eaS_den ρ Γ next m

/-- The term for the `j`th register an instruction uses stands for that
register's value. -/
theorem argAt_den (ρ : Env) (Γ : CtxS) (srcs : List Reg) (j : Nat) :
    (argAt Γ.regs srcs j).den ρ = (srcs.map (Γ.den ρ).val).getD j 0 := by
  unfold argAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases srcs[j]? <;> rfl

/-- What an instruction computes with, as the context's terms. -/
def fillOf (Γ : CtxS) (srcs : List Reg) (next : BitVec 64) (ea cell : Val) : Filling where
  slot
    | .arg j => argAt Γ.regs srcs j
    | .cell => cell
    | .ea => ea
    | .next => .lit next
  old := Γ.flags

/-- **An instruction's terms, filled in with the context's, stand for what
its description computes from what the context says.** -/
theorem fill_den {ρ ρ' : Env} {Γ : CtxS} (s : Sem) (next : BitVec 64) {cell : Val} {x : BitVec 64}
    (hΓ : Γ.den ρ' = Γ.den ρ) (hx : cell.den ρ' = x) :
    (∀ t : Val, t.slotOnly = true →
      (t.fillN (fillOf Γ s.srcs next (eaTerm Γ next s.ea) cell)).den ρ'
        = t.den (slotEnv (s.srcs.map (Γ.den ρ).val) (Γ.den ρ).flags next
            ((s.ea.map (eaOf (Γ.den ρ).val next)).getD 0) x)) ∧
    (∀ f : FlagsT, f.slotOnly = true →
      (f.fill (fillOf Γ s.srcs next (eaTerm Γ next s.ea) cell)).den ρ'
        = f.den (slotEnv (s.srcs.map (Γ.den ρ).val) (Γ.den ρ).flags next
            ((s.ea.map (eaOf (Γ.den ρ).val next)).getD 0) x)) := by
  have hs : (ρ'.filled (fillOf Γ s.srcs next (eaTerm Γ next s.ea) cell)).slot
      = (slotEnv (s.srcs.map (Γ.den ρ).val) (Γ.den ρ).flags next
          ((s.ea.map (eaOf (Γ.den ρ).val next)).getD 0) x).slot := by
    funext sl
    cases sl with
    | arg j =>
      show (argAt Γ.regs s.srcs j).den ρ' = (s.srcs.map (Γ.den ρ).val).getD j 0
      rw [← hΓ]
      exact argAt_den ρ' Γ s.srcs j
    | cell => exact hx
    | ea =>
      show (eaTerm Γ next s.ea).den ρ' = _
      rw [eaTerm_den, hΓ]
      rfl
    | next => rfl
  have ho : (ρ'.filled (fillOf Γ s.srcs next (eaTerm Γ next s.ea) cell)).old
      = (slotEnv (s.srcs.map (Γ.den ρ).val) (Γ.den ρ).flags next
          ((s.ea.map (eaOf (Γ.den ρ).val next)).getD 0) x).old :=
    congrArg CtxOf.flags hΓ
  exact ⟨fun t ht => (Val.den_fillN ρ' _ t).trans (Val.den_slots hs ho t ht),
    fun f hf => (FlagsT.den_fill ρ' _ f).trans (FlagsT.den_slots hs ho f hf)⟩

/-- The registers with those an instruction writes given its terms, filled
in; the later winning. -/
def setRegs (σ : Filling) : List (Reg × Val) → Regs Val → Regs Val
  | [], m => m
  | p :: l, m => setRegs σ l (m.set p.1 (p.2.fillN σ))

theorem setRegs_den (ρ : Env) (σ : Filling) :
    (l : List (Reg × Val)) → (m : Regs Val) → (f : Reg → BitVec 64) →
    (∀ r, (m.get r).den ρ = f r) →
    ∀ r, ((setRegs σ l m).get r).den ρ
      = (l.map fun p => (p.1, (p.2.fillN σ).den ρ)).foldl
          (fun f p => fun r => if r = p.1 then p.2 else f r) f r
  | [], _, _, hm, r => hm r
  | p :: l, m, f, hm, r => by
    refine setRegs_den ρ σ l (m.set p.1 (p.2.fillN σ)) _ (fun r' => ?_) r
    show ((m.set p.1 (p.2.fillN σ)).get r').den ρ
      = if r' = p.1 then (p.2.fillN σ).den ρ else f r'
    rw [Regs.get_set]
    split
    · rfl
    · exact hm r'

/-- **The checker's step.** The context after an instruction, and the term
for where control goes. `k` is a name no term yet mentions, for what is
read where the context does not say. -/
def stepHeld (Γ : CtxS) (k : Nat) (next : BitVec 64) (i : Instr) : Option (CtxS × Val) :=
  match i.sem with
  | some s =>
    match readCell Γ k next s.rd with
    | some (cell, extra) =>
      let Γ₁ : CtxS := { Γ with known := extra ++ Γ.known }
      let σ := fillOf Γ s.srcs next (eaTerm Γ next s.ea) cell
      if !s.guard.okS Γ₁ Γ.flags (s.ga.fillN σ) (s.gb.fillN σ) (s.gc.fillN σ) then none else
      match writeCell Γ₁ next (s.store.fillN σ) s.wr with
      | some held' =>
        some ({ Γ₁ with
                regs := setRegs σ s.outs Γ.regs
                flags := s.flags.fill σ
                held := held' },
          match s.goes with
          | some t => t.fillN σ
          | none => .lit next)
      | none => none
    | none => none
  | none => none

theorem stepHeld_sound {ρ : Env} {Γ Γ' : CtxS} {k : Nat} {next : BitVec 64} {i : Instr} {t : Val}
    (h : stepHeld Γ k next i = some (Γ', t)) (hu : Γ.under k = true) :
    Steps fetch sys Ψ i next (Γ.den ρ) fun t' Δ =>
      ∃ x, t' = t.den (ρ.setVal k x) ∧ Δ = Γ'.den (ρ.setVal k x) := by
  unfold stepHeld at h
  cases hsem : i.sem with
  | none => rw [hsem] at h; cases h
  | some s =>
    rw [hsem] at h
    simp only at h
    have hd : i.desc = some s.toDesc := by rw [← sem_desc, hsem]; rfl
    have hso := sem_slotOnly hsem
    simp only [Sem.slotOnly, Bool.and_eq_true] at hso
    obtain ⟨⟨⟨⟨⟨⟨hga, hgb⟩, hgc⟩, houts⟩, hflags⟩, hstore⟩, hgoes⟩ := hso
    split at h
    · next cell extra hrc =>
      have hgd : s.guard.okS { Γ with known := extra ++ Γ.known } Γ.flags
          (s.ga.fillN (fillOf Γ s.srcs next (eaTerm Γ next s.ea) cell))
          (s.gb.fillN (fillOf Γ s.srcs next (eaTerm Γ next s.ea) cell))
          (s.gc.fillN (fillOf Γ s.srcs next (eaTerm Γ next s.ea) cell)) = true := by
        cases hq : s.guard.okS { Γ with known := extra ++ Γ.known } Γ.flags
          (s.ga.fillN (fillOf Γ s.srcs next (eaTerm Γ next s.ea) cell))
          (s.gb.fillN (fillOf Γ s.srcs next (eaTerm Γ next s.ea) cell))
          (s.gc.fillN (fillOf Γ s.srcs next (eaTerm Γ next s.ea) cell)) with
        | true => rfl
        | false =>
          simp only [hq, Bool.not_false, ↓reduceIte] at h
          cases h
      simp only [hgd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · next held' hwc =>
        cases h
        have hR := readCell_sound (fetch := fetch) (sys := sys) (Ψ := Ψ) (ρ := ρ) hu s.rd hrc
        refine Steps.mono (Steps.desc
          (R := fun x Γr => Γr = CtxS.den (ρ.setVal k x) { Γ with known := extra ++ Γ.known } ∧
            cell.den (ρ.setVal k x) = x)
          (W := fun x _ Γw => Γw = CtxS.den (ρ.setVal k x)
            { Γ with known := extra ++ Γ.known, held := held' }) hd ?_ ?_ ?_) ?_
        · show match s.rd with
            | some (m, n) => _
            | none => _
          cases hrd : s.rd with
          | none =>
            rw [hrd] at hR
            obtain ⟨he, hc⟩ := hR
            subst he
            exact ⟨(CtxS.den_setVal ρ k 0 Γ hu).symm, hc⟩
          | some mn => rw [hrd] at hR; exact hR
        · rintro x Γr ⟨rfl, hx⟩
          refine ⟨_, rfl, ?_⟩
          have hΓ : Γ.den (ρ.setVal k x) = Γ.den ρ := CtxS.den_setVal ρ k x Γ hu
          have hval : (CtxS.den (ρ.setVal k x) { Γ with known := extra ++ Γ.known }).val
              = (Γ.den ρ).val := (congrArg CtxOf.val hΓ : (Γ.den (ρ.setVal k x)).val = _)
          have hW := writeCell_sound (fetch := fetch) (sys := sys) (Ψ := Ψ) (ρ := ρ.setVal k x)
            (Γ := { Γ with known := extra ++ Γ.known }) s.wr hwc
          show match s.wr with
            | some (m, n) => _
            | none => _
          cases hwr : s.wr with
          | none =>
            rw [hwr] at hW
            show CtxS.den (ρ.setVal k x) { Γ with known := extra ++ Γ.known, held := held' } = _
            rw [hW]
          | some mn =>
            obtain ⟨m, n⟩ := mn
            rw [hwr] at hW
            rw [(fill_den s next hΓ hx).1 _ hstore, hval] at hW
            exact hW
        · rintro x Γr ⟨rfl, hx⟩ Ψ' n hk
          have hΓ : Γ.den (ρ.setVal k x) = Γ.den ρ := CtxS.den_setVal ρ k x Γ hu
          have hfill := fill_den s next hΓ hx
          have hok := GuardE.okS_den (ρ := ρ.setVal k x) hgd hk
          rw [hfill.1 _ hga, hfill.1 _ hgb, hfill.1 _ hgc] at hok
          have hfl : Γ.flags.den (ρ.setVal k x) = (Γ.den ρ).flags := congrArg CtxOf.flags hΓ
          rw [hfl] at hok
          exact hok
        · rintro t' Δ ⟨x, Γr, Γw, ⟨rfl, hx⟩, rfl, rfl, rfl⟩
          have hΓ : Γ.den (ρ.setVal k x) = Γ.den ρ := CtxS.den_setVal ρ k x Γ hu
          have hfill := fill_den s next hΓ hx
          refine ⟨x, ?_, ?_⟩
          · show (Option.map _ s.goes).getD next = _
            cases hgo : s.goes with
            | none => rfl
            | some tg =>
              rw [hgo] at hgoes
              exact (hfill.1 tg hgoes).symm
          · refine ctx_ext ?_ ?_ rfl rfl
            · funext r
              show List.foldl _ (Γ.den (ρ.setVal k x)).val (s.outs.map _) r
                = ((setRegs _ s.outs Γ.regs).get r).den (ρ.setVal k x)
              rw [setRegs_den (ρ.setVal k x) _ s.outs Γ.regs (Γ.den (ρ.setVal k x)).val
                (fun _ => rfl) r]
              refine congrFun (congrArg _ (List.map_congr_left fun p hp => ?_)) r
              rw [hfill.1 p.2 (List.all_eq_true.mp houts p hp)]
              rfl
            · exact (hfill.2 s.flags hflags).symm
      · cases h
    · cases h

end TypedAsm.U
