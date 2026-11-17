import TypedAsm.U.FindFact
import TypedAsm.U.FlagsS
import TypedAsm.U.RegardS
import TypedAsm.U.Bridge
import TypedAsm.U.Guard
import TypedAsm.U.Text
import TypedAsm.U.Span

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

/-- The fact a context has that an address is a pointer to text: the first,
of a value the address is. With what says whether there is more. -/
def findStr (a : Val) : List (Val × TyS) → Option (Val × Val)
  | [] => none
  | (q, .str c) :: rest => if q.same a then some (q, c) else findStr a rest
  | _ :: rest => findStr a rest

theorem findStr_spec {a : Val} : (l : List (Val × TyS)) → {q c : Val} →
    findStr a l = some (q, c) → (q, TyS.str c) ∈ l ∧ q.same a = true
  | [], _, _, h => by cases h
  | (p, τ) :: rest, q, c, h => by
    have tail : findStr a rest = some (q, c) → (q, TyS.str c) ∈ (p, τ) :: rest ∧ q.same a = true :=
      fun h' => ⟨List.mem_cons_of_mem _ (findStr_spec rest h').1, (findStr_spec rest h').2⟩
    cases τ with
    | str c' =>
      simp only [findStr] at h
      split at h
      · next hs => cases h; exact ⟨List.mem_cons_self, hs⟩
      · exact tail h
    | _ => exact tail h

/-- A term for so many bytes read: no more than so many bytes, which the
term says by the operator at its head. -/
def narrow (n : Nat) (x : Val) : Val :=
  match n with
  | 1 => .un .low8 x
  | 2 => .un .low16 x
  | 4 => .un (.trunc .w32) x
  | _ => x

theorem narrow_den (ρ : Env) (n : Nat) (x : Val) : (narrow n x).den ρ = cutN n (x.den ρ) := by
  by_cases h1 : n = 1
  · subst h1; rfl
  · by_cases h2 : n = 2
    · subst h2; rfl
    · by_cases h4 : n = 4
      · subst h4; rfl
      · unfold narrow cutN
        split <;> first | contradiction | (split <;> first | contradiction | rfl)

/-- The term for the bytes an instruction reads, and what reading them
tells. Nothing where it reads none. In a region the context holds: the value
held there, where one is held at those eight bytes, and otherwise the name
`k`, for a value the context does not say. In a block a value is known to
point into: the name `k`, of which is then known what the block's shape
says is at those bytes. A byte of text, through a pointer to text: the name
`k`, and of the pointer it is then known that there is more unless that
byte is nought. -/
def readCell (kinds : Nat → Option ShapeS) (Γ : CtxS) (k : Nat) (next : BitVec 64) :
    Option (Mem × Nat) → Option (Val × List (Val × TyS))
  | none => some (.lit 0, [])
  | some (m, n) =>
    match findHeld (eaS Γ.regs next m) n Γ.held 0 with
    | some (_, _, S, o) =>
      if n = 8 then
        match S.slotAt o with
        | some v => some (v, [])
        | none => some (.var k, [])
      else some (narrow n (.var k), [])
    | none =>
      match findFact kinds (eaS Γ.regs next m) n Γ.known with
      | some (_, Sh, _, _, o) => some (narrow n (.var k), readFactsS Sh o n (.var k))
      | none =>
        if n = 1 then
          match findStr (eaS Γ.regs next m) Γ.known with
          | some (q, _) => some (narrow 1 (.var k), [(q, .str (narrow 1 (.var k)))])
          | none => none
        else none

theorem readCell_sound {ρ : Env} {kinds : Nat → Option ShapeS} (hk : KindsOk Ψ kinds) {Γ : CtxS}
    {k : Nat} {next : BitVec 64} {cell : Val}
    {extra : List (Val × TyS)} (hu : Γ.under k = true) :
    (rd : Option (Mem × Nat)) → readCell kinds Γ k next rd = some (cell, extra) →
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
      refine (Reads.held (CtxS.held_den ρ Γ hl) hin).narrow.mono ?_
      rintro x Γr ⟨⟨rfl, hslot⟩, hcut⟩
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
      · exact key (narrow n (.var k))
          (by rw [narrow_den, show (Val.var k).den (ρ.setVal k x) = x from
            Env.setVal_get_self ρ k x]; exact hcut) h
    · split at h
      · next p Sh w off o hfind =>
        cases h
        obtain ⟨τ, hmem, hpt, hin, ha⟩ := findFact_spec (ρ := ρ) Γ.known hfind
        have hf : (p.den ρ, τ.den ρ) ∈ (Γ.den ρ).known :=
          List.mem_map.mpr ⟨(p, τ), hmem, rfl⟩
        have haddr : eaOf (Γ.den ρ).val next m + BitVec.ofNat 64 off
            = p.den ρ + BitVec.ofNat 64 o := by
          rw [← eaS_den]; exact ha
        refine (Reads.shared hf (TyS.pointee_den hk ρ hpt) haddr (by rw [ShapeS.den_size]; exact hin)).narrow.mono ?_
        rintro x Γr ⟨rfl, hcut⟩
        refine ⟨?_, by rw [narrow_den, show (Val.var k).den (ρ.setVal k x) = x from
          Env.setVal_get_self ρ k x]; exact hcut⟩
        have hΓ := CtxS.den_setVal ρ k x Γ hu
        refine ctx_ext (congrArg CtxOf.val hΓ).symm (congrArg CtxOf.flags hΓ).symm
          (congrArg CtxOf.held hΓ).symm ?_
        show readFacts (Sh.den ρ) o n x ++ (Γ.den ρ).known
          = (readFactsS Sh o n (.var k) ++ Γ.known).map _
        have hSh : Sh.den (ρ.setVal k x) = Sh.den ρ := by
          have hu' := hu
          simp only [CtxS.under, Bool.and_eq_true, List.all_eq_true] at hu'
          exact TyS.pointee_setVal hk ρ k x (hu'.1.2 _ hmem).2 hpt
        rw [List.map_append, readFactsS_den, hSh]
        congr 1
        · show _ = readFacts (Sh.den ρ) o n ((Val.var k).den (ρ.setVal k x))
          rw [show (Val.var k).den (ρ.setVal k x) = x from Env.setVal_get_self ρ k x]
        · exact (congrArg CtxOf.known hΓ).symm
      · split at h
        · next h1 =>
          subst h1
          split at h
          · next q c hstr =>
            cases h
            obtain ⟨hmem, hsame⟩ := findStr_spec Γ.known hstr
            have hf : (q.den ρ, Ty.str (c.den ρ)) ∈ (Γ.den ρ).known :=
              List.mem_map.mpr ⟨(q, .str c), hmem, rfl⟩
            have haddr : eaOf (Γ.den ρ).val next m = q.den ρ := by
              rw [← eaS_den]; exact (Val.same_den ρ hsame).symm
            show Reads fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) 1 _
            rw [haddr]
            refine (Reads.text hf).narrow.mono ?_
            rintro x Γr ⟨rfl, hcut⟩
            have hcell : (narrow 1 (.var k)).den (ρ.setVal k x) = x := by
              rw [narrow_den, show (Val.var k).den (ρ.setVal k x) = x from
                Env.setVal_get_self ρ k x]
              exact hcut
            refine ⟨?_, hcell⟩
            have hΓ := CtxS.den_setVal ρ k x Γ hu
            refine ctx_ext (congrArg CtxOf.val hΓ).symm (congrArg CtxOf.flags hΓ).symm
              (congrArg CtxOf.held hΓ).symm ?_
            have hq : q.under k = true := by
              have hu' := hu
              simp only [CtxS.under, Bool.and_eq_true, List.all_eq_true] at hu'
              exact (hu'.1.2 _ hmem).1
            show (q.den ρ, Ty.str x) :: (Γ.den ρ).known
              = (q.den (ρ.setVal k x), Ty.str ((narrow 1 (.var k)).den (ρ.setVal k x)))
                :: (Γ.den (ρ.setVal k x)).known
            rw [hcell, Val.den_setVal ρ k x _ hq, hΓ]
          · cases h
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
def writeCell (kinds : Nat → Option ShapeS) (Γ : CtxS) (next : BitVec 64) (v : Val) :
    Option (Mem × Nat) → Option (List (Val × HeldS))
  | none => some Γ.held
  | some (m, n) =>
    match findHeld (eaS Γ.regs next m) n Γ.held 0 with
    | some (j, b, S, o) => if n ≤ 8 then some (Γ.held.set j (b, S.put o n v)) else none
    | none =>
      match findFact kinds (eaS Γ.regs next m) n Γ.known with
      | some (_, Sh, w, _, o) =>
        if w && decide (n ≤ 8) && valsOkS Γ v o n Sh.vals then some Γ.held else none
      | none => none

theorem writeCell_sound {ρ : Env} {kinds : Nat → Option ShapeS} (hk : KindsOk Ψ kinds) {Γ : CtxS}
    {next : BitVec 64} {v : Val} {held' : List (Val × HeldS)} :
    (wr : Option (Mem × Nat)) → writeCell kinds Γ next v wr = some held' →
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
          obtain ⟨τ, hmem, hpt, hin, ha⟩ := findFact_spec (ρ := ρ) Γ.known hfind
          have hf : (p.den ρ, τ.den ρ) ∈ (Γ.den ρ).known :=
            List.mem_map.mpr ⟨(p, τ), hmem, rfl⟩
          have haddr : eaOf (Γ.den ρ).val next m + BitVec.ofNat 64 off
              = p.den ρ + BitVec.ofNat 64 o := by
            rw [← eaS_den]; exact ha
          show Writes fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) n (v.den ρ) (Γ.den ρ)
          exact Writes.shared (v.den ρ) hf (TyS.pointee_den hk ρ hpt) haddr (by rw [ShapeS.den_size]; exact hin) hn
            (by rw [ShapeS.den_vals]; exact valsOkS_sound ρ Sh.vals hvals)
        · cases h
      · cases h

/-- A region saying nothing of the `n` bytes from `o`. -/
def HeldS.clear (S : HeldS) (o n : Nat) : HeldS :=
  ⟨S.size, S.slots.filter (ShapeOf.clearOf o n)⟩

theorem HeldS.clear_den (ρ : Env) (S : HeldS) (o n : Nat) :
    (S.clear o n).den ρ = (S.den ρ).clear o n := by
  show (⟨S.size, (S.slots.filter (ShapeOf.clearOf o n)).map fun p => (p.1, p.2.den ρ)⟩ : Held)
    = ⟨S.size, (S.slots.map fun p => (p.1, p.2.den ρ)).filter (ShapeOf.clearOf o n)⟩
  rw [List.filter_map]
  rfl


/-- Whether no typed value of a block reaches into the `n` bytes from `o`. -/
def ValsS.free (o n : Nat) : ValsS → Bool
  | .nil => true
  | .cons o' _ rest => (o' + 8 ≤ o || o + n ≤ o') && rest.free o n

theorem ValsS.free_den (ρ : Env) (o n : Nat) :
    (vs : ValsS) → (vs.den ρ).all (ShapeOf.clearOf o n) = vs.free o n
  | .nil => rfl
  | .cons o' τ rest => by
    show (ShapeOf.clearOf o n (o', τ.den ρ) && (rest.den ρ).all _) = _
    rw [ValsS.free_den ρ o n rest]
    rfl

/-! ## An address known only to lie within a stretch -/

/-- The region the context holds that an address lies a stretch into: so far
in, for at most so much more, the bytes asked for inside the region
wherever in the stretch the address is. -/
def findHeldR (Γ : CtxS) (a : Val) (n : Nat) :
    List (Val × HeldS) → Nat → Option (Nat × Val × HeldS × Nat × Nat)
  | [], _ => none
  | (b, S) :: rest, k =>
    match Γ.spanFrom a b with
    | some (o, M) =>
      if o + M + n ≤ S.size then some (k, b, S, o, M) else findHeldR Γ a n rest (k + 1)
    | none => findHeldR Γ a n rest (k + 1)

theorem findHeldR_spec {Γ : CtxS} {a : Val} {n : Nat} :
    (l : List (Val × HeldS)) → (k₀ : Nat) → {k : Nat} → {b : Val} → {S : HeldS} → {o M : Nat} →
    findHeldR Γ a n l k₀ = some (k, b, S, o, M) →
    ∃ j, k = k₀ + j ∧ l[j]? = some (b, S) ∧ o + M + n ≤ S.size ∧ Γ.spanFrom a b = some (o, M)
  | [], _, _, _, _, _, _, h => by cases h
  | (b', S') :: rest, k₀, k, b, S, o, M, h => by
    unfold findHeldR at h
    split at h
    · next o' M' hsp =>
      split at h
      · next hin =>
        cases h
        exact ⟨0, rfl, rfl, hin, hsp⟩
      · obtain ⟨j, hj, hl, hin, ha⟩ := findHeldR_spec rest (k₀ + 1) h
        exact ⟨j + 1, by omega, hl, hin, ha⟩
    · obtain ⟨j, hj, hl, hin, ha⟩ := findHeldR_spec rest (k₀ + 1) h
      exact ⟨j + 1, by omega, hl, hin, ha⟩

/-- The fact a context has that an address lies a stretch into a block
others may point into. -/
def findFactR (kinds : Nat → Option ShapeS) (Γ : CtxS) (a : Val) (n : Nat) :
    List (Val × TyS) → Option (Val × TyS × ShapeS × Bool × Nat × Nat × Nat)
  | [] => none
  | (p, τ) :: rest =>
    match τ.pointee kinds, Γ.spanFrom a p with
    | some (Sh, w, off), some (d, M) =>
      if d + off + M + n ≤ Sh.size then some (p, τ, Sh, w, off, d, M)
      else findFactR kinds Γ a n rest
    | _, _ => findFactR kinds Γ a n rest

theorem findFactR_spec {kinds : Nat → Option ShapeS} {Γ : CtxS} {a : Val} {n : Nat} :
    (l : List (Val × TyS)) → {p : Val} → {τ : TyS} → {Sh : ShapeS} → {w : Bool} →
    {off d M : Nat} → findFactR kinds Γ a n l = some (p, τ, Sh, w, off, d, M) →
    (p, τ) ∈ l ∧ τ.pointee kinds = some (Sh, w, off) ∧ d + off + M + n ≤ Sh.size ∧
      Γ.spanFrom a p = some (d, M)
  | [], _, _, _, _, _, _, _, h => by cases h
  | (q, υ) :: rest, p, τ, Sh, w, off, d, M, h => by
    have tail : findFactR kinds Γ a n rest = some (p, τ, Sh, w, off, d, M) →
        (p, τ) ∈ (q, υ) :: rest ∧ τ.pointee kinds = some (Sh, w, off) ∧
          d + off + M + n ≤ Sh.size ∧ Γ.spanFrom a p = some (d, M) := fun h' => by
      obtain ⟨hm, h1, h2, h3⟩ := findFactR_spec rest h'
      exact ⟨List.mem_cons_of_mem _ hm, h1, h2, h3⟩
    unfold findFactR at h
    split at h
    · next Sh' w' off' d' M' hpt hsp =>
      split at h
      · next hin =>
        cases h
        exact ⟨List.mem_cons_self, hpt, hin, hsp⟩
      · exact tail h
    · exact tail h

/-- The bytes an instruction reads at an address known only to lie within a
stretch: the name `k`, nothing being said of what is there. -/
def readRanged (kinds : Nat → Option ShapeS) (Γ : CtxS) (k : Nat) (next : BitVec 64) :
    Option (Mem × Nat) → Option (Val × List (Val × TyS))
  | none => none
  | some (m, n) =>
    if (findHeldR Γ (eaS Γ.regs next m) n Γ.held 0).isSome ||
        (findFactR kinds Γ (eaS Γ.regs next m) n Γ.known).isSome then
      some (narrow n (.var k), [])
    else none

theorem readRanged_sound {ρ : Env} {kinds : Nat → Option ShapeS} (hk : KindsOk Ψ kinds) {Γ : CtxS}
    {k : Nat} {next : BitVec 64} {cell : Val} {extra : List (Val × TyS)} (hu : Γ.under k = true)
    {m : Mem} {n : Nat} (h : readRanged kinds Γ k next (some (m, n)) = some (cell, extra)) :
    Reads fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) n
      (fun x Γr => Γr = CtxS.den (ρ.setVal k x) { Γ with known := extra ++ Γ.known } ∧
        cell.den (ρ.setVal k x) = x) := by
  simp only [readRanged] at h
  split at h
  · next hc =>
    cases h
    have core : Reads fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) n
        (fun _ Γr => Γr = Γ.den ρ) := by
      intro j Ψ' he hwf s hw
      rcases Bool.or_eq_true_iff.mp hc with hh | hf
      · obtain ⟨⟨i, b, S, o, M⟩, hfind⟩ := Option.isSome_iff_exists.mp hh
        obtain ⟨i', _, hl, hin, hsp⟩ := findHeldR_spec Γ.held 0 hfind
        obtain ⟨o', ha, h1, h2⟩ := CtxS.spanFrom_den hsp hw.known
        have R := Reads.held (fetch := fetch) (sys := sys) (Ψ := Ψ) (CtxS.held_den ρ Γ hl)
          (o := o') (n := n) (by show o' + n ≤ S.size; omega) j Ψ' he hwf s hw
        rw [← eaS_den, ha]
        obtain ⟨hr, Γr, ⟨rfl, _⟩, hv, hfl, hw'⟩ := R
        exact ⟨hr, _, rfl, hv, hfl, hw'⟩
      · obtain ⟨⟨p, τ, Sh, w, off, d, M⟩, hfind⟩ := Option.isSome_iff_exists.mp hf
        obtain ⟨hmem, hpt, hin, hsp⟩ := findFactR_spec Γ.known hfind
        obtain ⟨o', ha, h1, h2⟩ := CtxS.spanFrom_den hsp hw.known
        have hfm : (p.den ρ, τ.den ρ) ∈ (Γ.den ρ).known := List.mem_map.mpr ⟨(p, τ), hmem, rfl⟩
        refine Reads.sharedAt (fetch := fetch) (sys := sys) (Ψ := Ψ) hfm (TyS.pointee_den hk ρ hpt)
          (o := o' + off) ?_ (by rw [ShapeS.den_size]; omega) j Ψ' he hwf s hw
        rw [← eaS_den, ha, BitVec.ofNat_add, BitVec.add_assoc]
    refine core.narrow.mono ?_
    rintro x Γr ⟨rfl, hcut⟩
    exact ⟨(CtxS.den_setVal ρ k x Γ hu).symm, by
      rw [narrow_den, show (Val.var k).den (ρ.setVal k x) = x from Env.setVal_get_self ρ k x]
      exact hcut⟩
  · cases h

/-- What the context holds once an instruction has written its bytes at an
address known only to lie within a stretch: the region holds no value the
stretch reaches into; or, in a block a value is known to point into, the
stretch holds no typed value and the block is as it was. -/
def writeRanged (kinds : Nat → Option ShapeS) (Γ : CtxS) (next : BitVec 64) :
    Option (Mem × Nat) → Option (List (Val × HeldS))
  | none => none
  | some (m, n) =>
    if n ≤ 8 then
      match findHeldR Γ (eaS Γ.regs next m) n Γ.held 0 with
      | some (j, b, S, o, M) => some (Γ.held.set j (b, S.clear o (M + n)))
      | none =>
        match findFactR kinds Γ (eaS Γ.regs next m) n Γ.known with
        | some (_, _, Sh, w, off, d, M) =>
          if w && Sh.vals.free (d + off) (M + n) then some Γ.held else none
        | none => none
    else none

theorem writeRanged_sound {ρ : Env} {kinds : Nat → Option ShapeS} (hk : KindsOk Ψ kinds) {Γ : CtxS}
    {next : BitVec 64} (v : Val) {held' : List (Val × HeldS)} {m : Mem} {n : Nat}
    (h : writeRanged kinds Γ next (some (m, n)) = some held') :
    Writes fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) n (v.den ρ)
      (CtxS.den ρ { Γ with held := held' }) := by
  simp only [writeRanged] at h
  split at h
  · next hn =>
    split at h
    · next j b S o M hfind =>
      cases h
      obtain ⟨i, hi, hl, hin, hsp⟩ := findHeldR_spec Γ.held 0 hfind
      have hji : j = i := by omega
      subst hji
      have e : CtxS.den ρ { Γ with held := Γ.held.set j (b, S.clear o (M + n)) }
          = { Γ.den ρ with
              held := (Γ.den ρ).held.set j (b.den ρ, (S.den ρ).clear o (M + n)) } := by
        refine ctx_ext rfl rfl ?_ rfl
        show (Γ.held.set j (b, S.clear o (M + n))).map (fun b => (b.1.den ρ, b.2.den ρ))
            ++ restDen ρ Γ.rest
          = ((Γ.held.map fun b => (b.1.den ρ, b.2.den ρ)) ++ restDen ρ Γ.rest).set j _
        have hj : j < (Γ.held.map fun b => (b.1.den ρ, b.2.den ρ)).length := by
          rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hl).1
        rw [List.set_append_left _ _ hj, List.map_set, HeldS.clear_den]
      rw [e]
      refine ⟨rfl, rfl, fun k' Ψ' he hwf s hw => ?_⟩
      obtain ⟨o', ha, h1, h2⟩ := CtxS.spanFrom_den hsp hw.known
      have W := Writes.heldIn (fetch := fetch) (sys := sys) (Ψ := Ψ) (v.den ρ)
        (CtxS.held_den ρ Γ hl) (o := o) (o' := o') (L := M + n) (n := n) h1 (by omega)
        (by show o + (M + n) ≤ S.size; omega) hn
      rw [← eaS_den, ha]
      exact W.2.2 k' Ψ' he hwf s hw
    · split at h
      · next p τ Sh w off d M hfind =>
        split at h
        · next hc =>
          cases h
          rw [Bool.and_eq_true] at hc
          obtain ⟨hw', hfree⟩ := hc
          subst hw'
          obtain ⟨hmem, hpt, hin, hsp⟩ := findFactR_spec Γ.known hfind
          have hfm : (p.den ρ, τ.den ρ) ∈ (Γ.den ρ).known :=
            List.mem_map.mpr ⟨(p, τ), hmem, rfl⟩
          refine ⟨rfl, rfl, fun k' Ψ' he hwf s hw => ?_⟩
          obtain ⟨o', ha, h1, h2⟩ := CtxS.spanFrom_den hsp hw.known
          have hall : ∀ q ∈ (Sh.den ρ).vals, ShapeOf.clearOf (d + off) (M + n) q = true := by
            have := ValsS.free_den ρ (d + off) (M + n) Sh.vals
            rw [hfree, ← ShapeS.den_vals, List.all_eq_true] at this
            exact this
          have W := Writes.shared (fetch := fetch) (sys := sys) (Ψ := Ψ) (v.den ρ) hfm
            (TyS.pointee_den hk ρ hpt) (a := (eaS Γ.regs next m).den ρ) (o := o' + off) (n := n)
            (by rw [ha, BitVec.ofNat_add, BitVec.add_assoc])
            (by rw [ShapeS.den_size]; omega) hn
            (fun q hq => .inl (by
              have := hall q hq
              simp only [ShapeOf.clearOf, Bool.or_eq_true, decide_eq_true_eq] at this
              omega))
          rw [← eaS_den]
          exact W.2.2 k' Ψ' he hwf s hw
        · cases h
      · cases h
  · cases h

/-- The bytes an instruction reads: found exactly, or within a stretch. -/
def readAny (kinds : Nat → Option ShapeS) (Γ : CtxS) (k : Nat) (next : BitVec 64)
    (rd : Option (Mem × Nat)) : Option (Val × List (Val × TyS)) :=
  match readCell kinds Γ k next rd with
  | some r => some r
  | none => readRanged kinds Γ k next rd

theorem readAny_sound {ρ : Env} {kinds : Nat → Option ShapeS} (hk : KindsOk Ψ kinds) {Γ : CtxS}
    {k : Nat} {next : BitVec 64} {cell : Val}
    {extra : List (Val × TyS)} (hu : Γ.under k = true) :
    (rd : Option (Mem × Nat)) → readAny kinds Γ k next rd = some (cell, extra) →
    match rd with
    | some (m, n) => Reads fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) n
        (fun x Γr => Γr = CtxS.den (ρ.setVal k x) { Γ with known := extra ++ Γ.known } ∧
          cell.den (ρ.setVal k x) = x)
    | none => extra = [] ∧ cell.den (ρ.setVal k 0) = 0 := by
  intro rd h
  unfold readAny at h
  split at h
  · next r hr => cases h; exact readCell_sound hk hu rd hr
  · cases rd with
    | none => cases h
    | some mn => exact readRanged_sound hk hu h

/-- What is held once an instruction has written: exactly, or within a
stretch. -/
def writeAny (kinds : Nat → Option ShapeS) (Γ : CtxS) (next : BitVec 64) (v : Val)
    (wr : Option (Mem × Nat)) : Option (List (Val × HeldS)) :=
  match writeCell kinds Γ next v wr with
  | some r => some r
  | none => writeRanged kinds Γ next wr

theorem writeAny_sound {ρ : Env} {kinds : Nat → Option ShapeS} (hk : KindsOk Ψ kinds) {Γ : CtxS}
    {next : BitVec 64} {v : Val} {held' : List (Val × HeldS)} :
    (wr : Option (Mem × Nat)) → writeAny kinds Γ next v wr = some held' →
    match wr with
    | some (m, n) => Writes fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) n (v.den ρ)
        (CtxS.den ρ { Γ with held := held' })
    | none => held' = Γ.held := by
  intro wr h
  unfold writeAny at h
  split at h
  · next r hr => cases h; exact writeCell_sound hk wr hr
  · cases wr with
    | none => cases h
    | some mn => exact writeRanged_sound hk v h

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
def stepHeld (kinds : Nat → Option ShapeS) (Γ : CtxS) (k : Nat) (next : BitVec 64) (i : Instr) :
    Option (CtxS × Val) :=
  match i.sem with
  | some s =>
    match readAny kinds Γ k next s.rd with
    | some (cell, extra) =>
      let Γ₁ : CtxS := { Γ with known := extra ++ Γ.known }
      let σ := fillOf Γ s.srcs next (eaTerm Γ next s.ea) cell
      if !s.guard.okS Γ₁ Γ.flags (s.ga.fillN σ) (s.gb.fillN σ) (s.gc.fillN σ) then none else
      match writeAny kinds Γ₁ next (s.store.fillN σ) s.wr with
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

theorem stepHeld_sound {ρ : Env} {kinds : Nat → Option ShapeS} (hk : KindsOk Ψ kinds)
    {Γ Γ' : CtxS} {k : Nat} {next : BitVec 64} {i : Instr} {t : Val}
    (h : stepHeld kinds Γ k next i = some (Γ', t)) (hu : Γ.under k = true) :
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
        have hR := readAny_sound (fetch := fetch) (sys := sys) (Ψ := Ψ) (ρ := ρ) hk hu s.rd hrc
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
          have hW := writeAny_sound (fetch := fetch) (sys := sys) (Ψ := Ψ) (ρ := ρ.setVal k x) hk
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
