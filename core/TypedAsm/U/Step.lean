import TypedAsm.U.Fresh
import TypedAsm.U.Held

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
  show (Γ.held.map _)[j]? = _
  rw [List.getElem?_map, h]
  rfl

/-- The term for the bytes an instruction reads: nothing where it reads
none; the value the region holds there, where it holds one at those eight
bytes; and otherwise the name `k`, for a value the context does not say. -/
def readCell (Γ : CtxS) (k : Nat) (next : BitVec 64) : Option (Mem × Nat) → Option Val
  | none => some (.lit 0)
  | some (m, n) =>
    match findHeld (eaS Γ.regs next m) n Γ.held 0 with
    | some (_, _, S, o) =>
      if n = 8 then
        match S.slotAt o with
        | some v => some v
        | none => some (.var k)
      else some (.var k)
    | none => none

theorem readCell_sound {ρ : Env} {Γ : CtxS} {k : Nat} {next : BitVec 64} {cell : Val}
    (hu : Γ.under k = true) :
    (rd : Option (Mem × Nat)) → readCell Γ k next rd = some cell →
    match rd with
    | some (m, n) => Reads fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) n
        (fun x Γr => Γr = Γ.den ρ ∧ cell.den (ρ.setVal k x) = x)
    | none => cell.den (ρ.setVal k 0) = 0
  | none, h => by cases h; rfl
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
      refine ⟨rfl, ?_⟩
      split at h
      · next h8 =>
        split at h
        · next v hv =>
          cases h
          have hm := HeldS.slotAt_mem hv
          have hx := hslot h8 (cell.den ρ) (by
            show (o, cell.den ρ) ∈ S.slots.map _
            exact List.mem_map.mpr ⟨(o, cell), hm, rfl⟩)
          -- the slot's term mentions no name from `k` on
          have hcu : cell.under k = true := by
            simp only [CtxS.under, Bool.and_eq_true, List.all_eq_true] at hu
            exact (hu.1.2 (b, S) (List.mem_of_getElem? hl)).2 (o, cell) hm
          rw [Val.den_setVal ρ k x _ hcu]
          exact hx.symm
        · cases h; exact Env.setVal_get_self ρ k x
      · cases h; exact Env.setVal_get_self ρ k x
    · cases h

/-- What the context holds once an instruction has written its bytes: the
region they are in holds the value written there. -/
def writeCell (Γ : CtxS) (next : BitVec 64) (v : Val) :
    Option (Mem × Nat) → Option (List (Val × HeldS))
  | none => some Γ.held
  | some (m, n) =>
    match findHeld (eaS Γ.regs next m) n Γ.held 0 with
    | some (j, b, S, o) => if n ≤ 8 then some (Γ.held.set j (b, S.put o n v)) else none
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
          show (Γ.held.set j (b, S.put o n v)).map _ = (Γ.held.map _).set j _
          rw [List.map_set, HeldS.put_den]
        rw [e]
        exact hW
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

/-- What an instruction leaves, on the terms a context gives it, is what its
description computes from what the context says. -/
theorem effect_den (ρ : Env) (Γ : CtxS) (next : BitVec 64) {i : Instr} {d : Desc}
    (hd : i.desc = some d) (cell : BitVec 64) :
    effectOf i [(argAt Γ.regs d.srcs 0).den ρ, (argAt Γ.regs d.srcs 1).den ρ,
        (argAt Γ.regs d.srcs 2).den ρ] (Γ.flags.den ρ) next ((eaTerm Γ next d.ea).den ρ) cell
      = d.run (d.srcs.map (Γ.den ρ).val) (Γ.den ρ).flags next
        ((d.ea.map (eaOf (Γ.den ρ).val next)).getD 0) cell := by
  unfold effectOf
  rw [hd]
  simp only
  rw [args_den ρ Γ d.srcs (desc_srcs_le hd), eaTerm_den]
  rfl

theorem target_den (ρ : Env) (Γ : CtxS) (next : BitVec 64) {i : Instr} {d : Desc}
    (hd : i.desc = some d) (cell : BitVec 64) :
    targetOf i [(argAt Γ.regs d.srcs 0).den ρ, (argAt Γ.regs d.srcs 1).den ρ,
        (argAt Γ.regs d.srcs 2).den ρ] (Γ.flags.den ρ) next ((eaTerm Γ next d.ea).den ρ) cell
      = (d.goes (d.srcs.map (Γ.den ρ).val) (Γ.den ρ).flags next
        ((d.ea.map (eaOf (Γ.den ρ).val next)).getD 0) cell).getD next := by
  unfold targetOf
  rw [hd]
  simp only
  rw [args_den ρ Γ d.srcs (desc_srcs_le hd), eaTerm_den]
  rfl

/-- **The checker's step for any instruction whose memory, if it touches
any, is memory the context holds.** The bytes it reads are found, and are
the value held there or a value given the name `k`; each register it writes
holds the term for what the instruction gives it, made as simple as it can
be; the bytes it writes are found, and the region holds what was written.
With the context after, the address control goes to. -/
def stepHeld (Γ : CtxS) (k : Nat) (next : BitVec 64) (i : Instr) : Option (CtxS × Val) :=
  match i.desc with
  | some d =>
    match readCell Γ k next d.rd with
    | some cell =>
      let a := argAt Γ.regs d.srcs 0
      let b := argAt Γ.regs d.srcs 1
      let c := argAt Γ.regs d.srcs 2
      let ea := eaTerm Γ next d.ea
      match writeCell Γ next (.stored i a b c Γ.flags next ea cell) d.wr with
      | some held' =>
        some ({ Γ with
                regs := setOuts (fun j => simpOut i j a b c Γ.flags next ea cell) i.outs 0 Γ.regs
                flags := .out i a b c Γ.flags next ea cell
                held := held' },
          .goes i a b c Γ.flags next ea cell)
      | none => none
    | none => none
  | none => none

theorem stepHeld_sound {ρ : Env} {Γ Γ' : CtxS} {k : Nat} {next : BitVec 64} {i : Instr} {t : Val}
    (h : stepHeld Γ k next i = some (Γ', t)) (hu : Γ.under k = true)
    (hg : ∀ d, i.desc = some d → ∀ x : BitVec 64,
      d.guard (d.srcs.map (Γ.den ρ).val) (Γ.den ρ).flags next
        ((d.ea.map (eaOf (Γ.den ρ).val next)).getD 0) x = true) :
    Steps fetch sys Ψ i next (Γ.den ρ) fun t' Δ =>
      ∃ x, t' = t.den (ρ.setVal k x) ∧ Δ = Γ'.den (ρ.setVal k x) := by
  unfold stepHeld at h
  cases hd : i.desc with
  | none => rw [hd] at h; cases h
  | some d =>
    rw [hd] at h
    simp only at h
    split at h
    · next cell hrc =>
      split at h
      · next held' hwc =>
        cases h
        have hR := readCell_sound (fetch := fetch) (sys := sys) (Ψ := Ψ) (ρ := ρ) hu d.rd hrc
        refine Steps.mono (Steps.desc
          (R := fun x Γr => Γr = Γ.den ρ ∧ cell.den (ρ.setVal k x) = x)
          (W := fun x _ Γw => Γw = CtxS.den (ρ.setVal k x) { Γ with held := held' }) hd ?_ ?_ ?_) ?_
        · cases hrd : d.rd with
          | none => rw [hrd] at hR; exact ⟨rfl, hR⟩
          | some mn => rw [hrd] at hR; exact hR
        · rintro x Γr ⟨rfl, hx⟩
          refine ⟨_, rfl, ?_⟩
          have hΓ : Γ.den (ρ.setVal k x) = Γ.den ρ := CtxS.den_setVal ρ k x Γ hu
          have hW := writeCell_sound (fetch := fetch) (sys := sys) (Ψ := Ψ) (ρ := ρ.setVal k x)
            d.wr hwc
          cases hwr : d.wr with
          | none =>
            rw [hwr] at hW
            show CtxS.den (ρ.setVal k x) { Γ with held := held' } = Γ.den ρ
            rw [hW, ← hΓ]
          | some mn =>
            obtain ⟨m, n⟩ := mn
            rw [hwr] at hW
            show Writes fetch sys Ψ (Γ.den ρ) (eaOf (Γ.den ρ).val next m) n _ _
            have hst : (Val.stored i (argAt Γ.regs d.srcs 0) (argAt Γ.regs d.srcs 1)
                (argAt Γ.regs d.srcs 2) Γ.flags next (eaTerm Γ next d.ea) cell).den (ρ.setVal k x)
                = (d.run (d.srcs.map (Γ.den ρ).val) (Γ.den ρ).flags next
                  ((d.ea.map (eaOf (Γ.den ρ).val next)).getD 0) x).store := by
              show (effectOf i _ _ next _ (cell.den (ρ.setVal k x))).store = _
              rw [effect_den (ρ.setVal k x) Γ next hd, hΓ, hx]
            rw [hst, hΓ] at hW
            exact hW
        · intro x Γr _
          exact hg d hd x
        · rintro t' Δ ⟨x, Γr, Γw, ⟨rfl, hx⟩, rfl, rfl, rfl⟩
          have hΓ : Γ.den (ρ.setVal k x) = Γ.den ρ := CtxS.den_setVal ρ k x Γ hu
          refine ⟨x, ?_, ?_⟩
          · show _ = targetOf i _ _ next _ (cell.den (ρ.setVal k x))
            rw [target_den (ρ.setVal k x) Γ next hd, hΓ, hx]
          · have he := effect_den (ρ.setVal k x) Γ next hd (cell.den (ρ.setVal k x))
            rw [hΓ, hx] at he
            have houts := desc_outs hd (d.srcs.map (Γ.den ρ).val) (Γ.den ρ).flags next
              ((d.ea.map (eaOf (Γ.den ρ).val next)).getD 0) x
            refine ctx_ext ?_ ?_ rfl rfl
            · funext r
              show List.foldl _ (Γ.den (ρ.setVal k x)).val _ r
                = ((setOuts _ i.outs 0 Γ.regs).get r).den (ρ.setVal k x)
              rw [← houts]
              refine (setOuts_den (ρ.setVal k x) _ _ 0 Γ.regs _ (fun _ => rfl)
                (fun j hj => ?_) r).symm
              rw [simpOut_den]
              show ((effectOf i _ _ next _ (cell.den (ρ.setVal k x))).regs.getD (0 + j)
                (Reg.rax, 0)).2 = _
              rw [hx, he, Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
              rfl
            · show _ = (effectOf i _ _ next _ (cell.den (ρ.setVal k x))).flags
              rw [hx, he]
              rfl
      · cases h
    · cases h

end TypedAsm.U
