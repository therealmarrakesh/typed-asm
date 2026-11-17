import TypedAsm.U.Desc
import TypedAsm.Memory

/-!
# What the machine does with a described instruction

One statement for all of them: where the bytes the instruction reads may be
read, those it writes may be written, and it does not fault for a reason of
its own, the machine goes on to the state the description gives.
-/

namespace TypedAsm.U

/-- So many bytes at an address, as a number. -/
def loadN (s : State) (n : Nat) (a : BitVec 64) : BitVec 64 :=
  match n with
  | 1 => (s.load8 a).setWidth 64
  | 2 => (s.load16 a).setWidth 64
  | 4 => (s.load32 a).setWidth 64
  | 8 => s.load64 a
  | _ => 0

/-- So many bytes at an address given the low bytes of a number. -/
def storeN (s : State) (n : Nat) (a v : BitVec 64) : State :=
  match n with
  | 1 => s.store8 a (v.setWidth 8)
  | 2 => s.store16 a (v.setWidth 16)
  | 4 => s.store32 a (v.setWidth 32)
  | 8 => s.store64 a v
  | _ => s

theorem wbytes_eq (w : Width) : w.bytes.toNat = wbytes w := by cases w <;> rfl

theorem read_ok {s : State} {w : Width} {a : BitVec 64} (h : s.canRead a (wbytes w) = true) :
    s.read w a = .next (s.load w a) := by
  unfold State.read
  rw [wbytes_eq, h]
  rfl

theorem write_ok {s : State} {w : Width} {a : BitVec 64} {v : BitVec w.bits}
    (h : s.canWrite a (wbytes w) = true) : s.write w a v = .next (s.store w a v) := by
  unfold State.write
  rw [wbytes_eq, h]
  rfl

theorem loadN_w (s : State) (w : Width) (a : BitVec 64) :
    (loadN s (wbytes w) a).setWidth w.bits = s.load w a := by
  cases w
  · show ((s.load32 a).setWidth 64).setWidth 32 = s.load32 a
    simp
  · show (s.load64 a).setWidth 64 = s.load64 a
    simp

theorem storeN_w (s : State) (w : Width) (a : BitVec 64) (v : BitVec w.bits) :
    storeN s (wbytes w) a (wide v) = s.store w a v := by
  cases w
  · show s.store32 a ((v.setWidth 64).setWidth 32) = s.store32 a v
    simp
  · show s.store64 a (v.setWidth 64) = s.store64 a v
    simp

/-- What an operand holds, at a width. -/
def rmGet (s : State) (w : Width) : RM → BitVec w.bits
  | .reg r => s.readReg w r
  | .mem m => s.load w (s.ea m)

/-- The state with an operand given a value, at a width. -/
def rmPut (s : State) (w : Width) (x : RM) (v : BitVec w.bits) : State :=
  match x with
  | .reg r => s.writeReg w r v
  | .mem m => s.store w (s.ea m) v

theorem readRM_ok {s : State} {w : Width} {x : RM}
    (h : ∀ m, x = .mem m → s.canRead (s.ea m) (wbytes w) = true) :
    s.readRM w x = .next (rmGet s w x) := by
  cases x with
  | reg r => rfl
  | mem m =>
    show (s.read w (s.ea m)).through m = _
    rw [read_ok (h m rfl), Result.through_next]
    rfl

theorem writeRM_ok {s : State} {w : Width} {x : RM} {v : BitVec w.bits}
    (h : ∀ m, x = .mem m → s.canWrite (s.ea m) (wbytes w) = true) :
    s.writeRM w x v = .next (rmPut s w x v) := by
  cases x with
  | reg r => rfl
  | mem m =>
    show (s.write w (s.ea m) v).through m = _
    rw [write_ok (h m rfl), Result.through_next]
    rfl

namespace Desc

/-- The address a described instruction uses, in a state. -/
def addrOf (d : Desc) (s : State) : BitVec 64 :=
  match d.addr with
  | some m => s.ea m
  | none => 0

/-- The values it computes with. -/
def vals (d : Desc) (s : State) : List (BitVec 64) := d.srcs.map s.getReg

/-- The bytes at its address. -/
def cell (d : Desc) (s : State) : BitVec 64 := loadN s d.bytes (d.addrOf s)

/-- What it leaves, in a state. -/
def effect (d : Desc) (s : State) : Effect := d.run (d.vals s) s.flags (d.addrOf s) (d.cell s)

/-- Whether it does not fault for a reason of its own, in a state. -/
def guarded (d : Desc) (s : State) : Bool := d.guard (d.vals s) s.flags (d.addrOf s) (d.cell s)

/-- The state it leaves. -/
def after (d : Desc) (s : State) : State :=
  let e := d.effect s
  let s₁ := if d.writes then storeN s d.bytes (d.addrOf s) e.store else s
  { e.regs.foldl (fun t p => t.setReg p.1 p.2) s₁ with flags := e.flags }

end Desc

theorem storeN_flags (s : State) (n : Nat) (a v : BitVec 64) :
    (storeN s n a v).flags = s.flags := by
  unfold storeN
  split <;> rfl

theorem withFlags_self (t : State) (f : Flags) (h : t.flags = f) : { t with flags := f } = t := by
  cases t
  cases h
  rfl

/-- A described instruction that writes no register and leaves the flags:
what it leaves is its store. -/
theorem Desc.after_store (d : Desc) (s : State) (hw : d.writes = true)
    (hregs : (d.effect s).regs = []) (hfl : (d.effect s).flags = s.flags) :
    d.after s = storeN s d.bytes (d.addrOf s) (d.effect s).store := by
  unfold Desc.after
  simp only [hw, ↓reduceIte, hregs, List.foldl_nil, hfl]
  exact withFlags_self _ _ (storeN_flags _ _ _ _)

set_option linter.unusedSimpArgs false

theorem storeN_w' (s : State) (w : Width) (a : BitVec 64) (v : BitVec w.bits) :
    storeN s (wbytes w) a (v.setWidth 64) = s.store w a v := storeN_w s w a v

open Lean.Parser.Tactic in
/-- Unfolds the machine's step and a description's, on operands written out. -/
syntax "desc_simp" (" [" term,* "]")? (" at " ident)? : tactic
macro_rules
  | `(tactic| desc_simp $[[$ts,*]]? $[at $h]?) => do
    let extra : Array (Lean.TSyntax `term) := match ts with
      | some ts => ts.getElems
      | none => #[]
    let loc ← match h with
      | some h => `(Lean.Parser.Tactic.location| at $h:ident)
      | none => `(Lean.Parser.Tactic.location| at ⊢)
    `(tactic| simp only [exec, bind, Result.bind, pure, State.readRM, State.writeRM, State.readRI,
      State.readNarrow, State.writeRM8, State.shiftCount, Operands.src, Operands.dst,
      Result.through_next, Result.onStack_next, Result.ofOption,
      Desc.after, Desc.effect, Desc.vals, Desc.cell, Desc.addrOf, Desc.guarded, rmRegs, srcRegs,
      rmVal, srcVal, opsMem, rmMem, rmSet, wide, List.map, List.cons_append, List.nil_append,
      List.getD_cons_zero, List.getD_cons_succ, List.length_cons, List.length_nil,
      Option.getD_some, Option.isSome_none, Option.isSome_some, Bool.false_and, Bool.true_and,
      Bool.and_true, Bool.and_false, List.foldl_cons, List.foldl_nil, State.writeReg,
      State.readReg, ↓reduceIte, Bool.false_eq_true, loadN_w, storeN_w, storeN_w', $[$extra:term],*] $loc)

theorem read8_ok {s : State} {a : BitVec 64} (h : s.canRead a 1 = true) :
    s.read8 a = .next (s.load8 a) := by
  unfold State.read8
  rw [h]
  rfl

theorem read16_ok {s : State} {a : BitVec 64} (h : s.canRead a 2 = true) :
    s.read16 a = .next (s.load16 a) := by
  unfold State.read16
  rw [h]
  rfl

theorem read64_ok {s : State} {a : BitVec 64} (h : s.canRead a 8 = true) :
    s.read64 a = .next (s.load64 a) := by
  unfold State.read64
  rw [h]
  rfl

theorem write8_ok {s : State} {a : BitVec 64} {v : BitVec 8} (h : s.canWrite a 1 = true) :
    s.write8 a v = .next (s.store8 a v) := by
  unfold State.write8
  rw [h]
  rfl

theorem write16_ok {s : State} {a : BitVec 64} {v : BitVec 16} (h : s.canWrite a 2 = true) :
    s.write16 a v = .next (s.store16 a v) := by
  unfold State.write16
  rw [h]
  rfl

theorem write64_ok {s : State} {a : BitVec 64} {v : BitVec 64} (h : s.canWrite a 8 = true) :
    s.write64 a v = .next (s.store64 a v) := by
  unfold State.write64
  rw [h]
  rfl

theorem loadN_1 (s : State) (a : BitVec 64) : (loadN s 1 a).setWidth 8 = s.load8 a := by
  show ((s.load8 a).setWidth 64).setWidth 8 = _
  simp

theorem loadN_2 (s : State) (a : BitVec 64) : (loadN s 2 a).setWidth 16 = s.load16 a := by
  show ((s.load16 a).setWidth 64).setWidth 16 = _
  simp

theorem loadN_4 (s : State) (a : BitVec 64) : (loadN s 4 a).setWidth 32 = s.load32 a := by
  show ((s.load32 a).setWidth 64).setWidth 32 = _
  simp

theorem loadN_8 (s : State) (a : BitVec 64) : loadN s 8 a = s.load64 a := rfl

theorem storeN_1 (s : State) (a : BitVec 64) (v : BitVec 8) :
    storeN s 1 a (v.setWidth 64) = s.store8 a v := by
  show s.store8 a ((v.setWidth 64).setWidth 8) = _
  simp

theorem storeN_2 (s : State) (a : BitVec 64) (v : BitVec 16) :
    storeN s 2 a (v.setWidth 64) = s.store16 a v := by
  show s.store16 a ((v.setWidth 64).setWidth 16) = _
  simp

theorem storeN_8 (s : State) (a v : BitVec 64) : storeN s 8 a v = s.store64 a v := rfl

theorem ea_pushMem (s : State) : s.ea pushMem = s.getReg .rsp - 8 := by
  show s.getReg .rsp + 0 + (-8 : BitVec 32).signExtend 64 = _
  have : (-8 : BitVec 32).signExtend 64 = -8 := by decide
  rw [this]
  bv_omega

theorem ea_topMem (s : State) : s.ea topMem = s.getReg .rsp := by
  show s.getReg .rsp + 0 + (0 : BitVec 32).signExtend 64 = _
  have : (0 : BitVec 32).signExtend 64 = 0 := by decide
  rw [this]
  bv_omega

/-- **What the machine does with a described instruction**: where what it
reads may be read, what it writes may be written, and it does not fault for
a reason of its own, it goes on to the state the description gives. -/
theorem exec_desc (sys : Syscall) (s : State) {i : Instr} {d : Desc} (hd : i.desc = some d)
    (hr : d.reads = true → s.canRead (d.addrOf s) d.bytes = true)
    (hw : d.writes = true → s.canWrite (d.addrOf s) d.bytes = true)
    (hg : d.guarded s = true) : exec sys i s = .next (d.after s) := by
  cases i with
  | nop => cases hd; rfl
  | movAbs dst imm => cases hd; rfl
  | lea w dst addr => cases hd; rfl
  | bswap w r => cases hd; rfl
  | cdq => cases hd; rfl
  | cqo => cases hd; rfl
  | test w dst src =>
    cases hd
    rcases dst with dst | m <;> rcases src with src | imm
    · desc_simp
    · desc_simp
    · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr rfl
      desc_simp [read_ok hr']
    · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr rfl
      desc_simp [read_ok hr']
  | unary op w dst =>
    cases op <;> cases hd <;> rcases dst with dst | m
    · desc_simp
    · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr rfl
      have hw' : s.canWrite (s.ea m) (wbytes w) = true := hw rfl
      desc_simp [read_ok hr', write_ok hw']
    · desc_simp
      rfl
    · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr rfl
      have hw' : s.canWrite (s.ea m) (wbytes w) = true := hw rfl
      desc_simp [read_ok hr', write_ok hw']
      congr 1
      exact (withFlags_self _ _ (State.flags_store _ _ _ _)).symm
  | shift op w dst c =>
    cases hd
    rcases dst with dst | m <;> rcases c with n | _
    · desc_simp
    · desc_simp
    · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr rfl
      have hw' : s.canWrite (s.ea m) (wbytes w) = true := hw rfl
      desc_simp [read_ok hr', write_ok hw']
    · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr rfl
      have hw' : s.canWrite (s.ea m) (wbytes w) = true := hw rfl
      desc_simp [read_ok hr', write_ok hw']
  | imul2 w dst src =>
    cases hd
    rcases src with src | m
    · desc_simp
    · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr rfl
      desc_simp [read_ok hr']
  | imul3 w dst src imm =>
    cases hd
    rcases src with src | m
    · desc_simp
    · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr rfl
      desc_simp [read_ok hr']
  | popcnt w dst src =>
    cases hd
    rcases src with src | m
    · desc_simp
    · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr rfl
      desc_simp [read_ok hr']
  | mulDiv op w src =>
    cases hd
    rcases src with src | m
    · desc_simp at hg
      desc_simp
      split at hg
      · next x hx => obtain ⟨lo, hi, f⟩ := x; simp only [hx]; rfl
      · cases hg
    · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr rfl
      desc_simp at hg
      desc_simp [read_ok hr']
      split at hg
      · next x hx => obtain ⟨lo, hi, f⟩ := x; simp only [hx]; rfl
      · cases hg
  | cmov c w dst src =>
    cases hd
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (show (c.eval s.flags).isSome = true from hg)
    rcases src with src | m
    · desc_simp [hb]
      rfl
    · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr rfl
      desc_simp [hb, read_ok hr']
      rfl
  | movsxd dst src =>
    cases hd
    rcases src with src | m
    · (desc_simp) <;> try rfl
    · have hr' : s.canRead (s.ea m) (wbytes .w32) = true := hr rfl
      (desc_simp [read_ok hr', loadN_4, State.load]) <;> try rfl
  | store8 dst src =>
    cases hd
    have hw' : s.canWrite (s.ea dst) 1 = true := hw rfl
    (desc_simp [write8_ok hw', storeN_1]) <;> try rfl
  | store16 dst src =>
    cases hd
    have hw' : s.canWrite (s.ea dst) 2 = true := hw rfl
    (desc_simp [write16_ok hw', storeN_2]) <;> try rfl
  | movzx w dst sw src =>
    cases hd
    rcases src with src | m
    · (desc_simp) <;> try rfl
    · cases sw
      · have hr' : s.canRead (s.ea m) 1 = true := hr rfl
        (desc_simp [read8_ok hr', loadN_1, nbytes, NarrowW.bits]) <;> try rfl
      · have hr' : s.canRead (s.ea m) 2 = true := hr rfl
        (desc_simp [read16_ok hr', loadN_2, nbytes, NarrowW.bits]) <;> try rfl
  | movsx w dst sw src =>
    cases hd
    rcases src with src | m
    · (desc_simp) <;> try rfl
    · cases sw
      · have hr' : s.canRead (s.ea m) 1 = true := hr rfl
        (desc_simp [read8_ok hr', loadN_1, nbytes, NarrowW.bits]) <;> try rfl
      · have hr' : s.canRead (s.ea m) 2 = true := hr rfl
        (desc_simp [read16_ok hr', loadN_2, nbytes, NarrowW.bits]) <;> try rfl
  | setcc c dst =>
    cases hd
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (show (c.eval s.flags).isSome = true from hg)
    rcases dst with dst | m
    · (desc_simp [hb]) <;> try rfl
    · have hw' : s.canWrite (s.ea m) 1 = true := hw rfl
      (desc_simp [hb, write8_ok hw', storeN_1]) <;> try rfl
  | push r =>
    cases hd
    have hw' : s.canWrite (s.getReg .rsp - 8) 8 = true := by
      have this : s.canWrite (s.ea pushMem) 8 = true := hw rfl
      rwa [ea_pushMem] at this
    have hw'' : (s.setReg .rsp (s.getReg .rsp - 8)).canWrite (s.getReg .rsp - 8) 8 = true := hw'
    (desc_simp [State.push64, write64_ok hw'', ea_pushMem, storeN_8]) <;> try rfl
  | pop r =>
    cases hd
    have hr' : s.canRead (s.getReg .rsp) 8 = true := by
      have this : s.canRead (s.ea topMem) 8 = true := hr rfl
      rwa [ea_topMem] at this
    (desc_simp [State.pop64, read64_ok hr', ea_topMem, loadN_8]) <;> try rfl
  | alu op w ops =>
    cases hd
    rcases ops with ⟨dst | m, src⟩ | ⟨dst, m⟩ | ⟨dst | m, imm⟩
    · desc_simp at hg
      obtain ⟨⟨r, f⟩, he⟩ := Option.isSome_iff_exists.mp hg
      cases hwd : op.writesDst <;> desc_simp [he, hwd]
    · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr rfl
      desc_simp at hg
      obtain ⟨⟨r, f⟩, he⟩ := Option.isSome_iff_exists.mp hg
      cases hwd : op.writesDst
      · desc_simp [he, hwd, read_ok hr']
      · have hw' : s.canWrite (s.ea m) (wbytes w) = true := hw (by desc_simp [hwd])
        desc_simp [he, hwd, read_ok hr', write_ok hw']
    · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr rfl
      desc_simp at hg
      obtain ⟨⟨r, f⟩, he⟩ := Option.isSome_iff_exists.mp hg
      cases hwd : op.writesDst <;> desc_simp [he, hwd, read_ok hr']
    · desc_simp at hg
      obtain ⟨⟨r, f⟩, he⟩ := Option.isSome_iff_exists.mp hg
      cases hwd : op.writesDst <;> desc_simp [he, hwd]
    · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr rfl
      desc_simp at hg
      obtain ⟨⟨r, f⟩, he⟩ := Option.isSome_iff_exists.mp hg
      cases hwd : op.writesDst
      · desc_simp [he, hwd, read_ok hr']
      · have hw' : s.canWrite (s.ea m) (wbytes w) = true := hw (by desc_simp [hwd])
        desc_simp [he, hwd, read_ok hr', write_ok hw']
  | mov w ops =>
    cases hd
    rcases ops with ⟨dst | m, src⟩ | ⟨dst, m⟩ | ⟨dst | m, imm⟩
    · rfl
    · have hw' : s.canWrite (s.ea m) (wbytes w) = true := hw rfl
      show (s.write w (s.ea m) (s.readReg w src)).through m = _
      rw [write_ok hw', Result.through_next, ← storeN_w, Desc.after_store _ _ rfl rfl rfl]
      rfl
    · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr rfl
      show (do let v ← (s.read w (s.ea m)).through m; .next (s.writeReg w dst v)) = _
      rw [read_ok hr', Result.through_next, ← loadN_w]
      rfl
    · rfl
    · have hw' : s.canWrite (s.ea m) (wbytes w) = true := hw rfl
      show (s.write w (s.ea m) (imm.signExtend w.bits)).through m = _
      rw [write_ok hw', Result.through_next, ← storeN_w, Desc.after_store _ _ rfl rfl rfl]
      rfl
  | jmp t => cases hd
  | jcc c rel => cases hd
  | call t => cases hd
  | ret => cases hd
  | ud2 => cases hd
  | syscall => cases hd
end TypedAsm.U
