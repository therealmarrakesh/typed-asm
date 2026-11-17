import TypedAsm.U.Table
import TypedAsm.U.Unfold
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

/-- The values a described instruction computes with, in a state. -/
def vals (d : Desc) (s : State) : List (BitVec 64) := d.srcs.map s.getReg

/-- The address it uses as a number. -/
def eaOf (d : Desc) (s : State) : BitVec 64 :=
  match d.ea with
  | some m => s.ea m
  | none => 0

/-- The bytes it reads. -/
def cell (d : Desc) (s : State) : BitVec 64 :=
  match d.rd with
  | some (m, n) => loadN s n (s.ea m)
  | none => 0

def effect (d : Desc) (s : State) : Effect := d.run (d.vals s) s.flags s.rip (d.eaOf s) (d.cell s)

def guarded (d : Desc) (s : State) : Bool :=
  d.guard (d.vals s) s.flags s.rip (d.eaOf s) (d.cell s)

def target (d : Desc) (s : State) : Option (BitVec 64) :=
  d.goes (d.vals s) s.flags s.rip (d.eaOf s) (d.cell s)

/-- The state it leaves: its bytes written, at the address its operand
named before anything changed; its registers and the flags given their
values; and the instruction pointer where control goes. -/
def after (d : Desc) (s : State) : State :=
  let e := d.effect s
  let s₁ := match d.wr with
    | some (m, n) => storeN s n (s.ea m) e.store
    | none => s
  let s₂ : State := { e.regs.foldl (fun t p => t.setReg p.1 p.2) s₁ with flags := e.flags }
  match d.target s with
  | some t => { s₂ with rip := t }
  | none => s₂

end Desc

theorem storeN_flags (s : State) (n : Nat) (a v : BitVec 64) :
    (storeN s n a v).flags = s.flags := by
  unfold storeN
  split <;> simp only [State.store64, State.store32, State.store16, State.store8]

theorem withFlags_self (t : State) (f : Flags) (h : t.flags = f) : { t with flags := f } = t := by
  cases t
  cases h
  rfl

/-- A described instruction that writes no register, leaves the flags and
goes on to the next: what it leaves is its store. -/
theorem Desc.after_store (d : Desc) (s : State) (m : Mem) (n : Nat) (hw : d.wr = some (m, n))
    (hregs : (d.effect s).regs = []) (hfl : (d.effect s).flags = s.flags)
    (ht : d.target s = none) : d.after s = storeN s n (s.ea m) (d.effect s).store := by
  unfold Desc.after
  simp only [hw, hregs, List.foldl_nil, hfl, ht]
  exact withFlags_self _ _ (storeN_flags _ _ _ _)

set_option linter.unusedSimpArgs false

theorem add_neg (x y : BitVec 64) : x + -y = x - y := (BitVec.sub_eq_add_neg x y).symm

/-- A count written in an instruction is itself. -/
theorem count_toNat (k : BitVec 8) : (BitVec.ofNat 64 k.toNat).toNat = k.toNat := by
  have := k.isLt
  rw [BitVec.toNat_ofNat]
  omega

/-- A value at a width, widened and taken at the width again, is itself. -/
theorem setWidth_wide (w : Width) (r : BitVec w.bits) :
    BitVec.setWidth w.bits (BitVec.setWidth 64 r) = r := by
  cases w <;> simp [Width.bits]

theorem storeN_w' (s : State) (w : Width) (a : BitVec 64) (v : BitVec w.bits) :
    storeN s (wbytes w) a (v.setWidth 64) = s.store w a v := storeN_w s w a v

attribute [desc_unfold]
  Result.bind State.readRM State.writeRM State.readRI State.readNarrow State.writeRM8
  State.shiftCount Operands.src Operands.dst Result.through_next Result.onStack_next
  Result.ofOption Desc.after Desc.effect Desc.vals Desc.cell Desc.eaOf Desc.guarded Desc.target
  Sem.toDesc Sem.give slotEnv Val.den FlagsT.den A rmV srcV immV countV Un.eval Bin.eval Tri.eval
  FOp.eval FSrc.eval GuardE.eval Option.map_some Option.map_none setWidth_wide rmRegs srcRegs
  opsMem rmMem wide List.map List.cons_append List.nil_append List.getD_cons_zero
  List.getD_cons_succ List.length_cons List.length_nil Option.getD_some Option.isSome_none
  Option.isSome_some Bool.false_and Bool.true_and Bool.and_true Bool.and_false List.foldl_cons
  List.foldl_nil State.writeReg State.readReg Bool.false_eq_true loadN_w storeN_w storeN_w'

/-- Unfolds the machine's step and a description's, on operands written out. -/
macro "desc_simp" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" " at " h:ident : tactic =>
  `(tactic| simp only [desc_unfold, exec, bind, pure, ↓reduceIte, $ts,*] at $h:ident)
macro "desc_simp" " at " h:ident : tactic => `(tactic| simp only [desc_unfold, exec, bind, pure, ↓reduceIte] at $h:ident)
macro "desc_simp" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| simp only [desc_unfold, exec, bind, pure, ↓reduceIte, $ts,*])
macro "desc_simp" : tactic => `(tactic| simp only [desc_unfold, exec, bind, pure, ↓reduceIte])

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

attribute [goes_unfold]
  Result.bind State.readRM State.push64 State.pop64 Result.through_next Result.onStack_next
  Result.ofOption Desc.after Desc.effect Desc.vals Desc.cell Desc.eaOf Desc.guarded Desc.target
  Sem.toDesc Sem.give slotEnv Val.den FlagsT.den A rmV srcV immV countV Un.eval Bin.eval Tri.eval
  FOp.eval FSrc.eval GuardE.eval Option.map_some Option.map_none setWidth_wide List.map
  List.getD_cons_zero List.getD_cons_succ Option.getD_some Option.isSome_some List.foldl_cons
  List.foldl_nil State.readReg loadN_8 storeN_8 ea_pushMem ea_topMem BitVec.setWidth_eq
  Width.bits

/-- Unfolds the machine's step and a description's, for an instruction that
passes control elsewhere. -/
macro "goes_simp" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| simp only [goes_unfold, exec, bind, pure, ↓reduceIte, $ts,*])
macro "goes_simp" : tactic => `(tactic| simp only [goes_unfold, exec, bind, pure, ↓reduceIte])

set_option maxRecDepth 4000 in
/-- **What the machine does with any described instruction**: where what it
reads may be read, what it writes may be written, and it does not fault for
a reason of its own, it goes on to the state the description gives. -/
theorem exec_desc (sys : Syscall) (s : State) {i : Instr} {d : Desc} (hd : i.desc = some d)
    (hr : ∀ m n, d.rd = some (m, n) → s.canRead (s.ea m) n = true)
    (hw : ∀ m n, d.wr = some (m, n) → s.canWrite (s.ea m) n = true)
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
    · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr _ _ rfl
      desc_simp [read_ok hr']
    · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr _ _ rfl
      desc_simp [read_ok hr']
  | unary op w dst =>
    cases op <;> cases hd <;> rcases dst with dst | m
    · desc_simp
    · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr _ _ rfl
      have hw' : s.canWrite (s.ea m) (wbytes w) = true := hw _ _ rfl
      desc_simp [read_ok hr', write_ok hw']
    · desc_simp
      rfl
    · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr _ _ rfl
      have hw' : s.canWrite (s.ea m) (wbytes w) = true := hw _ _ rfl
      desc_simp [read_ok hr', write_ok hw']
      congr 1
      exact (withFlags_self _ _ (State.flags_store _ _ _ _)).symm
  | shift op w dst c =>
    cases hd
    rcases dst with dst | m <;> rcases c with n | _
    · desc_simp [shift_fst op s.flags, count_toNat]
    · desc_simp [shift_fst op s.flags, count_toNat]
    · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr _ _ rfl
      have hw' : s.canWrite (s.ea m) (wbytes w) = true := hw _ _ rfl
      desc_simp [read_ok hr', write_ok hw', shift_fst op s.flags, count_toNat]
    · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr _ _ rfl
      have hw' : s.canWrite (s.ea m) (wbytes w) = true := hw _ _ rfl
      desc_simp [read_ok hr', write_ok hw', shift_fst op s.flags, count_toNat]
  | imul2 w dst src =>
    cases hd
    rcases src with src | m
    · desc_simp
    · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr _ _ rfl
      desc_simp [read_ok hr']
  | imul3 w dst src imm =>
    cases hd
    rcases src with src | m
    · desc_simp
    · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr _ _ rfl
      desc_simp [read_ok hr']
  | popcnt w dst src =>
    cases hd
    rcases src with src | m
    · desc_simp
    · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr _ _ rfl
      desc_simp [read_ok hr']
  | mulDiv op w src =>
    cases hd
    rcases src with src | m
    · desc_simp at hg
      desc_simp
      split at hg
      · next x hx => obtain ⟨lo, hi, f⟩ := x; simp only [hx] <;> rfl
      · cases hg
    · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr _ _ rfl
      desc_simp at hg
      desc_simp [read_ok hr']
      split at hg
      · next x hx => obtain ⟨lo, hi, f⟩ := x; simp only [hx] <;> rfl
      · cases hg
  | cmov c w dst src =>
    cases hd
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (show (c.eval s.flags).isSome = true from hg)
    rcases src with src | m
    · desc_simp [hb]
      rfl
    · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr _ _ rfl
      desc_simp [hb, read_ok hr']
      rfl
  | movsxd dst src =>
    cases hd
    rcases src with src | m
    · (desc_simp) <;> try rfl
    · have hr' : s.canRead (s.ea m) (wbytes .w32) = true := hr _ _ rfl
      (desc_simp [read_ok hr', loadN_4, State.load]) <;> try rfl
  | store8 dst src =>
    cases hd
    have hw' : s.canWrite (s.ea dst) 1 = true := hw _ _ rfl
    (desc_simp [write8_ok hw', storeN_1]) <;> try rfl
  | store16 dst src =>
    cases hd
    have hw' : s.canWrite (s.ea dst) 2 = true := hw _ _ rfl
    (desc_simp [write16_ok hw', storeN_2]) <;> try rfl
  | movzx w dst sw src =>
    cases hd
    rcases src with src | m
    · (desc_simp) <;> try rfl
    · cases sw
      · have hr' : s.canRead (s.ea m) 1 = true := hr _ _ rfl
        (desc_simp [read8_ok hr', loadN_1, nbytes, NarrowW.bits]) <;> try rfl
      · have hr' : s.canRead (s.ea m) 2 = true := hr _ _ rfl
        (desc_simp [read16_ok hr', loadN_2, nbytes, NarrowW.bits]) <;> try rfl
  | movsx w dst sw src =>
    cases hd
    rcases src with src | m
    · (desc_simp) <;> try rfl
    · cases sw
      · have hr' : s.canRead (s.ea m) 1 = true := hr _ _ rfl
        (desc_simp [read8_ok hr', loadN_1, nbytes, NarrowW.bits]) <;> try rfl
      · have hr' : s.canRead (s.ea m) 2 = true := hr _ _ rfl
        (desc_simp [read16_ok hr', loadN_2, nbytes, NarrowW.bits]) <;> try rfl
  | setcc c dst =>
    cases hd
    rcases dst with dst | m
    · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (show (c.eval s.flags).isSome = true from hg)
      (desc_simp [hb, condBit]) <;> try rfl
    · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (show (c.eval s.flags).isSome = true from hg)
      have hw' : s.canWrite (s.ea m) 1 = true := hw _ _ rfl
      (desc_simp [hb, condBit, write8_ok hw', storeN_1]) <;> try rfl
  | push r =>
    cases hd
    have hw' : s.canWrite (s.getReg .rsp - 8) 8 = true := by
      have this : s.canWrite (s.ea pushMem) 8 = true := hw pushMem 8 rfl
      rwa [ea_pushMem] at this
    have hw'' : (s.setReg .rsp (s.getReg .rsp - 8)).canWrite (s.getReg .rsp - 8) 8 = true := hw'
    (desc_simp [State.push64, add_neg, write64_ok hw'', ea_pushMem, storeN_8]) <;> try rfl
  | pop r =>
    cases hd
    have hr' : s.canRead (s.getReg .rsp) 8 = true := by
      have this : s.canRead (s.ea topMem) 8 = true := hr _ _ rfl
      rwa [ea_topMem] at this
    (desc_simp [State.pop64, read64_ok hr', ea_topMem, loadN_8]) <;> try rfl
  | alu op w ops =>
    cases hwd : op.writesDst
    · simp only [Instr.desc, Instr.sem, hwd, Bool.false_eq_true, ↓reduceIte, Option.map_some,
        Option.some.injEq] at hd
      subst hd
      rcases ops with ⟨dst | m, src⟩ | ⟨dst, m⟩ | ⟨dst | m, imm⟩
      · desc_simp at hg
        obtain ⟨⟨r, f⟩, he⟩ := Option.isSome_iff_exists.mp hg
        desc_simp [he, hwd]
      · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr m (wbytes w) rfl
        desc_simp at hg
        obtain ⟨⟨r, f⟩, he⟩ := Option.isSome_iff_exists.mp hg
        desc_simp [he, hwd, read_ok hr']
      · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr m (wbytes w) rfl
        desc_simp at hg
        obtain ⟨⟨r, f⟩, he⟩ := Option.isSome_iff_exists.mp hg
        desc_simp [he, hwd, read_ok hr']
      · desc_simp at hg
        obtain ⟨⟨r, f⟩, he⟩ := Option.isSome_iff_exists.mp hg
        desc_simp [he, hwd]
      · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr m (wbytes w) rfl
        desc_simp at hg
        obtain ⟨⟨r, f⟩, he⟩ := Option.isSome_iff_exists.mp hg
        desc_simp [he, hwd, read_ok hr']
    · simp only [Instr.desc, Instr.sem, hwd, Bool.false_eq_true, ↓reduceIte, Option.map_some,
        Option.some.injEq] at hd
      subst hd
      rcases ops with ⟨dst | m, src⟩ | ⟨dst, m⟩ | ⟨dst | m, imm⟩
      · desc_simp at hg
        obtain ⟨⟨r, f⟩, he⟩ := Option.isSome_iff_exists.mp hg
        desc_simp [he, hwd]
      · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr m (wbytes w) rfl
        have hw' : s.canWrite (s.ea m) (wbytes w) = true := hw m (wbytes w) rfl
        desc_simp at hg
        obtain ⟨⟨r, f⟩, he⟩ := Option.isSome_iff_exists.mp hg
        desc_simp [he, hwd, read_ok hr', write_ok hw']
      · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr m (wbytes w) rfl
        desc_simp at hg
        obtain ⟨⟨r, f⟩, he⟩ := Option.isSome_iff_exists.mp hg
        desc_simp [he, hwd, read_ok hr']
      · desc_simp at hg
        obtain ⟨⟨r, f⟩, he⟩ := Option.isSome_iff_exists.mp hg
        desc_simp [he, hwd]
      · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr m (wbytes w) rfl
        have hw' : s.canWrite (s.ea m) (wbytes w) = true := hw m (wbytes w) rfl
        desc_simp at hg
        obtain ⟨⟨r, f⟩, he⟩ := Option.isSome_iff_exists.mp hg
        desc_simp [he, hwd, read_ok hr', write_ok hw']
  | mov w ops =>
    cases hd
    rcases ops with ⟨dst | m, src⟩ | ⟨dst, m⟩ | ⟨dst | m, imm⟩
    · rfl
    · have hw' : s.canWrite (s.ea m) (wbytes w) = true := hw m (wbytes w) rfl
      show (s.write w (s.ea m) (s.readReg w src)).through m = _
      rw [write_ok hw', Result.through_next, ← storeN_w, Desc.after_store _ _ m _ rfl rfl rfl rfl]
      rfl
    · have hr' : s.canRead (s.ea m) (wbytes w) = true := hr m (wbytes w) rfl
      show (do let v ← (s.read w (s.ea m)).through m; .next (s.writeReg w dst v)) = _
      rw [read_ok hr', Result.through_next, ← loadN_w]
      rfl
    · rfl
    · have hw' : s.canWrite (s.ea m) (wbytes w) = true := hw m (wbytes w) rfl
      show (s.write w (s.ea m) (imm.signExtend w.bits)).through m = _
      rw [write_ok hw', Result.through_next, ← storeN_w, Desc.after_store _ _ m _ rfl rfl rfl rfl]
      rfl
  | jmp t =>
    rcases t with rel | (r | m)
    · cases hd; rfl
    · cases hd
      goes_simp
    · cases hd
      have hr' : s.canRead (s.ea m) (wbytes .w64) = true := hr m 8 rfl
      goes_simp [read_ok hr', State.load]
  | jcc c rel =>
    cases hd
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (show (c.eval s.flags).isSome = true from hg)
    goes_simp [hb]
    cases b <;> rfl
  | ret =>
    cases hd
    have hr' : s.canRead (s.getReg .rsp) 8 = true := by
      have this : s.canRead (s.ea topMem) 8 = true := hr topMem 8 rfl
      rwa [ea_topMem] at this
    goes_simp [read64_ok hr']
    rfl
  | call t =>
    have hw' : s.canWrite (s.getReg .rsp - 8) 8 = true := by
      have this : s.canWrite (s.ea pushMem) 8 = true := by
        rcases t with rel | (r | m) <;> cases hd <;> exact hw pushMem 8 rfl
      rwa [ea_pushMem] at this
    have hw'' : (s.setReg .rsp (s.getReg .rsp - 8)).canWrite (s.getReg .rsp - 8) 8 = true := hw'
    rcases t with rel | (r | m)
    · cases hd
      goes_simp [add_neg, write64_ok hw'']
      rfl
    · cases hd
      goes_simp [add_neg, write64_ok hw'']
      rfl
    · cases hd
      have hr' : s.canRead (s.ea m) (wbytes .w64) = true := hr m 8 rfl
      goes_simp [add_neg, read_ok hr', write64_ok hw'', State.load]
      rfl
  | ud2 => cases hd
  | syscall => cases hd
end TypedAsm.U
