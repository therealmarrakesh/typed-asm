import TypedAsm.Decode
import Std.Tactic.BVDecide

/-!
# Decoding inverts encoding

For every instruction, decoding its encoding gives the instruction back,
whatever bytes follow.
-/

namespace TypedAsm

/-! ## Names and numbers -/

theorem Reg.ofNum_low_ext (r : Reg) : Reg.ofNum (r.num % 8 + extBit r.ext) = r := by
  cases r <;> rfl

theorem Reg.low_lt (r : Reg) : r.low < 8 := by
  cases r <;> decide

theorem Reg.ofNum_low_add (r : Reg) : Reg.ofNum (r.low + extBit r.ext) = r := by
  cases r <;> rfl

theorem IndexReg.ofNum_toReg (i : IndexReg) :
    IndexReg.ofNum (i.toReg.num % 8 + extBit i.toReg.ext) = some i := by
  cases i <;> rfl

/-- An index register is never encoded as "no index". -/
theorem IndexReg.not_none (i : IndexReg) : ¬(i.toReg.num % 8 = 4 ∧ i.toReg.ext = false) := by
  cases i <;> decide

theorem Scale.ofCode_code (s : Scale) : Scale.ofCode s.code = s := by
  cases s <;> rfl

theorem Scale.code_lt (s : Scale) : s.code < 4 := by
  cases s <;> decide

theorem Cond.ofCode_code (c : Cond) : Cond.ofCode c.code = some c := by
  cases c <;> rfl

theorem Cond.code_lt (c : Cond) : c.code < 16 := by
  cases c <;> decide

theorem AluOp.ofCode_code (op : AluOp) : AluOp.ofCode op.code = op := by
  cases op <;> rfl

theorem AluOp.code_lt (op : AluOp) : op.code < 8 := by
  cases op <;> decide

theorem ShiftOp.ofCode_code (op : ShiftOp) : ShiftOp.ofCode op.code = some op := by
  cases op <;> rfl

theorem ShiftOp.code_lt (op : ShiftOp) : op.code < 8 := by
  cases op <;> decide

theorem MulDivOp.ofCode_code (op : MulDivOp) : MulDivOp.ofCode op.code = some op := by
  cases op <;> rfl

theorem MulDivOp.code_lt (op : MulDivOp) : op.code < 8 := by
  cases op <;> decide

/-! ## Bytes and their fields -/

theorem byte_toNat {n : Nat} (h : n < 256) : (byte n).toNat = n := by
  simp only [byte, BitVec.toNat_ofNat]
  omega

theorem modrm_mode {mode reg rm : Nat} (h : mode < 4) : (modrmByte mode reg rm).toNat / 64 = mode := by
  rw [modrmByte, byte_toNat (by omega)]; omega

theorem modrm_reg {mode reg rm : Nat} (h : mode < 4) :
    (modrmByte mode reg rm).toNat / 8 % 8 = reg % 8 := by
  rw [modrmByte, byte_toNat (by omega)]; omega

theorem modrm_rm {mode reg rm : Nat} (h : mode < 4) : (modrmByte mode reg rm).toNat % 8 = rm % 8 := by
  rw [modrmByte, byte_toNat (by omega)]; omega

theorem sib_scale {scale index base : Nat} (h : scale < 4) :
    (sibByte scale index base).toNat / 64 = scale := by
  rw [sibByte, byte_toNat (by omega)]; omega

theorem sib_index {scale index base : Nat} (h : scale < 4) :
    (sibByte scale index base).toNat / 8 % 8 = index % 8 := by
  rw [sibByte, byte_toNat (by omega)]; omega

theorem sib_base {scale index base : Nat} (h : scale < 4) :
    (sibByte scale index base).toNat % 8 = base % 8 := by
  rw [sibByte, byte_toNat (by omega)]; omega

/-! ## Reading back what was written -/

theorem take32_le32 (v : BitVec 32) (rest : List Byte) : take32 (le32 v ++ rest) = some (v, rest) := by
  have h : v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v := by
    bv_decide
  simp only [le32, take32, List.cons_append, List.nil_append, h]

theorem take64_le64 (v : BitVec 64) (rest : List Byte) : take64 (le64 v ++ rest) = some (v, rest) := by
  have h : v.extractLsb' 32 32 ++ v.extractLsb' 0 32 = v := by bv_decide
  simp only [le64, take64, List.append_assoc, take32_le32, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, h]

theorem take8s_imm8 {v : BitVec 32} (h : fits8 v = true) (rest : List Byte) :
    take8s (imm8 v ++ rest) = some (v, rest) := by
  simp only [fits8, beq_iff_eq] at h
  simp only [imm8, take8s, List.cons_append, List.nil_append, h]

/-- The displacement the encoder chose is read back. -/
theorem takeDisp_dispEnc (b : Reg) (d : BitVec 32) (rest : List Byte) :
    takeDisp (dispEnc b d).1 ((dispEnc b d).2 ++ rest) = some (d, rest) := by
  unfold dispEnc
  split
  · next h =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    simp [takeDisp, h.1]
  · split
    · next h => simp [takeDisp, take8s_imm8 h]
    · simp [takeDisp, take32_le32]

theorem dispEnc_mode_lt (b : Reg) (d : BitVec 32) : (dispEnc b d).1 < 3 := by
  unfold dispEnc
  split
  · decide
  · split <;> simp

/-- A base of `rbp` or `r13` is never encoded in the mode that means "no base". -/
theorem dispEnc_mode_ne_zero {b : Reg} (d : BitVec 32) (h : b.low = 5) : (dispEnc b d).1 ≠ 0 := by
  unfold dispEnc
  split
  · next hc => simp [h] at hc
  · split <;> simp

/-! ## The `REX` prefix -/

/-- An opcode byte that cannot be mistaken for a `REX` prefix or for the
`F3` prefix. Every first opcode byte the encoder emits is one. -/
def PlainOp (op : Byte) : Prop :=
  (op.toNat < 0x40 ∨ 0x50 ≤ op.toNat) ∧ op.toNat ≠ 0xF3

theorem takeRex_rex (w r x b f : Bool) {op : Byte} (hop : PlainOp op) (t : List Byte) :
    takeRex (rex w r x b f ++ op :: t) = (⟨w || r || x || b || f, w, r, x, b⟩, op :: t) := by
  obtain ⟨hop, -⟩ := hop
  cases w <;> cases r <;> cases x <;> cases b <;> cases f <;>
    simp [rex, takeRex, byte, Rex.none] <;> omega

/-- Decoding an instruction with no `F3` prefix: the `REX` prefix is read,
then the opcode. -/
theorem decodeFrom_rex (w r x b f : Bool) {op : Byte} (hop : PlainOp op) (t : List Byte) :
    decodeFrom (rex w r x b f ++ op :: t)
      = decodeOp false ⟨w || r || x || b || f, w, r, x, b⟩ op.toNat t := by
  have hnot : ∀ p : Byte, p ∈ (rex w r x b f ++ [op]).head? → p.toNat ≠ 0xF3 := by
    intro p hp
    cases w <;> cases r <;> cases x <;> cases b <;> cases f <;>
      simp [rex, byte] at hp <;> subst hp <;> first | exact hop.2 | decide
  have hsplit : ∃ p rest, rex w r x b f ++ op :: t = p :: rest ∧ p.toNat ≠ 0xF3 := by
    cases hr : rex w r x b f with
    | nil => exact ⟨op, t, rfl, hop.2⟩
    | cons p ps =>
      refine ⟨p, ps ++ op :: t, rfl, hnot p ?_⟩
      simp [hr]
  obtain ⟨p, rest, heq, hp⟩ := hsplit
  have key := takeRex_rex w r x b f hop t
  simp only [decodeFrom, heq, hp, ite_false] at key ⊢
  rw [key]

/-- Decoding an instruction with the `F3` prefix. -/
theorem decodeFrom_f3_rex (w r x b f : Bool) {op : Byte} (hop : PlainOp op) (t : List Byte) :
    decodeFrom (0xF3 :: (rex w r x b f ++ op :: t))
      = decodeOp true ⟨w || r || x || b || f, w, r, x, b⟩ op.toNat t := by
  have key := takeRex_rex w r x b f hop t
  simp only [decodeFrom, show (0xF3 : Byte).toNat = 0xF3 from rfl, ite_true]
  rw [key]

/-! ## Operands -/

-- The cases below share one list of simp lemmas, not all of which each case needs.
set_option linter.unusedSimpArgs false in
/-- An operand is read back, along with the register field it was written with. -/
theorem takeOperand_encode (rm : RM) (reg : Nat) (p w r : Bool) (rest : List Byte) :
    takeOperand ⟨p, w, r, (rm.encode reg).x, (rm.encode reg).b⟩ ((rm.encode reg).bytes ++ rest)
      = some (reg % 8, rm, rest) := by
  cases rm with
  | reg r' =>
    simp [RM.encode, takeOperand, modrm_mode, modrm_reg, modrm_rm, Reg.ofNum_low_ext]
  | mem m =>
    cases m with
    | rip disp =>
      simp [RM.encode, Mem.encode, takeOperand, modrm_mode, modrm_reg, modrm_rm, take32_le32]
    | sib base index disp =>
      cases base with
      | none =>
        cases index with
        | none =>
          simp [RM.encode, Mem.encode, takeOperand, modrm_mode, modrm_reg, modrm_rm, sib_scale,
            sib_index, sib_base, take32_le32]
        | some is =>
          obtain ⟨i, s⟩ := is
          have hs := s.code_lt
          have hi := i.not_none
          simp [RM.encode, Mem.encode, takeOperand, modrm_mode, modrm_reg, modrm_rm, sib_scale hs,
            sib_index hs, sib_base hs, take32_le32, IndexReg.ofNum_toReg, Scale.ofCode_code, hi]
      | some b =>
        have hm := dispEnc_mode_lt b disp
        have hm4 : (dispEnc b disp).1 < 4 := by omega
        have hm3 : (dispEnc b disp).1 ≠ 3 := by omega
        have hd := takeDisp_dispEnc b disp rest
        have h5 := dispEnc_mode_ne_zero (b := b) disp
        have hlow : b.num % 8 = b.low := rfl
        cases index with
        | none =>
          by_cases h4 : b.low = 4
          · have h5' : ¬ b.low = 5 := by omega
            simp [RM.encode, Mem.encode, takeOperand, h4, modrm_mode hm4, modrm_reg hm4,
              modrm_rm hm4, hm3, sib_index, sib_base, hd]
            rw [← h4]; exact Reg.ofNum_low_add b
          · have hrm4 : ¬ b.num % 8 = 4 := by rw [hlow]; exact h4
            by_cases hb5 : b.low = 5
            · have := h5 hb5
              simp [RM.encode, Mem.encode, takeOperand, h4, modrm_mode hm4, modrm_reg hm4,
                modrm_rm hm4, hm3, hrm4, hd, hlow, hb5, this, Reg.ofNum_low_add]
              rw [← hb5]; exact Reg.ofNum_low_add b
            · simp [RM.encode, Mem.encode, takeOperand, h4, modrm_mode hm4, modrm_reg hm4,
                modrm_rm hm4, hm3, hrm4, hd, hlow, hb5, Reg.ofNum_low_add]
        | some is =>
          obtain ⟨i, s⟩ := is
          have hs := s.code_lt
          have hi := i.not_none
          by_cases hb5 : b.low = 5
          · have := h5 hb5
            simp [RM.encode, Mem.encode, takeOperand, modrm_mode hm4, modrm_reg hm4, modrm_rm hm4,
              hm3, sib_scale hs, sib_index hs, sib_base hs, hd, hlow, hb5, this,
              IndexReg.ofNum_toReg, Scale.ofCode_code, hi, Reg.ofNum_low_add]
            rw [← hb5]; exact Reg.ofNum_low_add b
          · simp [RM.encode, Mem.encode, takeOperand, modrm_mode hm4, modrm_reg hm4, modrm_rm hm4,
              hm3, sib_scale hs, sib_index hs, sib_base hs, hd, hlow, hb5,
              IndexReg.ofNum_toReg, Scale.ofCode_code, hi, Reg.ofNum_low_add]

/-! ## Instructions -/

instance (op : Byte) : Decidable (PlainOp op) := by
  unfold PlainOp
  infer_instance

theorem Width.ofRexW (w : Width) : (if w.rexW = true then Width.w64 else Width.w32) = w := by
  cases w <;> rfl

theorem AluOp.ofCode_mod (op : AluOp) : AluOp.ofCode (op.code % 8) = op := by
  cases op <;> rfl

theorem ShiftOp.ofCode_mod (op : ShiftOp) : ShiftOp.ofCode (op.code % 8) = some op := by
  cases op <;> rfl

theorem MulDivOp.ofCode_mod (op : MulDivOp) : MulDivOp.ofCode (op.code % 8) = some op := by
  cases op <;> rfl

/-- Brings an encoding into the form "prefix, opcode byte, the rest". -/
macro "rt_shape" : tactic =>
  `(tactic| simp only [Instr.encode, encodeOp, List.append_assoc, List.cons_append,
      List.nil_append, AluOp.code, ShiftOp.code, MulDivOp.code, Cond.code])

/-- Evaluates the decoder on an opcode and reads the operands back. -/
macro "rt_decode" : tactic =>
  `(tactic| simp [decodeOp, decode0F, takeMem, takeOperand_encode, take32_le32, take64_le64,
      Reg.ofNum_low_ext, Width.ofRexW, AluOp.ofCode_mod, ShiftOp.ofCode_mod, MulDivOp.ofCode_mod,
      Cond.ofCode, AluOp.ofCode, ShiftOp.ofCode, MulDivOp.ofCode, byteRegOk, byteRmOk, byte])

/-- The usual proof: shape the encoding, read the prefix, evaluate the decoder. -/
macro "rt" : tactic =>
  `(tactic| (rt_shape; rw [decodeFrom_rex _ _ _ _ _ (by decide)]; rt_decode))

theorem decodeFrom_alu_rm_r (op : AluOp) (w : Width) (dst : RM) (src : Reg) (rest : List Byte) :
    decodeFrom ((Instr.alu op w (.rm_r dst src)).encode ++ rest)
      = some (.alu op w (.rm_r dst src), rest) := by
  cases op <;> rt

theorem decodeFrom_alu_r_m (op : AluOp) (w : Width) (dst : Reg) (src : Mem) (rest : List Byte) :
    decodeFrom ((Instr.alu op w (.r_m dst src)).encode ++ rest)
      = some (.alu op w (.r_m dst src), rest) := by
  cases op <;> rt

theorem decodeFrom_mov_rm_r (w : Width) (dst : RM) (src : Reg) (rest : List Byte) :
    decodeFrom ((Instr.mov w (.rm_r dst src)).encode ++ rest)
      = some (.mov w (.rm_r dst src), rest) := by
  rt

theorem decodeFrom_mov_r_m (w : Width) (dst : Reg) (src : Mem) (rest : List Byte) :
    decodeFrom ((Instr.mov w (.r_m dst src)).encode ++ rest)
      = some (.mov w (.r_m dst src), rest) := by
  rt

theorem decodeFrom_lea (w : Width) (dst : Reg) (m : Mem) (rest : List Byte) :
    decodeFrom ((Instr.lea w dst m).encode ++ rest) = some (.lea w dst m, rest) := by
  rt

theorem decodeFrom_test_reg (w : Width) (dst : RM) (r : Reg) (rest : List Byte) :
    decodeFrom ((Instr.test w dst (.reg r)).encode ++ rest) = some (.test w dst (.reg r), rest) := by
  rt

/-- As `rt`, for encodings whose register has been made concrete. -/
macro "rt_reg" : tactic =>
  `(tactic| (rt_shape; simp only [Reg.low, Reg.num, Reg.ext]
             rw [decodeFrom_rex _ _ _ _ _ (by decide)]
             simp [decodeOp, decode0F, take32_le32, take64_le64, extBit, Reg.ofNum, byte]))

/-- For encodings with no prefix and a fixed opcode. -/
macro "rt_plain" : tactic =>
  `(tactic| simp [Instr.encode, Cond.code, decodeFrom, takeRex, Rex.none, decodeOp, decode0F,
      take32_le32, Cond.ofCode, byte])

theorem decodeFrom_alu_rm_i (op : AluOp) (w : Width) (dst : RM) (imm : BitVec 32)
    (rest : List Byte) :
    decodeFrom ((Instr.alu op w (.rm_i dst imm)).encode ++ rest)
      = some (.alu op w (.rm_i dst imm), rest) := by
  by_cases h8 : fits8 imm = true
  · simp only [Instr.encode, h8, ite_true]
    cases op <;>
      (simp only [encodeOp, List.append_assoc, List.cons_append, List.nil_append, AluOp.code]
       rw [decodeFrom_rex _ _ _ _ _ (by decide)]
       simp [decodeOp, takeOperand_encode, take8s_imm8 h8, Width.ofRexW, AluOp.ofCode])
  · by_cases hax : dst = .reg .rax
    · subst hax
      simp only [Instr.encode, h8, Bool.false_eq_true, ↓reduceIte]
      cases op <;>
        (simp only [List.append_assoc, List.cons_append, List.nil_append, AluOp.code]
         rw [decodeFrom_rex _ _ _ _ _ (by decide)]
         simp [decodeOp, take32_le32, Width.ofRexW, AluOp.ofCode, byte])
    · simp only [Instr.encode, h8, hax, Bool.false_eq_true, ↓reduceIte]
      cases op <;>
        (simp only [encodeOp, List.append_assoc, List.cons_append, List.nil_append, AluOp.code]
         rw [decodeFrom_rex _ _ _ _ _ (by decide)]
         simp [decodeOp, takeOperand_encode, take32_le32, Width.ofRexW, AluOp.ofCode])

theorem decodeFrom_test_imm (w : Width) (dst : RM) (i : BitVec 32) (rest : List Byte) :
    decodeFrom ((Instr.test w dst (.imm i)).encode ++ rest) = some (.test w dst (.imm i), rest) := by
  by_cases hax : dst = .reg .rax
  · subst hax
    simp only [Instr.encode, ite_true, List.append_assoc, List.cons_append, List.nil_append]
    rw [decodeFrom_rex _ _ _ _ _ (by decide)]
    simp [decodeOp, take32_le32, Width.ofRexW]
  · simp only [Instr.encode, hax, ite_false, encodeOp, List.append_assoc, List.cons_append,
      List.nil_append]
    rw [decodeFrom_rex _ _ _ _ _ (by decide)]
    simp [decodeOp, takeOperand_encode, take32_le32, Width.ofRexW]

theorem decodeFrom_unary (op : UnOp) (w : Width) (dst : RM) (rest : List Byte) :
    decodeFrom ((Instr.unary op w dst).encode ++ rest) = some (.unary op w dst, rest) := by
  cases op <;> rt

theorem decodeFrom_shift (op : ShiftOp) (w : Width) (dst : RM) (c : Count) (rest : List Byte) :
    decodeFrom ((Instr.shift op w dst c).encode ++ rest) = some (.shift op w dst c, rest) := by
  cases c with
  | cl => cases op <;> rt
  | imm n =>
    by_cases h1 : (n == 1) = true
    · have hn : n = 1 := by simpa using h1
      subst hn
      cases op <;>
        (simp only [Instr.encode, beq_self_eq_true, ite_true, encodeOp, List.append_assoc,
           List.cons_append, List.nil_append, ShiftOp.code]
         rw [decodeFrom_rex _ _ _ _ _ (by decide)]
         simp [decodeOp, takeOperand_encode, Width.ofRexW, ShiftOp.ofCode])
    · cases op <;>
        (simp only [Instr.encode, h1, Bool.false_eq_true, ↓reduceIte, encodeOp, List.append_assoc, List.cons_append,
           List.nil_append, ShiftOp.code]
         rw [decodeFrom_rex _ _ _ _ _ (by decide)]
         simp [decodeOp, takeOperand_encode, Width.ofRexW, ShiftOp.ofCode])

theorem decodeFrom_mulDiv (op : MulDivOp) (w : Width) (src : RM) (rest : List Byte) :
    decodeFrom ((Instr.mulDiv op w src).encode ++ rest) = some (.mulDiv op w src, rest) := by
  cases op <;> rt

theorem decodeFrom_imul2 (w : Width) (dst : Reg) (src : RM) (rest : List Byte) :
    decodeFrom ((Instr.imul2 w dst src).encode ++ rest) = some (.imul2 w dst src, rest) := by
  rt

theorem decodeFrom_imul3 (w : Width) (dst : Reg) (src : RM) (imm : BitVec 32) (rest : List Byte) :
    decodeFrom ((Instr.imul3 w dst src imm).encode ++ rest) = some (.imul3 w dst src imm, rest) := by
  by_cases h8 : fits8 imm = true
  · simp only [Instr.encode, h8, ite_true, encodeOp, List.append_assoc, List.cons_append,
      List.nil_append]
    rw [decodeFrom_rex _ _ _ _ _ (by decide)]
    simp [decodeOp, takeOperand_encode, take8s_imm8 h8, Width.ofRexW, Reg.ofNum_low_ext]
  · simp only [Instr.encode, h8, Bool.false_eq_true, ↓reduceIte, encodeOp, List.append_assoc, List.cons_append,
      List.nil_append]
    rw [decodeFrom_rex _ _ _ _ _ (by decide)]
    simp [decodeOp, takeOperand_encode, take32_le32, Width.ofRexW, Reg.ofNum_low_ext]

theorem decodeFrom_popcnt (w : Width) (dst : Reg) (src : RM) (rest : List Byte) :
    decodeFrom ((Instr.popcnt w dst src).encode ++ rest) = some (.popcnt w dst src, rest) := by
  rt_shape
  rw [decodeFrom_f3_rex _ _ _ _ _ (by decide)]
  rt_decode

theorem decodeFrom_bswap (w : Width) (r : Reg) (rest : List Byte) :
    decodeFrom ((Instr.bswap w r).encode ++ rest) = some (.bswap w r, rest) := by
  cases r <;> (rt_reg; try exact Width.ofRexW w)

theorem decodeFrom_mov_rm_i (w : Width) (dst : RM) (imm : BitVec 32) (rest : List Byte) :
    decodeFrom ((Instr.mov w (.rm_i dst imm)).encode ++ rest)
      = some (.mov w (.rm_i dst imm), rest) := by
  cases w with
  | w64 => rt
  | w32 =>
    cases dst with
    | mem m => rt
    | reg r => cases r <;> rt_reg

theorem decodeFrom_movAbs (dst : Reg) (imm : BitVec 64) (rest : List Byte) :
    decodeFrom ((Instr.movAbs dst imm).encode ++ rest) = some (.movAbs dst imm, rest) := by
  cases dst <;> rt_reg

theorem decodeFrom_store8 (dst : Mem) (src : Reg) (rest : List Byte) :
    decodeFrom ((Instr.store8 dst src).encode ++ rest) = some (.store8 dst src, rest) := by
  rt_shape
  rw [decodeFrom_rex _ _ _ _ _ (by decide)]
  rt_decode

theorem decodeFrom_movzx (w : Width) (dst : Reg) (sw : NarrowW) (src : RM) (rest : List Byte) :
    decodeFrom ((Instr.movzx w dst sw src).encode ++ rest) = some (.movzx w dst sw src, rest) := by
  cases sw with
  | w16 => rt
  | w8 =>
    rt_shape
    rw [decodeFrom_rex _ _ _ _ _ (by decide)]
    rt_decode

theorem decodeFrom_movsx (w : Width) (dst : Reg) (sw : NarrowW) (src : RM) (rest : List Byte) :
    decodeFrom ((Instr.movsx w dst sw src).encode ++ rest) = some (.movsx w dst sw src, rest) := by
  cases sw with
  | w16 => rt
  | w8 =>
    rt_shape
    rw [decodeFrom_rex _ _ _ _ _ (by decide)]
    rt_decode

theorem decodeFrom_movsxd (dst : Reg) (src : RM) (rest : List Byte) :
    decodeFrom ((Instr.movsxd dst src).encode ++ rest) = some (.movsxd dst src, rest) := by
  rt

theorem decodeFrom_cmov (c : Cond) (w : Width) (dst : Reg) (src : RM) (rest : List Byte) :
    decodeFrom ((Instr.cmov c w dst src).encode ++ rest) = some (.cmov c w dst src, rest) := by
  cases c <;> rt

theorem decodeFrom_setcc (c : Cond) (dst : RM) (rest : List Byte) :
    decodeFrom ((Instr.setcc c dst).encode ++ rest) = some (.setcc c dst, rest) := by
  cases c <;>
    (rt_shape
     rw [decodeFrom_rex _ _ _ _ _ (by decide)]
     rt_decode)

theorem decodeFrom_push (r : Reg) (rest : List Byte) :
    decodeFrom ((Instr.push r).encode ++ rest) = some (.push r, rest) := by
  cases r <;> rt_reg

theorem decodeFrom_pop (r : Reg) (rest : List Byte) :
    decodeFrom ((Instr.pop r).encode ++ rest) = some (.pop r, rest) := by
  cases r <;> rt_reg

theorem decodeFrom_jmp (t : Target) (rest : List Byte) :
    decodeFrom ((Instr.jmp t).encode ++ rest) = some (.jmp t, rest) := by
  cases t with
  | rel d => rt_plain
  | ind rm => rt

theorem decodeFrom_call (t : Target) (rest : List Byte) :
    decodeFrom ((Instr.call t).encode ++ rest) = some (.call t, rest) := by
  cases t with
  | rel d => rt_plain
  | ind rm => rt

theorem decodeFrom_jcc (c : Cond) (d : BitVec 32) (rest : List Byte) :
    decodeFrom ((Instr.jcc c d).encode ++ rest) = some (.jcc c d, rest) := by
  cases c <;> rt_plain

/-- **Decoding inverts encoding.** Whatever bytes follow an instruction's
encoding, decoding gives back the instruction and leaves those bytes. -/
theorem decodeFrom_encode (i : Instr) (rest : List Byte) :
    decodeFrom (i.encode ++ rest) = some (i, rest) := by
  cases i with
  | alu op w ops =>
    cases ops with
    | rm_r dst src => exact decodeFrom_alu_rm_r op w dst src rest
    | r_m dst src => exact decodeFrom_alu_r_m op w dst src rest
    | rm_i dst imm => exact decodeFrom_alu_rm_i op w dst imm rest
  | test w dst src =>
    cases src with
    | reg r => exact decodeFrom_test_reg w dst r rest
    | imm i => exact decodeFrom_test_imm w dst i rest
  | unary op w dst => exact decodeFrom_unary op w dst rest
  | shift op w dst c => exact decodeFrom_shift op w dst c rest
  | mulDiv op w src => exact decodeFrom_mulDiv op w src rest
  | imul2 w dst src => exact decodeFrom_imul2 w dst src rest
  | imul3 w dst src imm => exact decodeFrom_imul3 w dst src imm rest
  | popcnt w dst src => exact decodeFrom_popcnt w dst src rest
  | bswap w r => exact decodeFrom_bswap w r rest
  | cdq => rt_plain
  | cqo => rt_plain
  | mov w ops =>
    cases ops with
    | rm_r dst src => exact decodeFrom_mov_rm_r w dst src rest
    | r_m dst src => exact decodeFrom_mov_r_m w dst src rest
    | rm_i dst imm => exact decodeFrom_mov_rm_i w dst imm rest
  | movAbs dst imm => exact decodeFrom_movAbs dst imm rest
  | store8 dst src => exact decodeFrom_store8 dst src rest
  | movzx w dst sw src => exact decodeFrom_movzx w dst sw src rest
  | movsx w dst sw src => exact decodeFrom_movsx w dst sw src rest
  | movsxd dst src => exact decodeFrom_movsxd dst src rest
  | lea w dst addr => exact decodeFrom_lea w dst addr rest
  | cmov c w dst src => exact decodeFrom_cmov c w dst src rest
  | setcc c dst => exact decodeFrom_setcc c dst rest
  | push r => exact decodeFrom_push r rest
  | pop r => exact decodeFrom_pop r rest
  | jmp t => exact decodeFrom_jmp t rest
  | jcc c d => exact decodeFrom_jcc c d rest
  | call t => exact decodeFrom_call t rest
  | ret => rt_plain
  | nop => rt_plain
  | ud2 => rt_plain
  | syscall => rt_plain

/-- Decoding an instruction's encoding gives the instruction and its length. -/
theorem decode_encode (i : Instr) (rest : List Byte) :
    decode (i.encode ++ rest) = some (i, i.length) := by
  simp [decode, decodeFrom_encode, Instr.length]

end TypedAsm
