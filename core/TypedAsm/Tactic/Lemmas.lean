import Lean.Elab.Command
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.RCases
import Lean.Meta.Tactic.Simp.RegisterCommand
import Lean.Elab.Deriving.ToExpr
import Lean.Util.CollectAxioms
import Lean.Meta.Eval
import Std.Data.HashMap
import TypedAsm.Addr
import TypedAsm.Facts
import TypedAsm.Reify
import TypedAsm.Program
import TypedAsm.Fn
import TypedAsm.Print
import TypedAsm.Blocks
import TypedAsm.LinuxOld
import TypedAsm.Owned
import TypedAsm.RegMap
import TypedAsm.Entry
import TypedAsm.Segments
import TypedAsm.EndToEnd
import TypedAsm.Lookup
import TypedAsm.FnEx

/-!
# The tactics: lemmas

Lemmas the tactics apply.
-/

namespace TypedAsm

/-! ## Lemmas the tactics apply -/

/-- The byte a displacement reaches, computed from the displacement. -/
theorem byteDisp_of (disp : BitVec 32) (hlt : disp.toNat < 2 ^ 31) :
    byteDisp disp.toNat disp := by
  refine ⟨?_, hlt⟩
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

/-- Releasing the pieces at the top of the stack that come to `k` bytes, with
what is left of the stack computed. -/
theorem Straight.freeFrame' {Ψ : MemTy} {next : BitVec 64} {Γ : Ctx} {k : Nat} {imm : BitVec 32}
    {rest : List Shape} (hk : byteDisp k imm) (hd : stackDrop Γ.stack k = some rest) :
    Straight Ψ next Γ (.alu .add .w64 (.rm_i (.reg .rsp) imm))
      { Γ.moveSp (BitVec.ofNat 64 k) with
        stack := rest, room := Γ.room + k, flags := Flags.Known } := by
  obtain ⟨top, hst, hlen⟩ := stackDrop_eq hd
  exact .freeFrame hk hst hlen

/-! Which piece of the stack a byte above the stack pointer is in: at a fixed
distance, through an index scaled by eight, and through any index. -/

theorem stackAt_lit {d o : Nat} (h : o ≤ d) : d = o + (d - o) := by omega

theorem stackAt_idx8 {x j o : Nat} (ho : o % 8 = 0) (hm : o / 8 ≤ j) :
    8 * (x + j) = o + (0 + 8 * (x + (j - o / 8))) := by omega

theorem stackAt_bytes {x dd o : Nat} (h : o ≤ dd) : x + dd = o + (x + (dd - o)) := by omega

/-- A piece of the stack may be regarded as two, cut a fixed distance above
the stack pointer. -/
theorem BlockOk.splitStackAt {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}
    {a : BitVec 64} {Γ : Ctx} {k d : Nat} {S : Shape}
    (hk : Γ.stack[k]? = some S) (_hlo : stackOff Γ.stack k < d)
    (hm : d - stackOff Γ.stack k ≤ S.size)
    (hrest : BlockOk Φ fetch sys Ψ a
      { Γ with stack := Γ.stack.take k ++
          [S.take (d - stackOff Γ.stack k), S.drop (d - stackOff Γ.stack k)] ++
          Γ.stack.drop (k + 1) }) :
    BlockOk Φ fetch sys Ψ a Γ :=
  .splitStack hk hm hrest

/-- The two pieces of the stack that meet a fixed distance above the stack
pointer may be regarded as one. -/
theorem BlockOk.joinStackAt {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}
    {a : BitVec 64} {Γ : Ctx} {k d : Nat} {S₁ S₂ : Shape}
    (hk : Γ.stack[k]? = some S₁) (hk' : Γ.stack[k + 1]? = some S₂)
    (_hd : stackOff Γ.stack (k + 1) = d)
    (hrest : BlockOk Φ fetch sys Ψ a
      { Γ with stack := Γ.stack.take k ++ [S₁.append S₂] ++ Γ.stack.drop (k + 2) }) :
    BlockOk Φ fetch sys Ψ a Γ :=
  .joinStack hk hk' hrest

/-- Eight bytes of the stack, a fixed distance above the stack pointer, may
be given a name for the value they hold. -/
theorem BlockOk.nameSlotAt {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}
    {a : BitVec 64} {Γ : Ctx} {k d : Nat} {S : Shape}
    (hk : Γ.stack[k]? = some S) (_hlo : stackOff Γ.stack k ≤ d)
    (hi : d - stackOff Γ.stack k + 8 ≤ S.size)
    (hrest : ∀ v, BlockOk Φ fetch sys Ψ a
      { Γ with stack := Γ.stack.set k (S.set (d - stackOff Γ.stack k) (.eq v)) }) :
    BlockOk Φ fetch sys Ψ a Γ :=
  .nameSlot hk hi hrest

/-! Operands at a fixed address. Which block the address falls in, and where,
is found by computation: the first premise of each lemma below is there only
to be solved by `rfl`, which determines the block and the byte. -/

/-- The block among `bs` that contains address `a`, with the byte of it that
`a` is at. -/
def MemTy.locate (bs : List (BitVec 64 × Layout)) (a : BitVec 64) :
    Option (BitVec 64 × Nat) :=
  bs.findSome? fun x =>
    if (a - x.1).toNat < x.2.size then some (x.1, (a - x.1).toNat) else none

section Globals

variable {bs : List (BitVec 64 × Layout)} {kinds : List (Nat × Shape)} {next base : BitVec 64}
  {Γ : Ctx} {l : Layout} {d n : Nat} {disp : BitVec 32} {τ : Ty}

theorem ReadOk.global_of
    (_ : MemTy.locate bs (next + disp.signExtend 64) = some (base, d))
    (hl : MemTy.ofList bs kinds base = some l)
    (haddr : next + disp.signExtend 64 = base + BitVec.ofNat 64 d)
    (hin : d + n ≤ l.shape.size) :
    ReadOk (MemTy.ofList bs kinds) next Γ n (.mem (.rip disp)) :=
  .global hl haddr hin

theorem WriteIntOk.global_of
    (_ : MemTy.locate bs (next + disp.signExtend 64) = some (base, d))
    (hl : MemTy.ofList bs kinds base = some l) (hw : l.writable = true)
    (haddr : next + disp.signExtend 64 = base + BitVec.ofNat 64 d)
    (hin : d + n ≤ l.shape.size) (hfree : l.shape.free d n = true) :
    WriteIntOk (MemTy.ofList bs kinds) next Γ n (.mem (.rip disp)) Γ :=
  .global hl hw haddr hin hfree

theorem Holds.global_of
    (_ : MemTy.locate bs (next + disp.signExtend 64) = some (base, d))
    (hl : MemTy.ofList bs kinds base = some l)
    (haddr : next + disp.signExtend 64 = base + BitVec.ofNat 64 d)
    (hi : l.shape.valAt d = some τ) :
    Holds (MemTy.ofList bs kinds) next Γ (.mem (.rip disp)) τ :=
  .global hl haddr hi

/-- Bytes at an exactly known address, which is found among the program's
blocks. -/
theorem ReadOk.placed_of {m : Mem} {p : BitVec 64} (he : EaIs Γ m p)
    (_ : MemTy.locate bs p = some (base, d))
    (hl : MemTy.ofList bs kinds base = some l) (haddr : p = base + BitVec.ofNat 64 d)
    (hin : d + n ≤ l.shape.size) : ReadOk (MemTy.ofList bs kinds) next Γ n (.mem m) :=
  .placed he hl haddr hin

theorem WriteIntOk.placed_of {m : Mem} {p : BitVec 64} (he : EaIs Γ m p)
    (_ : MemTy.locate bs p = some (base, d))
    (hl : MemTy.ofList bs kinds base = some l) (hw : l.writable = true)
    (haddr : p = base + BitVec.ofNat 64 d)
    (hin : d + n ≤ l.shape.size) (hfree : l.shape.free d n = true) :
    WriteIntOk (MemTy.ofList bs kinds) next Γ n (.mem m) Γ :=
  .placed he hl hw haddr hin hfree

theorem Holds.placed_of {m : Mem} {p : BitVec 64} (he : EaIs Γ m p)
    (_ : MemTy.locate bs p = some (base, d))
    (hl : MemTy.ofList bs kinds base = some l) (haddr : p = base + BitVec.ofNat 64 d)
    (hi : l.shape.valAt d = some τ) : Holds (MemTy.ofList bs kinds) next Γ (.mem m) τ :=
  .placed he hl haddr hi

/-- Where an index into a table at a fixed address lands: `k` bytes on from
the table, which is `off` bytes into its block. -/
theorem table_addr {c base : BitVec 64} {sc : Scale} {off k : Nat}
    (hd : disp.signExtend 64 = base + BitVec.ofNat 64 off)
    (hk : (c <<< sc.shift) + (0 : BitVec 32).signExtend 64 = BitVec.ofNat 64 k) :
    (c <<< sc.shift) + disp.signExtend 64 = base + BitVec.ofNat 64 (off + k) := by
  have hk' : c <<< sc.shift = BitVec.ofNat 64 k := by simpa using hk
  rw [hk', hd, BitVec.ofNat_add]
  ac_rfl

/-- Bytes of a table at a fixed address, reached through an index that holds
an exactly known value: the table is found among the program's blocks, and
the index is shown to land inside it. -/
theorem ReadOk.table_of {x : IndexReg} {sc : Scale} {c : BitVec 64} {off k : Nat}
    (hx : Γ.regs x.toReg = .eq c)
    (_ : MemTy.locate bs (disp.signExtend 64) = some (base, off))
    (hl : MemTy.ofList bs kinds base = some l)
    (hd : disp.signExtend 64 = base + BitVec.ofNat 64 off)
    (hk : (c <<< sc.shift) + (0 : BitVec 32).signExtend 64 = BitVec.ofNat 64 k)
    (hin : off + k + n ≤ l.shape.size) :
    ReadOk (MemTy.ofList bs kinds) next Γ n (.mem (.sib none (some (x, sc)) disp)) :=
  .placed (.absIndexed hx) hl (table_addr hd hk) hin

theorem WriteIntOk.table_of {x : IndexReg} {sc : Scale} {c : BitVec 64} {off k : Nat}
    (hx : Γ.regs x.toReg = .eq c)
    (_ : MemTy.locate bs (disp.signExtend 64) = some (base, off))
    (hl : MemTy.ofList bs kinds base = some l) (hw : l.writable = true)
    (hd : disp.signExtend 64 = base + BitVec.ofNat 64 off)
    (hk : (c <<< sc.shift) + (0 : BitVec 32).signExtend 64 = BitVec.ofNat 64 k)
    (hin : off + k + n ≤ l.shape.size) (hfree : l.shape.free (off + k) n = true) :
    WriteIntOk (MemTy.ofList bs kinds) next Γ n (.mem (.sib none (some (x, sc)) disp)) Γ :=
  .placed (.absIndexed hx) hl hw (table_addr hd hk) hin hfree

theorem Holds.table_of {x : IndexReg} {sc : Scale} {c : BitVec 64} {off k : Nat}
    (hx : Γ.regs x.toReg = .eq c)
    (_ : MemTy.locate bs (disp.signExtend 64) = some (base, off))
    (hl : MemTy.ofList bs kinds base = some l)
    (hd : disp.signExtend 64 = base + BitVec.ofNat 64 off)
    (hk : (c <<< sc.shift) + (0 : BitVec 32).signExtend 64 = BitVec.ofNat 64 k)
    (hi : l.shape.valAt (off + k) = some τ) :
    Holds (MemTy.ofList bs kinds) next Γ (.mem (.sib none (some (x, sc)) disp)) τ :=
  .placed (.absIndexed hx) hl (table_addr hd hk) hi

theorem Straight.loadGlobal_of {r : Reg} (hd : r ≠ .rsp)
    (_ : MemTy.locate bs (next + disp.signExtend 64) = some (base, d))
    (hl : MemTy.ofList bs kinds base = some l)
    (haddr : next + disp.signExtend 64 = base + BitVec.ofNat 64 d)
    (hi : l.shape.valAt d = some τ) :
    Straight (MemTy.ofList bs kinds) next Γ (.mov .w64 (.r_m r (.rip disp))) (Γ.setReg r τ) :=
  .loadGlobal hd hl haddr hi

theorem Straight.storeGlobal_of {s : Reg} (hs : s ≠ .rsp)
    (_ : MemTy.locate bs (next + disp.signExtend 64) = some (base, d))
    (hl : MemTy.ofList bs kinds base = some l) (hw : l.writable = true)
    (haddr : next + disp.signExtend 64 = base + BitVec.ofNat 64 d)
    (hi : l.shape.valAt d = some τ) (hso : l.shape.sole d = true) (hsub : Sub (Γ.regs s) τ) :
    Straight (MemTy.ofList bs kinds) next Γ (.mov .w64 (.rm_r (.mem (.rip disp)) s)) Γ :=
  .storeGlobal hs hl hw haddr hi hso hsub

/-- A register holding exactly an address inside one of the program's
blocks is a pointer into that block, as writable as the block is. This is
`BlockOk.castPtr` with the block found from the address. -/
theorem BlockOk.castPtr_of {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {a : BitVec 64}
    {r : Reg} {v : BitVec 64} {i : Nat} (hr : r ≠ .rsp) (hΓ : Γ.regs r = .eq v)
    (_ : MemTy.locate bs v = some (base, i))
    (hl : MemTy.ofList bs kinds base = some l) (hv : v = base + BitVec.ofNat 64 i)
    (hrest : BlockOk Φ fetch sys (MemTy.ofList bs kinds) a
      (Γ.setReg r (.ptr l.shape l.writable i))) :
    BlockOk Φ fetch sys (MemTy.ofList bs kinds) a Γ :=
  .castPtr hr hΓ hl hv (fun h => h) hrest

/-- The same for a block of a declared kind: the register is a pointer to a
block of that kind. This is `BlockOk.castRef` with the block found from the
address. -/
theorem BlockOk.castRef_of {Φ : CodeTy} {fetch : Fetch} {sys : Syscall} {a : BitVec 64}
    {r : Reg} {v : BitVec 64} {i tag : Nat} (hr : r ≠ .rsp) (hΓ : Γ.regs r = .eq v)
    (_ : MemTy.locate bs v = some (base, i))
    (hl : MemTy.ofList bs kinds base = some l) (htag : l.tag = some tag)
    (hv : v = base + BitVec.ofNat 64 i)
    (hrest : BlockOk Φ fetch sys (MemTy.ofList bs kinds) a
      (Γ.setReg r (.ref tag l.writable i))) :
    BlockOk Φ fetch sys (MemTy.ofList bs kinds) a Γ :=
  .castRef hr hΓ hl htag hv (fun h => h) hrest

end Globals

/-! Indexed operands: which byte a scaled index lands on. These hold for any
index, since addresses wrap; what needs a bound on the index is the byte
being inside the block. -/

/-- An index scaled by 8 with a displacement that is a multiple of 8 lands
on a whole eight-byte cell. -/
theorem index8_slot (c : BitVec 64) (disp : BitVec 32)
    (h8 : disp.toNat % 8 = 0) (hd : disp.toNat < 2 ^ 31) :
    (c <<< Scale.s8.shift) + disp.signExtend 64
      = BitVec.ofNat 64 (8 * (c.toNat + disp.toNat / 8)) := by
  apply BitVec.eq_of_toNat_eq
  rw [sext_toNat hd]
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Scale.shift]
  omega

/-- After `cmp a, b`, "below" holds exactly when `a` is less than `b` as
unsigned numbers. This is the fact a bounds check establishes. -/
theorem cmp_below_iff (a b : BitVec 64) :
    Cond.eval (AluOp.apply .cmp a b).2 .b = some (decide (a.toNat < b.toNat)) := by
  have h := subBorrow_cf .w64 a b
  simp only [AluOp.apply, Cond.eval]
  rw [h]
  rfl

theorem cmp_below {a b : BitVec 64} (h : Cond.eval (AluOp.apply .cmp a b).2 .b = some true) :
    a.toNat < b.toNat := by
  rw [cmp_below_iff] at h
  simpa using h

theorem cmp_not_below {a b : BitVec 64}
    (h : Cond.eval (AluOp.apply .cmp a b).2 .b = some false) : b.toNat ≤ a.toNat := by
  rw [cmp_below_iff] at h
  simpa using h

/-- After `cmp a, b`, "less" holds exactly when `a` is less than `b` as
signed numbers. -/
theorem cmp_less_iff (a b : BitVec 64) :
    Cond.eval (AluOp.apply .cmp a b).2 .l = some (a.slt b) := by
  have := a.isLt; have := b.isLt
  simp only [AluOp.apply, Cond.eval, subBorrow, Flags.ofResult, bind, Option.bind, pure,
    Option.some.injEq, BitVec.slt]
  rw [Bool.eq_iff_iff]
  simp [BitVec.msb_eq_decide, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toInt_eq_toNat_cond]
  generalize hr : (36893488147419103232 - b.toNat % 36893488147419103232 + a.toNat)
    % 18446744073709551616 = r
  by_cases h1 : 9223372036854775808 ≤ a.toNat <;> by_cases h2 : 9223372036854775808 ≤ b.toNat <;>
    by_cases h3 : 9223372036854775808 ≤ r <;> simp [h1, h2, h3] <;> omega

theorem cmp_less {a b : BitVec 64} (h : Cond.eval (AluOp.apply .cmp a b).2 .l = some true) :
    a.slt b = true := by
  rw [cmp_less_iff] at h
  simpa using h

theorem cmp_not_less {a b : BitVec 64} (h : Cond.eval (AluOp.apply .cmp a b).2 .l = some false) :
    a.slt b = false := by
  rw [cmp_less_iff] at h
  simpa using h

/-- What a subtraction leaves, written as one: so that a fact may be stated
of `a - b`. -/
@[asm_fact] theorem aluSub_fst (a b : BitVec 64) : (AluOp.sub.apply a b).1 = a - b := by
  simp only [AluOp.apply, subBorrow_fst]

/-- What an addition leaves, written as one. -/
@[asm_fact] theorem aluAdd_fst (a b : BitVec 64) : (AluOp.add.apply a b).1 = a + b := by
  simp only [AluOp.apply, addCarry_fst]

/-- The low half of a signed multiply is the product: what `imul` leaves in
its destination. -/
@[asm_fact] theorem imulTrunc_fst (a b : BitVec 64) : (imulTrunc a b).1 = a * b := by
  have lo : ∀ x : BitVec 64, BitVec.setWidth 64 (BitVec.signExtend 128 x) = x := by
    intro x
    ext i hi
    simp [BitVec.getElem_setWidth, BitVec.getLsbD_signExtend, hi]
    omega
  simp only [imulTrunc]
  rw [BitVec.setWidth_mul _ _ (by omega), lo, lo]

/-- The zero flag after any two-operand operation says whether its result
is zero. -/
theorem AluOp.apply_zf {n : Nat} (op : AluOp) (a b : BitVec n) :
    (op.apply a b).2.zf = some ((op.apply a b).1 == 0) := by
  cases op <;> rfl

/-- "Equal" holding after an operation means its result was zero; and so on
for the three other ways a test of the zero flag can go. For a comparison
the result is the difference. -/
theorem zero_of_e {n : Nat} {op : AluOp} {a b : BitVec n}
    (h : Cond.eval (op.apply a b).2 .e = some true) : (op.apply a b).1 = 0 := by
  have e : Cond.eval (op.apply a b).2 .e = (op.apply a b).2.zf := rfl
  rw [e, AluOp.apply_zf] at h
  simpa using h

theorem ne_zero_of_not_e {n : Nat} {op : AluOp} {a b : BitVec n}
    (h : Cond.eval (op.apply a b).2 .e = some false) : (op.apply a b).1 ≠ 0 := by
  have e : Cond.eval (op.apply a b).2 .e = (op.apply a b).2.zf := rfl
  rw [e, AluOp.apply_zf] at h
  simpa using h

theorem ne_zero_of_ne {n : Nat} {op : AluOp} {a b : BitVec n}
    (h : Cond.eval (op.apply a b).2 .ne = some true) : (op.apply a b).1 ≠ 0 := by
  have e : Cond.eval (op.apply a b).2 .ne = (op.apply a b).2.zf.map (!·) := rfl
  rw [e, AluOp.apply_zf] at h
  simpa using h

theorem zero_of_not_ne {n : Nat} {op : AluOp} {a b : BitVec n}
    (h : Cond.eval (op.apply a b).2 .ne = some false) : (op.apply a b).1 = 0 := by
  have e : Cond.eval (op.apply a b).2 .ne = (op.apply a b).2.zf.map (!·) := rfl
  rw [e, AluOp.apply_zf] at h
  simpa using h

/-- The same for flags set from a result directly, as a `test` sets them. -/
theorem zero_of_e' {n : Nat} {r : BitVec n} {c o : Bool}
    (h : Cond.eval (Flags.ofResult r c o) .e = some true) : r = 0 := by
  simpa [Cond.eval, Flags.ofResult] using h

theorem ne_zero_of_not_e' {n : Nat} {r : BitVec n} {c o : Bool}
    (h : Cond.eval (Flags.ofResult r c o) .e = some false) : r ≠ 0 := by
  simpa [Cond.eval, Flags.ofResult] using h

theorem ne_zero_of_ne' {n : Nat} {r : BitVec n} {c o : Bool}
    (h : Cond.eval (Flags.ofResult r c o) .ne = some true) : r ≠ 0 := by
  simpa [Cond.eval, Flags.ofResult] using h

theorem zero_of_not_ne' {n : Nat} {r : BitVec n} {c o : Bool}
    (h : Cond.eval (Flags.ofResult r c o) .ne = some false) : r = 0 := by
  simpa [Cond.eval, Flags.ofResult] using h

/-- After `cmp a, b`, "above or equal" failing means `a` is less than `b` as
unsigned numbers: the way a loop over a count carries on. -/
theorem cmp_not_ae {a b : BitVec 64}
    (h : Cond.eval (AluOp.apply .cmp a b).2 .ae = some false) : a.toNat < b.toNat := by
  have e : Cond.eval (AluOp.apply .cmp a b).2 .ae
      = (Cond.eval (AluOp.apply .cmp a b).2 .b).map (!·) := rfl
  rw [e, cmp_below_iff] at h
  simpa using h

/-- After `cmp a, b`, "above or equal" holding means `b` is at most `a`. -/
theorem cmp_ae {a b : BitVec 64}
    (h : Cond.eval (AluOp.apply .cmp a b).2 .ae = some true) : b.toNat ≤ a.toNat := by
  have e : Cond.eval (AluOp.apply .cmp a b).2 .ae
      = (Cond.eval (AluOp.apply .cmp a b).2 .b).map (!·) := rfl
  rw [e, cmp_below_iff] at h
  simpa using h

theorem getElem?_replicate_of_lt {n i : Nat} {τ : Ty} (h : i < n) :
    (List.replicate n τ)[i]? = some τ := by
  simp [h]

/-- Exact-value types are compared by comparing the values. -/
theorem Sub.of_eq {a b : BitVec 64} (h : a = b) : Sub (.eq a) (.eq b) :=
  h ▸ .refl _

/-- An unsigned divide whose dividend has a zero upper half and whose divisor
is known not to be zero cannot raise a divide error. -/
theorem Straight.divSafe {Ψ : MemTy} {next : BitVec 64} {Γ : Ctx} {w : Width} {r : Reg}
    {a d b : BitVec 64} (hr : r ≠ .rsp) (hΓa : Γ.regs .rax = .eq a) (hΓd : Γ.regs .rdx = .eq d)
    (hΓr : Γ.regs r = .eq b) (hd : d.setWidth w.bits = 0) (hb : b.setWidth w.bits ≠ 0) :
    Straight Ψ next Γ (.mulDiv .div w (.reg r))
      { (Γ.setReg .rax (.eq ((a.setWidth w.bits / b.setWidth w.bits).setWidth 64))).setReg .rdx
          (.eq ((a.setWidth w.bits % b.setWidth w.bits).setWidth 64)) with
        flags := (· = Flags.unknown) } :=
  .mulDivExact hr hΓa hΓd hΓr (by rw [hd]; exact MulDivOp.eval_div _ _ hb)

/-- A signed divide whose dividend has been sign-extended into `rdx` (as
`cqo` and `cdq` do) and whose divisor is known not to be zero cannot raise a
divide error, unless it is the most negative number divided by minus one. -/
theorem Straight.idivSafe {Ψ : MemTy} {next : BitVec 64} {Γ : Ctx} {w : Width} {r : Reg}
    {a d b : BitVec 64} (hr : r ≠ .rsp) (hΓa : Γ.regs .rax = .eq a) (hΓd : Γ.regs .rdx = .eq d)
    (hΓr : Γ.regs r = .eq b) (hd : d.setWidth w.bits = signFill (a.setWidth w.bits))
    (hb : b.setWidth w.bits ≠ 0)
    (hov : a.setWidth w.bits ≠ BitVec.intMin w.bits ∨ b.setWidth w.bits ≠ -1#w.bits) :
    Straight Ψ next Γ (.mulDiv .idiv w (.reg r))
      { (Γ.setReg .rax (.eq (((a.setWidth w.bits).sdiv (b.setWidth w.bits)).setWidth 64))).setReg
          .rdx (.eq (((a.setWidth w.bits).srem (b.setWidth w.bits)).setWidth 64)) with
        flags := (· = Flags.unknown) } :=
  .mulDivExact hr hΓa hΓd hΓr (by rw [hd]; exact MulDivOp.eval_idiv _ _ hb hov)

/-- The unsigned divide by a value in memory: a typed value of a block or of
the stack, exactly known and known not to be zero. -/
theorem Straight.divHeld {Ψ : MemTy} {next : BitVec 64} {Γ : Ctx} {w : Width} {m : Mem}
    {a d b : BitVec 64} (hm : Holds Ψ next Γ (.mem m) (.eq b)) (hΓa : Γ.regs .rax = .eq a)
    (hΓd : Γ.regs .rdx = .eq d) (hd : d.setWidth w.bits = 0) (hb : b.setWidth w.bits ≠ 0) :
    Straight Ψ next Γ (.mulDiv .div w (.mem m))
      { (Γ.setReg .rax (.eq ((a.setWidth w.bits / b.setWidth w.bits).setWidth 64))).setReg .rdx
          (.eq ((a.setWidth w.bits % b.setWidth w.bits).setWidth 64)) with
        flags := (· = Flags.unknown) } :=
  .mulDivHeld hm hΓa hΓd (by rw [hd]; exact MulDivOp.eval_div _ _ hb)

/-- The signed divide by a value in memory, likewise. -/
theorem Straight.idivHeld {Ψ : MemTy} {next : BitVec 64} {Γ : Ctx} {w : Width} {m : Mem}
    {a d b : BitVec 64} (hm : Holds Ψ next Γ (.mem m) (.eq b)) (hΓa : Γ.regs .rax = .eq a)
    (hΓd : Γ.regs .rdx = .eq d) (hd : d.setWidth w.bits = signFill (a.setWidth w.bits))
    (hb : b.setWidth w.bits ≠ 0)
    (hov : a.setWidth w.bits ≠ BitVec.intMin w.bits ∨ b.setWidth w.bits ≠ -1#w.bits) :
    Straight Ψ next Γ (.mulDiv .idiv w (.mem m))
      { (Γ.setReg .rax (.eq (((a.setWidth w.bits).sdiv (b.setWidth w.bits)).setWidth 64))).setReg
          .rdx (.eq (((a.setWidth w.bits).srem (b.setWidth w.bits)).setWidth 64)) with
        flags := (· = Flags.unknown) } :=
  .mulDivHeld hm hΓa hΓd (by rw [hd]; exact MulDivOp.eval_idiv _ _ hb hov)

theorem Flags.cf_isSome_of_known {f : Flags} (h : Flags.Known f) : f.cf.isSome = true := by
  simp only [Flags.Known, Flags.defined, Bool.and_eq_true] at h
  exact h.1.1.1

/-- When the flags are known, every condition is decided. -/
theorem Cond.decided_of_known {P : Flags → Prop} (hP : ∀ f, P f → Flags.Known f) (c : Cond) :
    ∀ f, P f → ∃ b, c.eval f = some b :=
  fun f hf => Cond.eval_some (hP f hf) c

end TypedAsm
