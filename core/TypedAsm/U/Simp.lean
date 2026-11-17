import TypedAsm.U.Check

/-!
# Terms made simpler

What an instruction gives a register is, as a term, "the instruction's
result on these inputs". Two things make such terms as plain as they can
be. Where every input is a number written out, the result is worked out:
one rule, for every instruction. And where the instruction is a move, the
taking of an address, or a push or a pop moving the stack pointer, the
result is read as the copy or the sum it is; so that an address that has
been moved about and stepped is still seen to be so many bytes from where
it started, which is how the bytes it names are found.
-/

namespace TypedAsm.U

open TypedAsm

/-- The number a term is, if it is one written out. -/
def Val.lit? : Val → Option (BitVec 64)
  | .lit v => some v
  | _ => none

def FlagsT.lit? : FlagsT → Option Flags
  | .lit f => some f
  | _ => none

theorem Val.lit?_den {ρ : Env} {a : Val} {v : BitVec 64} (h : a.lit? = some v) : a.den ρ = v := by
  cases a <;> first | (cases h; rfl) | cases h

theorem FlagsT.lit?_den {ρ : Env} {a : FlagsT} {f : Flags} (h : a.lit? = some f) : a.den ρ = f := by
  cases a <;> first | (cases h; rfl) | cases h

/-- **What an instruction gives a register, worked out**, where every input
is a number written out: one rule for every instruction. -/
def foldOut (i : Instr) (k : Nat) (a b c : Val) (fl : FlagsT) (next : BitVec 64) (ea cell : Val) :
    Val :=
  match a.lit?, b.lit?, c.lit?, fl.lit?, ea.lit?, cell.lit? with
  | some va, some vb, some vc, some f, some ve, some vcell =>
    .lit ((effectOf i [va, vb, vc] f next ve vcell).regs.getD k (.rax, 0)).2
  | _, _, _, _, _, _ => .out i k a b c fl next ea cell

theorem foldOut_den (ρ : Env) (i : Instr) (k : Nat) (a b c : Val) (fl : FlagsT) (next : BitVec 64)
    (ea cell : Val) :
    (foldOut i k a b c fl next ea cell).den ρ = (Val.out i k a b c fl next ea cell).den ρ := by
  unfold foldOut
  split
  · next va vb vc f ve vcell ha hb hc hf he hcell =>
    show _ = ((effectOf i [a.den ρ, b.den ρ, c.den ρ] (fl.den ρ) next (ea.den ρ) (cell.den ρ)).regs.getD k
      (.rax, 0)).2
    rw [Val.lit?_den ha, Val.lit?_den hb, Val.lit?_den hc, FlagsT.lit?_den hf, Val.lit?_den he,
      Val.lit?_den hcell]
    rfl
  · rfl

/-- **What an instruction gives a register, read as a copy or a sum** where
it is one: a move, an address taken, a number added or taken away, the
stack pointer after a push or a pop. Otherwise worked out, or left as it
is. This is what lets an address be found by arithmetic after it has been
moved and stepped. -/
def simpOut (i : Instr) (k : Nat) (a b c : Val) (fl : FlagsT) (next : BitVec 64) (ea cell : Val) :
    Val :=
  match i, k with
  | .mov .w64 (.rm_r (.reg _) _), 0 => a
  | .mov .w64 (.r_m _ _), 0 => cell
  | .movAbs _ imm, 0 => .lit imm
  | .mov .w64 (.rm_i (.reg _) imm), 0 => .lit (imm.signExtend 64)
  | .mov .w32 (.rm_i (.reg _) imm), 0 => .lit ((imm.signExtend 32).setWidth 64)
  | .lea .w64 _ _, 0 => ea
  | .push _, 0 => .add b (.lit (-8))
  | .pop _, 0 => .add a (.lit 8)
  | .pop _, 1 => cell
  | .call _, 0 => .add a (.lit (-8))
  | .ret, 0 => .add a (.lit 8)
  | _, _ => foldOut i k a b c fl next ea cell

/-! What each of those instructions gives, on any inputs. -/

theorem effectOf_mov64 (d s : Reg) (va vb vc : BitVec 64) (fl : Flags) (next ea cell : BitVec 64) :
    ((effectOf (.mov .w64 (.rm_r (.reg d) s)) [va, vb, vc] fl next ea cell).regs.getD 0 (.rax, 0)).2
      = va := by
  show BitVec.setWidth 64 (BitVec.setWidth 64 va) = va
  simp

theorem effectOf_load64 (d : Reg) (m : Mem) (va vb vc : BitVec 64) (fl : Flags)
    (next ea cell : BitVec 64) :
    ((effectOf (.mov .w64 (.r_m d m)) [va, vb, vc] fl next ea cell).regs.getD 0 (.rax, 0)).2
      = cell := by
  show BitVec.setWidth 64 (BitVec.setWidth 64 cell) = cell
  simp

theorem effectOf_movAbs (d : Reg) (imm va vb vc : BitVec 64) (fl : Flags)
    (next ea cell : BitVec 64) :
    ((effectOf (.movAbs d imm) [va, vb, vc] fl next ea cell).regs.getD 0 (.rax, 0)).2 = imm := rfl

theorem effectOf_movImm64 (d : Reg) (imm : BitVec 32) (va vb vc : BitVec 64) (fl : Flags)
    (next ea cell : BitVec 64) :
    ((effectOf (.mov .w64 (.rm_i (.reg d) imm)) [va, vb, vc] fl next ea cell).regs.getD 0
      (.rax, 0)).2 = imm.signExtend 64 := by
  show BitVec.setWidth 64 (imm.signExtend 64) = imm.signExtend 64
  simp

theorem effectOf_movImm32 (d : Reg) (imm : BitVec 32) (va vb vc : BitVec 64) (fl : Flags)
    (next ea cell : BitVec 64) :
    ((effectOf (.mov .w32 (.rm_i (.reg d) imm)) [va, vb, vc] fl next ea cell).regs.getD 0
      (.rax, 0)).2 = (imm.signExtend 32).setWidth 64 := rfl

theorem effectOf_lea64 (d : Reg) (m : Mem) (va vb vc : BitVec 64) (fl : Flags)
    (next ea cell : BitVec 64) :
    ((effectOf (.lea .w64 d m) [va, vb, vc] fl next ea cell).regs.getD 0 (.rax, 0)).2 = ea := by
  show BitVec.setWidth 64 (BitVec.setWidth 64 ea) = ea
  simp

theorem effectOf_push (r : Reg) (va vb vc : BitVec 64) (fl : Flags) (next ea cell : BitVec 64) :
    ((effectOf (.push r) [va, vb, vc] fl next ea cell).regs.getD 0 (.rax, 0)).2 = vb + (-8) := by
  show vb - 8 = vb + (-8)
  bv_omega

theorem effectOf_pop0 (r : Reg) (va vb vc : BitVec 64) (fl : Flags) (next ea cell : BitVec 64) :
    ((effectOf (.pop r) [va, vb, vc] fl next ea cell).regs.getD 0 (.rax, 0)).2 = va + 8 := rfl

theorem effectOf_pop1 (r : Reg) (va vb vc : BitVec 64) (fl : Flags) (next ea cell : BitVec 64) :
    ((effectOf (.pop r) [va, vb, vc] fl next ea cell).regs.getD 1 (.rax, 0)).2 = cell := rfl

theorem effectOf_call (t : Target) (va vb vc : BitVec 64) (fl : Flags) (next ea cell : BitVec 64) :
    ((effectOf (.call t) [va, vb, vc] fl next ea cell).regs.getD 0 (.rax, 0)).2 = va + (-8) := by
  rcases t with rel | (r | m) <;> (show va - 8 = va + (-8); bv_omega)

theorem effectOf_ret (va vb vc : BitVec 64) (fl : Flags) (next ea cell : BitVec 64) :
    ((effectOf .ret [va, vb, vc] fl next ea cell).regs.getD 0 (.rax, 0)).2 = va + 8 := rfl

theorem simpOut_den (ρ : Env) (i : Instr) (k : Nat) (a b c : Val) (fl : FlagsT) (next : BitVec 64)
    (ea cell : Val) :
    (simpOut i k a b c fl next ea cell).den ρ = (Val.out i k a b c fl next ea cell).den ρ := by
  unfold simpOut
  split
  · exact (effectOf_mov64 _ _ _ _ _ _ _ _ _).symm
  · exact (effectOf_load64 _ _ _ _ _ _ _ _ _).symm
  · exact (effectOf_movAbs _ _ _ _ _ _ _ _ _).symm
  · exact (effectOf_movImm64 _ _ _ _ _ _ _ _ _).symm
  · exact (effectOf_movImm32 _ _ _ _ _ _ _ _ _).symm
  · exact (effectOf_lea64 _ _ _ _ _ _ _ _ _).symm
  · exact (effectOf_push _ _ _ _ _ _ _ _).symm
  · exact (effectOf_pop0 _ _ _ _ _ _ _ _).symm
  · exact (effectOf_pop1 _ _ _ _ _ _ _ _).symm
  · exact (effectOf_call _ _ _ _ _ _ _ _).symm
  · exact (effectOf_ret _ _ _ _ _ _ _).symm
  · exact foldOut_den ρ i k a b c fl next ea cell

end TypedAsm.U
