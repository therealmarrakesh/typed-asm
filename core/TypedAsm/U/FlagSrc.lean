import TypedAsm.U.Term
import TypedAsm.U.CondRel

/-!
# Where an instruction's flags come from

The flags an instruction leaves are those of a subtraction of two of the
things it works on, or of a test of two of them, or say at least whether its
result is zero and whether it is negative. Here is which, and of what, as
one table, and that the instructions do so. With what a condition says after
a subtraction or a test, this gives what a decided jump says of the values
the program compared.
-/

namespace TypedAsm.U

open TypedAsm

/-- One of the things an instruction works on. -/
inductive Opnd
  /-- The value of a register it uses, by position. -/
  | arg (j : Nat)
  /-- The bytes it reads. -/
  | cell
  /-- A number written in it. -/
  | imm (v : BitVec 32)
  | zero
  /-- The first register it writes. -/
  | out
  /-- The bytes it writes. -/
  | stored
  deriving DecidableEq

/-- How flags come of two operands. -/
inductive FlagKind
  /-- As of the first less the second. -/
  | sub
  /-- As of a test of the first against the second. -/
  | tst
  /-- The zero and sign flags are the first's; of the others nothing is said. -/
  | res
  deriving DecidableEq

def rmOpnd (x : RM) (j : Nat) : Opnd :=
  match x with
  | .reg _ => .arg j
  | .mem _ => .cell

def srcOpnd : Operands → Opnd
  | .rm_r d _ => .arg (rmRegs d).length
  | .r_m _ _ => .cell
  | .rm_i _ imm => .imm imm

def resOpnd (x : RM) : Opnd :=
  match x with
  | .reg _ => .out
  | .mem _ => .stored

/-- **Where each instruction's flags come from.** -/
def _root_.TypedAsm.Instr.flagSrc : Instr → Option (FlagKind × Width × Opnd × Opnd)
  | .alu .sub w ops | .alu .cmp w ops => some (.sub, w, rmOpnd ops.dst 0, srcOpnd ops)
  | .alu .and w ops => some (.tst, w, rmOpnd ops.dst 0, srcOpnd ops)
  | .alu .add w ops | .alu .or w ops | .alu .xor w ops =>
    some (.res, w, resOpnd ops.dst, resOpnd ops.dst)
  | .test w dst (.reg _) => some (.tst, w, rmOpnd dst 0, .arg (rmRegs dst).length)
  | .test w dst (.imm i) => some (.tst, w, rmOpnd dst 0, .imm i)
  | .unary .neg w dst => some (.sub, w, .zero, rmOpnd dst 0)
  | _ => none

/-- An operand, at a width. -/
def Opnd.sem (i : Instr) (vals : List (BitVec 64)) (fl : Flags) (next ea cell : BitVec 64)
    (w : Width) : Opnd → BitVec w.bits
  | .arg j => (vals.getD j 0).setWidth w.bits
  | .cell => cell.setWidth w.bits
  | .imm v => v.signExtend w.bits
  | .zero => 0
  | .out => (((effectOf i vals fl next ea cell).regs.getD 0 (.rax, 0)).2).setWidth w.bits
  | .stored => (effectOf i vals fl next ea cell).store.setWidth w.bits

def FlagKind.Holds {n : Nat} : FlagKind → BitVec n → BitVec n → Flags → Prop
  | .sub, x, y, F => F = (subBorrow x y false).2
  | .tst, x, y, F => F = Flags.ofResult (x &&& y) false false
  | .res, x, _, F => F.zf = some (x == 0) ∧ F.sf = some x.msb

theorem wide_low (w : Width) (r : BitVec w.bits) : (wide r).setWidth w.bits = r := by
  cases w <;> simp [wide, Width.bits]

/-- **Each instruction's flags come from where the table says.** -/
theorem flagSrc_sound {i : Instr} {k : FlagKind} {w : Width} {A B : Opnd}
    (h : i.flagSrc = some (k, w, A, B)) (va vb vc : BitVec 64) (fl : Flags)
    (next ea cell : BitVec 64) :
    k.Holds (A.sem i [va, vb, vc] fl next ea cell w) (B.sem i [va, vb, vc] fl next ea cell w)
      (effectOf i [va, vb, vc] fl next ea cell).flags := by
  cases i with
  | alu op w' ops =>
    cases op <;> first
      | (cases h; done)
      | (cases h
         rcases ops with ⟨dst | m, src⟩ | ⟨dst, m⟩ | ⟨dst | m, imm⟩ <;> first
           | rfl
           | (refine ⟨?_, ?_⟩ <;>
               (show some _ = some _
                unfold Opnd.sem resOpnd Operands.dst
                first
                  | (show some _ = some ((wide _).setWidth _ == 0); rw [wide_low]; rfl)
                  | (show some _ = some ((wide _).setWidth _).msb; rw [wide_low]; rfl))))
  | test w' dst src =>
    cases src <;> cases h <;> cases dst <;> rfl
  | unary op w' dst =>
    cases op
    · cases h; cases dst <;> rfl
    · cases h
  | _ => cases h

end TypedAsm.U
