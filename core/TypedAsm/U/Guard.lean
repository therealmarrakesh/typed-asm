import TypedAsm.U.Instr

/-!
# Instructions that cannot fault of themselves

Most instructions fault only if memory they touch may not be touched. A
few can fault for a reason of their own: a divide, by its divisor; an
operation that reads a flag, where the flag is undefined. Here is which do
not, as a table, and that their descriptions say so. For those, nothing is
left to be shown of the instruction itself.
-/

namespace TypedAsm.U

open TypedAsm

/-- Whether an instruction cannot fault for a reason of its own. -/
def _root_.TypedAsm.Instr.noGuard : Instr → Bool
  | .alu .adc _ _ | .alu .sbb _ _ => false
  | .alu _ _ _ => true
  | .mulDiv _ _ _ | .cmov _ _ _ _ | .setcc _ _ | .jcc _ _ => false
  | .ud2 | .syscall => false
  | _ => true

theorem desc1_noGuard {i : Instr} {d : Desc1} (hn : i.noGuard = true) (hd : i.desc1 = some d)
    (vals : List (BitVec 64)) (fl : Flags) (a c : BitVec 64) : d.guard vals fl a c = true := by
  cases i with
  | alu op w ops => cases op <;> first | (cases hn; done) | (cases hd; rfl)
  | unary op w dst => cases op <;> cases hd <;> rfl
  | mulDiv op w src => cases hn
  | cmov cnd w dst src => cases hn
  | setcc cnd dst => cases hn
  | jmp t => cases hd
  | jcc cnd rel => cases hd
  | call t => cases hd
  | ret => cases hd
  | ud2 => cases hd
  | syscall => cases hd
  | _ => cases hd; rfl

/-- **An instruction that cannot fault of itself does not**, whatever it is
run on. -/
theorem desc_noGuard {i : Instr} {d : Desc} (hn : i.noGuard = true) (hd : i.desc = some d)
    (vals : List (BitVec 64)) (fl : Flags) (next a c : BitVec 64) :
    d.guard vals fl next a c = true := by
  cases hi : i.desc1 with
  | some d₁ =>
    have e : d = d₁.toDesc := Option.some.inj ((desc_of_desc1 hi).symm.trans hd).symm
    subst e
    exact desc1_noGuard hn hi vals fl a c
  | none =>
    cases i with
    | jmp t => rcases t with rel | (r | m) <;> cases hd <;> rfl
    | jcc cnd rel => cases hn
    | call t => rcases t with rel | (r | m) <;> cases hd <;> rfl
    | ret => cases hd; rfl
    | unary op w dst => cases op <;> cases hi
    | _ => first | (cases hi; done) | (cases hd; done)

end TypedAsm.U
