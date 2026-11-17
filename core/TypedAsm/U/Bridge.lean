import TypedAsm.U.Table
import TypedAsm.U.Norm

/-!
# An instruction's terms are its own

Every term in an instruction's description speaks only of what the
instruction computes with: of no name, and of no family's value. So what
the description comes to, with a context's terms put in, turns only on
what those terms stand for.
-/

namespace TypedAsm.U

open TypedAsm

set_option maxRecDepth 4000 in
/-- **Every instruction's terms speak only of what it computes with.** -/
theorem sem_slotOnly {i : Instr} {s : Sem} (h : i.sem = some s) : s.slotOnly = true := by
  cases i with
  | alu op w ops =>
    cases op <;> rcases ops with ⟨dst | m, src⟩ | ⟨dst, m⟩ | ⟨dst | m, imm⟩ <;> cases h <;> rfl
  | test w dst src => cases dst <;> cases src <;> cases h <;> rfl
  | unary op w dst => cases op <;> cases dst <;> cases h <;> rfl
  | shift op w dst c => cases dst <;> cases c <;> cases h <;> rfl
  | mulDiv op w src => cases src <;> cases h <;> rfl
  | imul2 w dst src => cases src <;> cases h <;> rfl
  | imul3 w dst src imm => cases src <;> cases h <;> rfl
  | popcnt w dst src => cases src <;> cases h <;> rfl
  | mov w ops => rcases ops with ⟨dst | m, src⟩ | ⟨dst, m⟩ | ⟨dst | m, imm⟩ <;> cases h <;> rfl
  | movzx w dst sw src => cases src <;> cases h <;> rfl
  | movsx w dst sw src => cases src <;> cases h <;> rfl
  | movsxd dst src => cases src <;> cases h <;> rfl
  | cmov c w dst src => cases src <;> cases h <;> rfl
  | setcc c dst => cases dst <;> cases h <;> rfl
  | jmp t => rcases t with rel | (r | m) <;> cases h <;> rfl
  | call t => rcases t with rel | (r | m) <;> cases h <;> rfl
  | ud2 => cases h
  | syscall => cases h
  | _ => cases h; rfl

end TypedAsm.U
