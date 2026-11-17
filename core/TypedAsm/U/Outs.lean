import TypedAsm.U.Instr

/-!
# Which registers an instruction writes

A table, by instruction; and that it is the registers each description
gives values to, in its order, whatever values the description is run on.
A checker that works on terms gives each a term without running anything.
-/

namespace TypedAsm.U

open TypedAsm

/-- The registers an instruction writes, in the order its description gives
them. Which they are does not turn on any value. -/
def _root_.TypedAsm.Instr.outs : Instr → List Reg
  | .alu op _ ops => if op.writesDst then rmRegs ops.dst else []
  | .unary _ _ dst => rmRegs dst
  | .shift _ _ dst _ => rmRegs dst
  | .mulDiv _ _ _ => [.rax, .rdx]
  | .imul2 _ dst _ => [dst]
  | .imul3 _ dst _ _ => [dst]
  | .popcnt _ dst _ => [dst]
  | .bswap _ r => [r]
  | .cdq => [.rdx]
  | .cqo => [.rdx]
  | .mov _ ops => rmRegs ops.dst
  | .movAbs dst _ => [dst]
  | .movzx _ dst _ _ => [dst]
  | .movsx _ dst _ _ => [dst]
  | .movsxd dst _ => [dst]
  | .lea _ dst _ => [dst]
  | .cmov _ _ dst _ => [dst]
  | .setcc _ dst => rmRegs dst
  | .push _ => [.rsp]
  | .pop r => [.rsp, r]
  | .call _ => [.rsp]
  | .ret => [.rsp]
  | _ => []

theorem desc1_outs {i : Instr} {d : Desc1} (hd : i.desc1 = some d) (vals : List (BitVec 64))
    (fl : Flags) (a c : BitVec 64) : (d.run vals fl a c).regs.map (·.1) = i.outs := by
  cases i with
  | alu op w ops =>
    cases hd
    rcases ops with ⟨dst | m, src⟩ | ⟨dst, m⟩ | ⟨dst | m, imm⟩ <;>
      simp only [Instr.outs, Operands.dst, rmRegs] <;> cases op.writesDst <;> rfl
  | unary op w dst => cases op <;> cases hd <;> cases dst <;> rfl
  | shift op w dst cnt => cases hd; cases dst <;> rfl
  | mulDiv op w src =>
    cases hd
    simp only [Instr.outs]
    split <;> rfl
  | mov w ops =>
    cases hd
    rcases ops with ⟨dst | m, src⟩ | ⟨dst, m⟩ | ⟨dst | m, imm⟩ <;> rfl
  | setcc cnd dst => cases hd; cases dst <;> rfl
  | jmp t => cases hd
  | jcc cnd rel => cases hd
  | call t => cases hd
  | ret => cases hd
  | ud2 => cases hd
  | syscall => cases hd
  | _ => cases hd; rfl

/-- **The registers a description writes are the instruction's**, whatever
it is run on. -/
theorem desc_outs {i : Instr} {d : Desc} (hd : i.desc = some d) (vals : List (BitVec 64))
    (fl : Flags) (next a c : BitVec 64) : (d.run vals fl next a c).regs.map (·.1) = i.outs := by
  cases hi : i.desc1 with
  | some d₁ =>
    have e : d = d₁.toDesc := Option.some.inj ((desc_of_desc1 hi).symm.trans hd).symm
    subst e
    exact desc1_outs hi vals fl a c
  | none =>
    cases i with
    | jmp t => rcases t with rel | (r | m) <;> cases hd <;> rfl
    | jcc cnd rel => cases hd; rfl
    | call t => rcases t with rel | (r | m) <;> cases hd <;> rfl
    | ret => cases hd; rfl
    | unary op w dst => cases op <;> cases hi
    | _ => first | (cases hi; done) | (cases hd; done)

end TypedAsm.U
