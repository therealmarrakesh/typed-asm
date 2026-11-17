import TypedAsm.U.Table
import TypedAsm.U.Norm

/-!
# The table agrees with the machine

The machine's own step is proved to do what each instruction's description
says, the description being functions of its inputs. Here the one table of
instructions as data is shown to come to those same functions, instruction
by instruction: by unfolding, the operators being the machine's own.
-/

namespace TypedAsm.U

open TypedAsm

theorem Desc.ext' {d e : Desc} (h1 : d.srcs = e.srcs) (h2 : d.ea = e.ea) (h3 : d.rd = e.rd)
    (h4 : d.wr = e.wr) (h5 : ∀ v f n a c, d.guard v f n a c = e.guard v f n a c)
    (h6 : ∀ v f n a c, d.run v f n a c = e.run v f n a c)
    (h7 : ∀ v f n a c, d.goes v f n a c = e.goes v f n a c) : d = e := by
  obtain ⟨s1, e1, r1, w1, g1, u1, o1⟩ := d
  obtain ⟨s2, e2, r2, w2, g2, u2, o2⟩ := e
  simp only at h1 h2 h3 h4 h5 h6 h7
  subst h1 h2 h3 h4
  have hg : g1 = g2 := by funext v f n a c; exact h5 v f n a c
  have hu : u1 = u2 := by funext v f n a c; exact h6 v f n a c
  have ho : o1 = o2 := by funext v f n a c; exact h7 v f n a c
  subst hg hu ho
  rfl

/-- A number written in an instruction is, at its width, itself. -/
theorem immV_low (ρ : Env) (w : Width) (imm : BitVec 32) :
    ((immV w imm).den ρ).setWidth w.bits = imm.signExtend w.bits := wide_low w _

/-- A count written in an instruction is itself. -/
theorem countV_imm (ρ : Env) (k : BitVec 8) (j : Nat) :
    ((countV (.imm k) j).den ρ).toNat = k.toNat := by
  show (BitVec.ofNat 64 k.toNat).toNat = k.toNat
  have := k.isLt
  rw [BitVec.toNat_ofNat]
  omega

/-- One form agrees: outright, or once the row is unfolded and a number
written in the instruction, re-read at its width, is itself. -/
macro "bridge" : tactic => `(tactic|
  first
    | rfl
    | (show some _ = some _
       refine congrArg some (Desc.ext' rfl rfl rfl rfl (fun v f n a c => ?_) (fun v f n a c => ?_)
         (fun v f n a c => ?_)) <;>
       first
         | rfl
         | (simp only [Sem.toDesc, Sem.give, AluOp.writesDst, Operands.dst, Bool.false_eq_true,
              ↓reduceIte, List.map_cons, List.map_nil, Val.den, FlagsT.den, FOp.eval, FSrc.eval,
              GuardE.eval, Bin.eval, Tri.eval, rmV, srcV, immV_low, countV_imm,
              BitVec.sub_eq_add_neg]
            first | rfl | (split <;> rfl))))

set_option maxRecDepth 4000 in
/-- **The table comes to the descriptions the machine's step follows.** -/
theorem sem_desc (i : Instr) : i.sem.map Sem.toDesc = i.desc := by
  cases i with
  | alu op w ops =>
    cases op <;> rcases ops with ⟨dst | m, src⟩ | ⟨dst, m⟩ | ⟨dst | m, imm⟩ <;> bridge
  | test w dst src => cases dst <;> cases src <;> bridge
  | unary op w dst => cases op <;> cases dst <;> bridge
  | shift op w dst c =>
    cases dst <;> cases c <;>
      (show some _ = some _
       refine congrArg some (Desc.ext' rfl rfl rfl rfl (fun _ _ _ _ _ => rfl) (fun v f n a c => ?_)
         (fun _ _ _ _ _ => rfl))
       simp only [Sem.toDesc, Sem.give, List.map_cons, List.map_nil, Val.den, FlagsT.den,
         FSrc.eval, Bin.eval, rmV, countV_imm]
       first
         | (show Effect.mk [(_, wide (ShiftOp.eval op Flags.unknown _ _).1)] _ _
              = Effect.mk [(_, wide (ShiftOp.eval op f _ _).1)] _ _
            rw [shift_fst op f]
            rfl)
         | (show Effect.mk [] _ (wide (ShiftOp.eval op Flags.unknown _ _).1)
              = Effect.mk [] _ (wide (ShiftOp.eval op f _ _).1)
            rw [shift_fst op f]
            rfl))
  | mulDiv op w src =>
    cases src <;>
      (show some _ = some _
       refine congrArg some (Desc.ext' rfl rfl rfl rfl (fun _ _ _ _ _ => rfl) (fun v f n a c => ?_)
         (fun _ _ _ _ _ => rfl))
       first
         | (show Effect.mk
                [(Reg.rax, Tri.eval (.mulLo op w) (v.getD 0 0) (v.getD 1 0) (v.getD 2 0)),
                 (Reg.rdx, Tri.eval (.mulHi op w) (v.getD 0 0) (v.getD 1 0) (v.getD 2 0))]
                (FSrc.eval (.mul op w) f (v.getD 0 0) (v.getD 1 0) (v.getD 2 0)) 0
              = (match MulDivOp.eval op ((v.getD 0 0).setWidth w.bits)
                    ((v.getD 1 0).setWidth w.bits) ((v.getD 2 0).setWidth w.bits) with
                 | .next (lo, hi, fl') => Effect.mk [(Reg.rax, wide lo), (Reg.rdx, wide hi)] fl' 0
                 | _ => Effect.mk [(Reg.rax, v.getD 1 0), (Reg.rdx, v.getD 0 0)] f 0)
            simp only [Tri.eval, FSrc.eval]
            generalize MulDivOp.eval op _ _ _ = res
            cases res with
            | next p => obtain ⟨lo, hi, fl'⟩ := p; rfl
            | _ => rfl)
         | (show Effect.mk
                [(Reg.rax, Tri.eval (.mulLo op w) (v.getD 0 0) (v.getD 1 0) (c)),
                 (Reg.rdx, Tri.eval (.mulHi op w) (v.getD 0 0) (v.getD 1 0) (c))]
                (FSrc.eval (.mul op w) f (v.getD 0 0) (v.getD 1 0) (c)) 0
              = (match MulDivOp.eval op ((v.getD 0 0).setWidth w.bits)
                    ((v.getD 1 0).setWidth w.bits) ((c).setWidth w.bits) with
                 | .next (lo, hi, fl') => Effect.mk [(Reg.rax, wide lo), (Reg.rdx, wide hi)] fl' 0
                 | _ => Effect.mk [(Reg.rax, v.getD 1 0), (Reg.rdx, v.getD 0 0)] f 0)
            simp only [Tri.eval, FSrc.eval]
            generalize MulDivOp.eval op _ _ _ = res
            cases res with
            | next p => obtain ⟨lo, hi, fl'⟩ := p; rfl
            | _ => rfl)
      )
  | imul2 w dst src => cases src <;> bridge
  | imul3 w dst src imm => cases src <;> bridge
  | popcnt w dst src => cases src <;> bridge
  | bswap w r => bridge
  | cdq => bridge
  | cqo => bridge
  | mov w ops => rcases ops with ⟨dst | m, src⟩ | ⟨dst, m⟩ | ⟨dst | m, imm⟩ <;> bridge
  | movAbs dst imm => bridge
  | store8 dst src => bridge
  | store16 dst src => bridge
  | movzx w dst sw src => cases src <;> bridge
  | movsx w dst sw src => cases src <;> bridge
  | movsxd dst src => cases src <;> bridge
  | lea w dst addr => bridge
  | cmov c w dst src => cases src <;> bridge
  | setcc c dst => cases dst <;> bridge
  | push r =>
    show some _ = some _
    refine congrArg some (Desc.ext' rfl rfl rfl rfl (fun _ _ _ _ _ => rfl) (fun v f n a c => ?_)
      (fun _ _ _ _ _ => rfl))
    show Effect.mk [(Reg.rsp, v.getD 1 0 + -8)] f (v.getD 0 0)
      = Effect.mk [(Reg.rsp, v.getD 1 0 - 8)] f (v.getD 0 0)
    rw [BitVec.sub_eq_add_neg]
  | pop r => bridge
  | jmp t => rcases t with rel | (r | m) <;> bridge
  | jcc c rel => bridge
  | call t =>
    rcases t with rel | (r | m) <;>
      (show some _ = some _
       refine congrArg some (Desc.ext' rfl rfl rfl rfl (fun _ _ _ _ _ => rfl) (fun v f n a c => ?_)
         (fun _ _ _ _ _ => rfl))
       show Effect.mk [(Reg.rsp, v.getD 0 0 + -8)] f n = Effect.mk [(Reg.rsp, v.getD 0 0 - 8)] f n
       rw [BitVec.sub_eq_add_neg])
  | ret => bridge
  | nop => bridge
  | ud2 => rfl
  | syscall => rfl

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
