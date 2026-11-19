import TypedAsm.U.Exec

/-!
# Where the machine does not go on

An instruction that has a description goes on to the next state only where
what it reads may be read, what it writes may be written, and it does not
fault for a reason of its own. Otherwise it faults or is stuck. With
`exec_desc` this says exactly what the machine does with every described
instruction: `exec_exact`.
-/

namespace TypedAsm.U

open TypedAsm

theorem canWrite_setReg (s : State) (r : Reg) (v a : BitVec 64) (n : Nat) :
    (s.setReg r v).canWrite a n = s.canWrite a n := rfl

/-- Works through an instruction's steps to one that faults. -/
local macro "stops" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| repeat (first
      | simp only [exec, Result.all_bind, Result.all_pure, Result.all_next,
          Result.all_fault, Result.all_stuck, Result.all_through, Result.all_onStack,
          State.readRM, State.read, State.read8, State.read16, State.read64, State.readNarrow,
          State.pop64, Operands.src, Operands.dst, wbytes_eq,
          State.writeRM, State.writeRM8, State.write, State.write8, State.write16, State.write64,
          State.push64, canWrite_setReg, Bool.false_eq_true, ↓reduceIte, $ts,*]
      | split
      | (apply Result.All.of_forall; intro _)))

set_option hygiene false in
/-- Settles one form: its description read off, and where it reads memory at
all, the step that is not allowed found among its steps. -/
local macro "rd_done" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (obtain rfl := Option.some.inj hσ) <;>
    (simp only [Sem.toDesc, Sem.give, rmMem, opsMem, Operands.dst, $ts,*, Option.isSome_some,
      Option.isSome_none, ↓reduceIte, Option.map_some, Option.map_none, Option.some.injEq,
      Prod.mk.injEq, reduceCtorEq, Bool.false_eq_true, Bool.true_and, Bool.false_and] at hm) <;>
    (obtain ⟨rfl, rfl⟩ := hm; (try simp only [nbytes, wbytes, ea_topMem] at hc); stops [hc, wbytes]))

/-- **Where what an instruction reads may not be read, it does not go on.** -/
theorem exec_noread (sys : Syscall) (s : State) {i : Instr} {d : Desc} {m : Mem} {n : Nat}
    (hd : i.desc = some d) (hm : d.rd = some (m, n)) (hc : s.canRead (s.ea m) n = false) :
    (exec sys i s).All (fun _ => False) := by
  obtain ⟨σ, hσ, rfl⟩ := Option.map_eq_some_iff.mp hd
  cases i with
  | ud2 => cases hσ
  | syscall => cases hσ
  | alu op w ops =>
    cases ops with
    | rm_r x r => cases x <;> cases hwd : op.writesDst <;> rd_done [hwd]
    | r_m r m' => cases hwd : op.writesDst <;> rd_done [hwd]
    | rm_i x imm => cases x <;> cases hwd : op.writesDst <;> rd_done [hwd]
  | test w dst src => cases dst <;> rd_done [Operands.dst]
  | unary op w dst => cases op <;> cases dst <;> rd_done [Operands.dst]
  | shift op w dst c => cases dst <;> rd_done [Operands.dst]
  | mulDiv op w src => cases src <;> rd_done [Operands.dst]
  | imul2 w dst src => cases src <;> rd_done [Operands.dst]
  | imul3 w dst src imm => cases src <;> rd_done [Operands.dst]
  | popcnt w dst src => cases src <;> rd_done [Operands.dst]
  | bswap w r => rd_done [Operands.dst]
  | cdq => rd_done [Operands.dst]
  | cqo => rd_done [Operands.dst]
  | mov w ops =>
    cases ops with
    | rm_r x r => cases x <;> rd_done [Operands.dst]
    | r_m r m' => rd_done [Operands.dst]
    | rm_i x imm => cases x <;> rd_done [Operands.dst]
  | movAbs dst imm => rd_done [Operands.dst]
  | store8 dst src => rd_done [Operands.dst]
  | store16 dst src => rd_done [Operands.dst]
  | movzx w dst sw src => cases src <;> cases sw <;> rd_done [Operands.dst]
  | movsx w dst sw src => cases src <;> cases sw <;> rd_done [Operands.dst]
  | movsxd dst src => cases src <;> rd_done [Operands.dst]
  | lea w dst addr => rd_done [Operands.dst]
  | cmov c w dst src => cases src <;> rd_done [Operands.dst]
  | setcc c dst => cases dst <;> rd_done [Operands.dst]
  | push r => rd_done [Operands.dst]
  | pop r => rd_done [Operands.dst]
  | jmp t => cases t with | rel d => rd_done [Operands.dst] | ind rm => cases rm <;> rd_done [Operands.dst]
  | jcc c rel => rd_done [Operands.dst]
  | call t => cases t with | rel d => rd_done [Operands.dst] | ind rm => cases rm <;> rd_done [Operands.dst]
  | ret => rd_done [Operands.dst]
  | nop => rd_done [Operands.dst]

set_option hygiene false in
/-- Settles one form: its description read off, and where it writes memory at
all, the step that is not allowed found among its steps. -/
local macro "wr_done" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (obtain rfl := Option.some.inj hσ) <;>
    (simp only [Sem.toDesc, Sem.give, rmMem, opsMem, Operands.dst, $ts,*, Option.isSome_some,
      Option.isSome_none, ↓reduceIte, Option.map_some, Option.map_none, Option.some.injEq,
      Prod.mk.injEq, reduceCtorEq, Bool.false_eq_true, Bool.true_and, Bool.false_and] at hm) <;>
    (obtain ⟨rfl, rfl⟩ := hm; (try simp only [nbytes, wbytes, ea_pushMem] at hc); stops [hc, wbytes]))

/-- **Where what an instruction writes may not be written, it does not go
on.** -/
theorem exec_nowrite (sys : Syscall) (s : State) {i : Instr} {d : Desc} {m : Mem} {n : Nat}
    (hd : i.desc = some d) (hm : d.wr = some (m, n)) (hc : s.canWrite (s.ea m) n = false) :
    (exec sys i s).All (fun _ => False) := by
  obtain ⟨σ, hσ, rfl⟩ := Option.map_eq_some_iff.mp hd
  cases i with
  | ud2 => cases hσ
  | syscall => cases hσ
  | alu op w ops =>
    cases ops with
    | rm_r x r => cases x <;> cases hwd : op.writesDst <;> wr_done [hwd]
    | r_m r m' => cases hwd : op.writesDst <;> wr_done [hwd]
    | rm_i x imm => cases x <;> cases hwd : op.writesDst <;> wr_done [hwd]
  | test w dst src => cases dst <;> wr_done [Operands.dst]
  | unary op w dst => cases op <;> cases dst <;> wr_done [Operands.dst]
  | shift op w dst c => cases dst <;> wr_done [Operands.dst]
  | mulDiv op w src => cases src <;> wr_done [Operands.dst]
  | imul2 w dst src => cases src <;> wr_done [Operands.dst]
  | imul3 w dst src imm => cases src <;> wr_done [Operands.dst]
  | popcnt w dst src => cases src <;> wr_done [Operands.dst]
  | bswap w r => wr_done [Operands.dst]
  | cdq => wr_done [Operands.dst]
  | cqo => wr_done [Operands.dst]
  | mov w ops =>
    cases ops with
    | rm_r x r => cases x <;> wr_done [Operands.dst]
    | r_m r m' => wr_done [Operands.dst]
    | rm_i x imm => cases x <;> wr_done [Operands.dst]
  | movAbs dst imm => wr_done [Operands.dst]
  | store8 dst src => wr_done [Operands.dst]
  | store16 dst src => wr_done [Operands.dst]
  | movzx w dst sw src => cases src <;> cases sw <;> wr_done [Operands.dst]
  | movsx w dst sw src => cases src <;> cases sw <;> wr_done [Operands.dst]
  | movsxd dst src => cases src <;> wr_done [Operands.dst]
  | lea w dst addr => wr_done [Operands.dst]
  | cmov c w dst src => cases src <;> wr_done [Operands.dst]
  | setcc c dst => cases dst <;> wr_done [Operands.dst]
  | push r => wr_done [Operands.dst]
  | pop r => wr_done [Operands.dst]
  | jmp t => cases t with | rel d => wr_done [Operands.dst] | ind rm => cases rm <;> wr_done [Operands.dst]
  | jcc c rel => wr_done [Operands.dst]
  | call t => cases t with | rel d => wr_done [Operands.dst] | ind rm => cases rm <;> wr_done [Operands.dst]
  | ret => wr_done [Operands.dst]
  | nop => wr_done [Operands.dst]

set_option hygiene false in
/-- Settles one form that has no fault of its own: its description says so. -/
local macro "gd_none" : tactic =>
  `(tactic| (obtain rfl := Option.some.inj hσ) <;>
    (simp only [Desc.guarded, Sem.toDesc, Sem.give, GuardE.eval, Operands.dst, reduceCtorEq,
      Bool.true_eq_false] at hc))

set_option hygiene false in
/-- Says an instruction's own fault condition of the values the machine
computes with. -/
local macro "gd_vals" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [Desc.guarded, Desc.vals, Desc.cell, Desc.eaOf, Sem.toDesc, Sem.give,
      GuardE.eval, slotEnv, Val.den, A, rmV, srcV, immV, rmRegs, srcRegs, rmMem, opsMem,
      Operands.dst, List.map, List.cons_append, List.nil_append, List.getD_cons_zero,
      List.getD_cons_succ, Option.map_some, Option.getD_some, loadN_w, setWidth_wide,
      List.length_cons, List.length_nil, Nat.zero_add, List.getD_eq_getElem?_getD,
      List.getElem?_cons_succ, List.getElem?_cons_zero, Option.isSome_some, Option.isSome_none,
      wide, Bool.false_eq_true, ↓reduceIte, Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none, $ts,*] at hc)

/-- **Where an instruction faults for a reason of its own, it does not go
on.** -/
theorem exec_noguard (sys : Syscall) (s : State) {i : Instr} {d : Desc}
    (hd : i.desc = some d) (hc : d.guarded s = false) :
    (exec sys i s).All (fun _ => False) := by
  obtain ⟨σ, hσ, rfl⟩ := Option.map_eq_some_iff.mp hd
  cases i with
  | ud2 => cases hσ
  | syscall => cases hσ
  | alu op w ops =>
    cases ops with
    | rm_r x r =>
      cases x <;> cases hwd : op.writesDst <;> obtain rfl := Option.some.inj hσ <;>
        gd_vals [hwd] <;> stops [hc, Result.ofOption, State.readReg, hwd]
    | r_m r m' =>
      cases hwd : op.writesDst <;> obtain rfl := Option.some.inj hσ <;>
        gd_vals [hwd] <;> stops [hc, Result.ofOption, State.readReg, hwd]
    | rm_i x imm =>
      cases x <;> cases hwd : op.writesDst <;> obtain rfl := Option.some.inj hσ <;>
        gd_vals [hwd] <;> stops [hc, Result.ofOption, State.readReg, hwd]
  | test w dst src => gd_none
  | unary op w dst => cases op <;> cases dst <;> gd_none
  | shift op w dst c => cases dst <;> gd_none
  | mulDiv op w src =>
    cases src <;> obtain rfl := Option.some.inj hσ <;> gd_vals [State.readReg] <;>
      simp only [exec, Result.all_bind, State.readRM, State.readReg, State.read, wbytes_eq,
        Result.all_through]
    · simp only [Result.all_next]
      split at hc
      · cases hc
      · next hne => exact Result.all_iff.mpr fun a ha => (hne a ha).elim
    · split
      · simp only [Result.all_next]
        split at hc
        · cases hc
        · next hne => exact Result.all_iff.mpr fun a ha => (hne a ha).elim
      · simp only [Result.all_fault]
  | imul2 w dst src => gd_none
  | imul3 w dst src imm => gd_none
  | popcnt w dst src => gd_none
  | bswap w r => gd_none
  | cdq => gd_none
  | cqo => gd_none
  | mov w ops =>
    cases ops with
    | rm_r x r => cases x <;> gd_none
    | r_m r m' => gd_none
    | rm_i x imm => cases x <;> gd_none
  | movAbs dst imm => gd_none
  | store8 dst src => gd_none
  | store16 dst src => gd_none
  | movzx w dst sw src => gd_none
  | movsx w dst sw src => gd_none
  | movsxd dst src => gd_none
  | lea w dst addr => gd_none
  | cmov c w dst src =>
    obtain rfl := Option.some.inj hσ
    have hn : c.eval s.flags = none := by
      simpa [Desc.guarded, Sem.toDesc, GuardE.eval] using hc
    stops [hn, Result.ofOption]
  | setcc c dst =>
    cases dst <;> obtain rfl := Option.some.inj hσ <;>
    (have hn : c.eval s.flags = none := by
      simpa [Desc.guarded, Sem.toDesc, GuardE.eval] using hc) <;>
    stops [hn, Result.ofOption]
  | push r => gd_none
  | pop r => gd_none
  | jmp t => cases t with | rel d => gd_none | ind rm => cases rm <;> gd_none
  | jcc c rel =>
    obtain rfl := Option.some.inj hσ
    have hn : c.eval s.flags = none := by
      simpa [Desc.guarded, Sem.toDesc, GuardE.eval] using hc
    stops [hn, Result.ofOption]
  | call t => cases t with | rel d => gd_none | ind rm => cases rm <;> gd_none
  | ret => gd_none
  | nop => gd_none

/-- **What the machine does with a described instruction, exactly**: it
goes on to a state just where what the instruction reads may be read, what
it writes may be written, and it does not fault for a reason of its own; and
the state is then the one its description gives. -/
theorem exec_exact (sys : Syscall) (s t : State) {i : Instr} {d : Desc} (hd : i.desc = some d) :
    exec sys i s = .next t ↔
      (∀ m n, d.rd = some (m, n) → s.canRead (s.ea m) n = true) ∧
      (∀ m n, d.wr = some (m, n) → s.canWrite (s.ea m) n = true) ∧
      d.guarded s = true ∧ t = d.after s := by
  constructor
  · intro h
    have hr : ∀ m n, d.rd = some (m, n) → s.canRead (s.ea m) n = true := fun m n hm => by
      cases hc : s.canRead (s.ea m) n with
      | true => rfl
      | false =>
        have := exec_noread sys s hd hm hc
        rw [h] at this
        exact this.elim
    have hw : ∀ m n, d.wr = some (m, n) → s.canWrite (s.ea m) n = true := fun m n hm => by
      cases hc : s.canWrite (s.ea m) n with
      | true => rfl
      | false =>
        have := exec_nowrite sys s hd hm hc
        rw [h] at this
        exact this.elim
    have hg : d.guarded s = true := by
      cases hc : d.guarded s with
      | true => rfl
      | false =>
        have := exec_noguard sys s hd hc
        rw [h] at this
        exact this.elim
    refine ⟨hr, hw, hg, ?_⟩
    rw [exec_desc sys s hd hr hw hg] at h
    exact (Result.next.inj h).symm
  · rintro ⟨hr, hw, hg, rfl⟩
    exact exec_desc sys s hd hr hw hg

end TypedAsm.U
