import TypedAsm.U.Exact
import TypedAsm.U.Held
import TypedAsm.Looks
import TypedAsm.Asm

/-!
# What an instruction touches, and what it leaves alone

Each instruction is described as data: the registers it computes with, the
registers it writes, the bytes it reads and writes, what it does to the
flags. Here is what that description comes to of the machine, as plain
facts about one step, each proved once for every described instruction:
which registers, bytes of memory, flags and permissions the step leaves as
they were. They are for use in any proof about a program, by the ordinary
means: a run is made of such steps.
-/

namespace TypedAsm.U

open TypedAsm

/-- **A described instruction that goes on, goes on to the state its
description gives.** -/
theorem exec_after {sys : Syscall} {s t : State} {i : Instr} {σ : Sem} (hσ : i.sem = some σ)
    (h : exec sys i s = .next t) : t = σ.toDesc.after s :=
  ((exec_exact sys s t (show i.desc = some σ.toDesc by rw [← sem_desc, hσ]; rfl)).mp h).2.2.2

/-- Registers given values one after another: one not among them is as it
was. -/
theorem getReg_foldl_setReg (l : List (Reg × BitVec 64)) (s : State) (r : Reg)
    (h : r ∉ l.map Prod.fst) :
    (l.foldl (fun t p => t.setReg p.1 p.2) s).getReg r = s.getReg r := by
  induction l generalizing s with
  | nil => rfl
  | cons p l ih =>
    rw [List.map_cons, List.mem_cons, not_or] at h
    rw [List.foldl_cons, ih _ h.2, State.getReg_setReg_other _ _ _ _ h.1]

theorem getReg_storeN (s : State) (n : Nat) (a v : BitVec 64) (r : Reg) :
    (storeN s n a v).getReg r = s.getReg r :=
  congrFun (storeN_regs s n a v) r

/-- The registers a description's state after differs in are those it
writes. -/
theorem Desc.after_getReg (σ : Sem) (s : State) (r : Reg) (h : r ∉ σ.outs.map Prod.fst) :
    (σ.toDesc.after s).getReg r = s.getReg r := by
  have hr : r ∉ (σ.toDesc.effect s).regs.map Prod.fst := by
    show r ∉ (σ.outs.map _).map Prod.fst
    rw [List.map_map]
    exact h
  unfold Desc.after
  simp only
  split <;> split <;>
    first
      | (show State.getReg (List.foldl _ _ _) r = _
         rw [getReg_foldl_setReg _ _ _ hr, getReg_storeN])
      | (show State.getReg (List.foldl _ _ _) r = _
         rw [getReg_foldl_setReg _ _ _ hr])

/-- **An instruction changes only the registers it writes.** -/
theorem exec_getReg {sys : Syscall} {s t : State} {i : Instr} {σ : Sem} (hσ : i.sem = some σ)
    (h : exec sys i s = .next t) {r : Reg} (hr : r ∉ σ.outs.map Prod.fst) :
    t.getReg r = s.getReg r := by
  rw [exec_after hσ h]
  exact Desc.after_getReg σ s r hr

/-! ## Memory -/

theorem mem_foldl_setReg (l : List (Reg × BitVec 64)) (s : State) :
    (l.foldl (fun t p => t.setReg p.1 p.2) s).mem = s.mem := by
  induction l generalizing s with
  | nil => rfl
  | cons p l ih => rw [List.foldl_cons, ih]; rfl

/-- A store of any number of bytes leaves a byte outside them as it was. -/
theorem storeN_mem_other (s : State) (n : Nat) (a v x : BitVec 64)
    (h : BitVec.ofNat 64 n ≤ x - a) : (storeN s n a v).mem x = s.mem x := by
  by_cases hn : n ≤ 8
  · exact storeN_mem_out s n a v x hn h
  · unfold storeN
    split <;> first | omega | rfl

/-- The bytes a description's state after differs in are those it writes. -/
theorem Desc.after_mem (σ : Sem) (s : State) (a : BitVec 64)
    (h : ∀ m n, σ.wr = some (m, n) → BitVec.ofNat 64 n ≤ a - s.ea m) :
    (σ.toDesc.after s).mem a = s.mem a := by
  unfold Desc.after
  simp only
  split <;> split
  all_goals
    (show State.mem (List.foldl _ _ _) a = _
     rw [mem_foldl_setReg])
  all_goals
    (rename_i m n hw
     exact storeN_mem_other s n (s.ea m) _ a (h m n hw))

/-- **An instruction changes only the bytes of memory it writes**: a byte
that is not one of them, counting on from where it writes, is as it was. -/
theorem exec_mem {sys : Syscall} {s t : State} {i : Instr} {σ : Sem} (hσ : i.sem = some σ)
    (h : exec sys i s = .next t) {a : BitVec 64}
    (ha : ∀ m n, σ.wr = some (m, n) → BitVec.ofNat 64 n ≤ a - s.ea m) :
    t.mem a = s.mem a := by
  rw [exec_after hσ h]
  exact Desc.after_mem σ s a ha

/-- An instruction that writes no memory leaves all of it. -/
theorem exec_mem_of_no_write {sys : Syscall} {s t : State} {i : Instr} {σ : Sem}
    (hσ : i.sem = some σ) (h : exec sys i s = .next t) (hw : σ.wr = none) : t.mem = s.mem :=
  funext fun _ => exec_mem hσ h fun m n e => by rw [hw] at e; cases e

/-! ## Permissions -/

theorem perm_foldl_setReg (l : List (Reg × BitVec 64)) (s : State) :
    (l.foldl (fun t p => t.setReg p.1 p.2) s).perm = s.perm := by
  induction l generalizing s with
  | nil => rfl
  | cons p l ih => rw [List.foldl_cons, ih]; rfl

theorem Desc.after_perm (d : Desc) (s : State) : (d.after s).perm = s.perm := by
  unfold Desc.after
  simp only
  split <;> split <;>
    first
      | (show State.perm (List.foldl _ _ _) = _
         rw [perm_foldl_setReg, storeN_perm])
      | (show State.perm (List.foldl _ _ _) = _
         rw [perm_foldl_setReg])

/-- **No instruction changes what memory may be read or written.** Only a
system call does. -/
theorem exec_perm {sys : Syscall} {s t : State} {i : Instr} {σ : Sem} (hσ : i.sem = some σ)
    (h : exec sys i s = .next t) : t.perm = s.perm := by
  rw [exec_after hσ h]
  exact Desc.after_perm _ s

/-! ## Flags -/

/-- **An instruction whose description leaves the flags, leaves them.** -/
theorem exec_flags {sys : Syscall} {s t : State} {i : Instr} {σ : Sem} (hσ : i.sem = some σ)
    (h : exec sys i s = .next t) (hf : σ.flags = .old) : t.flags = s.flags := by
  rw [exec_after hσ h]
  have he : (σ.toDesc.effect s).flags = s.flags := by
    show σ.flags.den _ = _
    rw [hf]
    rfl
  unfold Desc.after
  simp only
  split <;> exact he

/-! ## What an instruction does not look at

An instruction's description lists the registers it computes with, the
registers it writes, and the memory operands it addresses. A register that
is none of those has no part in what the instruction does: with any other
value in it, the instruction does the same, and leaves that other value
there. -/

/-- The memory operands an instruction addresses. -/
def Sem.mems (σ : Sem) : List Mem :=
  σ.ea.toList ++ (σ.rd.map Prod.fst).toList ++ (σ.wr.map Prod.fst).toList

/-- **The registers an instruction has to do with**: those it computes
with, those it writes, and those its memory operands are addressed by. -/
def Sem.regs (σ : Sem) : List Reg :=
  σ.srcs ++ σ.outs.map Prod.fst ++ σ.mems.flatMap memRegs

theorem State.setReg_comm (s : State) {r r' : Reg} (h : r ≠ r') (v v' : BitVec 64) :
    (s.setReg r v).setReg r' v' = (s.setReg r' v').setReg r v := by
  cases r <;> cases r' <;> first | exact absurd rfl h | rfl

/-- An address is as it was where a register it is not made of is given
another value. -/
theorem ea_setReg (s : State) (r : Reg) (v : BitVec 64) (m : Mem) (h : r ∉ memRegs m) :
    (s.setReg r v).ea m = s.ea m := by
  cases m with
  | rip d => rfl
  | sib base index d =>
    have hb : ∀ b, base = some b → (s.setReg r v).getReg b = s.getReg b := fun b hb =>
      State.getReg_setReg_other _ _ _ _ (fun e => h (by subst hb; subst e; simp [memRegs]))
    have hi : ∀ x, index = some x → (s.setReg r v).getReg x.1.toReg = s.getReg x.1.toReg :=
      fun x hx => State.getReg_setReg_other _ _ _ _
        (fun e => h (by subst hx; rw [← e]; simp [memRegs]))
    cases base with
    | none =>
      cases index with
      | none => rfl
      | some x => simp only [State.ea, hi x rfl]
    | some b =>
      cases index with
      | none => simp only [State.ea, hb b rfl]
      | some x => simp only [State.ea, hb b rfl, hi x rfl]

theorem storeN_setReg (s : State) (n : Nat) (a x v : BitVec 64) (r : Reg) :
    storeN (s.setReg r v) n a x = (storeN s n a x).setReg r v := by
  unfold storeN
  split <;> rfl

theorem loadN_setReg (s : State) (n : Nat) (a v : BitVec 64) (r : Reg) :
    loadN (s.setReg r v) n a = loadN s n a := by
  unfold loadN
  split <;> rfl

theorem foldl_setReg_comm (l : List (Reg × BitVec 64)) (s : State) (r : Reg) (v : BitVec 64)
    (h : r ∉ l.map Prod.fst) :
    l.foldl (fun t p => t.setReg p.1 p.2) (s.setReg r v)
      = (l.foldl (fun t p => t.setReg p.1 p.2) s).setReg r v := by
  induction l generalizing s with
  | nil => rfl
  | cons p l ih =>
    rw [List.map_cons, List.mem_cons, not_or] at h
    rw [List.foldl_cons, List.foldl_cons, State.setReg_comm s h.1, ih _ h.2]

/-- What a description is given of a state is the same where a register
the instruction has nothing to do with holds another value. -/
theorem Desc.inputs_setReg (σ : Sem) (s : State) (r : Reg) (v : BitVec 64) (h : r ∉ σ.regs) :
    σ.toDesc.vals (s.setReg r v) = σ.toDesc.vals s ∧
      σ.toDesc.eaOf (s.setReg r v) = σ.toDesc.eaOf s ∧
      σ.toDesc.cell (s.setReg r v) = σ.toDesc.cell s := by
  simp only [Sem.regs, List.mem_append, not_or] at h
  obtain ⟨⟨hs, -⟩, hm⟩ := h
  have hea : ∀ m ∈ σ.mems, (s.setReg r v).ea m = s.ea m := fun m hmm =>
    ea_setReg s r v m (fun hr => hm (List.mem_flatMap.mpr ⟨m, hmm, hr⟩))
  refine ⟨?_, ?_, ?_⟩
  · exact List.map_congr_left fun x hx =>
      State.getReg_setReg_other _ _ _ _ (fun e => hs (e ▸ hx))
  · show (match σ.ea with | some m => (s.setReg r v).ea m | none => 0) = _
    cases he : σ.ea with
    | none => simp only [Desc.eaOf, Sem.toDesc, he]
    | some m =>
      simp only [Desc.eaOf, Sem.toDesc, he]
      exact hea m (by simp [Sem.mems, he])
  · cases hr : σ.rd with
    | none => simp only [Desc.cell, Sem.toDesc, hr]
    | some p =>
      obtain ⟨m, n⟩ := p
      simp only [Desc.cell, Sem.toDesc, hr]
      rw [hea m (by simp [Sem.mems, hr]), loadN_setReg]

/-- The state a description leaves, from what it is given: what it
writes, what it computes, and where control goes. -/
def afterWith (wr : Option (Mem × Nat)) (e : Effect) (tgt : Option (BitVec 64)) (s : State) :
    State :=
  let s₁ := match wr with
    | some (m, n) => storeN s n (s.ea m) e.store
    | none => s
  let s₂ : State := { e.regs.foldl (fun t p => t.setReg p.1 p.2) s₁ with flags := e.flags }
  match tgt with
  | some t => { s₂ with rip := t }
  | none => s₂

theorem Desc.after_eq (d : Desc) (s : State) :
    d.after s = afterWith d.wr (d.effect s) (d.target s) s := rfl

theorem afterWith_setReg (wr : Option (Mem × Nat)) (e : Effect) (tgt : Option (BitVec 64))
    (s : State) (r : Reg) (v : BitVec 64)
    (hea : ∀ m n, wr = some (m, n) → (s.setReg r v).ea m = s.ea m)
    (hr : r ∉ e.regs.map Prod.fst) :
    afterWith wr e tgt (s.setReg r v) = (afterWith wr e tgt s).setReg r v := by
  cases wr with
  | none =>
    cases tgt <;>
      (simp only [afterWith]
       rw [foldl_setReg_comm _ _ _ _ hr]
       rfl)
  | some p =>
    obtain ⟨m, n⟩ := p
    cases tgt <;>
      (simp only [afterWith]
       rw [hea m n rfl, storeN_setReg, foldl_setReg_comm _ _ _ _ hr]
       rfl)

/-- **A described instruction does the same whatever a register it has
nothing to do with holds**, and leaves that register holding it. -/
theorem exec_setReg {sys : Syscall} {s t : State} {i : Instr} {σ : Sem} (hσ : i.sem = some σ)
    (h : exec sys i s = .next t) {r : Reg} (hr : r ∉ σ.regs) (v : BitVec 64) :
    exec sys i (s.setReg r v) = .next (t.setReg r v) := by
  have hd : i.desc = some σ.toDesc := by rw [← sem_desc, hσ]; rfl
  obtain ⟨hrd, hwr, hg, rfl⟩ := (exec_exact sys s t hd).mp h
  obtain ⟨hv, he, hc⟩ := Desc.inputs_setReg σ s r v hr
  have hr' := hr
  simp only [Sem.regs, List.mem_append, not_or] at hr'
  obtain ⟨⟨-, hout⟩, hm⟩ := hr'
  have hea : ∀ m ∈ σ.mems, (s.setReg r v).ea m = s.ea m := fun m hmm =>
    ea_setReg s r v m (fun hx => hm (List.mem_flatMap.mpr ⟨m, hmm, hx⟩))
  have heff : σ.toDesc.effect (s.setReg r v) = σ.toDesc.effect s := by
    unfold Desc.effect
    rw [hv, he, hc]
    rfl
  have htgt : σ.toDesc.target (s.setReg r v) = σ.toDesc.target s := by
    unfold Desc.target
    rw [hv, he, hc]
    rfl
  have hgd : σ.toDesc.guarded (s.setReg r v) = σ.toDesc.guarded s := by
    unfold Desc.guarded
    rw [hv, he, hc]
    rfl
  refine (exec_exact sys (s.setReg r v) _ hd).mpr ⟨fun m n hmn => ?_, fun m n hmn => ?_, ?_, ?_⟩
  · rw [hea m (by
      have : σ.rd = some (m, n) := hmn
      simp [Sem.mems, this])]
    exact hrd m n hmn
  · rw [hea m (by
      have : σ.wr = some (m, n) := hmn
      simp [Sem.mems, this])]
    exact hwr m n hmn
  · rw [hgd]; exact hg
  · rw [Desc.after_eq, Desc.after_eq, heff, htgt]
    refine (afterWith_setReg _ _ _ s r v (fun m n hmn => hea m (by
      have : σ.wr = some (m, n) := hmn
      simp [Sem.mems, this])) ?_).symm
    show r ∉ (σ.outs.map _).map Prod.fst
    rw [List.map_map]
    exact hout

/-! ## Over a whole run

A run is steps one after another, so what every step leaves alone the run
leaves alone. These are proved by induction on the run, once; what is left
for a particular program is a fact about its instructions as written. -/

/-- Whether an instruction leaves a register: it is not one of those its
description says it writes. Of a system call that is for the system to say;
an instruction that has no description goes nowhere. -/
def _root_.TypedAsm.Instr.leaves (i : Instr) (r : Reg) : Bool :=
  match i.sem with
  | some σ => !(σ.outs.map Prod.fst).contains r
  | none => true

/-- The instructions that have no description: a system call, and the one
that is not to be reached. -/
theorem sem_none {i : Instr} (h : i.sem = none) : i = .syscall ∨ i = .ud2 := by
  cases i with
  | syscall => exact .inl rfl
  | ud2 => exact .inr rfl
  | unary op w dst => cases op <;> cases h
  | jmp t => cases t with | rel d => cases h | ind rm => cases rm <;> cases h
  | call t => cases t with | rel d => cases h | ind rm => cases rm <;> cases h
  | _ => cases h

/-- **One step leaves a register that its instruction leaves**, a system
call's three registers apart. -/
theorem step_getReg {fetch : Fetch} {s s' : State} {r : Reg}
    (h : TypedAsm.step fetch linux s = .next s')
    (hl : ∀ i len, fetch s.rip = some (i, len) → i.leaves r = true)
    (h1 : r ≠ .rax) (h2 : r ≠ .rcx) (h3 : r ≠ .r11) : s'.getReg r = s.getReg r := by
  unfold TypedAsm.step at h
  cases hf : fetch s.rip with
  | none => rw [hf] at h; cases h
  | some p =>
    obtain ⟨i, len⟩ := p
    rw [hf] at h
    simp only at h
    have hli := hl i len hf
    unfold Instr.leaves at hli
    cases hσ : i.sem with
    | some σ =>
      rw [hσ] at hli
      have hr : r ∉ σ.outs.map Prod.fst := by simpa using hli
      exact exec_getReg hσ h hr
    | none =>
      rcases sem_none hσ with rfl | rfl
      · have hk := Result.all_iff.mp (linux_keeps { s with rip := s.rip + len }) s' h
        exact hk r h1 h2 h3
      · cases h

/-- **A run leaves a register that every instruction it can fetch leaves.** -/
theorem run_getReg {fetch : Fetch} {r : Reg}
    (hl : ∀ a i len, fetch a = some (i, len) → i.leaves r = true)
    (h1 : r ≠ .rax) (h2 : r ≠ .rcx) (h3 : r ≠ .r11) {s s' : State}
    (h : TypedAsm.Steps fetch linux s s') : s'.getReg r = s.getReg r := by
  induction h with
  | refl => rfl
  | step hstep _ ih => rw [ih, step_getReg hstep (fun i len => hl _ i len) h1 h2 h3]

/-- What is so of every instruction of a program as written is so of every
instruction the machine can fetch from it. -/
theorem fetch_of_table {L : Type} [IsLabel L] (base : BitVec 64) (code : List (Asm L))
    {P : Instr → Prop} (h : ∀ e ∈ Asm.table base code, P e.2.1) :
    ∀ (a : BitVec 64) (i : Instr) (len : BitVec 64),
      Asm.fetch base code a = some (i, len) → P i := fun a i len hf =>
  h (a.toNat, i, len) (Lookup.first_mem hf)

/-- Whether an instruction has nothing to do with a register: it is not one
of those its description computes with, writes, or addresses memory by. -/
def _root_.TypedAsm.Instr.ignores (i : Instr) (r : Reg) : Bool :=
  match i.sem with
  | some σ => !σ.regs.contains r
  | none => true

/-- **One step does the same whatever a register its instruction has
nothing to do with holds**, and leaves it holding that: a register that is
not one of a system call's either. -/
theorem step_setReg {fetch : Fetch} {s s' : State} {r : Reg}
    (h : TypedAsm.step fetch linux s = .next s')
    (hl : ∀ i len, fetch s.rip = some (i, len) → i.ignores r = true)
    (hr : r ∉ sysRegs) (v : BitVec 64) :
    TypedAsm.step fetch linux (s.setReg r v) = .next (s'.setReg r v) := by
  unfold TypedAsm.step at h ⊢
  show (match fetch s.rip with
    | none => Result.stuck
    | some (i, len) => exec linux i (({ s with rip := s.rip + len } : State).setReg r v)) = _
  cases hf : fetch s.rip with
  | none => rw [hf] at h; cases h
  | some p =>
    obtain ⟨i, len⟩ := p
    rw [hf] at h
    simp only at h ⊢
    have hli := hl i len hf
    unfold Instr.ignores at hli
    cases hσ : i.sem with
    | some σ =>
      rw [hσ] at hli
      have hr' : r ∉ σ.regs := by simpa using hli
      exact exec_setReg hσ h hr' v
    | none =>
      rcases sem_none hσ with rfl | rfl
      · exact linux_setReg h hr v
      · cases h

/-- **A run is the same run whatever a register holds that no instruction
it can fetch has anything to do with**: each state it reaches, with that
value in the register. -/
theorem run_setReg {fetch : Fetch} {r : Reg}
    (hl : ∀ a i len, fetch a = some (i, len) → i.ignores r = true)
    (hr : r ∉ sysRegs) (v : BitVec 64) {s s' : State}
    (h : TypedAsm.Steps fetch linux s s') :
    TypedAsm.Steps fetch linux (s.setReg r v) (s'.setReg r v) := by
  induction h with
  | refl => exact .refl _
  | step hstep _ ih => exact .step (step_setReg hstep (fun i len => hl _ i len) hr v) ih

end TypedAsm.U
