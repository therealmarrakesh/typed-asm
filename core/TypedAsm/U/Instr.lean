import TypedAsm.U.Exec

/-!
# Every instruction, described

An instruction that passes control elsewhere is described as the others
are: what it uses, what it reads and writes, and its function; and besides,
where control goes. A call writes its return address below the stack
pointer; a return reads one at it. What is read and what is written are
given separately, since a call through memory reads its target in one place
and writes its return address in another.
-/

namespace TypedAsm.U

/-- An instruction as what it uses and what it does with it. The functions
are given the values of `srcs` in order, the flags, the address of the next
instruction, the address `ea` names, and the bytes read as a number. -/
structure Desc where
  /-- The registers whose values the instruction computes with. -/
  srcs : List Reg
  /-- A memory operand whose address it uses as a number. -/
  ea : Option Mem := none
  /-- The bytes it reads: where, and how many. -/
  rd : Option (Mem × Nat) := none
  /-- The bytes it writes. -/
  wr : Option (Mem × Nat) := none
  /-- Whether it does not fault for a reason of its own. -/
  guard : List (BitVec 64) → Flags → BitVec 64 → BitVec 64 → BitVec 64 → Bool :=
    fun _ _ _ _ _ => true
  run : List (BitVec 64) → Flags → BitVec 64 → BitVec 64 → BitVec 64 → Effect
  /-- Where control goes, if not to the next instruction. -/
  goes : List (BitVec 64) → Flags → BitVec 64 → BitVec 64 → BitVec 64 → Option (BitVec 64) :=
    fun _ _ _ _ _ => none

/-- An instruction that touches memory in one place, as one that reads and
writes there. -/
def Desc1.toDesc (d : Desc1) : Desc where
  srcs := d.srcs
  ea := d.addr
  rd := if d.reads then d.addr.map (·, d.bytes) else none
  wr := if d.writes then d.addr.map (·, d.bytes) else none
  guard := fun vals fl _ a c => d.guard vals fl a c
  run := fun vals fl _ a c => d.run vals fl a c

/-- **Each instruction, described.** Nothing for a system call, which is
described by the system, or for what is not to be reached. -/
def _root_.TypedAsm.Instr.desc : Instr → Option Desc
  | .jmp (.rel d) =>
    some {
      srcs := []
      run := fun _ fl _ _ _ => ⟨[], fl, 0⟩
      goes := fun _ _ next _ _ => some (next + d.signExtend 64) }
  | .jmp (.ind (.reg r)) =>
    some {
      srcs := [r]
      run := fun _ fl _ _ _ => ⟨[], fl, 0⟩
      goes := fun vals _ _ _ _ => some (vals.getD 0 0) }
  | .jmp (.ind (.mem m)) =>
    some {
      srcs := [], rd := some (m, 8)
      run := fun _ fl _ _ _ => ⟨[], fl, 0⟩
      goes := fun _ _ _ _ cell => some cell }
  | .jcc c d =>
    some {
      srcs := []
      guard := fun _ fl _ _ _ => (c.eval fl).isSome
      run := fun _ fl _ _ _ => ⟨[], fl, 0⟩
      goes := fun _ fl next _ _ =>
        some (if (c.eval fl).getD false then next + d.signExtend 64 else next) }
  | .call (.rel d) =>
    some {
      srcs := [.rsp], wr := some (pushMem, 8)
      run := fun vals fl next _ _ => ⟨[(.rsp, vals.getD 0 0 - 8)], fl, next⟩
      goes := fun _ _ next _ _ => some (next + d.signExtend 64) }
  | .call (.ind (.reg r)) =>
    some {
      srcs := [.rsp, r], wr := some (pushMem, 8)
      run := fun vals fl next _ _ => ⟨[(.rsp, vals.getD 0 0 - 8)], fl, next⟩
      goes := fun vals _ _ _ _ => some (vals.getD 1 0) }
  | .call (.ind (.mem m)) =>
    some {
      srcs := [.rsp], rd := some (m, 8), wr := some (pushMem, 8)
      run := fun vals fl next _ _ => ⟨[(.rsp, vals.getD 0 0 - 8)], fl, next⟩
      goes := fun _ _ _ _ cell => some cell }
  | .ret =>
    some {
      srcs := [.rsp], rd := some (topMem, 8)
      run := fun vals fl _ _ _ => ⟨[(.rsp, vals.getD 0 0 + 8)], fl, 0⟩
      goes := fun _ _ _ _ cell => some cell }
  | i => i.desc1.map Desc1.toDesc

namespace Desc

/-- The values a described instruction computes with, in a state. -/
def vals (d : Desc) (s : State) : List (BitVec 64) := d.srcs.map s.getReg

/-- The address it uses as a number. -/
def eaOf (d : Desc) (s : State) : BitVec 64 :=
  match d.ea with
  | some m => s.ea m
  | none => 0

/-- The bytes it reads. -/
def cell (d : Desc) (s : State) : BitVec 64 :=
  match d.rd with
  | some (m, n) => loadN s n (s.ea m)
  | none => 0

def effect (d : Desc) (s : State) : Effect := d.run (d.vals s) s.flags s.rip (d.eaOf s) (d.cell s)

def guarded (d : Desc) (s : State) : Bool :=
  d.guard (d.vals s) s.flags s.rip (d.eaOf s) (d.cell s)

def target (d : Desc) (s : State) : Option (BitVec 64) :=
  d.goes (d.vals s) s.flags s.rip (d.eaOf s) (d.cell s)

/-- The state it leaves: its bytes written, at the address its operand
named before anything changed; its registers and the flags given their
values; and the instruction pointer where control goes. -/
def after (d : Desc) (s : State) : State :=
  let e := d.effect s
  let s₁ := match d.wr with
    | some (m, n) => storeN s n (s.ea m) e.store
    | none => s
  let s₂ : State := { e.regs.foldl (fun t p => t.setReg p.1 p.2) s₁ with flags := e.flags }
  match d.target s with
  | some t => { s₂ with rip := t }
  | none => s₂

end Desc

open TypedAsm
set_option linter.unusedSimpArgs false

/-- Unfolds the machine's step and a description's, for an instruction that
passes control elsewhere. -/
syntax "goes_simp" (" [" term,* "]")? : tactic
macro_rules
  | `(tactic| goes_simp $[[$ts,*]]?) => do
    let extra : Array (Lean.TSyntax `term) := match ts with
      | some ts => ts.getElems
      | none => #[]
    `(tactic| simp only [exec, bind, Result.bind, pure, State.readRM, State.push64, State.pop64,
      Result.through_next, Result.onStack_next, Result.ofOption,
      Desc.after, Desc.effect, Desc.vals, Desc.cell, Desc.eaOf, Desc.guarded, Desc.target,
      List.map, List.getD_cons_zero, List.getD_cons_succ, Option.getD_some, Option.isSome_some,
      List.foldl_cons, List.foldl_nil, State.readReg, ↓reduceIte, loadN_8, storeN_8,
      ea_pushMem, ea_topMem, BitVec.setWidth_eq, Width.bits, $[$extra:term],*])

theorem exec_goes (sys : Syscall) (s : State) {i : Instr} {d : Desc} (hd : i.desc = some d)
    (hr : ∀ m n, d.rd = some (m, n) → s.canRead (s.ea m) n = true)
    (hw : ∀ m n, d.wr = some (m, n) → s.canWrite (s.ea m) n = true)
    (hg : d.guarded s = true) (hi : i.desc1 = none) : exec sys i s = .next (d.after s) := by
  cases i with
  | jmp t =>
    rcases t with rel | (r | m)
    · cases hd; rfl
    · cases hd
      goes_simp
    · cases hd
      have hr' : s.canRead (s.ea m) (wbytes .w64) = true := hr m 8 rfl
      goes_simp [read_ok hr', State.load]
  | jcc c rel =>
    cases hd
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (show (c.eval s.flags).isSome = true from hg)
    goes_simp [hb]
    cases b <;> rfl
  | ret =>
    cases hd
    have hr' : s.canRead (s.getReg .rsp) 8 = true := by
      have this : s.canRead (s.ea topMem) 8 = true := hr topMem 8 rfl
      rwa [ea_topMem] at this
    goes_simp [read64_ok hr']
    rfl
  | call t =>
    have hw' : s.canWrite (s.getReg .rsp - 8) 8 = true := by
      have this : s.canWrite (s.ea pushMem) 8 = true := by
        rcases t with rel | (r | m) <;> cases hd <;> exact hw pushMem 8 rfl
      rwa [ea_pushMem] at this
    have hw'' : (s.setReg .rsp (s.getReg .rsp - 8)).canWrite (s.getReg .rsp - 8) 8 = true := hw'
    rcases t with rel | (r | m)
    · cases hd
      goes_simp [write64_ok hw'']
      rfl
    · cases hd
      goes_simp [write64_ok hw'']
      rfl
    · cases hd
      have hr' : s.canRead (s.ea m) (wbytes .w64) = true := hr m 8 rfl
      goes_simp [read_ok hr', write64_ok hw'', State.load]
      rfl
  | unary op w dst => cases op <;> cases hi
  | _ => first | (cases hi; done) | (cases hd; done)

/-- An instruction with a single-cell description is described by it. -/
theorem desc_of_desc1 {i : Instr} {d₁ : Desc1} (h : i.desc1 = some d₁) :
    i.desc = some d₁.toDesc := by
  cases i with
  | jmp t => cases h
  | jcc c rel => cases h
  | call t => cases h
  | ret => cases h
  | _ => exact congrArg (Option.map Desc1.toDesc) h

theorem Desc1.toDesc_after (d : Desc1) (s : State) : d.toDesc.after s = d.after s := by
  unfold Desc.after Desc1.after Desc.effect Desc1.effect Desc.target Desc.cell Desc1.cell
    Desc.eaOf Desc1.addrOf Desc.vals Desc1.vals Desc1.toDesc
  cases d.reads <;> cases d.writes <;> cases d.addr <;> rfl

theorem Desc1.toDesc_guarded (d : Desc1) (s : State) : d.toDesc.guarded s = d.guarded s := by
  unfold Desc.guarded Desc1.guarded Desc.cell Desc1.cell Desc.eaOf Desc1.addrOf Desc.vals
    Desc1.vals Desc1.toDesc
  cases d.reads <;> cases d.addr <;> rfl

/-- **What the machine does with any described instruction**: where what it
reads may be read, what it writes may be written, and it does not fault for
a reason of its own, it goes on to the state the description gives, at the
place the description says control goes. -/
theorem exec_desc (sys : Syscall) (s : State) {i : Instr} {d : Desc} (hd : i.desc = some d)
    (hr : ∀ m n, d.rd = some (m, n) → s.canRead (s.ea m) n = true)
    (hw : ∀ m n, d.wr = some (m, n) → s.canWrite (s.ea m) n = true)
    (hg : d.guarded s = true) : exec sys i s = .next (d.after s) := by
  cases hi : i.desc1 with
  | none => exact exec_goes sys s hd hr hw hg hi
  | some d₁ =>
    have e : d = d₁.toDesc := Option.some.inj ((desc_of_desc1 hi).symm.trans hd).symm
    subst e
    rw [Desc1.toDesc_after]
    refine exec_desc1 sys s hi (fun hrd m hm => hr m _ ?_) (fun hwr m hm => hw m _ ?_)
      (by rw [← Desc1.toDesc_guarded]; exact hg)
    · show (if d₁.reads = true then d₁.addr.map (·, d₁.bytes) else none) = _
      simp only [hrd, ↓reduceIte, hm]; rfl
    · show (if d₁.writes = true then d₁.addr.map (·, d₁.bytes) else none) = _
      simp only [hwr, ↓reduceIte, hm]; rfl

end TypedAsm.U
