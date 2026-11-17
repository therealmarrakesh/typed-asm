import TypedAsm.U.Sem
import TypedAsm.U.Exec

/-!
# One statement for every instruction that goes on to the next

An instruction is described by the registers it uses, the address and
bytes it touches, and its function (`Instr.desc`). What a context must
provide for it is one thing: access to those bytes. `Access` says what that
is, of the machine: the bytes may be read, or written, as the instruction
needs, and what the context becomes for the value read and the value
written. How a context comes to provide it, from a region it holds or from
what it knows of a value, is a matter for the memory model, and is the same
question whichever instruction asks.

Given access, the instruction is typed: the registers it writes take the
values its function gives, and so do the flags.
-/

namespace TypedAsm.U

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

/-- The address a memory operand names, from the values of the registers
and where the instruction pointer is. -/
def eaOf (val : Reg → BitVec 64) (rip : BitVec 64) : Mem → BitVec 64
  | .sib base index disp =>
    let b := match base with
      | some r => val r
      | none => 0
    let i := match index with
      | some (r, scale) => val r.toReg <<< scale.shift
      | none => 0
    b + i + disp.signExtend 64
  | .rip disp => rip + disp.signExtend 64

theorem ea_eq {s : State} {val : Reg → BitVec 64} (h : ∀ r, s.getReg r = val r) (m : Mem) :
    s.ea m = eaOf val s.rip m := by
  cases m with
  | sib base index disp =>
    unfold State.ea eaOf
    cases base <;> cases index <;> simp only [h]
  | rip disp => rfl

/-- A context after an instruction's effect on the registers and the flags. -/
def CtxOf.apply (Γ : Ctx) (e : Effect) : Ctx :=
  { Γ with
    val := e.regs.foldl (fun f p => fun r => if r = p.1 then p.2 else f r) Γ.val
    flags := e.flags }

/-- A state with registers given values, the later winning, and the flags
given: it matches the context so changed. -/
theorem WellTyped.apply {n : Nat} {Γ : Ctx} {s : State} (h : WellTyped fetch sys Ψ n Γ s)
    (e : Effect) :
    WellTyped fetch sys Ψ n (Γ.apply e)
      { e.regs.foldl (fun t p => t.setReg p.1 p.2) s with flags := e.flags } := by
  have key : ∀ (l : List (Reg × BitVec 64)) (t : State) (f : Reg → BitVec 64),
      (∀ r, t.getReg r = f r) →
      ∀ r, (l.foldl (fun t p => t.setReg p.1 p.2) t).getReg r
        = l.foldl (fun f p => fun r => if r = p.1 then p.2 else f r) f r := by
    intro l
    induction l with
    | nil => exact fun t f hf r => hf r
    | cons p l ih =>
      intro t f hf r
      refine ih _ _ (fun r' => ?_) r
      show (t.setReg p.1 p.2).getReg r' = if r' = p.1 then p.2 else f r'
      by_cases hr : r' = p.1
      · rw [hr, State.getReg_setReg_same]; simp
      · rw [State.getReg_setReg_other _ _ _ _ hr]; simp only [hr, ↓reduceIte]; exact hf r'
  have same : ∀ (l : List (Reg × BitVec 64)) (t : State),
      (l.foldl (fun t p => t.setReg p.1 p.2) t).memory = t.memory ∧
      (l.foldl (fun t p => t.setReg p.1 p.2) t).perms = t.perms := by
    intro l
    induction l with
    | nil => exact fun t => ⟨rfl, rfl⟩
    | cons p l ih => exact fun t => ih _
  obtain ⟨hm, hp⟩ := same e.regs s
  have hmem : ∀ a, (State.mem { e.regs.foldl (fun t p => t.setReg p.1 p.2) s with
      flags := e.flags }) a = s.mem a := fun a => by
    show (e.regs.foldl (fun t p => t.setReg p.1 p.2) s).memory.get a = s.memory.get a
    rw [hm]
  have hperm : ∀ a, (State.perm { e.regs.foldl (fun t p => t.setReg p.1 p.2) s with
      flags := e.flags }) a = s.perm a := fun a => by
    show (e.regs.foldl (fun t p => t.setReg p.1 p.2) s).perms.get a = s.perms.get a
    rw [hp]
  have hload : ∀ a, (State.load64 { e.regs.foldl (fun t p => t.setReg p.1 p.2) s with
      flags := e.flags }) a = s.load64 a := fun a => by
    simp only [State.load64, State.load32, State.load16, State.load8, hmem]
  have hcr : ∀ a k, (State.canRead { e.regs.foldl (fun t p => t.setReg p.1 p.2) s with
      flags := e.flags }) a k = s.canRead a k := fun a k => by
    simp only [State.canRead, hperm]
  have hcw : ∀ a k, (State.canWrite { e.regs.foldl (fun t p => t.setReg p.1 p.2) s with
      flags := e.flags }) a k = s.canWrite a k := fun a k => by
    simp only [State.canWrite, hperm]
  exact
    { val := fun r => key e.regs s Γ.val h.val r
      known := h.known
      flags := rfl
      heapPerm := fun a l hl => by rw [hcr, hcw]; exact h.heapPerm a l hl
      heap := fun a l hl p hp => by rw [hload]; exact h.heap a l hl p hp
      text := fun a l hl ht => by rw [hmem]; exact h.text a l hl ht
      said := fun a l bs hl hs k hk => by rw [hmem]; exact h.said a l bs hl hs k hk
      held :=
        { perm := fun b hb => by rw [hcw]; exact h.held.perm b hb
          size_lt := h.held.size_lt
          fits := h.held.fits
          vals := fun b hb p hp => by rw [hload]; exact h.held.vals b hb p hp
          heap := h.held.heap
          apart := h.held.apart } }

end TypedAsm.U
