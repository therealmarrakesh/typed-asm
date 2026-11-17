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

/-- `Access … Γ a n rd wr ok P`: the context `Γ` provides the `n` bytes at
`a` to an instruction that reads them (`rd`), writes them (`wr`), or both.
In every state matching `Γ` they may be so used; and for the value `x` they
hold and any value `v` that may be written there (`ok v`), the state, with
`v` written if anything is, matches a context `Γ₁` with `P x v Γ₁`, whose
registers and flags are `Γ`'s. -/
def Access (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (Γ : Ctx) (a : BitVec 64) (n : Nat)
    (rd wr : Bool) (ok : BitVec 64 → Prop) (P : BitVec 64 → BitVec 64 → Ctx → Prop) : Prop :=
  ∀ k, ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → ∀ s : State, WellTyped fetch sys Ψ' k Γ s →
    (rd = true → s.canRead a n = true) ∧ (wr = true → s.canWrite a n = true) ∧
    ∀ v, ok v → ∃ Γ₁, P (loadN s n a) v Γ₁ ∧ Γ₁.val = Γ.val ∧ Γ₁.flags = Γ.flags ∧
      WellTyped fetch sys Ψ' k Γ₁ (if wr then storeN s n a v else s)

/-- An instruction that touches no memory is provided for by any context. -/
theorem Access.none (Γ : Ctx) (a : BitVec 64) (n : Nat) :
    Access fetch sys Ψ Γ a n false false (fun _ => True) (fun _ _ Γ₁ => Γ₁ = Γ) := by
  intro k Ψ' he hwf s hw
  refine ⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion h, fun v _ => ?_⟩
  exact ⟨Γ, rfl, rfl, rfl, hw⟩

theorem storeN_rip (s : State) (n : Nat) (a v : BitVec 64) : (storeN s n a v).rip = s.rip := by
  unfold storeN
  split <;> rfl

theorem Desc.after_rip (d : Desc) (s : State) : (d.after s).rip = s.rip := by
  have key : ∀ (l : List (Reg × BitVec 64)) (t : State),
      (l.foldl (fun t p => t.setReg p.1 p.2) t).rip = t.rip := by
    intro l
    induction l with
    | nil => exact fun _ => rfl
    | cons p l ih => exact fun t => ih _
  unfold Desc.after
  show (List.foldl (fun (t : State) (p : Reg × BitVec 64) => t.setReg p.1 p.2) _ _).rip = _
  rw [key]
  split
  · exact storeN_rip _ _ _ _
  · rfl

/-- **Every instruction that goes on to the next, typed by one statement.**
Where the context provides the bytes the instruction touches, and the
instruction does not fault for a reason of its own whatever those bytes
hold, it takes the context to one in which the registers it writes hold the
values its function gives of the registers it uses, the flags and those
bytes; and the flags likewise. -/
theorem Steps.desc {i : Instr} {d : Desc} {next : BitVec 64} {Γ : Ctx}
    {ok : BitVec 64 → Prop} {P : BitVec 64 → BitVec 64 → Ctx → Prop} (hd : i.desc = some d)
    (hacc : Access fetch sys Ψ Γ ((d.addr.map (eaOf Γ.val next)).getD 0) d.bytes d.reads d.writes
      ok P)
    (hok : ∀ x, ok (d.run (d.srcs.map Γ.val) Γ.flags ((d.addr.map (eaOf Γ.val next)).getD 0) x).store)
    (hg : ∀ x Γ₁,
      P x (d.run (d.srcs.map Γ.val) Γ.flags ((d.addr.map (eaOf Γ.val next)).getD 0) x).store Γ₁ →
      d.guard (d.srcs.map Γ.val) Γ.flags ((d.addr.map (eaOf Γ.val next)).getD 0) x = true) :
    Steps fetch sys Ψ i next Γ fun Γ' => ∃ x Γ₁,
      P x (d.run (d.srcs.map Γ.val) Γ.flags ((d.addr.map (eaOf Γ.val next)).getD 0) x).store Γ₁ ∧
      Γ' = Γ₁.apply (d.run (d.srcs.map Γ.val) Γ.flags ((d.addr.map (eaOf Γ.val next)).getD 0) x) := by
  intro n Ψ' he hwf s hrip hw
  -- what the description reads of the state is what the context says
  have haddr : d.addrOf s = (d.addr.map (eaOf Γ.val next)).getD 0 := by
    unfold Desc.addrOf
    cases d.addr with
    | none => rfl
    | some m =>
      show s.ea m = eaOf Γ.val next m
      rw [ea_eq hw.val m, hrip]
  have hvals : d.vals s = d.srcs.map Γ.val := by
    unfold Desc.vals
    exact List.map_congr_left fun r _ => hw.val r
  obtain ⟨hr, hwr, hP⟩ := hacc n Ψ' he hwf s hw
  have heff : d.effect s = d.run (d.srcs.map Γ.val) Γ.flags
      ((d.addr.map (eaOf Γ.val next)).getD 0) (loadN s d.bytes ((d.addr.map (eaOf Γ.val next)).getD 0)) := by
    unfold Desc.effect Desc.cell
    rw [hvals, hw.flags, haddr]
  obtain ⟨Γ₁, hP₁, hval, hfl, hw₁⟩ := hP _ (hok (loadN s d.bytes _))
  have hguard : d.guarded s = true := by
    unfold Desc.guarded Desc.cell
    rw [hvals, hw.flags, haddr]
    exact hg _ Γ₁ hP₁
  refine ⟨d.after s, exec_desc sys s hd (by rw [haddr]; exact hr) (by rw [haddr]; exact hwr) hguard,
    d.after_rip s, Ψ', MemTy.Ext.refl _, hwf, _, ⟨_, Γ₁, hP₁, rfl⟩, ?_⟩
  have := hw₁.apply (d.run (d.srcs.map Γ.val) Γ.flags ((d.addr.map (eaOf Γ.val next)).getD 0)
    (loadN s d.bytes ((d.addr.map (eaOf Γ.val next)).getD 0)))
  unfold Desc.after
  rw [heff, haddr]
  exact this

end TypedAsm.U
