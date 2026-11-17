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
      complete := fun a ha => by rw [hperm] at ha; exact h.complete a ha
      held :=
        { perm := fun b hb => by rw [hcw]; exact h.held.perm b hb
          size_lt := h.held.size_lt
          fits := h.held.fits
          vals := fun b hb p hp => by rw [hload]; exact h.held.vals b hb p hp
          heap := h.held.heap
          apart := h.held.apart } }

/-- `Reads … Γ a n P`: the context `Γ` provides the `n` bytes at `a` to be
read. In every state matching `Γ` they may be read; and for the value `x`
they hold, the state matches a context `Γr` with `P x Γr`, whose registers
and flags are `Γ`'s: `Γ` with whatever reading tells. -/
def Reads (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (Γ : Ctx) (a : BitVec 64) (n : Nat)
    (P : BitVec 64 → Ctx → Prop) : Prop :=
  ∀ k, ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → ∀ s : State, WellTyped fetch sys Ψ' k Γ s →
    s.canRead a n = true ∧
    ∃ Γr, P (loadN s n a) Γr ∧ Γr.val = Γ.val ∧ Γr.flags = Γ.flags ∧
      WellTyped fetch sys Ψ' k Γr s

/-- `Writes … Γ a n v Γw`: the context `Γ` provides the `n` bytes at `a` to
be written with `v`, and is `Γw` once they are: in every state matching `Γ`
they may be written, and the state with `v` there matches `Γw`, whose
registers and flags are `Γ`'s. -/
def Writes (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (Γ : Ctx) (a : BitVec 64) (n : Nat)
    (v : BitVec 64) (Γw : Ctx) : Prop :=
  Γw.val = Γ.val ∧ Γw.flags = Γ.flags ∧
  ∀ k, ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → ∀ s : State, WellTyped fetch sys Ψ' k Γ s →
    s.canWrite a n = true ∧ WellTyped fetch sys Ψ' k Γw (storeN s n a v)

theorem storeN_rip (s : State) (n : Nat) (a v : BitVec 64) : (storeN s n a v).rip = s.rip := by
  unfold storeN
  split <;> rfl

theorem foldl_setReg_rip (l : List (Reg × BitVec 64)) (t : State) :
    (l.foldl (fun (t : State) (p : Reg × BitVec 64) => t.setReg p.1 p.2) t).rip = t.rip := by
  induction l generalizing t with
  | nil => rfl
  | cons p l ih => exact ih _

/-- **Every instruction typed by one statement**, whether it goes on to the
next or passes control elsewhere. Where the context provides the bytes the
instruction reads, and then those it writes, and the instruction does not
fault for a reason of its own whatever it reads, it takes the context to
one in which the registers it writes hold the values its function gives of
the registers it uses, the flags and the bytes read, and the flags
likewise; at the place its description says control goes. -/
theorem Steps.desc {i : Instr} {d : Desc} {next : BitVec 64} {Γ : Ctx}
    {R : BitVec 64 → Ctx → Prop} {W : BitVec 64 → Ctx → Ctx → Prop} (hd : i.desc = some d)
    (hrd : match d.rd with
      | some (m, n) => Reads fetch sys Ψ Γ (eaOf Γ.val next m) n R
      | none => R 0 Γ)
    (hwr : ∀ x Γr, R x Γr → ∃ Γw, W x Γr Γw ∧
      match d.wr with
      | some (m, n) => Writes fetch sys Ψ Γr (eaOf Γ.val next m) n
          (d.run (d.srcs.map Γ.val) Γ.flags next ((d.ea.map (eaOf Γ.val next)).getD 0) x).store Γw
      | none => Γw = Γr)
    (hg : ∀ x Γr, R x Γr →
      d.guard (d.srcs.map Γ.val) Γ.flags next ((d.ea.map (eaOf Γ.val next)).getD 0) x = true) :
    Steps fetch sys Ψ i next Γ fun t Γ' => ∃ x Γr Γw, R x Γr ∧ W x Γr Γw ∧
      Γ' = Γw.apply (d.run (d.srcs.map Γ.val) Γ.flags next ((d.ea.map (eaOf Γ.val next)).getD 0) x) ∧
      t = ((d.goes (d.srcs.map Γ.val) Γ.flags next ((d.ea.map (eaOf Γ.val next)).getD 0) x).getD
        next) := by
  intro n Ψ' he hwf s hrip hw
  -- what the description reads of the state is what the context says
  have hea : ∀ m, s.ea m = eaOf Γ.val next m := fun m => by rw [ea_eq hw.val m, hrip]
  have heaOf : d.eaOf s = (d.ea.map (eaOf Γ.val next)).getD 0 := by
    unfold Desc.eaOf
    cases d.ea with
    | none => rfl
    | some m => exact hea m
  have hvals : d.vals s = d.srcs.map Γ.val := by
    unfold Desc.vals
    exact List.map_congr_left fun r _ => hw.val r
  -- the bytes read
  have hread : (∀ m n, d.rd = some (m, n) → s.canRead (s.ea m) n = true) ∧
      ∃ Γr, R (d.cell s) Γr ∧ Γr.val = Γ.val ∧ Γr.flags = Γ.flags ∧
        WellTyped fetch sys Ψ' n Γr s := by
    unfold Desc.cell
    cases hrdm : d.rd with
    | none =>
      rw [hrdm] at hrd
      refine ⟨fun m' n' h => ?_, Γ, hrd, rfl, rfl, hw⟩
      cases h
    | some mn =>
      obtain ⟨m, k⟩ := mn
      rw [hrdm] at hrd
      obtain ⟨hcr, Γr, hR, hv, hf, hwr'⟩ := hrd n Ψ' he hwf s hw
      refine ⟨fun m' n' h => ?_, Γr, ?_, hv, hf, hwr'⟩
      · cases h; rw [hea]; exact hcr
      · show R (loadN s k (s.ea m)) Γr
        rw [hea]; exact hR
  obtain ⟨hcanR, Γr, hR, hval, hfl, hwΓr⟩ := hread
  have heff : d.effect s = d.run (d.srcs.map Γ.val) Γ.flags next
      ((d.ea.map (eaOf Γ.val next)).getD 0) (d.cell s) := by
    unfold Desc.effect
    rw [hvals, hw.flags, heaOf, hrip]
  have htgt : d.target s = d.goes (d.srcs.map Γ.val) Γ.flags next
      ((d.ea.map (eaOf Γ.val next)).getD 0) (d.cell s) := by
    unfold Desc.target
    rw [hvals, hw.flags, heaOf, hrip]
  have hguard : d.guarded s = true := by
    unfold Desc.guarded
    rw [hvals, hw.flags, heaOf, hrip]
    exact hg _ Γr hR
  -- the bytes written
  obtain ⟨Γw, hW, hwrite⟩ := hwr _ Γr hR
  have hstore : (∀ m n, d.wr = some (m, n) → s.canWrite (s.ea m) n = true) ∧
      Γw.val = Γ.val ∧ Γw.flags = Γ.flags ∧
      WellTyped fetch sys Ψ' n Γw
        (match d.wr with
          | some (m, n) => storeN s n (s.ea m) (d.effect s).store
          | none => s) := by
    cases hwm : d.wr with
    | none =>
      rw [hwm] at hwrite
      subst hwrite
      refine ⟨fun m' n' h => ?_, hval, hfl, hwΓr⟩
      cases h
    | some mn =>
      obtain ⟨m, k⟩ := mn
      rw [hwm] at hwrite
      obtain ⟨hv, hf, hall⟩ := hwrite
      obtain ⟨hcw, hwt⟩ := hall n Ψ' he hwf s hwΓr
      refine ⟨fun m' n' h => ?_, hv.trans hval, hf.trans hfl, ?_⟩
      · cases h; rw [hea]; exact hcw
      · show WellTyped fetch sys Ψ' n Γw (storeN s k (s.ea m) (d.effect s).store)
        rw [hea, heff]; exact hwt
  obtain ⟨hcanW, _, _, hwΓw⟩ := hstore
  refine ⟨d.after s, exec_desc sys s hd hcanR hcanW hguard,
    Γw.apply (d.run (d.srcs.map Γ.val) Γ.flags next ((d.ea.map (eaOf Γ.val next)).getD 0)
      (d.cell s)), ⟨d.cell s, Γr, Γw, hR, hW, rfl, ?_⟩, ?_⟩
  · -- where the machine is
    unfold Desc.after
    rw [htgt]
    cases d.goes (d.srcs.map Γ.val) Γ.flags next ((d.ea.map (eaOf Γ.val next)).getD 0)
        (d.cell s) with
    | some t => rfl
    | none =>
      show (List.foldl (fun (t : State) (p : Reg × BitVec 64) => t.setReg p.1 p.2) _ _).rip = next
      rw [foldl_setReg_rip]
      cases d.wr with
      | none => exact hrip
      | some mn => exact (storeN_rip _ _ _ _).trans hrip
  · -- and that it matches
    have h1 := hwΓw.apply (d.effect s)
    have h2 : WellTyped fetch sys Ψ' n (Γw.apply (d.effect s)) (d.after s) := by
      unfold Desc.after
      cases d.target s with
      | some t => exact h1.setRip t
      | none => exact h1
    rw [heff] at h2
    exact h2

end TypedAsm.U
