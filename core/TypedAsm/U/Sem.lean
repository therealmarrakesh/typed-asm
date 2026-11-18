import TypedAsm.U.Basic

/-!
# What it is for code to be typed

Code at an address is typed in a context if, from every state at that
address that matches the context, the machine is safe. An instruction is
typed from one context to others if the machine's own step takes every state
matching the first to a state matching one of the others. These are said
here as they stand, of the machine; there is no list of rules beside them.
What a checker concludes, it concludes of these.

Both are counted in steps, as what is known of a code value is: safe for so
many steps, for every count.
-/

namespace TypedAsm.U

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

/-- `Ok fetch sys Ψ n a Γ`: from any state at `a` that matches `Γ`, now or
however the memory typing has grown, the machine is safe for up to `n`
steps. -/
def Ok (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (n : Nat) (a : BitVec 64) (Γ : Ctx) : Prop :=
  ∀ k, k ≤ n → ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → ∀ s : State, s.rip = a →
    WellTyped fetch sys Ψ' k Γ s → SafeN fetch sys k s

theorem Ok.mono {n m : Nat} {a : BitVec 64} {Γ : Ctx} (h : Ok fetch sys Ψ n a Γ) (hle : m ≤ n) :
    Ok fetch sys Ψ m a Γ :=
  fun k hk => h k (Nat.le_trans hk hle)

/-- Typed code stays typed as the memory typing grows. -/
theorem Ok.ext {Ψ' : MemTy} {n : Nat} {a : BitVec 64} {Γ : Ctx} (h : Ok fetch sys Ψ n a Γ)
    (he : Ψ.Ext Ψ') : Ok fetch sys Ψ' n a Γ :=
  fun k hk Ψ'' he' => h k hk Ψ'' (he.trans he')

/-- Code wanting a family of contexts is code typed in each of them, for
fewer steps. -/
theorem hasTy_code_iff {n : Nat} {pre : Fam → Ctx} {v : BitVec 64} :
    HasTy fetch sys Ψ (n + 1) (.code pre) v ↔ ∀ x, Ok fetch sys Ψ n v (pre x) := by
  rw [hasTy_code]
  constructor
  · exact fun h x k hk Ψ' he hwf s hs hw => h x k (by omega) Ψ' he hwf s hs hw
  · exact fun h x k hk Ψ' he hwf s hs hw => h x k (by omega) Ψ' he hwf s hs hw

/-- `Steps fetch sys Ψ i next Γ Q`: the instruction `i`, with the instruction
pointer already at `next` past it, takes every state that matches `Γ` to a
state at some address `t` that matches some context `Γ'`, with `Q t Γ'`,
under the same memory typing: no instruction makes memory held alone into
memory others may point into. -/
def Steps (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (i : Instr) (next : BitVec 64) (Γ : Ctx)
    (Q : BitVec 64 → Ctx → Prop) : Prop :=
  ∀ n, ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → ∀ s : State, s.rip = next →
    WellTyped fetch sys Ψ' n Γ s →
    ∃ s', exec sys i s = .next s' ∧ ∃ Γ', Q s'.rip Γ' ∧ WellTyped fetch sys Ψ' n Γ' s'

/-- Where the instruction pointer is, is no part of what a context says. -/
theorem WellTyped.setRip {n : Nat} {Γ : Ctx} {s : State} (h : WellTyped fetch sys Ψ n Γ s)
    (v : BitVec 64) : WellTyped fetch sys Ψ n Γ { s with rip := v } :=
  { val := h.val
    known := h.known
    flags := h.flags
    heapPerm := h.heapPerm
    heap := h.heap
    text := h.text
    said := h.said
    rows := h.rows
    fed := h.fed
    complete := h.complete
    held :=
      { perm := h.held.perm
        size_lt := h.held.size_lt
        fits := h.held.fits
        vals := h.held.vals
        heap := h.held.heap
        apart := h.held.apart } }

/-- `Arrives fetch sys Ψ n t Γ`: a state that has just come to `t`, matching
`Γ`, is safe for up to `n` steps. It is what is asked of each place an
instruction may leave the machine. The state has what was known before the
step, which is one step's worth more than typed code at `t` needs. -/
def Arrives (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (n : Nat) (t : BitVec 64) (Γ : Ctx) :
    Prop :=
  ∀ k, k ≤ n → ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → ∀ s : State, s.rip = t →
    WellTyped fetch sys Ψ' (k + 1) Γ s → SafeN fetch sys k s

/-- At typed code, the machine arrives. -/
theorem Ok.arrives {n : Nat} {t : BitVec 64} {Γ : Ctx} (h : Ok fetch sys Ψ n t Γ) :
    Arrives fetch sys Ψ n t Γ :=
  fun k hk Ψ' he hwf s hs hw => h k hk Ψ' he hwf s hs (hw.mono (Nat.le_succ k))

/-- **An instruction typed, and the machine arriving wherever it may leave
it, is typed.** One statement for an instruction that goes on to the next
and for one that passes control elsewhere. -/
theorem Ok.step {a len : BitVec 64} {i : Instr} {n : Nat} {Γ : Ctx} {Q : BitVec 64 → Ctx → Prop}
    (hf : fetch a = some (i, len)) (hs : Steps fetch sys Ψ i (a + len) Γ Q)
    (hrest : ∀ t Γ', Q t Γ' → Arrives fetch sys Ψ n t Γ') : Ok fetch sys Ψ (n + 1) a Γ := by
  intro k hk Ψ' he hwf s hrip hw
  cases k with
  | zero => trivial
  | succ k =>
    obtain ⟨s', hex, Γ', hQ, hw'⟩ :=
      hs (k + 1) Ψ' he hwf _ (by show s.rip + len = a + len; rw [hrip]) (hw.setRip (s.rip + len))
    have hstep : TypedAsm.step fetch sys s = .next s' := by
      unfold TypedAsm.step
      rw [hrip, hf]
      rw [hrip] at hex
      exact hex
    refine ⟨by rw [hstep]; rfl, fun s'' hs'' => ?_⟩
    rw [hstep] at hs''
    cases hs''
    exact hrest _ Γ' hQ k (by omega) Ψ' he hwf s' rfl hw'

end TypedAsm.U
