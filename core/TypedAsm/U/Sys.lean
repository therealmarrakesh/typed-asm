import TypedAsm.U.Program
import TypedAsm.Linux

/-!
# System calls, described

What a call does to the program is one of a few things, whichever call it
is: nothing, beyond handing back a value; storing some bytes at an address
the program gave, and handing back a value; ending the program. A system is
described by saying, for each call number, which; and what it asks of the
state for the call to be let through, where it refuses some.

A call is then typed by what it is described to do, by one statement for
each of those few things. No call has a rule of its own.
-/

namespace TypedAsm.U

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

/-- The context a call returns in, with the value `v` handed back: `rax`
holds it, `rcx` the address after the call, `r11` the value `r` the kernel
left there, and the flags are undefined. -/
def CtxOf.afterSys (Γ : Ctx) (v r next : BitVec 64) : Ctx :=
  Γ.apply ⟨[(.rax, v), (.rcx, next), (.r11, r)], Flags.unknown, 0⟩

/-- What is in the world outside is no part of what a context says. -/
theorem WellTyped.setWorld {n : Nat} {Γ : Ctx} {s : State} (h : WellTyped fetch sys Ψ n Γ s)
    (w : World) : WellTyped fetch sys Ψ n Γ { s with world := w } :=
  { val := h.val
    known := h.known
    flags := h.flags
    heapPerm := h.heapPerm
    heap := h.heap
    text := h.text
    said := h.said
    rows := h.rows
    complete := h.complete
    held :=
      { perm := h.held.perm
        size_lt := h.held.size_lt
        fits := h.held.fits
        vals := h.held.vals
        heap := h.held.heap
        apart := h.held.apart } }

/-- A state a call returns in, with the world changed, matches the context
a call returns in. -/
theorem WellTyped.ret {n : Nat} {Γ : Ctx} {s : State} (h : WellTyped fetch sys Ψ n Γ s)
    (v : BitVec 64) (w : World) :
    WellTyped fetch sys Ψ n (Γ.afterSys v (w.saved 0) s.rip)
      (Linux.ret { s with world := w } v) :=
  ((h.setWorld w).apply ⟨[(.rax, v), (.rcx, s.rip), (.r11, w.saved 0)], Flags.unknown, 0⟩).setWorld
    w.spent

/-- What a call does to the program. -/
inductive SysKind
  /-- Nothing, beyond handing back a value: an error number or no more than
  a register says, where one is named. -/
  | world (most : Option Reg := none)
  /-- It stores at most so many bytes at the address in a register: as many
  as another register says, or a fixed number. -/
  | fills (buf : Reg) (room : Reg ⊕ Nat)
  /-- It ends the program. -/
  | ends
  /-- It hands back fresh memory, of as many whole pages as the length in
  `rsi` comes to, or an error number. -/
  | map
  /-- It takes back the memory at the address in `rdi`, of as many whole
  pages as the length in `rsi` comes to; or refuses. -/
  | unmap

/-- A system, described: what the call of each number does, and what the
system asks of the state for a call to be let through. -/
structure SysDesc where
  kind : BitVec 64 → Option SysKind
  pre : State → Prop := fun _ => True

/-- How many bytes a call may store. -/
def roomOf (s : State) : Reg ⊕ Nat → Nat
  | .inl r => (s.getReg r).toNat
  | .inr n => n

/-- The same from the values a context gives the registers. -/
def roomVal (val : Reg → BitVec 64) : Reg ⊕ Nat → Nat
  | .inl r => (val r).toNat
  | .inr n => n

/-- The bytes in whole pages that a length comes to. -/
def pages (len : BitVec 64) : Nat := (len.toNat + 4095) / 4096 * 4096

/-- `t` is `s` after a call that handed back an error number and touched
nothing of the program's, or handed back the address of `size` bytes of
fresh memory, zero, readable and writable, where nothing was accessible. -/
def Maps (s : State) (size : Nat) (t : State) : Prop :=
  (∃ v w, SysErr v ∧ t = Linux.ret { s with world := w } v) ∨
  ∃ a w, a.toNat % 4096 = 0 ∧ 0 < a.toNat ∧ a.toNat + size ≤ addrTop ∧
    s.unmapped a size = true ∧ t = Linux.ret { s.mapZero a size with world := w } a

/-- `t` is `s` after a call that refused, handing back an error number, and
touched nothing; or made the `size` bytes at `a` inaccessible, `a` being the
start of a page, and handed back zero. Which it did is told by what it
handed back: a program that still holds the memory must be able to know. -/
def Unmaps (s : State) (a : BitVec 64) (size : Nat) (t : State) : Prop :=
  (∃ v, SysErr v ∧ t = Linux.ret s v) ∨
  (a.toNat % 4096 = 0 ∧ a.toNat + size ≤ addrTop ∧ t = Linux.ret (s.unmap a size) 0)

/-- `Describes sys D`: the system does what `D` says, for every call `D`
describes that it lets through. -/
def Describes (sys : Syscall) (D : SysDesc) : Prop :=
  ∀ (s : State) (k : SysKind), D.kind (s.getReg .rax) = some k → D.pre s →
    match k with
    | .world most => ∃ t, sys s = .next t ∧ Linux.OnlyWorld s t ∧
      ∀ r, most = some r → Linux.Answered (s.getReg r).toNat (t.getReg .rax)
    | .fills b room => ∃ t, sys s = .next t ∧ Linux.Fills s (s.getReg b) (roomOf s room) t ∧
      Linux.Answered (roomOf s room) (t.getReg .rax)
    | .ends => ∃ c, sys s = .exit c
    | .map => s.getReg .rdi = 0 → ∃ t, sys s = .next t ∧ Maps s (pages (s.getReg .rsi)) t
    | .unmap => ∃ t, sys s = .next t ∧ Unmaps s (s.getReg .rdi) (pages (s.getReg .rsi)) t

/-- **A call that does nothing to the program** returns with a value in
`rax`: an error number or no more than a register held, where the call is
described so, and otherwise anything. -/
theorem Steps.world {D : SysDesc} (hD : Describes sys D) {Γ : Ctx} {next : BitVec 64}
    {most : Option Reg} (hk : D.kind (Γ.val .rax) = some (.world most))
    (hpre : ∀ n, ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → ∀ s : State, s.rip = next →
      WellTyped fetch sys Ψ' n Γ s → D.pre s) :
    Steps fetch sys Ψ .syscall next Γ fun t Γ' => t = next ∧ ∃ v r, Γ' = Γ.afterSys v r next ∧
      ∀ r', most = some r' → Linux.Answered (Γ.val r').toNat v := by
  intro n Ψ' he hwf s hrip hw
  obtain ⟨t, hst, ⟨v, w, rfl⟩, hans⟩ :=
    hD s (.world most) (by rw [hw.val]; exact hk) (hpre n Ψ' he hwf s hrip hw)
  refine ⟨_, hst, Γ.afterSys v (w.saved 0) next, ⟨hrip, v, _, rfl, fun r' hr' => by
    have := hans r' hr'
    rw [Linux.ret_rax, hw.val] at this
    exact this⟩, ?_⟩
  rw [← hrip]
  exact hw.ret v w

/-- `Havoc … Γ a n Γh`: whatever bytes, at most `n`, are stored at `a` where
they may be written, a state that matched `Γ` matches `Γh`: `Γ` with nothing
said of those bytes. -/
def Havoc (fetch : Fetch) (sys : Syscall) (Ψ : MemTy) (Γ : Ctx) (a : BitVec 64) (n : Nat)
    (Γh : Ctx) : Prop :=
  Γh.val = Γ.val ∧ Γh.flags = Γ.flags ∧
  ∀ k, ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → ∀ s : State, WellTyped fetch sys Ψ' k Γ s →
    ∀ data : List (BitVec 8), data.length ≤ n → s.canWrite a data.length = true →
    WellTyped fetch sys Ψ' k Γh (s.storeBytes a data)

/-- **A call that stores bytes at an address the program gives** returns
with a value in `rax`, the context saying nothing of those bytes. -/
theorem Steps.fills {D : SysDesc} (hD : Describes sys D) {Γ Γh : Ctx} {next : BitVec 64}
    {b : Reg} {room : Reg ⊕ Nat} (hk : D.kind (Γ.val .rax) = some (.fills b room))
    (hpre : ∀ n, ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → ∀ s : State, s.rip = next →
      WellTyped fetch sys Ψ' n Γ s → D.pre s)
    (hh : Havoc fetch sys Ψ Γ (Γ.val b) (roomVal Γ.val room) Γh) :
    Steps fetch sys Ψ .syscall next Γ fun t Γ' =>
      t = next ∧ ∃ v r, (Γ' = Γ.afterSys v r next ∨ Γ' = Γh.afterSys v r next) ∧
        Linux.Answered (roomVal Γ.val room) v := by
  intro n Ψ' he hwf s hrip hw
  obtain ⟨t, hst, hfills, hans⟩ := hD s (.fills b room) (by rw [hw.val]; exact hk)
    (hpre n Ψ' he hwf s hrip hw)
  have hroom : roomOf s room = roomVal Γ.val room := by
    cases room with
    | inl r => show (s.getReg r).toNat = (Γ.val r).toNat; rw [hw.val]
    | inr k => rfl
  rw [hroom] at hans
  rcases hfills with ⟨v, w, rfl⟩ | ⟨data, v, w, hlen, hcw, rfl⟩
  · rw [Linux.ret_rax] at hans
    refine ⟨_, hst, Γ.afterSys v (w.saved 0) next, ⟨hrip, v, _, .inl rfl, hans⟩, ?_⟩
    rw [← hrip]
    exact hw.ret v w
  · rw [Linux.give_rax] at hans
    refine ⟨_, hst, Γh.afterSys v (w.saved 0) next, ⟨hrip, v, _, .inr rfl, hans⟩, ?_⟩
    rw [hroom] at hlen
    have hb : s.getReg b = Γ.val b := hw.val b
    rw [hb] at hcw
    have h₁ := hh.2.2 n Ψ' he hwf s hw data hlen hcw
    rw [← hrip, hb]
    exact h₁.ret v w

/-- **A call that ends the program** is typed, whatever follows it. -/
theorem Ok.ends {D : SysDesc} (hD : Describes sys D) {Γ : Ctx} {a len : BitVec 64} {n : Nat}
    (hf : fetch a = some (.syscall, len)) (hk : D.kind (Γ.val .rax) = some .ends)
    (hpre : ∀ n, ∀ Ψ' : MemTy, Ψ.Ext Ψ' → Ψ'.WF → ∀ s : State, s.rip = a + len →
      WellTyped fetch sys Ψ' n Γ s → D.pre s) :
    Ok fetch sys Ψ n a Γ := by
  intro k _ Ψ' he hwf s hrip hw
  cases k with
  | zero => trivial
  | succ k =>
    have hw₁ := hw.setRip (s.rip + len)
    obtain ⟨c, hc⟩ := hD _ .ends (by rw [hw₁.val]; exact hk)
      (hpre (k + 1) Ψ' he hwf _ (by show s.rip + len = a + len; rw [hrip]) hw₁)
    have hstep : TypedAsm.step fetch sys s = .exit c := by
      unfold TypedAsm.step
      rw [hrip, hf]
      rw [hrip] at hc
      exact hc
    exact ⟨by rw [hstep]; rfl, fun s' hs' => by rw [hstep] at hs'; cases hs'⟩

end TypedAsm.U
