import TypedAsm.ArgText
import TypedAsm.Linux

/-!
# From a typed program to a safe run

Everything in one step. A program whose blocks are typed, started in a state
that meets its entry contract, is safe on the machine that fetches
instructions by decoding the bytes in memory: it never gets stuck and never
faults, whatever it reads, whatever the kernel answers, and however long it
runs.

There is one theorem for each entry contract: `Entry.safeMem` for a program
that does not look at its arguments, `EntryArgs.safeMem` for one that goes
through them as numbers, and `EntryTexts.safeMem` for one that reads their
text. Each asks for the same things: the typing of the blocks, that the
context allowed at the entry label is the one the contract provides, and
that the data the program is loaded with has the types the blocks claim.
-/

namespace TypedAsm

variable {L : Type} [DecidableEq L] {code : List (Asm L)} {base : BitVec 64}
  {blocks : List (BitVec 64 × Layout)} {kinds : List (Nat × Shape)}
  {At : L → Ctx → Prop} {start : L} {room : Nat} {s : State}

/-- When the blocks are all plain bytes, the data has the types the blocks
claim, whatever it is. -/
theorem Entry.plain {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}
    (h : ∀ x ∈ blocks, x.2.shape.vals = []) :
    ∀ n, ∀ x ∈ blocks, ∀ p ∈ x.2.shape.vals,
      HasTy fetch sys Ψ n p.2 (s.load64 (x.1 + BitVec.ofNat 64 p.1)) :=
  fun _ x hx p hp => by
    rw [h x hx] at hp
    cases hp

/-- A state meeting the entry contract is well typed, at the entry label. -/
theorem Entry.stateOk {parts : List (Nat × Perm × List Byte)} {sys : Syscall}
    (hstart : At start (entryCtx room))
    (hfields : ∀ n, ∀ x ∈ blocks, ∀ p ∈ x.2.shape.vals,
      HasTy (Asm.fetch base code) sys (.ofList blocks kinds) n p.2
        (s.load64 (x.1 + BitVec.ofNat 64 p.1)))
    (h : Entry (Asm.addr code base start) parts blocks room 0 s) :
    StateOk (.ofLabels code base At) (Asm.fetch base code) sys (.ofList blocks kinds) s :=
  ⟨entryCtx room, by rw [h.rip]; exact .intro hstart, fun n => h.matches HasTy.int (hfields n)⟩

/-- A typed program started in a state meeting its entry contract is safe on
the machine that looks instructions up in the program. -/
theorem Entry.safe {parts : List (Nat × Perm × List Byte)} {sys : Syscall}
    (h : Entry (Asm.addr code base start) parts blocks room 0 s)
    (hty : BlocksOk (.ofLabels code base At) (Asm.fetch base code) sys (.ofList blocks kinds))
    (hwf : (MemTy.ofList blocks kinds).WF) (hstart : At start (entryCtx room))
    (hfields : ∀ n, ∀ x ∈ blocks, ∀ p ∈ x.2.shape.vals,
      HasTy (Asm.fetch base code) sys (.ofList blocks kinds) n p.2
        (s.load64 (x.1 + BitVec.ofNat 64 p.1))) :
    Safe (Asm.fetch base code) sys s :=
  soundness_blocks hty hwf (h.stateOk hstart hfields)

/-- **A typed program started in a state meeting its entry contract is safe
on the machine that fetches instructions by decoding memory.** -/
theorem Entry.safeMem
    (h : Entry (Asm.addr code base start) (Asm.parts base code) blocks room 0 s)
    (hty : BlocksOk (.ofLabels code base At) (Asm.fetch base code) linux (.ofList blocks kinds))
    (hwf : (MemTy.ofList blocks kinds).WF) (hstart : At start (entryCtx room))
    (hfields : ∀ n, ∀ x ∈ blocks, ∀ p ∈ x.2.shape.vals,
      HasTy (Asm.fetch base code) linux (.ofList blocks kinds) n p.2
        (s.load64 (x.1 + BitVec.ofNat 64 p.1))) :
    SafeMem linux s :=
  .of_safe linux_frame (Asm.loaded h.loaded) (h.safe hty hwf hstart hfields)

/-- The same for a program that goes through its arguments: the entry label
allows the context for any number of them. -/
theorem EntryArgs.safe {parts : List (Nat × Perm × List Byte)} {sys : Syscall}
    (h : EntryArgs (Asm.addr code base start) parts blocks room s)
    (hty : BlocksOk (.ofLabels code base At) (Asm.fetch base code) sys (.ofList blocks kinds))
    (hwf : (MemTy.ofList blocks kinds).WF) (hstart : ∀ c, At start (argsCtx room c))
    (hfields : ∀ x ∈ blocks, x.2.shape.vals = []) :
    Safe (Asm.fetch base code) sys s :=
  let ⟨c, hE, hc⟩ := h
  soundness_blocks hty hwf
    ⟨argsCtx room c, by rw [hE.rip]; exact .intro (hstart c),
      fun _ => hE.matchesCount hc HasTy.int (fun _ => hasTy_eq.mpr rfl) hfields⟩

theorem EntryArgs.safeMem
    (h : EntryArgs (Asm.addr code base start) (Asm.parts base code) blocks room s)
    (hty : BlocksOk (.ofLabels code base At) (Asm.fetch base code) linux (.ofList blocks kinds))
    (hwf : (MemTy.ofList blocks kinds).WF) (hstart : ∀ c, At start (argsCtx room c))
    (hfields : ∀ x ∈ blocks, x.2.shape.vals = []) :
    SafeMem linux s :=
  .of_safe linux_frame (Asm.loaded h.choose_spec.1.loaded) (h.safe hty hwf hstart hfields)

/-- The same for a program that reads its arguments' text. The text is in
blocks the program's memory typing does not list, one for each argument,
wherever the kernel put them: the typing grows to take them in. -/
theorem EntryTexts.safe {parts : List (Nat × Perm × List Byte)} {sys : Syscall}
    (h : EntryTexts (Asm.addr code base start) parts blocks room s)
    (hty : BlocksOk (.ofLabels code base At) (Asm.fetch base code) sys (.ofList blocks kinds))
    (hkinds : MemTy.declared kinds blocks = MemTy.actual blocks)
    (hstart : ∀ c, At start (textsCtx room c))
    (hfields : ∀ x ∈ blocks, x.2.shape.vals = []) :
    Safe (Asm.fetch base code) sys s := by
  obtain ⟨c, Ψ', he, hΨ', hrip, -, hw⟩ :=
    h.wellTyped (kinds := kinds) (fetch := Asm.fetch base code) (sys := sys) hkinds hfields
  exact soundness_blocks_ext hty he hΨ'
    ⟨textsCtx room c, by rw [hrip]; exact .intro (hstart c), hw⟩

theorem EntryTexts.safeMem
    (h : EntryTexts (Asm.addr code base start) (Asm.parts base code) blocks room s)
    (hty : BlocksOk (.ofLabels code base At) (Asm.fetch base code) linux (.ofList blocks kinds))
    (hkinds : MemTy.declared kinds blocks = MemTy.actual blocks)
    (hstart : ∀ c, At start (textsCtx room c))
    (hfields : ∀ x ∈ blocks, x.2.shape.vals = []) :
    SafeMem linux s :=
  .of_safe linux_frame (Asm.loaded h.choose_spec.1.loaded) (h.safe hty hkinds hstart hfields)

/-! ## Safe, and ending only as wanted

A program typed against the system that lets it end only with a status
satisfying `Q` is safe under `linux`, and ends only with such a status:
wherever it reaches a system call that ends it. One typing gives both. The
second is said of the machine that looks instructions up in the program. -/

/-- What it is for the program started in `s` to end only with a status
satisfying `Q`. -/
def ExitsOnly (fetch : Fetch) (Q : BitVec 32 → Prop) (s : State) : Prop :=
  ∀ s', Steps fetch linux s s' → ∀ len c, fetch s'.rip = some (.syscall, len) →
    linux { s' with rip := s'.rip + len } = .exit c → Q c

theorem Entry.safeMem_exits {Q : BitVec 32 → Prop}
    (h : Entry (Asm.addr code base start) (Asm.parts base code) blocks room 0 s)
    (hty : BlocksOk (.ofLabels code base At) (Asm.fetch base code) (linux.exitsOnly Q)
      (.ofList blocks kinds))
    (hwf : (MemTy.ofList blocks kinds).WF) (hstart : At start (entryCtx room))
    (hfields : ∀ n, ∀ x ∈ blocks, ∀ p ∈ x.2.shape.vals,
      HasTy (Asm.fetch base code) (linux.exitsOnly Q) (.ofList blocks kinds) n p.2
        (s.load64 (x.1 + BitVec.ofNat 64 p.1))) :
    SafeMem linux s ∧ ExitsOnly (Asm.fetch base code) Q s :=
  have hs := Safe.of_exitsOnly (h.safe hty hwf hstart hfields)
  ⟨.of_safe linux_frame (Asm.loaded h.loaded) hs.1, hs.2⟩

theorem EntryArgs.safeMem_exits {Q : BitVec 32 → Prop}
    (h : EntryArgs (Asm.addr code base start) (Asm.parts base code) blocks room s)
    (hty : BlocksOk (.ofLabels code base At) (Asm.fetch base code) (linux.exitsOnly Q)
      (.ofList blocks kinds))
    (hwf : (MemTy.ofList blocks kinds).WF) (hstart : ∀ c, At start (argsCtx room c))
    (hfields : ∀ x ∈ blocks, x.2.shape.vals = []) :
    SafeMem linux s ∧ ExitsOnly (Asm.fetch base code) Q s :=
  have hs := Safe.of_exitsOnly (h.safe hty hwf hstart hfields)
  ⟨.of_safe linux_frame (Asm.loaded h.choose_spec.1.loaded) hs.1, hs.2⟩

theorem EntryTexts.safeMem_exits {Q : BitVec 32 → Prop}
    (h : EntryTexts (Asm.addr code base start) (Asm.parts base code) blocks room s)
    (hty : BlocksOk (.ofLabels code base At) (Asm.fetch base code) (linux.exitsOnly Q)
      (.ofList blocks kinds))
    (hkinds : MemTy.declared kinds blocks = MemTy.actual blocks)
    (hstart : ∀ c, At start (textsCtx room c))
    (hfields : ∀ x ∈ blocks, x.2.shape.vals = []) :
    SafeMem linux s ∧ ExitsOnly (Asm.fetch base code) Q s :=
  have hs := Safe.of_exitsOnly (h.safe hty hkinds hstart hfields)
  ⟨.of_safe linux_frame (Asm.loaded h.choose_spec.1.loaded) hs.1, hs.2⟩

/-! These rest on Lean's three standard axioms and nothing else: no proof in
the library is taken on trust from a solver or from compiled code. -/

/-- info: 'TypedAsm.Entry.safeMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Entry.safeMem

/--
info: 'TypedAsm.EntryArgs.safeMem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EntryArgs.safeMem

/--
info: 'TypedAsm.EntryTexts.safeMem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EntryTexts.safeMem

/-! ## Safe, and writing only as wanted

A program typed against the system that refuses a `write` unless what is
offered satisfies `R` is safe under `linux`, and offers only such writes:
wherever it reaches one. -/

/-- What it is for the program started in `s` to offer the kernel, at every
`write` it reaches, a descriptor and bytes satisfying `R`. -/
def WritesOnly (fetch : Fetch) (R : BitVec 64 → List (BitVec 8) → Prop) (s : State) : Prop :=
  ∀ s', Steps fetch linux s s' → ∀ len, fetch s'.rip = some (.syscall, len) →
    s'.getReg .rax = 1 → R (s'.getReg .rdi) s'.offered

theorem Entry.safeMem_writes {R : BitVec 64 → List (BitVec 8) → Prop}
    (h : Entry (Asm.addr code base start) (Asm.parts base code) blocks room 0 s)
    (hty : BlocksOk (.ofLabels code base At) (Asm.fetch base code) (linux.writesOnly R)
      (.ofList blocks kinds))
    (hwf : (MemTy.ofList blocks kinds).WF) (hstart : At start (entryCtx room))
    (hfields : ∀ n, ∀ x ∈ blocks, ∀ p ∈ x.2.shape.vals,
      HasTy (Asm.fetch base code) (linux.writesOnly R) (.ofList blocks kinds) n p.2
        (s.load64 (x.1 + BitVec.ofNat 64 p.1))) :
    SafeMem linux s ∧ WritesOnly (Asm.fetch base code) R s :=
  have hs := Safe.of_writesOnly (h.safe hty hwf hstart hfields)
  ⟨.of_safe linux_frame (Asm.loaded h.loaded) hs.1, hs.2⟩

end TypedAsm
