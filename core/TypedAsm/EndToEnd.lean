import TypedAsm.ArgText
import TypedAsm.LinuxOld
import TypedAsm.Output
import TypedAsm.Runs

/-!
# From a typed program to a safe run, in the old type system

It goes with the old core.
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

/-- Both at once: safe, ending only as wanted, and writing only as wanted. -/
theorem Entry.safeMem_exits_writes {Q : BitVec 32 → Prop}
    {R : BitVec 64 → List (BitVec 8) → Prop}
    (h : Entry (Asm.addr code base start) (Asm.parts base code) blocks room 0 s)
    (hty : BlocksOk (.ofLabels code base At) (Asm.fetch base code)
      ((linux.exitsOnly Q).writesOnly R) (.ofList blocks kinds))
    (hwf : (MemTy.ofList blocks kinds).WF) (hstart : At start (entryCtx room))
    (hfields : ∀ n, ∀ x ∈ blocks, ∀ p ∈ x.2.shape.vals,
      HasTy (Asm.fetch base code) ((linux.exitsOnly Q).writesOnly R) (.ofList blocks kinds) n p.2
        (s.load64 (x.1 + BitVec.ofNat 64 p.1))) :
    SafeMem linux s ∧ ExitsOnly (Asm.fetch base code) Q s ∧
      WritesOnly (Asm.fetch base code) R s :=
  have hw := Safe.of_writesOnly (h.safe hty hwf hstart hfields)
  have he := Safe.of_exitsOnly hw.1
  ⟨.of_safe linux_frame (Asm.loaded h.loaded) he.1, he.2,
    fun s' hs' len hf hax => hw.2 s' hs'.exitsOnly len hf hax⟩

theorem EntryArgs.safeMem_writes {R : BitVec 64 → List (BitVec 8) → Prop}
    (h : EntryArgs (Asm.addr code base start) (Asm.parts base code) blocks room s)
    (hty : BlocksOk (.ofLabels code base At) (Asm.fetch base code) (linux.writesOnly R)
      (.ofList blocks kinds))
    (hwf : (MemTy.ofList blocks kinds).WF) (hstart : ∀ c, At start (argsCtx room c))
    (hfields : ∀ x ∈ blocks, x.2.shape.vals = []) :
    SafeMem linux s ∧ WritesOnly (Asm.fetch base code) R s :=
  have hs := Safe.of_writesOnly (h.safe hty hwf hstart hfields)
  ⟨.of_safe linux_frame (Asm.loaded h.choose_spec.1.loaded) hs.1, hs.2⟩

theorem EntryArgs.safeMem_exits_writes {Q : BitVec 32 → Prop}
    {R : BitVec 64 → List (BitVec 8) → Prop}
    (h : EntryArgs (Asm.addr code base start) (Asm.parts base code) blocks room s)
    (hty : BlocksOk (.ofLabels code base At) (Asm.fetch base code)
      ((linux.exitsOnly Q).writesOnly R) (.ofList blocks kinds))
    (hwf : (MemTy.ofList blocks kinds).WF) (hstart : ∀ c, At start (argsCtx room c))
    (hfields : ∀ x ∈ blocks, x.2.shape.vals = []) :
    SafeMem linux s ∧ ExitsOnly (Asm.fetch base code) Q s ∧
      WritesOnly (Asm.fetch base code) R s :=
  have hw := Safe.of_writesOnly (h.safe hty hwf hstart hfields)
  have he := Safe.of_exitsOnly hw.1
  ⟨.of_safe linux_frame (Asm.loaded h.choose_spec.1.loaded) he.1, he.2,
    fun s' hs' len hf hax => hw.2 s' hs'.exitsOnly len hf hax⟩

theorem EntryTexts.safeMem_writes {R : BitVec 64 → List (BitVec 8) → Prop}
    (h : EntryTexts (Asm.addr code base start) (Asm.parts base code) blocks room s)
    (hty : BlocksOk (.ofLabels code base At) (Asm.fetch base code) (linux.writesOnly R)
      (.ofList blocks kinds))
    (hkinds : MemTy.declared kinds blocks = MemTy.actual blocks)
    (hstart : ∀ c, At start (textsCtx room c))
    (hfields : ∀ x ∈ blocks, x.2.shape.vals = []) :
    SafeMem linux s ∧ WritesOnly (Asm.fetch base code) R s :=
  have hs := Safe.of_writesOnly (h.safe hty hkinds hstart hfields)
  ⟨.of_safe linux_frame (Asm.loaded h.choose_spec.1.loaded) hs.1, hs.2⟩

theorem EntryTexts.safeMem_exits_writes {Q : BitVec 32 → Prop}
    {R : BitVec 64 → List (BitVec 8) → Prop}
    (h : EntryTexts (Asm.addr code base start) (Asm.parts base code) blocks room s)
    (hty : BlocksOk (.ofLabels code base At) (Asm.fetch base code)
      ((linux.exitsOnly Q).writesOnly R) (.ofList blocks kinds))
    (hkinds : MemTy.declared kinds blocks = MemTy.actual blocks)
    (hstart : ∀ c, At start (textsCtx room c))
    (hfields : ∀ x ∈ blocks, x.2.shape.vals = []) :
    SafeMem linux s ∧ ExitsOnly (Asm.fetch base code) Q s ∧
      WritesOnly (Asm.fetch base code) R s :=
  have hw := Safe.of_writesOnly (h.safe hty hkinds hstart hfields)
  have he := Safe.of_exitsOnly hw.1
  ⟨.of_safe linux_frame (Asm.loaded h.choose_spec.1.loaded) he.1, he.2,
    fun s' hs' len hf hax => hw.2 s' hs'.exitsOnly len hf hax⟩

end TypedAsm

