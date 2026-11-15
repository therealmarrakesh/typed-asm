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

variable {L : Type} [DecidableEq L] {code : List (Asm L)} {base dataBase : BitVec 64}
  {data : List Byte} {blocks : List (BitVec 64 × Layout)} {kinds : List (Nat × List Ty)}
  {At : L → Ctx → Prop} {start : L} {room : Nat} {s : State}

/-- When every field of every block is an integer, the data has the types the
blocks claim, whatever it is. -/
theorem Entry.fieldsInt {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}
    (h : ∀ x ∈ blocks, ∀ τ ∈ x.2.fields, τ = .int) :
    ∀ n, ∀ x ∈ blocks, ∀ i τ, x.2.fields[i]? = some τ →
      HasTy fetch sys Ψ n τ (s.load64 (x.1 + BitVec.ofNat 64 (8 * i))) :=
  fun _ x hx _ τ hi => by
    rw [h x hx τ (List.mem_of_getElem? hi)]
    exact HasTy.int _

/-- A state meeting the entry contract is well typed, at the entry label. -/
theorem Entry.stateOk {image : List Byte} {sys : Syscall}
    (hstart : At start (entryCtx room))
    (hfields : ∀ n, ∀ x ∈ blocks, ∀ i τ, x.2.fields[i]? = some τ →
      HasTy (Asm.fetch base code) sys (.ofList blocks kinds) n τ
        (s.load64 (x.1 + BitVec.ofNat 64 (8 * i))))
    (h : Entry (Asm.addr code base start) base image dataBase data blocks room 0 s) :
    StateOk (.ofLabels code base At) (Asm.fetch base code) sys (.ofList blocks kinds) s :=
  ⟨entryCtx room, by rw [h.rip]; exact .intro hstart, fun n => h.matches HasTy.int (hfields n)⟩

/-- A typed program started in a state meeting its entry contract is safe on
the machine that looks instructions up in the program. -/
theorem Entry.safe {image : List Byte} {sys : Syscall}
    (h : Entry (Asm.addr code base start) base image dataBase data blocks room 0 s)
    (hty : BlocksOk (.ofLabels code base At) (Asm.fetch base code) sys (.ofList blocks kinds))
    (hwf : (MemTy.ofList blocks kinds).WF) (hstart : At start (entryCtx room))
    (hfields : ∀ n, ∀ x ∈ blocks, ∀ i τ, x.2.fields[i]? = some τ →
      HasTy (Asm.fetch base code) sys (.ofList blocks kinds) n τ
        (s.load64 (x.1 + BitVec.ofNat 64 (8 * i)))) :
    Safe (Asm.fetch base code) sys s :=
  soundness_blocks hty hwf (h.stateOk hstart hfields)

/-- **A typed program started in a state meeting its entry contract is safe
on the machine that fetches instructions by decoding memory.** -/
theorem Entry.safeMem
    (h : Entry (Asm.addr code base start) base (Asm.image base code) dataBase data blocks room 0 s)
    (hty : BlocksOk (.ofLabels code base At) (Asm.fetch base code) linux (.ofList blocks kinds))
    (hwf : (MemTy.ofList blocks kinds).WF) (hstart : At start (entryCtx room))
    (hfields : ∀ n, ∀ x ∈ blocks, ∀ i τ, x.2.fields[i]? = some τ →
      HasTy (Asm.fetch base code) linux (.ofList blocks kinds) n τ
        (s.load64 (x.1 + BitVec.ofNat 64 (8 * i)))) :
    SafeMem linux s :=
  .of_safe linux_frame (Asm.loaded h.code) (h.safe hty hwf hstart hfields)

/-- The same for a program that goes through its arguments: the entry label
allows the context for any number of them. -/
theorem EntryArgs.safe {image : List Byte} {sys : Syscall}
    (h : EntryArgs (Asm.addr code base start) base image dataBase data blocks room s)
    (hty : BlocksOk (.ofLabels code base At) (Asm.fetch base code) sys (.ofList blocks kinds))
    (hwf : (MemTy.ofList blocks kinds).WF) (hstart : ∀ c, At start (argsCtx room c))
    (hfields : ∀ x ∈ blocks, ∀ τ ∈ x.2.fields, τ = .int) :
    Safe (Asm.fetch base code) sys s :=
  let ⟨c, hE, hc⟩ := h
  soundness_blocks hty hwf
    ⟨argsCtx room c, by rw [hE.rip]; exact .intro (hstart c),
      fun _ => hE.matchesCount hc HasTy.int (fun _ => hasTy_eq.mpr rfl) hfields⟩

theorem EntryArgs.safeMem
    (h : EntryArgs (Asm.addr code base start) base (Asm.image base code) dataBase data blocks
      room s)
    (hty : BlocksOk (.ofLabels code base At) (Asm.fetch base code) linux (.ofList blocks kinds))
    (hwf : (MemTy.ofList blocks kinds).WF) (hstart : ∀ c, At start (argsCtx room c))
    (hfields : ∀ x ∈ blocks, ∀ τ ∈ x.2.fields, τ = .int) :
    SafeMem linux s :=
  .of_safe linux_frame (Asm.loaded h.choose_spec.1.code) (h.safe hty hwf hstart hfields)

/-- The same for a program that reads its arguments' text. The text is in
blocks the program's memory typing does not list, one for each argument,
wherever the kernel put them: the typing grows to take them in. -/
theorem EntryTexts.safe {image : List Byte} {sys : Syscall}
    (h : EntryTexts (Asm.addr code base start) base image dataBase data blocks room s)
    (hty : BlocksOk (.ofLabels code base At) (Asm.fetch base code) sys (.ofList blocks kinds))
    (hkinds : MemTy.declared kinds blocks = MemTy.actual blocks)
    (hstart : ∀ c, At start (textsCtx room c))
    (hfields : ∀ x ∈ blocks, ∀ τ ∈ x.2.fields, τ = .int) :
    Safe (Asm.fetch base code) sys s := by
  obtain ⟨c, Ψ', he, hΨ', hrip, -, hw⟩ :=
    h.wellTyped (kinds := kinds) (fetch := Asm.fetch base code) (sys := sys) hkinds hfields
  exact soundness_blocks_ext hty he hΨ'
    ⟨textsCtx room c, by rw [hrip]; exact .intro (hstart c), hw⟩

theorem EntryTexts.safeMem
    (h : EntryTexts (Asm.addr code base start) base (Asm.image base code) dataBase data blocks
      room s)
    (hty : BlocksOk (.ofLabels code base At) (Asm.fetch base code) linux (.ofList blocks kinds))
    (hkinds : MemTy.declared kinds blocks = MemTy.actual blocks)
    (hstart : ∀ c, At start (textsCtx room c))
    (hfields : ∀ x ∈ blocks, ∀ τ ∈ x.2.fields, τ = .int) :
    SafeMem linux s :=
  .of_safe linux_frame (Asm.loaded h.choose_spec.1.code) (h.safe hty hkinds hstart hfields)

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

end TypedAsm
