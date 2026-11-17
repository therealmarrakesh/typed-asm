import TypedAsm.Output
import TypedAsm.Machine

/-!
# What a run does

What it is for a program, started in a state, to end only with a status
that is as wanted, to offer at each `write` only what is wanted, and so to
have written only that. Said of the machine and the Linux model; a type
system is one way of showing them.
-/

namespace TypedAsm

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

/-! These rest on Lean's three standard axioms and nothing else: no proof in
the library is taken on trust from a solver or from compiled code. -/

/-! ## Safe, and writing only as wanted

A program typed against the system that refuses a `write` unless what is
offered satisfies `R` is safe under `linux`, and offers only such writes:
wherever it reaches one. -/

/-- What it is for the program started in `s` to offer the kernel, at every
`write` it reaches, a descriptor and bytes satisfying `R`. -/
def WritesOnly (fetch : Fetch) (R : BitVec 64 → List (BitVec 8) → Prop) (s : State) : Prop :=
  ∀ s', Steps fetch linux s s' → ∀ len, fetch s'.rip = some (.syscall, len) →
    s'.getReg .rax = 1 → R (s'.getReg .rdi) s'.offered

/-! The same for a program that looks at its arguments, as numbers or as
text: for every number of them. -/

/-! ## Everything a program writes

The record the world keeps of what was written, over a whole run. -/

/-- **Everything a program has written.** Where every `write` the program
reaches offers a descriptor and bytes satisfying `R`, each entry the run has
added to the record of writes is the first so many bytes of something
satisfying `R`: the kernel may take fewer bytes than it is offered, and
nothing else is ever written. -/
def OutputOnly (fetch : Fetch) (R : BitVec 64 → List (BitVec 8) → Prop) (s : State) : Prop :=
  ∀ s', Steps fetch linux s s' → ∃ new, s'.world.writes = new ++ s.world.writes ∧
    ∀ w ∈ new, ∃ fd bytes n, R fd bytes ∧ w = bytes.take n

theorem WritesOnly.output {fetch : Fetch} {R : BitVec 64 → List (BitVec 8) → Prop} {s : State}
    (h : WritesOnly fetch R s) : OutputOnly fetch R s := by
  intro s' hs'
  induction hs' with
  | refl s => exact ⟨[], rfl, fun _ hw => by cases hw⟩
  | @step s t u hst _ ih =>
    obtain ⟨new, e, hall⟩ := ih (fun v hv => h v (.step hst hv))
    rcases step_writes hst with e' | ⟨⟨len, hf⟩, hax, n, e'⟩
    · exact ⟨new, by rw [e, e'], hall⟩
    · refine ⟨new ++ [s.offered.take n], by rw [e, e', List.append_assoc]; rfl, fun w hw => ?_⟩
      rcases List.mem_append.mp hw with hw | hw
      · exact hall w hw
      · rw [List.mem_singleton.mp hw]
        exact ⟨_, _, n, h s (.refl s) len hf hax, rfl⟩


end TypedAsm

