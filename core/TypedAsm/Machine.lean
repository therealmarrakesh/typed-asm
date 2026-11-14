import TypedAsm.Frame
import TypedAsm.Safety
import TypedAsm.Roundtrip

/-!
# The machine with code in memory

Until now the instruction at an address came from a table handed to the
semantics. Here it comes from memory: the bytes at `rip` are decoded, and
they must be executable.

The two agree. If a program's encoding is in executable memory, a run that
is safe by the table is safe on this machine, and takes the same steps.
-/

namespace TypedAsm

/-- No instruction is longer than this, so this many bytes are always enough to decode one. -/
def maxInstrLength : Nat := 15

namespace State

/-- Whether all `n` bytes starting at `a` are executable. -/
def canExec (s : State) (a : BitVec 64) (n : Nat) : Bool :=
  (List.range n).all fun i => (s.perm (a + BitVec.ofNat 64 i)).executable

/-- The `n` bytes of memory starting at `a`. -/
def bytesAt (s : State) (a : BitVec 64) (n : Nat) : List Byte :=
  (List.range n).map fun k => s.mem (a + BitVec.ofNat 64 k)

/-- The instruction at `rip` and its length, read from memory. Bytes that do
not decode are an invalid opcode; bytes that are not executable are a page fault. -/
def fetch (s : State) : Result (Instr × BitVec 64) :=
  match decode (s.bytesAt s.rip maxInstrLength) with
  | none => .fault .invalidOpcode
  | some (i, n) =>
    if s.canExec s.rip n then .next (i, BitVec.ofNat 64 n) else .fault .pageFault

end State

/-- One step of the machine with code in memory. -/
def stepMem (sys : Syscall) (s : State) : Outcome :=
  s.fetch >>= fun (i, len) => exec sys i { s with rip := s.rip + len }

/-- Reachability on the machine with code in memory. -/
inductive StepsMem (sys : Syscall) : State → State → Prop
  | refl (s : State) : StepsMem sys s s
  | step {s s' s'' : State} : stepMem sys s = .next s' → StepsMem sys s' s'' → StepsMem sys s s''

/-- Safety on the machine with code in memory: every reachable state takes a
step with an acceptable outcome. -/
def SafeMem (sys : Syscall) (s : State) : Prop :=
  ∀ s', StepsMem sys s s' → (stepMem sys s').isSafe = true

/-- Take up to `n` steps on the machine with code in memory, stopping early
at a fault, at exit, or when stuck. -/
def runMem (sys : Syscall) : Nat → State → Outcome
  | 0, s => .next s
  | n + 1, s =>
    match stepMem sys s with
    | .next s => runMem sys n s
    | o => o

/-! ## A program loaded in memory -/

/-- `Loaded fetch s`: wherever the table has an instruction, memory holds its
encoding in executable bytes, and the table's length is the encoding's length. -/
def Loaded (fetch : Fetch) (s : State) : Prop :=
  ∀ a i len, fetch a = some (i, len) →
    len = BitVec.ofNat 64 i.length ∧
    ∀ k (hk : k < i.length),
      s.mem (a + BitVec.ofNat 64 k) = i.encode[k] ∧ s.perm (a + BitVec.ofNat 64 k) = .rx

/-- A program stays loaded across any change that respects the frame. -/
theorem Loaded.frame {fetch : Fetch} {s s' : State} (h : Loaded fetch s) (hf : Frame s s') :
    Loaded fetch s' := by
  intro a i len ha
  obtain ⟨hlen, hbytes⟩ := h a i len ha
  refine ⟨hlen, fun k hk => ?_⟩
  obtain ⟨hm, hp⟩ := hbytes k hk
  have hne : s.perm (a + BitVec.ofNat 64 k) ≠ .none := by rw [hp]; decide
  refine ⟨?_, by rw [hf.perm _ hne]; exact hp⟩
  rw [hf.mem _ hne (by rw [hp]; rfl)]
  exact hm

/-! ## Instruction lengths -/

theorem rex_length_le (w r x b f : Bool) : (rex w r x b f).length ≤ 1 := by
  unfold rex
  split <;> simp

theorem dispEnc_length_le (b : Reg) (d : BitVec 32) : (dispEnc b d).2.length ≤ 4 := by
  unfold dispEnc
  split
  · simp
  · split <;> simp [imm8, le32]

theorem Mem.encode_length_le (m : Mem) (reg : Nat) : (m.encode reg).bytes.length ≤ 6 := by
  cases m with
  | rip disp => simp [Mem.encode, le32]
  | sib base index disp =>
    cases base with
    | none => cases index <;> simp [Mem.encode, le32]
    | some b =>
      have := dispEnc_length_le b disp
      cases index with
      | none =>
        simp only [Mem.encode]
        split <;> simp <;> omega
      | some is => simp [Mem.encode]; omega

theorem RM.encode_length_le (rm : RM) (reg : Nat) : (rm.encode reg).bytes.length ≤ 6 := by
  cases rm with
  | reg r => simp [RM.encode]
  | mem m => exact m.encode_length_le reg

theorem encodeOp_length_le (w : Bool) (opcode : List Byte) (reg : Nat) (regExt : Bool) (rm : RM)
    (force : Bool) (pre : List Byte) :
    (encodeOp w opcode reg regExt rm force pre).length ≤ pre.length + opcode.length + 7 := by
  have h₁ := rex_length_le w regExt (rm.encode reg).x (rm.encode reg).b force
  have h₂ := rm.encode_length_le reg
  simp only [encodeOp, List.length_append]
  omega

@[simp] theorem le32_length (v : BitVec 32) : (le32 v).length = 4 := rfl

@[simp] theorem le64_length (v : BitVec 64) : (le64 v).length = 8 := rfl

@[simp] theorem imm8_length (v : BitVec 32) : (imm8 v).length = 1 := rfl

/-- Bounds the length of an encoding built from a prefix, an operand and constants. -/
macro "len_bound" : tactic =>
  `(tactic| ((try simp only [List.length_append, List.length_cons, List.length_nil, le32_length,
               le64_length, imm8_length])
             grind [encodeOp_length_le, rex_length_le]))

/-- No instruction is longer than fifteen bytes. -/
theorem Instr.length_le (i : Instr) : i.length ≤ maxInstrLength := by
  unfold Instr.length maxInstrLength
  cases i with
  | alu op w ops => cases ops <;> simp only [Instr.encode] <;> (try split) <;> (try split) <;> len_bound
  | test w dst src => cases src <;> simp only [Instr.encode] <;> (try split) <;> len_bound
  | unary op w dst => cases op <;> simp only [Instr.encode] <;> len_bound
  | shift op w dst c => cases c <;> simp only [Instr.encode] <;> (try split) <;> len_bound
  | mulDiv op w src => simp only [Instr.encode]; len_bound
  | imul2 w dst src => simp only [Instr.encode]; len_bound
  | imul3 w dst src imm => simp only [Instr.encode]; split <;> len_bound
  | popcnt w dst src => simp only [Instr.encode]; len_bound
  | bswap w r => simp only [Instr.encode]; len_bound
  | cdq => decide
  | cqo => decide
  | mov w ops =>
    cases ops with
    | rm_r dst src => simp only [Instr.encode]; len_bound
    | r_m dst src => simp only [Instr.encode]; len_bound
    | rm_i dst imm => cases w <;> cases dst <;> simp only [Instr.encode] <;> len_bound
  | movAbs dst imm => simp only [Instr.encode]; len_bound
  | store8 dst src => simp only [Instr.encode]; len_bound
  | store16 dst src => simp only [Instr.encode]; len_bound
  | movzx w dst sw src => cases sw <;> simp only [Instr.encode] <;> len_bound
  | movsx w dst sw src => cases sw <;> simp only [Instr.encode] <;> len_bound
  | movsxd dst src => simp only [Instr.encode]; len_bound
  | lea w dst addr => simp only [Instr.encode]; len_bound
  | cmov c w dst src => simp only [Instr.encode]; len_bound
  | setcc c dst => simp only [Instr.encode]; len_bound
  | push r => simp only [Instr.encode]; len_bound
  | pop r => simp only [Instr.encode]; len_bound
  | jmp t => cases t <;> simp only [Instr.encode] <;> len_bound
  | jcc c d => simp only [Instr.encode]; len_bound
  | call t => cases t <;> simp only [Instr.encode] <;> len_bound
  | ret => decide
  | nop => decide
  | ud2 => decide
  | syscall => decide

/-! ## The two machines agree -/

/-- If memory from `a` begins with the bytes `l`, reading `n` bytes gives `l`
followed by what comes after it. -/
theorem State.bytesAt_eq {s : State} {a : BitVec 64} {l : List Byte} {n : Nat}
    (hl : ∀ k (hk : k < l.length), s.mem (a + BitVec.ofNat 64 k) = l[k]) (hle : l.length ≤ n) :
    s.bytesAt a n = l ++ s.bytesAt (a + BitVec.ofNat 64 l.length) (n - l.length) := by
  apply List.ext_getElem
  · simp [State.bytesAt]; omega
  · intro j h₁ h₂
    simp only [State.bytesAt, List.getElem_map, List.getElem_range, List.getElem_append]
    split
    · next hj => exact hl j hj
    · next hj =>
      have e : a + BitVec.ofNat 64 l.length + BitVec.ofNat 64 (j - l.length) = a + BitVec.ofNat 64 j := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        congr 2
        omega
      rw [e]

/-- Where the table has an instruction and the program is loaded, fetching
from memory finds the same instruction. -/
theorem Loaded.fetch_eq {fetch : Fetch} {s : State} {i : Instr} {len : BitVec 64}
    (h : Loaded fetch s) (hf : fetch s.rip = some (i, len)) : s.fetch = .next (i, len) := by
  obtain ⟨hlen, hbytes⟩ := h _ _ _ hf
  have hb := State.bytesAt_eq (s := s) (a := s.rip) (l := i.encode) (n := maxInstrLength)
    (fun k hk => (hbytes k hk).1) i.length_le
  have hx : s.canExec s.rip i.length = true := by
    simp only [State.canExec, List.all_eq_true, List.mem_range]
    intro k hk
    rw [(hbytes k hk).2]
    rfl
  simp only [State.fetch, hb, decode_encode, hx, ite_true, hlen]

/-- Where the table has an instruction and the program is loaded, the two
machines take the same step. -/
theorem Loaded.stepMem_eq {fetch : Fetch} {sys : Syscall} {s : State} {i : Instr}
    {len : BitVec 64} (h : Loaded fetch s) (hf : fetch s.rip = some (i, len)) :
    stepMem sys s = step fetch sys s := by
  simp only [stepMem, h.fetch_eq hf, Result.next_bind, step, hf]

/-- A step that is not stuck found an instruction in the table. -/
theorem fetch_of_isSafe {fetch : Fetch} {sys : Syscall} {s : State}
    (h : (step fetch sys s).isSafe = true) : ∃ i len, fetch s.rip = some (i, len) := by
  unfold step at h
  cases hf : fetch s.rip with
  | none => rw [hf] at h; cases h
  | some p => exact ⟨p.1, p.2, rfl⟩

/-- A step changes no permission and no byte that was not writable. -/
theorem step_frame {fetch : Fetch} {sys : Syscall} (hsys : ∀ s, (sys s).All (Frame s))
    {s s' : State} (h : step fetch sys s = .next s') : Frame s s' := by
  unfold step at h
  cases hf : fetch s.rip with
  | none => rw [hf] at h; cases h
  | some p =>
    obtain ⟨i, len⟩ := p
    rw [hf] at h
    have := exec_frame hsys i { s with rip := s.rip + len }
    rw [show exec sys i { s with rip := s.rip + len } = .next s' from h] at this
    exact (Frame.of_eq (s := s) (s' := { s with rip := s.rip + len }) rfl rfl).trans this

/-- On a safe run with the program loaded, every state the memory machine
reaches is one the table machine reaches, and the program is still loaded there. -/
theorem StepsMem.toSteps {fetch : Fetch} {sys : Syscall} (hsys : ∀ s, (sys s).All (Frame s))
    {s s' : State} (h : StepsMem sys s s') (hl : Loaded fetch s) (hs : Safe fetch sys s) :
    Steps fetch sys s s' ∧ Loaded fetch s' := by
  induction h with
  | refl => exact ⟨.refl _, hl⟩
  | step hstep _ ih =>
    obtain ⟨i, len, hf⟩ := fetch_of_isSafe (hs _ (.refl _))
    rw [hl.stepMem_eq hf] at hstep
    obtain ⟨hsteps, hl'⟩ := ih (hl.frame (step_frame hsys hstep)) (hs.step hstep)
    exact ⟨.step hstep hsteps, hl'⟩

/-- **Safety carries over to the machine with code in memory.** If a program
is loaded in executable memory, the operating system does not change code,
and the run is safe by the table, then it is safe when instructions are
fetched by decoding memory. -/
theorem SafeMem.of_safe {fetch : Fetch} {sys : Syscall} {s : State}
    (hsys : ∀ s, (sys s).All (Frame s)) (hl : Loaded fetch s) (hs : Safe fetch sys s) :
    SafeMem sys s := by
  intro s' h
  obtain ⟨hsteps, hl'⟩ := h.toSteps hsys hl hs
  have hsafe := hs s' hsteps
  obtain ⟨i, len, hf⟩ := fetch_of_isSafe hsafe
  rw [hl'.stepMem_eq hf]
  exact hsafe

end TypedAsm
