import TypedAsm.U.Labels

/-!
# What the checker on the one model answers

Each check gives the checker's step one instruction in one context, or its
walk a few, and looks at what it says: the term a register holds afterwards,
what a region holds, what is known of a value, or that it has no answer.
They are checked by the kernel as this file is compiled. `var n` is a value
the context says nothing more of.
-/

open TypedAsm TypedAsm.U

namespace Tests.Unified

/-! ## One instruction -/

/-- Registers each holding a name of its own; the stack pointer 32 bytes
into a 64-byte region at the address named 16. -/
def Γ0 : CtxS where
  regs := ⟨.var 0, .var 1, .var 2, .var 3, .add (.var 16) (.lit 32), .var 5, .var 6, .var 7,
    .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .var 15⟩
  flags := .var 0
  held := [(.var 16, ⟨64, []⟩)]

-- push rbx: the stack pointer is 24 bytes in, and the region holds there what rbx holds
example : ((stepHeld Γ0 20 100 (.push .rbx)).map fun r => r.1.regs.rsp)
    = some (.add (.add (.var 16) (.lit 32)) (.lit (-8))) := by decide +kernel
example : ((stepHeld Γ0 20 100 (.push .rbx)).map fun r => r.1.held.map fun b => b.2.slots.map (·.1))
    = some [[24]] := by decide +kernel
example : ((stepHeld Γ0 20 100 (.push .rbx)).map fun r => r.1.held.map fun b => b.2.slots.map (·.2))
    = some [[.var 3]] := by decide +kernel

-- a store outside the region is refused
example : (stepHeld Γ0 20 100 (.mov .w64 (.rm_r (.mem (.sib (some .rsp) none 64)) .rbx))).isNone
    = true := by decide +kernel

/-- The same registers, with `rdi` known to point at the start of a writable
block of sixteen bytes whose second eight hold a value that may be null. -/
def Γ1 : CtxS := { Γ0 with known := [(.var 7, .ptr (.mk 16 (.cons 8 (.nullable (.atom 0)) .nil)) true 0)] }

-- mov rax, [rdi+8]: rax holds a new name, of which is known what the block says
example : ((stepHeld Γ1 20 100 (.mov .w64 (.r_m .rax (.sib (some .rdi) none 8)))).map
    fun r => (r.1.regs.rax, r.1.known.head?))
    = some (.var 20, some (.var 20, .nullable (.atom 0))) := by decide +kernel

-- eight bytes past the end of the block: refused
example : (stepHeld Γ1 20 100 (.mov .w64 (.r_m .rax (.sib (some .rdi) none 16)))).isNone = true := by
  decide +kernel

/-! ## A few instructions -/

def Γw : CtxS where
  regs := ⟨.var 0, .var 1, .var 2, .var 3, .add (.var 16) (.lit 32), .var 5, .var 6, .var 7,
    .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .var 15⟩
  flags := .var 0
  held := [(.var 16, ⟨64, []⟩)]

/-- push rbx; mov rbx, rdi; pop rbx; then something not in the list. -/
def codeW : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .push .rbx, 1), (1, .mov .w64 (.rm_r (.reg .rbx) .rdi), 3), (4, .pop .rbx, 1)]

-- three instructions are stepped over, and the walk stops at address 5
example : (match walk codeW (fun _ => false) true 10 20 0 Γw with
    | .step _ _ _ _ (.step _ _ _ _ (.step _ _ _ _ (.stop a _))) => a
    | _ => 99) = 5 := by decide +kernel

-- after push, mov, pop: rbx holds what it held (the value pushed is the value popped)
example : (match walk codeW (fun _ => false) true 10 20 0 Γw with
    | .step _ _ _ _ (.step _ _ _ _ (.step _ _ _ _ (.stop _ Γ))) => Γ.regs.rbx.summands
    | _ => ([], 0)) = (match walk codeW (fun _ => false) true 10 20 0 Γw with
    | .step _ _ _ _ (.step _ _ _ _ (.step _ _ _ _ (.stop _ Γ))) =>
        ((Γ.held.head?.map fun b => b.2.slots.map (·.2)).getD []).head?.map (·.summands) |>.getD ([], 0)
    | _ => ([], 1)) := by decide +kernel

/-! ## A whole program -/

/-- `mov eax, 60; mov edi, 0; syscall`: a program that ends at once. -/
def codeE : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .mov .w32 (.rm_i (.reg .rax) 60), 5), (5, .mov .w32 (.rm_i (.reg .rdi) 0), 5),
   (10, .syscall, 2)]

-- the walk steps over the two moves and sees that the call ends the program
example : (match walk codeE (fun _ => false) true 10 20 0 Γw with
    | .step _ _ _ _ (.step _ _ _ _ .ends) => true
    | _ => false) = true := by decide +kernel

/-- **The program is typed, and so safe to enter**, on any machine that
fetches those instructions at those addresses, under any system that does
what Linux is described to do: by the walk alone, which the kernel runs. -/
example (fetch : Fetch) (sys : Syscall) (Ψ : U.MemTy) (hD : Describes sys linuxDesc)
    (hcode : ∀ e ∈ codeE, fetch e.1 = some (e.2.1, e.2.2)) (ρ : Env) (n : Nat) :
    Ok fetch sys Ψ (n + 1) 0 (Γw.den ρ) :=
  (walk_sound hD rfl (fun _ => trivial) codeE (fun _ => false) hcode true 10 20 0 Γw ρ (by decide +kernel)
    (Walk.holds_of_auto _ ρ (by decide +kernel))).2 (by decide +kernel)

/-- `test rdi, rdi; je there; mov eax, 60; syscall; there: mov eax, 231;
syscall`: a branch on a comparison, each
way ending the program. -/
def codeB : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .test .w64 (.reg .rdi) (.reg .rdi), 3), (3, .jcc .e 7, 2),
   (5, .mov .w32 (.rm_i (.reg .rax) 60), 5), (10, .syscall, 2),
   (12, .mov .w32 (.rm_i (.reg .rax) 231), 5), (17, .syscall, 2)]

/-- **Typed by the walk alone**: the comparison leaves the zero flag
defined, so the jump is decided, and both ways end the program. -/
example (fetch : Fetch) (sys : Syscall) (Ψ : U.MemTy) (hD : Describes sys linuxDesc)
    (hcode : ∀ e ∈ codeB, fetch e.1 = some (e.2.1, e.2.2)) (ρ : Env) (n : Nat) :
    Ok fetch sys Ψ (n + 1) 0 (Γw.den ρ) :=
  (walk_sound hD rfl (fun _ => trivial) codeB (fun _ => false) hcode true 10 20 0 Γw ρ (by decide +kernel)
    (Walk.holds_of_auto _ ρ (by decide +kernel))).2 (by decide +kernel)

-- with no comparison before it, the jump is not decided, and nothing is concluded
example : (walk (codeB.drop 1) (fun _ => false) true 10 20 3 Γw).auto = false := by decide +kernel

/-! ## What a branch teaches -/

/-- `rdi` may be null, and otherwise points at a block of sixteen bytes. -/
def Γn : CtxS :=
  { Γw with known := [(.var 7, .nullable (.ptr (.mk 16 (.cons 8 .any .nil)) true 0))] }

/-- `test rdi, rdi; j<c> out; mov rax, [rdi+8]; mov eax, 60; syscall;
out: mov eax, 231; syscall`. -/
def codeN (c : Cond) : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .test .w64 (.reg .rdi) (.reg .rdi), 3), (3, .jcc c 11, 2),
   (5, .mov .w64 (.r_m .rax (.sib (some .rdi) none 8)), 4),
   (9, .mov .w32 (.rm_i (.reg .rax) 60), 5), (14, .syscall, 2),
   (16, .mov .w32 (.rm_i (.reg .rax) 231), 5), (21, .syscall, 2)]

/-- **Jumping away when the pointer is null, the load is typed**: past the
jump the pointer is known not to be null, by the walk alone. -/
example (fetch : Fetch) (sys : Syscall) (Ψ : U.MemTy) (hD : Describes sys linuxDesc)
    (hcode : ∀ e ∈ codeN .e, fetch e.1 = some (e.2.1, e.2.2)) (ρ : Env) (n : Nat) :
    Ok fetch sys Ψ (n + 1) 0 (Γn.den ρ) :=
  (walk_sound hD rfl (fun _ => trivial) (codeN .e) (fun _ => false) hcode true 10 20 0 Γn ρ (by decide +kernel)
    (Walk.holds_of_auto _ ρ (by decide +kernel))).2 (by decide +kernel)

-- jumping away when it is not null, the load is of a pointer that is null: refused
example : (walk (codeN .ne) (fun _ => false) true 10 20 0 Γn).auto = false := by decide +kernel

/-! ## A program with labels -/

/-- `start: mov ecx, 5; loop: sub rcx, 1; jne loop; mov eax, 60; syscall`. -/
def codeL : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .mov .w32 (.rm_i (.reg .rcx) 5), 5),
   (5, .alu .sub .w64 (.rm_i (.reg .rcx) 1), 4), (9, .jcc .ne (-6), 2),
   (11, .mov .w32 (.rm_i (.reg .rax) 60), 5), (16, .syscall, 2)]

/-- Both labels ask the same: a stack, and nothing of any register. -/
def labelsL : List (BitVec 64 × CtxS) := [(0, Γw), (5, Γw)]

/-- **The loop is typed at both labels, for any number of steps**: the
walk from `start` stops at `loop`, the walk from `loop` comes back to it or
ends the program, and each context reached is decided to be one the label
asks. The kernel runs the whole check. -/
example (fetch : Fetch) (sys : Syscall) (Ψ : U.MemTy) (hD : Describes sys linuxDesc)
    (hcode : ∀ e ∈ codeL, fetch e.1 = some (e.2.1, e.2.2)) (ρ : Env) (n : Nat) :
    Ok fetch sys Ψ n 0 (Γw.den ρ) :=
  program_ok hD rfl (fun _ => trivial) hcode (labels := labelsL) (fuel := 10) (k := 20)
    (by decide +kernel) n (0, Γw) (List.mem_cons_self ..) ρ

/-- A label asking that `rcx` be five is not one the loop comes back to. -/
def labelsBad : List (BitVec 64 × CtxS) :=
  [(0, Γw), (5, { Γw with regs := Γw.regs.set .rcx (.lit 5) })]

example : checkProgram codeL labelsBad 10 20 = false := by decide +kernel

/-! ## Arithmetic on the stack pointer -/

/-- `sub rsp, 16; mov [rsp], rdi; mov rax, [rsp]; add rsp, 16; jmp 0`: a
frame made, used and given back, and then round again. -/
def codeF : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .alu .sub .w64 (.rm_i (.reg .rsp) 16), 4),
   (4, .mov .w64 (.rm_r (.mem (.sib (some .rsp) none 0)) .rdi), 4),
   (8, .mov .w64 (.r_m .rax (.sib (some .rsp) none 0)), 4),
   (12, .alu .add .w64 (.rm_i (.reg .rsp) 16), 4), (16, .jmp (.rel (-21)), 5)]

/-- **Typed as a loop on one label**: the stack pointer is back where it
was, as the sums show, so the context reached is the label's again. -/
example (fetch : Fetch) (sys : Syscall) (Ψ : U.MemTy) (hD : Describes sys linuxDesc)
    (hcode : ∀ e ∈ codeF, fetch e.1 = some (e.2.1, e.2.2)) (ρ : Env) (n : Nat) :
    Ok fetch sys Ψ n 0 (Γw.den ρ) :=
  program_ok hD rfl (fun _ => trivial) hcode (labels := [(0, Γw)]) (fuel := 10) (k := 20)
    (by decide +kernel) n (0, Γw) (List.mem_cons_self ..) ρ

/-! ## What one context being regarded as another comes to

Each consequence of the one statement, and each thing it does not allow,
at a label reached from a context that holds one stack region of sixty-four
bytes and says nothing of what is in it. The same bytes must be held after
as before: in any order and any division, never fewer. -/

/-- `start: jmp there; there: jmp there`. -/
def codeJ : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .jmp (.rel 0), 5), (5, .jmp (.rel (-5)), 5)]

/-- Whether the label `there` may ask to hold these regions. -/
def mayHold (h : List (Val × HeldS)) : Bool :=
  checkProgram codeJ [(0, Γw), (5, { Γw with held := h })] 10 20

-- the same region
example : mayHold [(.var 16, ⟨64, []⟩)] = true := by decide +kernel
-- nothing: refused. A context says all that is held; memory does not cease
-- to be held by a label leaving it out
example : mayHold [] = false := by decide +kernel
-- the region as two that lie end to end
example : mayHold [(.var 16, ⟨32, []⟩), (.add (.var 16) (.lit 32), ⟨32, []⟩)] = true := by
  decide +kernel
-- one part of it alone, the rest left out: refused
example : mayHold [(.add (.var 16) (.lit 8), ⟨16, []⟩)] = false := by decide +kernel
-- two parts with bytes between them left out: refused
example : mayHold [(.var 16, ⟨24, []⟩), (.add (.var 16) (.lit 32), ⟨32, []⟩)] = false := by
  decide +kernel
-- two parts that overlap: refused
example : mayHold [(.var 16, ⟨40, []⟩), (.add (.var 16) (.lit 32), ⟨32, []⟩)] = false := by
  decide +kernel
-- a part that runs past the end of the region: refused
example : mayHold [(.add (.var 16) (.lit 32), ⟨40, []⟩)] = false := by decide +kernel
-- a region somewhere else: refused
example : mayHold [(.var 15, ⟨8, []⟩)] = false := by decide +kernel
-- the region, with a name for the value in eight of its bytes, of which
-- the context reached says nothing: whatever is there is given the name
example : mayHold [(.var 16, ⟨64, [(24, .var 17)]⟩)] = true := by decide +kernel
-- the region said to hold there what `rdi` holds, which nothing shows: refused
example : mayHold [(.var 16, ⟨64, [(24, .var 7)]⟩)] = false := by decide +kernel
-- a value said to lie across the end of the region: refused
example : mayHold [(.var 16, ⟨64, [(60, .var 17)]⟩)] = false := by decide +kernel

-- from two regions that lie end to end, with a value in each, the label may
-- ask for the one region they make, the values where they then are
example : checkProgram codeJ
    [(0, { Γw with held := [(.add (.var 16) (.lit 32), ⟨32, [(0, .var 18)]⟩),
                            (.var 16, ⟨32, [(8, .var 17)]⟩)] }),
     (5, { Γw with held := [(.var 16, ⟨64, [(8, .var 17), (32, .var 18)]⟩)] })] 10 20 = true := by
  decide +kernel
-- but not for one region where they do not meet
example : checkProgram codeJ
    [(0, { Γw with held := [(.add (.var 16) (.lit 40), ⟨24, []⟩), (.var 16, ⟨32, []⟩)] }),
     (5, { Γw with held := [(.var 16, ⟨64, []⟩)] })] 10 20 = false := by
  decide +kernel

-- with a name for whatever else is held: the label keeps it, and may not
-- leave it out; and a label that names a rest is typed for any rest, so it
-- may be reached holding none
example : checkProgram codeJ [(0, { Γw with rest := some 0 }), (5, { Γw with rest := some 0 })]
    10 20 = true := by decide +kernel
example : checkProgram codeJ [(0, { Γw with rest := some 0 }), (5, Γw)] 10 20 = false := by
  decide +kernel
example : checkProgram codeJ [(0, Γw), (5, { Γw with rest := some 0 })] 10 20 = true := by
  decide +kernel

-- the frame loop again: the label may say the slot holds what `rdi` holds,
-- which the body puts there, and may not say it holds what `rsi` holds
example : checkProgram codeF [(0, { Γw with held := [(.var 16, ⟨64, [(16, .var 7)]⟩)] })] 10 20
    = true := by decide +kernel
example : checkProgram codeF [(0, { Γw with held := [(.var 16, ⟨64, [(16, .var 6)]⟩)] })] 10 20
    = false := by decide +kernel

/-- `start: mov ecx, <n>; there: jmp there`, the label `there` asking that
`rcx` may be null and is otherwise a pointer. -/
def checkZ (n : BitVec 32) : Bool :=
  checkProgram [(0, .mov .w32 (.rm_i (.reg .rcx) n), 5), (5, .jmp (.rel (-5)), 5)]
    [(0, Γw), (5, { Γw with known := [(.var 1, .nullable (.ptr (.mk 16 .nil) true 0))] })] 10 20

-- zero may be null, whatever else is known; one may not
example : checkZ 0 = true := by decide +kernel
example : checkZ 1 = false := by decide +kernel

end Tests.Unified
