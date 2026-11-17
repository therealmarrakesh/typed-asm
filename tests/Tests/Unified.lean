import TypedAsm.U.Upper
import TypedAsm.U.Labels
import TypedAsm.U.Open

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

/-- A program of these instructions, with no kinds of block. -/
abbrev prog (c : List (BitVec 64 × Instr × BitVec 64)) : Prog := { code := c }

/-- No kinds of block. -/
def noKinds : Nat → Option ShapeS := fun _ => none

/-! ## One instruction -/

/-- Registers each holding a name of its own; the stack pointer 32 bytes
into a 64-byte region at the address named 16. -/
def Γ0 : CtxS where
  regs := ⟨.var 0, .var 1, .var 2, .var 3, .add (.var 16) (.lit 32), .var 5, .var 6, .var 7,
    .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .var 15⟩
  flags := .var 0
  held := [(.var 16, ⟨64, []⟩)]

-- push rbx: the stack pointer is 24 bytes in, and the region holds there what rbx holds
example : ((stepHeld noKinds Γ0 20 100 (.push .rbx)).map fun r => r.1.regs.rsp)
    = some (.add (.add (.var 16) (.lit 32)) (.lit (-8))) := by decide +kernel
example : ((stepHeld noKinds Γ0 20 100 (.push .rbx)).map fun r => r.1.held.map fun b => b.2.slots.map (·.1))
    = some [[24]] := by decide +kernel
example : ((stepHeld noKinds Γ0 20 100 (.push .rbx)).map fun r => r.1.held.map fun b => b.2.slots.map (·.2))
    = some [[.var 3]] := by decide +kernel

-- a store outside the region is refused
example : (stepHeld noKinds Γ0 20 100 (.mov .w64 (.rm_r (.mem (.sib (some .rsp) none 64)) .rbx))).isNone
    = true := by decide +kernel

/-- The same registers, with `rdi` known to point at the start of a writable
block of sixteen bytes whose second eight hold a value that may be null. -/
def Γ1 : CtxS := { Γ0 with known := [(.var 7, .ptr (.mk 16 (.cons 8 (.nullable (.atom 0)) .nil)) true 0)] }

-- mov rax, [rdi+8]: rax holds a new name, of which is known what the block says
example : ((stepHeld noKinds Γ1 20 100 (.mov .w64 (.r_m .rax (.sib (some .rdi) none 8)))).map
    fun r => (r.1.regs.rax, r.1.known.head?))
    = some (.var 20, some (.var 20, .nullable (.atom 0))) := by decide +kernel

-- eight bytes past the end of the block: refused
example : (stepHeld noKinds Γ1 20 100 (.mov .w64 (.r_m .rax (.sib (some .rdi) none 16)))).isNone = true := by
  decide +kernel

/-! ## Results read plainly -/

-- `xor eax, eax` and `sub rax, rax`: nought, whatever the register held
example : ((stepHeld noKinds Γ0 20 100 (.alu .xor .w32 (.rm_r (.reg .rax) .rax))).map fun r => r.1.regs.rax)
    = some (.lit 0) := by decide +kernel
example : ((stepHeld noKinds Γ0 20 100 (.alu .sub .w64 (.rm_r (.reg .rax) .rax))).map fun r => r.1.regs.rax)
    = some (.lit 0) := by decide +kernel
-- `xor eax, ebx`: not nought
example : ((stepHeld noKinds Γ0 20 100 (.alu .xor .w32 (.rm_r (.reg .rax) .rbx))).map fun r =>
    r.1.regs.rax == .lit 0) = some false := by decide +kernel
-- `shl rdi, 3`: what `rdi` held, eight times over
example : ((stepHeld noKinds Γ0 20 100 (.shift .shl .w64 (.reg .rdi) (.imm 3))).map fun r => r.1.regs.rdi)
    = some (.shl (.var 7) 3) := by decide +kernel

/-! ## Writing through a pointer -/

/-- Whether a store through `rdi` is typed, `rdi` pointing at the start of
a block of sixteen bytes whose second eight hold a value that may be null. -/
def mayStore (writable : Bool) (i : Instr) : Bool :=
  (stepHeld noKinds { Γ0 with known := [(.var 7, .ptr (.mk 16 (.cons 8 (.nullable (.atom 0)) .nil))
    writable 0)] } 20 100 i).isSome

-- eight plain bytes written: typed
example : mayStore true (.mov .w64 (.rm_r (.mem (.sib (some .rdi) none 0)) .rsi)) = true := by
  decide +kernel
-- through a pointer that may not be written through: refused
example : mayStore false (.mov .w64 (.rm_r (.mem (.sib (some .rdi) none 0)) .rsi)) = false := by
  decide +kernel
-- the typed eight bytes written with a value nothing is known of: refused
example : mayStore true (.mov .w64 (.rm_r (.mem (.sib (some .rdi) none 8)) .rsi)) = false := by
  decide +kernel
-- written with zero, which may be null whatever else: typed
example : mayStore true (.mov .w64 (.rm_i (.mem (.sib (some .rdi) none 8)) 0)) = true := by
  decide +kernel
-- eight bytes written across the start of the typed value: refused
example : mayStore true (.mov .w64 (.rm_r (.mem (.sib (some .rdi) none 4)) .rsi)) = false := by
  decide +kernel
-- past the end of the block: refused
example : mayStore true (.mov .w64 (.rm_r (.mem (.sib (some .rdi) none 16)) .rsi)) = false := by
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
  (walk_sound hD rfl (fun _ => trivial) (pg := ↑codeE) (fun _ => false) hcode (KindsOk.none _) true 10 20 0 Γw ρ (by decide +kernel)
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
  (walk_sound hD rfl (fun _ => trivial) (pg := ↑codeB) (fun _ => false) hcode (KindsOk.none _) true 10 20 0 Γw ρ (by decide +kernel)
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
  (walk_sound hD rfl (fun _ => trivial) (codeN .e) (fun _ => false) hcode (KindsOk.none _) true 10 20 0 Γn ρ (by decide +kernel)
    (Walk.holds_of_auto _ ρ (by decide +kernel))).2 (by decide +kernel)

-- jumping away when it is not null, the load is of a pointer that is null: refused
example : (walk (codeN .ne) (fun _ => false) true 10 20 0 Γn).auto = false := by decide +kernel

/-! ## A program with labels

A label is an address and the family of contexts its code wants, written as
a context whose terms speak of the family's own values. -/

/-- The family of contexts in which the registers hold any values, the
stack pointer is thirty-two bytes into a region of sixty-four that is held,
and nothing else is. -/
def Pw : CtxS where
  regs := ⟨.bvar 0 0, .bvar 0 1, .bvar 0 2, .bvar 0 3, .add (.bvar 0 16) (.lit 32), .bvar 0 5,
    .bvar 0 6, .bvar 0 7, .bvar 0 8, .bvar 0 9, .bvar 0 10, .bvar 0 11, .bvar 0 12, .bvar 0 13,
    .bvar 0 14, .bvar 0 15⟩
  flags := .bvar 0
  held := [(.bvar 0 16, ⟨64, []⟩)]

/-- A label. -/
def lab (a : BitVec 64) (P : CtxS) : Label := ⟨a, P⟩

/-- `start: mov ecx, 5; loop: sub rcx, 1; jne loop; mov eax, 60; syscall`. -/
def codeL : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .mov .w32 (.rm_i (.reg .rcx) 5), 5),
   (5, .alu .sub .w64 (.rm_i (.reg .rcx) 1), 4), (9, .jcc .ne (-6), 2),
   (11, .mov .w32 (.rm_i (.reg .rax) 60), 5), (16, .syscall, 2)]

/-- Both labels ask the same: a stack, and nothing of any register. -/
def labelsL : List Label := [lab 0 Pw, lab 5 Pw]

/-- **The loop is typed at both labels, for any number of steps**: the
walk from `start` stops at `loop`, the walk from `loop` comes back to it or
ends the program, and each context reached is decided to be one the label
asks. The kernel runs the whole check. -/
example (fetch : Fetch) (sys : Syscall) (Ψ : U.MemTy) (hD : Describes sys linuxDesc)
    (hcode : ∀ e ∈ codeL, fetch e.1 = some (e.2.1, e.2.2)) (ρ : Env) (fam : Fam) (n : Nat) :
    Ok fetch sys Ψ n 0 (Pw.den { ρ with bound := fam :: ρ.bound }) :=
  program_ok hD rfl (fun _ => trivial) (pg := ↑codeL) hcode (KindsOk.none _) (labels := labelsL) (fuel := 10) (k := 0)
    (by decide +kernel) n (lab 0 Pw) (List.mem_cons_self ..) ρ fam

/-- A label asking that `rcx` be five is not one the loop comes back to. -/
def labelsBad : List Label :=
  [lab 0 Pw, lab 5 { Pw with regs := Pw.regs.set .rcx (.lit 5) }]

example : checkProgram codeL labelsBad 10 0 = false := by decide +kernel

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
    (hcode : ∀ e ∈ codeF, fetch e.1 = some (e.2.1, e.2.2)) (ρ : Env) (fam : Fam) (n : Nat) :
    Ok fetch sys Ψ n 0 (Pw.den { ρ with bound := fam :: ρ.bound }) :=
  program_ok hD rfl (fun _ => trivial) (pg := ↑codeF) hcode (KindsOk.none _) (labels := [lab 0 Pw]) (fuel := 10) (k := 0)
    (by decide +kernel) n (lab 0 Pw) (List.mem_cons_self ..) ρ fam

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
  checkProgram codeJ [lab 0 Pw, lab 5 ({ Pw with held := h })] 10 0

-- the same region
example : mayHold [(.bvar 0 16, ⟨64, []⟩)] = true := by decide +kernel
-- nothing: refused. A context says all that is held; memory does not cease
-- to be held by a label leaving it out
example : mayHold [] = false := by decide +kernel
-- the region as two that lie end to end
example : mayHold [(.bvar 0 16, ⟨32, []⟩), (.add (.bvar 0 16) (.lit 32), ⟨32, []⟩)] = true := by
  decide +kernel
-- one part of it alone, the rest left out: refused
example : mayHold [(.add (.bvar 0 16) (.lit 8), ⟨16, []⟩)] = false := by decide +kernel
-- two parts with bytes between them left out: refused
example : mayHold [(.bvar 0 16, ⟨24, []⟩), (.add (.bvar 0 16) (.lit 32), ⟨32, []⟩)] = false := by
  decide +kernel
-- two parts that overlap: refused
example : mayHold [(.bvar 0 16, ⟨40, []⟩), (.add (.bvar 0 16) (.lit 32), ⟨32, []⟩)] = false := by
  decide +kernel
-- a part that runs past the end of the region: refused
example : mayHold [(.add (.bvar 0 16) (.lit 32), ⟨40, []⟩)] = false := by decide +kernel
-- a region somewhere else: refused
example : mayHold [(.bvar 0 15, ⟨8, []⟩)] = false := by decide +kernel
-- the region, with a name for the value in eight of its bytes, of which
-- the context reached says nothing: whatever is there is given the name
example : mayHold [(.bvar 0 16, ⟨64, [(24, .bvar 0 17)]⟩)] = true := by decide +kernel
-- the region said to hold there what `rdi` holds, which nothing shows: refused
example : mayHold [(.bvar 0 16, ⟨64, [(24, .bvar 0 7)]⟩)] = false := by decide +kernel
-- a value said to lie across the end of the region: refused
example : mayHold [(.bvar 0 16, ⟨64, [(60, .bvar 0 17)]⟩)] = false := by decide +kernel

-- from two regions that lie end to end, with a value in each, the label may
-- ask for the one region they make, the values where they then are
example : checkProgram codeJ
    [lab 0 { Pw with held := [(.add (.bvar 0 16) (.lit 32), ⟨32, [(0, .bvar 0 18)]⟩),
                            (.bvar 0 16, ⟨32, [(8, .bvar 0 17)]⟩)] },
     lab 5 { Pw with held := [(.bvar 0 16, ⟨64, [(8, .bvar 0 17), (32, .bvar 0 18)]⟩)] }] 10 0 = true := by
  decide +kernel
-- but not for one region where they do not meet
example : checkProgram codeJ
    [lab 0 { Pw with held := [(.add (.bvar 0 16) (.lit 40), ⟨24, []⟩), (.bvar 0 16, ⟨32, []⟩)] },
     lab 5 { Pw with held := [(.bvar 0 16, ⟨64, []⟩)] }] 10 0 = false := by
  decide +kernel

-- with a name for whatever else is held: the label keeps it, and may not
-- leave it out; and a label that names a rest is typed for any rest, so it
-- may be reached holding none
example : checkProgram codeJ [lab 0 { Pw with rest := .bvar 0 }, lab 5 ({ Pw with rest := .bvar 0 })]
    10 0 = true := by decide +kernel
example : checkProgram codeJ [lab 0 { Pw with rest := .bvar 0 }, lab 5 (Pw)] 10 0 = false := by
  decide +kernel
example : checkProgram codeJ [lab 0 Pw, lab 5 ({ Pw with rest := .bvar 0 })] 10 0 = true := by
  decide +kernel

-- the frame loop again: the label may say the slot holds what `rdi` holds,
-- which the body puts there, and may not say it holds what `rsi` holds
example : checkProgram codeF [lab 0 { Pw with held := [(.bvar 0 16, ⟨64, [(16, .bvar 0 7)]⟩)] }] 10 0
    = true := by decide +kernel
example : checkProgram codeF [lab 0 { Pw with held := [(.bvar 0 16, ⟨64, [(16, .bvar 0 6)]⟩)] }] 10 0
    = false := by decide +kernel

/-- `start: mov ecx, <n>; there: jmp there`, the label `there` asking that
`rcx` may be null and is otherwise a pointer. -/
def checkZ (n : BitVec 32) : Bool :=
  checkProgram (prog [(0, .mov .w32 (.rm_i (.reg .rcx) n), 5), (5, .jmp (.rel (-5)), 5)])
    [lab 0 Pw, lab 5 { Pw with known := [(.bvar 0 1, .nullable (.ptr (.mk 16 .nil) true 0))] }] 10 0

-- zero may be null, whatever else is known; one may not
example : checkZ 0 = true := by decide +kernel
example : checkZ 1 = false := by decide +kernel

/-! ## Code wanting a family of contexts, inside another

A value known to be code wanting contexts in which `rax` holds a value of
the family the knowledge sits in, one out from its own. -/

/-- Code wanting `rax` to hold the first value of the family one out, and
any flags of its own. -/
def innerCode : TyS := .code (Γw.regs.set .rax (.bvar 1 0)) (.bvar 0) [] .nil .none

-- it speaks of an enclosing family, so it is not knowledge that stands alone,
-- and is knowledge that may sit inside one family
example : innerCode.closedAt 0 = false := by decide +kernel
example : innerCode.closedAt 1 = true := by decide +kernel

-- the enclosing family taken at a particular value: the inner code now wants
-- `rax` to hold that value, and its own flags are still its own
example : innerCode.open { b := fun _ => .var 7, f := .var 0 } 0
    = .code (Γw.regs.set .rax (.var 7)) (.bvar 0) [] .nil .none := by decide +kernel

-- its own family's value is untouched when the enclosing one is taken
example : (TyS.code (Γw.regs.set .rax (.bvar 0 0)) (.bvar 0) [] .nil .none).open
      { b := fun _ => .var 7, f := .var 0 } 0
    = .code (Γw.regs.set .rax (.bvar 0 0)) (.bvar 0) [] .nil .none := by decide +kernel

/-! ## Going to a value known to be code -/

/-- Registers each holding a value of the family's own. -/
def anyRegs : Regs Val :=
  ⟨.bvar 0 0, .bvar 0 1, .bvar 0 2, .bvar 0 3, .bvar 0 4, .bvar 0 5, .bvar 0 6, .bvar 0 7,
    .bvar 0 8, .bvar 0 9, .bvar 0 10, .bvar 0 11, .bvar 0 12, .bvar 0 13, .bvar 0 14, .bvar 0 15⟩

/-- Whether `jmp rax` is typed where `rax` is known to be code wanting
these registers and regions, the label's family holding the stack of `Pw`.
The code's family is one further in: its own values are the nearest, and
the label's are one out. -/
def mayJump (regs : Regs Val) (held : List (Val × HeldS)) : Bool :=
  checkProgram (prog [(0, .jmp (.ind (.reg .rax)), 2)])
    [lab 0 { Pw with known := [(.bvar 0 0, .code regs (.bvar 0) held .nil .none)] }] 10 0

-- code wanting any registers and the stack: the jump is typed
example : mayJump anyRegs [(.bvar 1 16, ⟨64, []⟩)] = true := by decide +kernel
-- code wanting `rdi` to be zero, which nothing shows: refused
example : mayJump (anyRegs.set .rdi (.lit 0)) [(.bvar 1 16, ⟨64, []⟩)] = false := by decide +kernel
-- code wanting `rdi` and `rsi` to hold one value, which nothing shows they
-- do: refused, whichever of the two the family's value is written for
example : mayJump (anyRegs.set .rdi (.bvar 0 6)) [(.bvar 1 16, ⟨64, []⟩)] = false := by
  decide +kernel
example : mayJump (anyRegs.set .rsi (.bvar 0 7)) [(.bvar 1 16, ⟨64, []⟩)] = false := by
  decide +kernel
-- code that would hold nothing: refused, the stack would be left out
example : mayJump anyRegs [] = false := by decide +kernel

/-- `ret`, the stack holding at its top a return address known to be code
wanting the stack pointer eight bytes on and the stack held. -/
def mayReturn (rsp' : Val) : Bool :=
  checkProgram (prog [(0, .ret, 1)])
    [lab 0 { Pw with
              held := [(.bvar 0 16, ⟨64, [(32, .bvar 0 17)]⟩)]
              known := [(.bvar 0 17, .code (anyRegs.set .rsp rsp') (.bvar 0)
                          [(.bvar 1 16, ⟨64, []⟩)] .nil .none)] }] 10 0

-- the return address wants the stack pointer just past it: typed
example : mayReturn (.add (.bvar 1 16) (.lit 40)) = true := by decide +kernel
-- it wants the stack pointer where it was before the return: refused
example : mayReturn (.add (.bvar 1 16) (.lit 32)) = false := by decide +kernel

/-! ## A function called

A function is code wanting its entry family: the registers as its caller
has them, eight bytes of stack with the return address in them, and
whatever else its caller holds. Of the return address the entry knows that
it is code wanting what the function returns with: here, `rax` holding what
`rdi` held, every other register as it was, the stack pointer past the
return address, the eight bytes held, and whatever else was held, held. -/

/-- What `f` returns with, written one family in from its entry: `own` the
registers that are as they were at entry, `rest` what else is held. -/
def fExit (rax : Val) (rest : RestS) : TyS :=
  .code ⟨rax, .bvar 1 1, .bvar 1 2, .bvar 1 3, .add (.bvar 1 4) (.lit 8), .bvar 1 5, .bvar 1 6,
      .bvar 1 7, .bvar 1 8, .bvar 1 9, .bvar 1 10, .bvar 1 11, .bvar 1 12, .bvar 1 13, .bvar 1 14,
      .bvar 1 15⟩
    (.bvar 0) [(.bvar 1 4, ⟨8, []⟩)] .nil rest

/-- The entry family of `f`, its return address known to be code wanting
the given exit. -/
def fEntry (exit : TyS) : CtxS where
  regs := anyRegs
  flags := .bvar 0
  held := [(.bvar 0 4, ⟨8, [(0, .bvar 0 16)]⟩)]
  known := [(.bvar 0 16, exit)]
  rest := .bvar 0

/-- `start: call f; mov eax, 60; syscall` and `f:` two instructions. -/
def codeCall (body : Instr) : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .call (.rel 95), 5), (5, .mov .w32 (.rm_i (.reg .rax) 60), 5), (10, .syscall, 2),
   (100, body, 3), (103, .ret, 1)]

/-- Whether the program is typed with `f` of the given body and exit. -/
def callOk (body : Instr) (exit : TyS) (caller : CtxS) : Bool :=
  checkProgram (codeCall body) [lab 0 caller, lab 100 (fEntry exit)] 10 0

/-- `mov rax, rdi`. -/
def movRaxRdi : Instr := .mov .w64 (.rm_r (.reg .rax) .rdi)

-- `f` returns what it was given and keeps every other register; the caller
-- calls it and ends the program: typed, the function and its caller both
example : callOk movRaxRdi (fExit (.bvar 1 7) (.bvar 1)) Pw = true := by decide +kernel

/-- **And so typed at both labels for every member of their families**:
what the kernel checked, as a theorem of the machine. -/
example (fetch : Fetch) (sys : Syscall) (Ψ : U.MemTy) (hD : Describes sys linuxDesc)
    (hcode : ∀ e ∈ codeCall movRaxRdi, fetch e.1 = some (e.2.1, e.2.2)) (ρ : Env) (fam : Fam)
    (n : Nat) :
    Ok fetch sys Ψ n 100
      ((fEntry (fExit (.bvar 1 7) (.bvar 1))).den { ρ with bound := fam :: ρ.bound }) :=
  program_ok hD rfl (fun _ => trivial) (pg := ↑(codeCall movRaxRdi)) hcode (KindsOk.none _)
    (labels := [lab 0 Pw, lab 100 (fEntry (fExit (.bvar 1 7) (.bvar 1)))]) (fuel := 10) (k := 0)
    (by decide +kernel) n _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) ρ fam

-- a body that changes `rbx`, which the exit says is as it was: refused
example : callOk (.mov .w64 (.rm_r (.reg .rbx) .rdi)) (fExit (.bvar 1 7) (.bvar 1)) Pw = false := by
  decide +kernel
-- an exit that says `rax` holds what `rsi` held, which the body does not do: refused
example : callOk movRaxRdi (fExit (.bvar 1 6) (.bvar 1)) Pw = false := by decide +kernel
-- an exit that leaves out what else the caller held: refused. The function
-- would return holding its caller's memory with nothing said of it
example : callOk movRaxRdi (fExit (.bvar 1 7) .none) Pw = false := by decide +kernel
-- a caller with no room below its stack pointer for the return address: refused
example : callOk movRaxRdi (fExit (.bvar 1 7) (.bvar 1))
    { Pw with regs := Pw.regs.set .rsp (.add (.bvar 0 16) (.lit 4)) } = false := by decide +kernel

/-! ## Ranges, and ways that cannot be taken -/

/-- `cmp rdi, 5; jb out; cmp rdi, 3; jb nowhere; out: mov eax, 60; syscall`:
the second jump goes where there is no code, and can never be taken. -/
def codeR : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .alu .cmp .w64 (.rm_i (.reg .rdi) 5), 4), (4, .jcc .b 6, 2),
   (6, .alu .cmp .w64 (.rm_i (.reg .rdi) 3), 4), (10, .jcc .b 188, 2),
   (12, .mov .w32 (.rm_i (.reg .rax) 60), 5), (17, .syscall, 2)]

-- past the first jump `rdi` is at least five; taking the second would make it
-- less than three: that way is seen to be impossible, and nothing is asked of it
example : checkProgram codeR [lab 0 Pw] 10 0 = true := by decide +kernel
-- entered past the first comparison, the second jump may be taken, to nowhere: refused
example : checkProgram codeR [lab 6 Pw] 10 0 = false := by decide +kernel

/-- The same at 32 bits: `mov edi, edi; cmp edi, 5; jb out; cmp edi, 3;
jb nowhere; out: exit`. The move leaves `rdi` below two to the thirty-second,
so what the 32-bit comparisons say of its low half they say of it. -/
def codeR32 : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .mov .w32 (.rm_r (.reg .rdi) .rdi), 2),
   (2, .alu .cmp .w32 (.rm_i (.reg .rdi) 5), 3), (5, .jcc .b 5, 2),
   (7, .alu .cmp .w32 (.rm_i (.reg .rdi) 3), 3), (10, .jcc .b 188, 2),
   (12, .mov .w32 (.rm_i (.reg .rax) 60), 5), (17, .syscall, 2)]

-- the second jump is seen to be impossible, as at 64 bits
example : checkProgram codeR32 [lab 0 Pw] 10 0 = true := by decide +kernel
-- entered past the move, nothing says `rdi` fits in 32 bits, so the comparisons
-- of its low half say nothing of it: the second jump may be taken. Refused
example : checkProgram codeR32 [lab 2 Pw] 10 0 = false := by decide +kernel
-- the range an operator's result lies in is read off the operator
example : (Val.un (.trunc .w32) (.var 3)).bound = ⟨0, 0xffffffff⟩ := by decide +kernel
example : (Val.un .low8 (.var 3)).bound = ⟨0, 0xff⟩ := by decide +kernel
example : (Val.fop (.condByte .e) (.var 0) (.lit 0) (.lit 0)).bound = ⟨0, 1⟩ := by decide +kernel

/-! ## Narrow reads -/

-- a byte read and widened is the byte read: the term says by its head that it
-- is a byte, and widening a byte does nothing
example : ((stepHeld noKinds { Γ0 with known := [(.var 7, .ptr (.mk 16 .nil) false 0)] } 20 100
      (.movzx .w32 .rax .w8 (.mem (.sib (some .rdi) none 3)))).map fun r => r.1.regs.rax)
    = some (.un .low8 (.var 20)) := by decide +kernel
-- and its range is read off it
example : (Val.un .low8 (.var 20)).bound = ⟨0, 0xff⟩ := by decide +kernel

/-! ## Pointers by kind -/

/-- A list node: sixteen bytes, the first eight nought or a pointer to
another node. The kind is number 7. -/
def node : ShapeS := .mk 16 (.cons 0 (.nullable (.ref 7 false 0)) .nil)

def kinds7 : Nat → Option ShapeS := fun t => if t = 7 then some node else none

/-- `rdi` is nought or points to a node. -/
def Pl : CtxS := { Pw with known := [(.bvar 0 7, .nullable (.ref 7 false 0))] }

/-- `loop: test rdi, rdi; je out; mov rdi, [rdi]; jmp loop; out: exit`: a
walk down a list to its end. -/
def codeList : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .test .w64 (.reg .rdi) (.reg .rdi), 3), (3, .jcc .e 8, 2),
   (5, .mov .w64 (.r_m .rdi (.sib (some .rdi) none 0)), 3), (8, .jmp (.rel (-13)), 5),
   (13, .mov .w32 (.rm_i (.reg .rax) 60), 5), (18, .syscall, 2)]

-- past the test `rdi` is not nought, so it points to a node; what is read
-- there is nought or points to a node again: the label's context, round the loop
example : checkProgram { code := codeList, kinds := kinds7 } [lab 0 Pl] 10 0 = true := by
  decide +kernel
-- the same program, the kind's shape not said: nothing is known to be at the pointer. Refused
example : checkProgram { code := codeList } [lab 0 Pl] 10 0 = false := by decide +kernel
-- entered at the load, `rdi` may be nought: refused
example : checkProgram { code := codeList, kinds := kinds7 } [lab 0 Pl, lab 5 Pl] 10 0 = false := by
  decide +kernel

/-! ## A call that stores bytes in a block others may point into -/

/-- `mov eax, 0; mov edx, 8; syscall; exit`: read eight bytes to where `rsi`
points. -/
def codeRdS : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .mov .w32 (.rm_i (.reg .rax) 0), 5), (5, .mov .w32 (.rm_i (.reg .rdx) 8), 5),
   (10, .syscall, 2), (12, .mov .w32 (.rm_i (.reg .rax) 60), 5), (17, .syscall, 2)]

/-- `rsi` points four bytes into a block of the given shape. -/
def buf (Sh : ShapeS) (w : Bool) : CtxS := { Pw with known := [(.bvar 0 6, .ptr Sh w 4)] }

-- sixteen plain bytes that may be written: the eight from the fourth lie in them
example : checkProgram codeRdS [lab 0 (buf (.mk 16 .nil) true)] 10 0 = true := by decide +kernel
-- through a pointer that may not be written through: refused
example : checkProgram codeRdS [lab 0 (buf (.mk 16 .nil) false)] 10 0 = false := by
  decide +kernel
-- over bytes that hold a pointer: refused, the block would no longer hold one
example : checkProgram codeRdS
    [lab 0 (buf (.mk 16 (.cons 8 (.ptr (.mk 8 .nil) false 0) .nil)) true)] 10 0 = false := by
  decide +kernel
-- past the end of the block: refused
example : checkProgram codeRdS [lab 0 (buf (.mk 8 .nil) true)] 10 0 = false := by decide +kernel
-- to an address nothing is known of: refused
example : checkProgram codeRdS [lab 0 Pw] 10 0 = false := by decide +kernel

/-! ## How large a value may be -/

/-- `rcx` is known to be at most nine. -/
def Γix : CtxS := { Γ0 with known := [(.var 1, .range 0 9)] }

-- an index scaled by eight is at most seventy-two; with twenty-four added, ninety-six
example : Γix.upper (.shl (.var 1) 3) = some 72 := by decide +kernel
example : Γix.upper (.add (.shl (.var 1) 3) (.lit 24)) = some 96 := by decide +kernel
-- a byte is at most 255, by its operator
example : Γix.upper (.un .low8 (.var 2)) = some 255 := by decide +kernel
-- of a value nothing is known of, the most a value can be
example : Γix.upper (.var 2) = some (2 ^ 64 - 1) := by decide +kernel
-- a range that wraps says nothing of how large
example : ({ Γ0 with known := [(.var 1, .range (-4) 9)] } : CtxS).upper (.var 1)
    = some (2 ^ 64 - 1) := by decide +kernel

/-! ## An index with a bound -/

/-- `rbx` points to a table of eight values. -/
def Pt : CtxS := { Pw with known := [(.bvar 0 3, .ptr (.mk 64 .nil) false 0)] }

/-- `cmp rcx, <bound>; jae out; mov rax, [rbx + rcx*8]; out: exit`. -/
def codeIx (bound : BitVec 32) : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .alu .cmp .w64 (.rm_i (.reg .rcx) bound), 4), (4, .jcc .ae 4, 2),
   (6, .mov .w64 (.r_m .rax (.sib (some .rbx) (some (.rcx, .s8)) 0)), 4),
   (10, .mov .w32 (.rm_i (.reg .rax) 60), 5), (15, .syscall, 2)]

-- past the comparison the index is below eight, so the eight bytes read lie in the table
example : checkProgram (codeIx 8) [lab 0 Pt] 10 0 = true := by decide +kernel
-- an index that may be eight: the read may be past the end. Refused
example : checkProgram (codeIx 9) [lab 0 Pt] 10 0 = false := by decide +kernel
-- entered past the comparison, the index may be anything: refused
example : checkProgram (codeIx 8) [lab 0 Pt, lab 6 Pt] 10 0 = false := by decide +kernel

/-- `cmp rcx, <bound>; jae out; mov [rsp + rcx*8], rdi; out: exit`: a store
into the stack at an index. -/
def codeSt (bound : BitVec 32) : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .alu .cmp .w64 (.rm_i (.reg .rcx) bound), 4), (4, .jcc .ae 4, 2),
   (6, .mov .w64 (.rm_r (.mem (.sib (some .rsp) (some (.rcx, .s8)) 0)) .rdi), 4),
   (10, .mov .w32 (.rm_i (.reg .rax) 60), 5), (15, .syscall, 2)]

-- thirty-two bytes are held above the stack pointer: four slots
example : checkProgram (codeSt 4) [lab 0 Pw] 10 0 = true := by decide +kernel
-- a fifth would be past what is held: refused
example : checkProgram (codeSt 5) [lab 0 Pw] 10 0 = false := by decide +kernel

/-! ## Text -/

/-- `rdi` points to text. -/
def Ps : CtxS := { Pw with known := [(.bvar 0 7, .str (.lit 0))] }

/-- `loop: movzx eax, byte [rdi]; test eax, eax; je out; add rdi, <step>;
add rcx, 1; jmp loop; out: exit`: the length of a text, counted in `rcx`. -/
def codeLen (step : BitVec 32) : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .movzx .w32 .rax .w8 (.mem (.sib (some .rdi) none 0)), 3),
   (3, .test .w32 (.reg .rax) (.reg .rax), 2), (5, .jcc .e 13, 2),
   (7, .alu .add .w64 (.rm_i (.reg .rdi) step), 4), (11, .alu .add .w64 (.rm_i (.reg .rcx) 1), 4),
   (15, .jmp (.rel (-20)), 5),
   (20, .mov .w32 (.rm_i (.reg .rax) 60), 5), (25, .syscall, 2)]

-- the byte read is not nought past the test, so there is more text, and the
-- address one on points to text: the label's context again, round the loop
example : checkProgram (codeLen 1) [lab 0 Ps] 12 0 = true := by decide +kernel
-- two bytes at a time: the second may be past the end. Refused
example : checkProgram (codeLen 2) [lab 0 Ps] 12 0 = false := by decide +kernel
-- entered past the test, the byte is not known not to be nought: refused
example : checkProgram (codeLen 1) [lab 0 Ps, lab 7 Ps] 12 0 = false := by decide +kernel
-- through a value not known to point to text: refused
example : checkProgram (codeLen 1) [lab 0 Pw] 12 0 = false := by decide +kernel

/-! ## Divides -/

/-- `test rcx, rcx; je out; xor edx, edx; div rcx; out: exit`: the divisor is
known not to be nought, and the high half is nought, so the divide does not
fault. -/
def codeD : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .test .w64 (.reg .rcx) (.reg .rcx), 3), (3, .jcc .e 5, 2),
   (5, .alu .xor .w32 (.rm_r (.reg .rdx) .rdx), 2), (7, .mulDiv .div .w64 (.reg .rcx), 3),
   (10, .mov .w32 (.rm_i (.reg .rax) 60), 5), (15, .syscall, 2)]

example : checkProgram codeD [lab 0 Pw] 10 0 = true := by decide +kernel
-- entered past the test, the divisor may be nought: refused
example : checkProgram codeD [lab 5 Pw] 10 0 = false := by decide +kernel
-- entered past the clearing of the high half, the quotient may not fit: refused
example : checkProgram codeD [lab 0 Pw, lab 7 Pw] 10 0 = false := by decide +kernel

/-- `cmp rcx, 1; jl out; cqo; idiv rcx; out: exit`: the divisor is at least
one, and the high half is the sign of the low, so the signed divide does not
fault. -/
def codeI : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .alu .cmp .w64 (.rm_i (.reg .rcx) 1), 4), (4, .jcc .l 5, 2),
   (6, .cqo, 2), (8, .mulDiv .idiv .w64 (.reg .rcx), 3),
   (11, .mov .w32 (.rm_i (.reg .rax) 60), 5), (16, .syscall, 2)]

example : checkProgram codeI [lab 0 Pw] 10 0 = true := by decide +kernel
-- entered past the comparison, the divisor may be nought or minus one: refused
example : checkProgram codeI [lab 6 Pw] 10 0 = false := by decide +kernel
-- without the sign carried into the high half: refused
example : checkProgram codeI [lab 0 Pw, lab 8 Pw] 10 0 = false := by decide +kernel

/-- `shr rdi, 1; jne on; cmp rdi, 1; jae nowhere; on: exit`: after the
shift, not taking `jne` means the result is zero, so it is not at least one. -/
def codeS : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .shift .shr .w64 (.reg .rdi) (.imm 1), 4), (4, .jcc .ne 6, 2),
   (6, .alu .cmp .w64 (.rm_i (.reg .rdi) 1), 4), (10, .jcc .ae 188, 2),
   (12, .mov .w32 (.rm_i (.reg .rax) 60), 5), (17, .syscall, 2)]

-- a shift leaves the zero flag that of its result: the jump after the
-- comparison is seen to be impossible
example : checkProgram codeS [lab 0 Pw] 10 0 = true := by decide +kernel

/-- `popcnt rax, rdi; jne on; cmp rdi, 1; jae nowhere; on: exit`: not taking
`jne` means `rdi` was zero. -/
def codeP : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .popcnt .w64 .rax (.reg .rdi), 5), (5, .jcc .ne 6, 2),
   (7, .alu .cmp .w64 (.rm_i (.reg .rdi) 1), 4), (11, .jcc .ae 187, 2),
   (13, .mov .w32 (.rm_i (.reg .rax) 60), 5), (18, .syscall, 2)]

example : checkProgram codeP [lab 0 Pw] 10 0 = true := by decide +kernel

/-- `cmp rdi, rsi; adc rax, 0; je out; out: exit`: the comparison leaves the
carry defined, so the addition with carry does not fault and leaves the
flags defined, so the jump is decided. And a widening multiply, which never
faults. -/
def codeA : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .alu .cmp .w64 (.rm_r (.reg .rdi) .rsi), 3), (3, .alu .adc .w64 (.rm_i (.reg .rax) 0), 4),
   (7, .jcc .e 3, 2), (9, .mulDiv .mul .w64 (.reg .rsi), 3),
   (12, .mov .w32 (.rm_i (.reg .rax) 60), 5), (17, .syscall, 2)]

example : checkProgram codeA [lab 0 Pw] 10 0 = true := by decide +kernel
-- entered at the addition with carry, the carry is not known to be defined: refused
example : checkProgram codeA [lab 3 Pw] 10 0 = false := by decide +kernel

/-! ## Memory mapped, used and given back

`mmap` hands back an error number or the address of fresh memory; `munmap`
hands back zero, or an error number with the memory held still. The
program's own tests of what is handed back tell the cases apart. -/

/-- `top: mmap(0, 4096); if error goto out; store rdi there;` then `tail`;
`out: exit`. -/
def codeM (tail : List (BitVec 64 × Instr × BitVec 64)) : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .mov .w32 (.rm_i (.reg .rax) 9), 5), (5, .mov .w32 (.rm_i (.reg .rdi) 0), 5),
   (10, .mov .w32 (.rm_i (.reg .rsi) 4096), 5), (15, .syscall, 2),
   (17, .alu .cmp .w64 (.rm_i (.reg .rax) (-4095)), 6), (23, .jcc .ae 75, 2),
   (25, .mov .w64 (.rm_r (.mem (.sib (some .rax) none 0)) .rdi), 3)] ++ tail ++
  [(100, .mov .w32 (.rm_i (.reg .rax) 60), 5), (105, .syscall, 2)]

/-- `munmap(rax, 4096)`. -/
def unmapIt : List (BitVec 64 × Instr × BitVec 64) :=
  [(28, .mov .w64 (.rm_r (.reg .rdi) .rax), 3), (31, .mov .w32 (.rm_i (.reg .rax) 11), 5),
   (36, .syscall, 2)]

-- mapped, used, given back, and the program ends: typed
example : checkProgram (codeM (unmapIt ++ [(38, .jmp (.rel 57), 5)])) [lab 0 Pw] 20 0 = true := by
  decide +kernel
-- mapped, used, and the program ends holding it: typed. A program may end
-- holding memory
example : checkProgram (codeM [(28, .jmp (.rel 67), 5)]) [lab 0 Pw] 20 0 = true := by
  decide +kernel
-- mapped, used, and round again without giving it back: refused. The label
-- at the top holds no such memory
example : checkProgram (codeM [(28, .jmp (.rel (-33)), 5)]) [lab 0 Pw] 20 0 = false := by
  decide +kernel
-- given back, and round again without asking whether it was: refused. If
-- `munmap` refused, the memory is held still
example : checkProgram (codeM (unmapIt ++ [(38, .jmp (.rel (-43)), 5)])) [lab 0 Pw] 20 0
    = false := by decide +kernel
-- given back, the result tested, and round again only if it was: typed
example : checkProgram (codeM (unmapIt ++
    [(38, .test .w64 (.reg .rax) (.reg .rax), 3), (41, .jcc .ne 57, 2),
     (43, .jmp (.rel (-48)), 5)])) [lab 0 Pw] 20 0 = true := by decide +kernel
-- the store made without asking whether memory was handed back: refused
example : checkProgram
    (prog [(0, .mov .w32 (.rm_i (.reg .rax) 9), 5), (5, .mov .w32 (.rm_i (.reg .rdi) 0), 5),
      (10, .mov .w32 (.rm_i (.reg .rsi) 4096), 5), (15, .syscall, 2),
      (17, .mov .w64 (.rm_r (.mem (.sib (some .rax) none 0)) .rdi), 3),
      (20, .mov .w32 (.rm_i (.reg .rax) 60), 5), (25, .syscall, 2)])
    [lab 0 Pw] 20 0 = false := by decide +kernel

/-! ## A call that stores bytes -/

/-- `mov [rsp], rdi; read(0, rsp, <count>); exit`: the buffer is the stack
from the stack pointer on, of which `Pw`'s family holds thirty-two bytes. -/
def codeRd (count : BitVec 32) : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .mov .w64 (.rm_r (.mem (.sib (some .rsp) none 0)) .rdi), 4),
   (4, .mov .w32 (.rm_i (.reg .rax) 0), 5), (9, .mov .w32 (.rm_i (.reg .rdi) 0), 5),
   (14, .mov .w64 (.rm_r (.reg .rsi) .rsp), 3), (17, .mov .w32 (.rm_i (.reg .rdx) count), 5),
   (22, .syscall, 2), (24, .mov .w32 (.rm_i (.reg .rax) 60), 5), (29, .syscall, 2)]

-- thirty-two bytes read into the thirty-two held above the stack pointer: typed
example : checkProgram (codeRd 32) [lab 0 Pw] 20 0 = true := by decide +kernel
-- thirty-three, one past the end of what is held: refused
example : checkProgram (codeRd 33) [lab 0 Pw] 20 0 = false := by decide +kernel

/-- The same, the program then going round to a label that says the stack
still holds at its thirty-second byte what `rdi` held: which the call may
have written over. -/
def afterRead (keeps : Bool) : Bool :=
  checkProgram
    (prog [(0, .mov .w64 (.rm_r (.mem (.sib (some .rsp) none 0)) .rdi), 4),
     (4, .mov .w32 (.rm_i (.reg .rax) 0), 5), (9, .mov .w64 (.rm_r (.reg .rsi) .rsp), 3),
     (12, .mov .w32 (.rm_i (.reg .rdx) 8), 5), (17, .syscall, 2), (19, .jmp (.rel 76), 5),
     (100, .jmp (.rel (-5)), 5)])
    [lab 0 Pw,
     lab 100 { Pw with
       regs := anyRegs.set .rsp (.add (.bvar 0 16) (.lit 32))
       held := [(.bvar 0 16, ⟨64, if keeps then [(32, .bvar 0 7)] else []⟩)] }] 20 0

-- what the bytes held is no longer known after the call: a label saying it is, refused
example : afterRead true = false := by decide +kernel
example : afterRead false = true := by decide +kernel

end Tests.Unified
