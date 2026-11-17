import TypedAsm.U.Span
import TypedAsm.U.Loader
import TypedAsm.U.Exits
import TypedAsm.U.Writes
import TypedAsm.U.Pages
import TypedAsm.Linux
import TypedAsm.U.Stack
import TypedAsm.U.Loaded
import TypedAsm.U.Whole
import TypedAsm.U.Order
import TypedAsm.U.Know
import TypedAsm.U.Labels
import TypedAsm.U.Open
import Tests.Typed.Steps

/-!
# The checker's tests: control

Labels, families of contexts, values known to be code, and calls. Each is checked by the kernel as this file is compiled: what the
checker accepts, and what it refuses.
-/

open TypedAsm TypedAsm.U

namespace Tests.Unified

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
    (hcode : ∀ e ∈ codeL, fetch e.1 = some (e.2.1, e.2.2)) (ρ : Env) (fam : Fam) (n : Nat)
    (hρ : ρ.fn = fun _ _ _ => 0) :
    Ok fetch sys Ψ n 0 (Pw.den { ρ with bound := fam :: ρ.bound }) :=
  program_ok hD rfl (PreSound.all (fun _ => trivial) _) (pg := ↑codeL) hcode (KindsOk.none _) StaticsOk.nil
    (LawsHold.nil _) (labels := labelsL) (fuel := 10) (k := 0)
    (by decide +kernel) n (lab 0 Pw) (List.mem_cons_self ..) ρ fam hρ

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
    (hcode : ∀ e ∈ codeF, fetch e.1 = some (e.2.1, e.2.2)) (ρ : Env) (fam : Fam) (n : Nat)
    (hρ : ρ.fn = fun _ _ _ => 0) :
    Ok fetch sys Ψ n 0 (Pw.den { ρ with bound := fam :: ρ.bound }) :=
  program_ok hD rfl (PreSound.all (fun _ => trivial) _) (pg := ↑codeF) hcode (KindsOk.none _) StaticsOk.nil
    (LawsHold.nil _) (labels := [lab 0 Pw]) (fuel := 10) (k := 0)
    (by decide +kernel) n (lab 0 Pw) (List.mem_cons_self ..) ρ fam hρ

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

/-! ## Code wanting one family, known to want another -/

/-- Code wanting these registers, the stack held, nothing else. -/
def codeT (regs : Regs Val) : TyS := .code regs (.bvar 0) [(.bvar 1 16, ⟨64, []⟩)] .nil .none

/-- `rax` is known to be so. -/
def raxIs (τ : TyS) : CtxS := { Pw with known := [(.bvar 0 0, τ)] }

/-- `nop; exit`, with a label at each: what the second asks of `rax` must
follow from what the first knows of it. -/
def codeEnt : List (BitVec 64 × Instr × BitVec 64) :=
  [(0, .nop, 1), (1, .mov .w32 (.rm_i (.reg .rax) 60), 5), (6, .syscall, 2)]

-- code ready whatever `rdi` holds is code ready where `rdi` holds nought
example : checkProgram codeEnt
    [lab 0 (raxIs (codeT anyRegs)), lab 1 (raxIs (codeT (anyRegs.set .rdi (.lit 0))))] 10 0
    = true := by decide +kernel
-- but code that wants nought in `rdi` is not code ready whatever it holds: refused
example : checkProgram codeEnt
    [lab 0 (raxIs (codeT (anyRegs.set .rdi (.lit 0)))), lab 1 (raxIs (codeT anyRegs))] 10 0
    = false := by decide +kernel
-- of a value nothing is known of, nothing follows: refused
example : checkProgram codeEnt [lab 0 Pw, lab 1 (raxIs (codeT anyRegs))] 10 0 = false := by
  decide +kernel

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
    (n : Nat) (hρ : ρ.fn = fun _ _ _ => 0) :
    Ok fetch sys Ψ n 100
      ((fEntry (fExit (.bvar 1 7) (.bvar 1))).den { ρ with bound := fam :: ρ.bound }) :=
  program_ok hD rfl (PreSound.all (fun _ => trivial) _) (pg := ↑(codeCall movRaxRdi)) hcode
    (KindsOk.none _) StaticsOk.nil (LawsHold.nil _)
    (labels := [lab 0 Pw, lab 100 (fEntry (fExit (.bvar 1 7) (.bvar 1)))]) (fuel := 10) (k := 0)
    (by decide +kernel) n _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) ρ fam hρ

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

end Tests.Unified
