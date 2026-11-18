import TypedAsm.U.Span
import TypedAsm.U.Loader
import TypedAsm.U.Exits
import TypedAsm.U.Writes
import TypedAsm.U.Pages
import TypedAsm.Linux
import TypedAsm.U.Loaded
import TypedAsm.U.Whole
import TypedAsm.U.Order
import TypedAsm.U.Know
import TypedAsm.U.Labels
import TypedAsm.U.Open

/-!
# The checker's tests: steps

One instruction at a time, and a few: what the checker's step says. Each is checked by the kernel as this file is compiled: what the
checker accepts, and what it refuses.
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
    | .step _ _ _ _ (.step _ _ _ _ (.step _ _ _ _ (.stop _ Γ))) => Γ.regs.rbx.linSame (.var 3)
    | _ => false) = true := by decide +kernel

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
    Ok fetch sys Ψ (n + 1) 0 (Γw.den ρ) := by
  have hu : Γw.under 20 = true := by decide +kernel
  have ha : (walk (↑(codeE) : Prog) (fun _ => false) true 10 20 0 Γw).auto = true := by
    decide +kernel
  have hm : (walk (↑(codeE) : Prog) (fun _ => false) true 10 20 0 Γw).moved = true := by
    decide +kernel
  have hh := Walk.holds_of_auto (fetch := fetch) (sys := sys) (Ψ := Ψ) (n := n)
    (walk (↑(codeE) : Prog) (fun _ => false) true 10 20 0 Γw) ρ ha
  have typed := walk_sound (n := n) hD rfl (PreSound.all (fun _ => trivial) _) (pg := ↑(codeE))
    (fun _ => false) hcode (KindsOk.none _) true 10 20 0 Γw ρ hu hh
  exact typed.2 hm

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
    Ok fetch sys Ψ (n + 1) 0 (Γw.den ρ) := by
  have hu : Γw.under 20 = true := by decide +kernel
  have ha : (walk (↑(codeB) : Prog) (fun _ => false) true 10 20 0 Γw).auto = true := by
    decide +kernel
  have hm : (walk (↑(codeB) : Prog) (fun _ => false) true 10 20 0 Γw).moved = true := by
    decide +kernel
  have hh := Walk.holds_of_auto (fetch := fetch) (sys := sys) (Ψ := Ψ) (n := n)
    (walk (↑(codeB) : Prog) (fun _ => false) true 10 20 0 Γw) ρ ha
  have typed := walk_sound (n := n) hD rfl (PreSound.all (fun _ => trivial) _) (pg := ↑(codeB))
    (fun _ => false) hcode (KindsOk.none _) true 10 20 0 Γw ρ hu hh
  exact typed.2 hm

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
    Ok fetch sys Ψ (n + 1) 0 (Γn.den ρ) := by
  have hu : Γn.under 20 = true := by decide +kernel
  have ha : (walk (↑(codeN .e) : Prog) (fun _ => false) true 10 20 0 Γn).auto = true := by
    decide +kernel
  have hm : (walk (↑(codeN .e) : Prog) (fun _ => false) true 10 20 0 Γn).moved = true := by
    decide +kernel
  have hh := Walk.holds_of_auto (fetch := fetch) (sys := sys) (Ψ := Ψ) (n := n)
    (walk (↑(codeN .e) : Prog) (fun _ => false) true 10 20 0 Γn) ρ ha
  have typed := walk_sound (n := n) hD rfl (PreSound.all (fun _ => trivial) _) (pg := ↑(codeN .e))
    (fun _ => false) hcode (KindsOk.none _) true 10 20 0 Γn ρ hu hh
  exact typed.2 hm

-- jumping away when it is not null, the load is of a pointer that is null: refused
example : (walk (codeN .ne) (fun _ => false) true 10 20 0 Γn).auto = false := by decide +kernel

end Tests.Unified
