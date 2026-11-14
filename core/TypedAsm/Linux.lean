import TypedAsm.Soundness
import TypedAsm.Frame

/-!
# A small model of Linux

The one system call it knows is `exit`. Every other call fails.
-/

namespace TypedAsm

/-- `exit` (number 60) ends the program with the status in `edi`. Every other
system call fails with `-ENOSYS` in `rax`. Like the real kernel, a returning
call overwrites `rcx` and `r11` and leaves the flags unknown. -/
def linux : Syscall := fun s =>
  if s.getReg .rax = 60 then .exit (s.readReg .w32 .rdi)
  else .next { ((s.setReg .rax (-38)).setReg .rcx s.rip).setReg .r11 0 with flags := .unknown }

/-- The Linux model satisfies what the type system assumes of the operating
system, for any program and memory typing. -/
theorem linuxOk (fetch : Fetch) (Ψ : MemTy) : SysOk fetch linux Ψ := by
  intro n Γ s h
  unfold linux
  split
  · exact ⟨rfl, fun s' he => by cases he⟩
  · refine ⟨rfl, fun s' he => ?_⟩
    cases he
    exact ⟨rfl, (((h.setReg (by decide) (HasTy.int _)).setReg (by decide) (HasTy.int _)).setReg
      (by decide) (HasTy.int _)).setFlags (P := Flags.Any) trivial⟩

/-- The Linux model changes no memory and no permission. -/
theorem linux_frame (s : State) : (linux s).All (Frame s) := by
  unfold linux
  split
  · trivial
  · exact Frame.of_eq rfl rfl

end TypedAsm
