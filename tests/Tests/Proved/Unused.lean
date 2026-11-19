import SumProgram
import TypedAsm.U.Touches

/-!
# A register a program never uses

The program of `examples/Sum` adds up five numbers and exits with the sum.
It has nothing to do with `r15`. That is proved here as any theorem in Lean
is: by induction on the run, from one fact about the machine, proved once
for every program, and one fact about this program's instructions as
written, which Lean decides by looking at them.
-/

open TypedAsm TypedAsm.U

namespace Tests.Proved.Unused

/-- No instruction of the program writes `r15`: read off its instructions. -/
theorem leaves_r15 : ∀ e ∈ Asm.table Sum.base Sum.code, e.2.1.leaves .r15 = true := by
  decide

/-- **However far the program runs, `r15` holds what it held at the start.** -/
theorem never_written {s : State} (h : Steps Sum.fetch linux Sum.start s) :
    s.getReg .r15 = Sum.start.getReg .r15 :=
  run_getReg (fetch_of_table Sum.base Sum.code leaves_r15) (by decide) (by decide) (by decide) h

end Tests.Proved.Unused
