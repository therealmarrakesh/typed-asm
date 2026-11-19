import SumProgram
import TypedAsm.U.Touches

/-!
# A register a program never uses

The program of `examples/Sum` adds up five numbers and exits with the sum.
It has nothing to do with `r15`: it never writes it, and nothing it does
turns on what it holds. That is proved here as any theorem in Lean is: by induction on the run, from one fact about the machine, proved once
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

/-- No instruction of the program has anything to do with `r15`: none
computes with it, writes it, or addresses memory by it. -/
theorem ignores_r15 : ∀ e ∈ Asm.table Sum.base Sum.code, e.2.1.ignores .r15 = true := by
  decide

/-- **And nothing the program does turns on what `r15` holds**: started with
any other value there, it runs the same, each state it reaches the same but
for that value in `r15`. -/
theorem never_read (v : BitVec 64) {s : State} (h : Steps Sum.fetch linux Sum.start s) :
    Steps Sum.fetch linux (Sum.start.setReg .r15 v) (s.setReg .r15 v) :=
  run_setReg (fetch_of_table Sum.base Sum.code ignores_r15) (by decide) v h

/-! Both rest on Lean's three standard axioms and nothing else. -/

/--
info: 'Tests.Proved.Unused.never_written' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms never_written

/--
info: 'Tests.Proved.Unused.never_read' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms never_read

end Tests.Proved.Unused
