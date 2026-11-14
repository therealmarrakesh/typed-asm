import TypedAsm.Instr
import TypedAsm.Print
import TypedAsm.Encode
import TypedAsm.Decode
import TypedAsm.Result
import TypedAsm.State
import TypedAsm.Memory
import TypedAsm.Step
import TypedAsm.Safety
import TypedAsm.Types
import TypedAsm.Typing
import TypedAsm.Soundness
import TypedAsm.Fn
import TypedAsm.Program
import TypedAsm.Asm
import TypedAsm.Linux
import TypedAsm.Blocks

/-!
# TypedAsm

Root module of the core library. Submodules go in `core/TypedAsm/` and are imported here.

`TypedAsm.Tactic` is deliberately not imported here. It depends on Lean's
metaprogramming library, which a program that only runs the model should not
have to link. Files that type programs import it themselves.
-/
