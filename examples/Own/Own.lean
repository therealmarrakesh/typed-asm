import OwnProgram
import TypedAsm.Tactic

/-!
# Own: typing and safety

The program is in `OwnProgram.lean`. This file types it and proves it safe.
It is kept separate so that running the program does not link the tactics.
-/

open TypedAsm

namespace Own

/-! ## The typing -/

/-- The contexts allowed at each label: nothing is known about any register,
and nothing is owned. In particular the program may not arrive at `fail`
still holding a page. -/
inductive At : Label → Ctx → Prop
  | start : At .start (entryCtx 0)

asm_typing At

/-! ## The program is well typed -/

theorem blocksOk : BlocksOk Φ fetch linux Ψ := by
  ty_program
  case start =>
    -- the arguments, then the `mmap` for a page to own, at an address called `p`
    ty_mmap_own as p
    -- an error number is negative: the test sends control to `fail`
    · ty_block
    -- a page: `p` is not negative, so the test lets control through; once
    -- its address is in `rbx`, regard the page as two blocks: its first
    -- sixteen bytes, and the rest
    · ty_split .rbx at 16
      -- the stores give the fields their types, in whichever block each
      -- address falls; the loads find them
      -- one block again; giving it back needs nothing said: the context then
      -- owns nothing
      ty_join .rbx
      -- two more pages, at `q`
      ty_mmap_own as q
      · ty_block
      -- a block for each page; give the second back
      · ty_split .rbx at 4096
        ty_munmap
        -- lea rcx, [rip + record]
        ty_step
        -- mov [rbx], rcx: the page's first field is now a pointer to the record
        ty_step
        -- so the page can become an ordinary block with that field
        ty_freeze .rbx
        ty_block

/-! ## Safety -/

asm_safety At.start

end Own

