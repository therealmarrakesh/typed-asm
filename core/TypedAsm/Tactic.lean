import TypedAsm.Tactic.Program

/-!
# Tactics for typing programs

These build typing derivations; the kernel checks the result, so nothing here
is trusted. They handle the mechanical parts and leave as goals whatever
needs an argument, typically a fact about values at a branch.

* `ty_block` types a whole block of a labelled program, finding jump targets
  by label. `ty_call sig` types a call. These are the usual entry points.
* A theorem marked `@[asm_fact]` is a fact about what the program computes
  that the checker may use where a block leaves a value to be shown the one
  a context asks for; a block that needs nothing else is then typed without
  being written out.
* `ty_steps` types the straight-line instructions at the start of a block.
* `ty_step` types one. `ty_step_with r` types one with a rule you name.
* `ty_branch` types a conditional jump and leaves the side that carries on.
* `ty_straight` types a single instruction, by the checker.
* `ty_name r as v` gives the value in a register a name; `ty_name_slot i as v`
  does the same for a stack slot.
* `ty_stack_detach at d` makes the pieces of the stack from byte `d` up
  blocks the context owns, so that one can be handed to a function: that is
  how a function is handed a local. `ty_stack_attach` makes them pieces of
  the stack again.
* `ty_open r` and `ty_null r` open a pointer to a kind of block and
  split a value that may be null.
* `ty_mmap shape` and `ty_mmap_kind tag` type an `mmap` for fresh memory;
  `ty_err r as e` then splits what it handed back into an error number and
  a pointer.
* `ty_fn_ptr r to sig` turns a register holding a function's address into a
  pointer to that function.
* `ty_code_ptr r to Δ` turns a register holding a label's address into a
  code pointer, for indirect jumps and calls.
* `ty_accept h` shows the current context is accepted at an address, given
  the fact `h` that the code typing allows some context there.
* `ty_into h` types one instruction and ends the block there, handing over
  to the label that follows.
* `ty_mmap_own as p` types an `mmap` whose memory the program then owns, at
  an address called `p`; `ty_munmap` types giving an owned block back;
  `ty_freeze r` turns the owned block whose address is in `r` into an
  ordinary shared block, and `r` into a pointer to it.
* `ty_split r at m` regards the owned block whose address is in `r` as two,
  the first `m` fields and the rest; `ty_join r` regards that block and the
  one that starts where it ends as one.
* `ty_own_first r` lists the owned block whose address is in `r` first, which
  is where a call takes the blocks it hands over from. A system call's
  buffer may be in an owned block, and a signature may take and give blocks
  (`FnSig.takes`, `FnSig.gives`).
* `ty_call sig returning ret` types a call to a function that hands back
  something it made (`FnSigEx`); inside such a function, `ty_return_as x`
  says which of the contexts it returns into.
* `ty_byte as b` types the load of a byte of text and splits on it: zero, or
  some `b` that is not, after which the pointer may be stepped forward.
* `ctx_sub` and `sub_regs` compare contexts.
-/
