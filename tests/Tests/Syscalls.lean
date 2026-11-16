import TypedAsm

/-!
# What the modelled system calls answer

Each check runs one call in the model, in a world chosen to make the kernel
answer one particular way, and looks at the result and at memory. The buffer
holds a mark, `0xAA`, in every byte beforehand, so that a byte the call left
alone is told apart from one it stored.
-/

open TypedAsm

namespace Tests.Syscalls

def mark : BitVec 8 := 0xAA

/-- A writable page at `0x10000`, marked throughout, in which a `getrandom`
of `len` bytes into `buf` with these flags is about to be made, the kernel
set to do `fates`. The bytes the kernel supplies are 1, 2, 3, … -/
def before (buf len flags : BitVec 64) (fates : List Fate) : State :=
  let s := (State.init.setPerm 0x10000 4096 .rw).storeBytes 0x10000 (List.replicate 4096 mark)
  let s := ((s.setReg .rdi buf).setReg .rsi len).setReg .rdx flags
  { s with world := { fates := fates, random := fun i => BitVec.ofNat 8 (i + 1) } }

/-- The result of the call, and the byte at `at_` afterwards. -/
def after (buf len flags : BitVec 64) (fates : List Fate) (at_ : BitVec 64) :
    BitVec 64 × BitVec 8 :=
  let t := Linux.getrandom (before buf len flags fates)
  (t.getReg .rax, t.mem at_)

-- Everything asked for: 512 bytes, the last of them stored.
#guard after 0x10000 512 0 [] 0x101ff == (512, 0)
-- Stopped early after 100: the hundredth byte is stored, the next is as it was.
#guard after 0x10000 512 0 [.short 100] 0x10063 == (100, 100)
#guard after 0x10000 512 0 [.short 100] 0x10064 == (100, mark)
-- The decision is used up: the call after it delivers everything.
#guard (Linux.getrandom (Linux.getrandom (before 0x10000 512 0 [.short 100]))).getReg .rax == 512
-- A call for no more than 256 bytes does not stop early, whatever the kernel is set to.
#guard after 0x10000 200 0 [.short 5] 0x100c7 == (200, 200)
-- With `GRND_RANDOM` it may.
#guard after 0x10000 200 2 [.short 5] 0x10005 == (5, mark)
-- "Would have to wait" is an answer only to a call that asked not to wait.
#guard after 0x10000 512 1 [.again] 0x10000 == (-11, mark)
#guard after 0x10000 512 0 [.again] 0x10000 == (512, 1)
#guard after 0x10000 512 5 [.again] 0x10000 == (512, 1)
-- Flags the kernel refuses, with nothing stored.
#guard after 0x10000 512 8 [] 0x10000 == (-22, mark)
#guard after 0x10000 512 6 [] 0x10000 == (-22, mark)
-- A buffer that runs off the end of the page is filled as far as the page goes.
#guard after 0x10f00 512 0 [] 0x10fff == (256, 0)
-- A buffer with no writable byte is a bad address.
#guard after 0x11000 512 0 [] 0x10fff == (-14, mark)
-- Nothing asked for, nothing stored.
#guard after 0x10000 0 0 [] 0x10000 == (0, mark)

end Tests.Syscalls
