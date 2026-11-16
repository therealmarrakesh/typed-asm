import TypedAsm
import CatProgram

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
#guard after 0x10000 512 1 [.fail .again] 0x10000 == (-11, mark)
#guard after 0x10000 512 0 [.fail .again] 0x10000 == (512, 1)
#guard after 0x10000 512 5 [.fail .again] 0x10000 == (512, 1)
-- Flags the kernel refuses, with nothing stored.
#guard after 0x10000 512 8 [] 0x10000 == (-22, mark)
#guard after 0x10000 512 6 [] 0x10000 == (-22, mark)
-- A buffer that runs off the end of the page is filled as far as the page goes.
#guard after 0x10f00 512 0 [] 0x10fff == (256, 0)
-- A buffer with no writable byte is a bad address.
#guard after 0x11000 512 0 [] 0x10fff == (-14, mark)
-- Nothing asked for, nothing stored.
#guard after 0x10000 0 0 [] 0x10000 == (0, mark)

/-! ## `write` -/

/-- The same page, holding `0, 1, 2, …`, with a `write` of `count` bytes from
`buf` to standard output about to be made. -/
def writing (buf count : BitVec 64) (fates : List Fate) : State :=
  let s := (State.init.setPerm 0x10000 4096 .rw).storeBytes 0x10000
    ((List.range 4096).map (BitVec.ofNat 8 ·))
  let s := (((s.setReg .rax 1).setReg .rdi 1).setReg .rsi buf).setReg .rdx count
  { s with world := { fates := fates } }

/-- The result of the call, and how many bytes reached the output. -/
def wrote (buf count : BitVec 64) (fates : List Fate) : BitVec 64 × Nat :=
  let t := Linux.write (writing buf count fates)
  (t.getReg .rax, t.world.output.length)

-- Everything.
#guard wrote 0x10000 100 [] == (100, 100)
-- The kernel took seven; the rest is the program's to send again.
#guard wrote 0x10000 100 [.short 7] == (7, 7)
-- It never takes nothing when something was offered.
#guard wrote 0x10000 100 [.short 0] == (100, 100)
-- No room left, or the reader gone: an error, and nothing written.
#guard wrote 0x10000 100 [.fail .nospc] == (-28, 0)
#guard wrote 0x10000 100 [.fail .pipe] == (-32, 0)
-- A buffer that runs off the end of the page is written as far as the page goes.
#guard wrote 0x10fc0 100 [] == (64, 64)
-- One with no readable byte is a bad address.
#guard wrote 0x11000 100 [] == (-14, 0)
-- A descriptor that is not open.
#guard (Linux.write ((writing 0x10000 100 []).setReg .rdi 7)).getReg .rax == -9

/-! ## `read` -/

/-- The marked page, with a `read` of `count` bytes into `buf` from standard
input about to be made, and `input` waiting. -/
def reading (buf count : BitVec 64) (input : List ReadEvent) : State :=
  let s := (State.init.setPerm 0x10000 4096 .rw).storeBytes 0x10000 (List.replicate 4096 mark)
  let s := (((s.setReg .rax 0).setReg .rdi 0).setReg .rsi buf).setReg .rdx count
  { s with world := { input := input } }

def tenBytes : List (BitVec 8) := (List.range 10).map fun i => BitVec.ofNat 8 (i + 1)

/-- The result, the byte at `at_` afterwards, and how many bytes are still
waiting in the first input event. -/
def readOf (buf count : BitVec 64) (input : List ReadEvent) (at_ : BitVec 64) :
    BitVec 64 × BitVec 8 × Nat :=
  let t := Linux.read (reading buf count input)
  (t.getReg .rax, t.mem at_, match t.world.input with | .bytes d :: _ => d.length | _ => 0)

-- Ten bytes waiting, sixteen asked for: ten delivered, the eleventh byte untouched.
#guard readOf 0x10000 16 [.bytes tenBytes] 0x10009 == (10, 10, 0)
#guard readOf 0x10000 16 [.bytes tenBytes] 0x1000a == (10, mark, 0)
-- Four asked for: four delivered and six still waiting.
#guard readOf 0x10000 4 [.bytes tenBytes] 0x10004 == (4, mark, 6)
-- An error the device reports, with nothing stored.
#guard readOf 0x10000 16 [.error .io, .bytes tenBytes] 0x10000 == (-5, mark, 10)
-- Nothing left to read.
#guard readOf 0x10000 16 [] 0x10000 == (0, mark, 0)
-- A buffer with three writable bytes takes three; the rest still waits.
#guard readOf 0x10ffd 16 [.bytes tenBytes] 0x10fff == (3, 3, 7)
-- One with none is a bad address, and nothing is lost.
#guard readOf 0x11000 16 [.bytes tenBytes] 0x10fff == (-14, mark, 10)

/-! ## `openat` -/

/-- A state about to open the file named `f`, which there is, or `g`, which
there is not, with these flags. -/
def opening (name : BitVec 8) (flags : BitVec 64) (fates : List Fate) : State :=
  let s := (State.init.setPerm 0x10000 4096 .rw).storeBytes 0x10000 [name, 0]
  let s := (((s.setReg .rax 257).setReg .rdi 0xffffff9c).setReg .rsi 0x10000).setReg .rdx flags
  { s with world := { fates := fates, files := #[{ path := [0x66] }] } }

def opened (name : BitVec 8) (flags : BitVec 64) (fates : List Fate := []) : BitVec 64 :=
  (Linux.openat (opening name flags fates)).getReg .rax

-- The file there is: the lowest free descriptor.
#guard opened 0x66 0 == 3
-- Asked for as a directory, which it is not.
#guard opened 0x66 0x10000 == -20
-- Opened only to name it: it has a descriptor, which cannot be read.
#guard opened 0x66 0x200000 == 3
#guard (Linux.read (((Linux.openat (opening 0x66 0x200000 [])).setReg .rdi 3).setReg .rdx 1)
  ).getReg .rax == -9
-- The process has too many files open.
#guard opened 0x66 0 [.fail .mfile] == -24
-- An error that is not one an `openat` fails with changes nothing.
#guard opened 0x66 0 [.fail .pipe] == 3
-- No such file; and one to be made as a directory, which cannot be.
#guard opened 0x67 0 == -2
#guard opened 0x67 0x10040 == -22

/-! ## `clock_gettime` -/

/-- A state about to ask clock `c` the time, with the clocks as given. -/
def asking (c : BitVec 64) (time : Nat → Nat → Nat) (hasClock : Nat → Bool := fun _ => false) :
    State :=
  let s := State.init.setPerm 0x10000 4096 .rw
  let s := ((s.setReg .rax 228).setReg .rdi c).setReg .rsi 0x10000
  { s with world := { time := time, hasClock := hasClock } }

/-- The result, and the seconds and nanoseconds stored. -/
def told (t : State) : BitVec 64 × BitVec 64 × BitVec 64 :=
  (t.getReg .rax, t.load64 0x10000, t.load64 0x10008)

/-- Clock 0 reads five seconds and seven nanoseconds, less a nanosecond at
each asking; every other clock moves on ten nanoseconds each time. -/
def clocks : Nat → Nat → Nat := fun c i => if c = 0 then 5000000007 - i else 10

-- Each clock has its own time.
#guard told (Linux.clockGettime (asking 0 clocks)) == (0, 5, 7)
#guard told (Linux.clockGettime (asking 1 clocks)) == (0, 0, 10)
-- A clock that only goes forward has moved on at the second asking.
#guard told (Linux.clockGettime ((Linux.clockGettime (asking 1 clocks)).setReg .rax 228))
  == (0, 0, 20)
-- The time of day may have been set back.
#guard told (Linux.clockGettime ((Linux.clockGettime (asking 0 clocks)).setReg .rax 228))
  == (0, 5, 6)
-- Not a clock.
#guard (Linux.clockGettime (asking 10 clocks)).getReg .rax == -22
#guard (Linux.clockGettime (asking 12 clocks)).getReg .rax == -22
-- The clock of some process, where the world has one.
#guard (Linux.clockGettime (asking 12 clocks (· == 12))).getReg .rax == 0

/-! ## A program under a kernel that does not oblige

Cat opens a file, reads it 64 bytes at a time and writes what it read. The
file here holds `two` and a newline. Its calls, in order, are an `openat`, a
`read`, a `write`, and the `read` that finds the end. It is safe whatever
they answer; what it writes depends on them. -/

def cat (fates : List Fate) : State × Outcome :=
  let s := Cat.startWith ["cat", "b"] Cat.someFiles
  runMemFinal linux 1000 { s with world := { s.world with fates := fates } }

-- Every call obliges.
#guard wroteAndExited "two\n" 0 (cat [])
-- No descriptor to be had: it reports the failure and writes nothing.
#guard wroteAndExited "" 1 (cat [.fail .mfile])
-- The file comes two bytes at a time: it goes round again, and loses nothing.
#guard wroteAndExited "two\n" 0 (cat [.full, .short 2, .full, .short 2])
-- The device fails: it takes that for the end of the file.
#guard wroteAndExited "" 0 (cat [.full, .fail .io])
-- The output takes one byte of four. It does not look, and three are lost.
#guard wroteAndExited "t" 0 (cat [.full, .full, .short 1])
-- The output takes none, for want of room. It does not look at that either.
#guard wroteAndExited "" 0 (cat [.full, .full, .fail .nospc])

/-! ## `close` -/

-- A descriptor is closed even when the call says the device failed.
#guard
  let s := (State.init.setReg .rax 3).setReg .rdi 1
  let t := Linux.close { s with world := { fates := [.fail .io] } }
  t.getReg .rax == -5 && (t.world.fd? 1).isNone

end Tests.Syscalls
