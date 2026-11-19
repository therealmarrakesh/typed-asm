import TypedAsm.Ranges
import TypedAsm.Frame

/-!
# A small model of Linux

The system calls a program can be typed to make: `exit` and `exit_group`,
`read`, `write`, `openat`, `close`, `lseek`, `fstat`, `mmap`, `munmap`,
`clock_gettime` and `getrandom`. Every other call number is modelled as
failing with `-ENOSYS`, but that is not what the real kernel does with them,
so the type system has no rule for them: a `syscall` is typed only when the
number in `rax` is exactly known and is one of these.

What the types rely on is the same for every one of them, and is true of
the real kernel whatever the arguments: the call returns to the next
instruction (or ends the program), memory that was accessible is changed
only inside a buffer the call was handed, and `rax`, `rcx`, `r11` and the
flags hold values nothing is known about. No typing rests on what a call
*answers*.

What a call answers is the outside world's business. Where the kernel has a
choice, the world makes it: how many bytes a call hands over, whether it
fails and with what, which bytes and what time it supplies, where memory
goes. So what is proved of a program for every world is proved for every
answer the model can give, and the model is made to give every answer Linux
may: a count short of what was asked, an error no argument explains, a
buffer filled only as far as it can be written. What a program may conclude
from a result is stated for each call that stores or sends bytes:
`read_stored`, `getrandom_stored`, `writeBy_stdout`.

What the model leaves out, none of which touches the above:

* Signals. A process of the model has no handlers, having no way to install
  one, so no call is interrupted with `EINTR`. A signal that ends or stops
  the process does so from outside and is no answer to a call; a `write` to
  a pipe whose reader has gone is answered with `EPIPE`, as it is when that
  signal is ignored.
* There are no directories. A file is found by its whole name, spelled
  exactly as in `World.files`, and a relative name needs `AT_FDCWD`.
* `openat` understands the access mode and `O_CREAT`, `O_EXCL`, `O_TRUNC`,
  `O_APPEND`, `O_DIRECTORY` and `O_PATH`; other flags are ignored.
  Permissions are two switches per file, not owners and modes.
* The standard streams are pipes unless the world says otherwise
  (`World.fds`): as pipes they cannot be sought, and `fstat` describes them
  so. A world in which descriptor 0 is a file is a program started with its
  input redirected from one. `fstat` fills in the kind, the size and the block
  counts; every field the model does not track is zero.
* Each clock has its own time, which the world supplies. The clocks that
  only go forward never go back; nothing relates one clock to another.
* `mmap` is modelled in one form only: fresh, private, zeroed memory that
  can be read and written (`PROT_READ|PROT_WRITE`,
  `MAP_PRIVATE|MAP_ANONYMOUS`), at an address the kernel chooses. Any other
  form is modelled as failing, which is not what the kernel does, so the
  type system types the call only in that form: this is the one call whose
  answer the types do rely on. Where the memory goes is the outside world's
  choice (`World.place`); all that is assumed of it is what the kernel
  guarantees: whole pages that were not accessible before.
* `munmap` gives back only memory that is writable; see `Linux.munmap`.
-/

namespace TypedAsm

namespace Linux

/-- The state a call returns in, with result `v`. Like the real kernel, a
returning call overwrites `rcx` and `r11` and leaves the flags unknown:
`rcx` holds the address the call returns to, and `r11` the flags the
processor saved when the call was made, which is no number the program can
count on: the world says what it is, anew at each call. -/
def ret (s : State) (v : BitVec 64) : State :=
  { ((s.setReg .rax v).setReg .rcx s.rip).setReg .r11 (s.world.saved 0) with
    flags := .unknown
    world := s.world.spent }

/-- The state a call returns in after storing `data` at `buf`, with result
`v` and the world as `w`. -/
def give (s : State) (buf : BitVec 64) (data : List (BitVec 8)) (v : BitVec 64) (w : World) :
    State :=
  ret { s.storeBytes buf data with world := w } v

/-- The file descriptor in a register. The kernel takes an `int`, which is
the low half of the register. -/
def fdArg (s : State) (r : Reg) : Nat :=
  ((s.getReg r).setWidth 32).toNat

/-- Counting up from `i`, the first of the next `fuel` bytes at `a` whose
permission does not satisfy `p`, or `i + fuel` if all do. -/
def runFrom (s : State) (p : Perm → Bool) (a : BitVec 64) : Nat → Nat → Nat
  | i, 0 => i
  | i, fuel + 1 =>
    if p (s.perm (a + BitVec.ofNat 64 i)) then runFrom s p a (i + 1) fuel else i

/-- How many of the `n` bytes at `a` can be written before one that cannot:
as far as the kernel gets when it copies into a buffer. -/
def writableRun (s : State) (a : BitVec 64) (n : Nat) : Nat :=
  runFrom s Perm.writable a 0 n

/-- How many of the `n` bytes at `a` can be read before one that cannot: as
far as the kernel gets when it copies out of a buffer. -/
def readableRun (s : State) (a : BitVec 64) (n : Nat) : Nat :=
  runFrom s Perm.readable a 0 n

theorem runFrom_spec (s : State) (p : Perm → Bool) (a : BitVec 64) : ∀ fuel i,
    i ≤ runFrom s p a i fuel ∧ runFrom s p a i fuel ≤ i + fuel ∧
    (∀ j, i ≤ j → j < runFrom s p a i fuel → p (s.perm (a + BitVec.ofNat 64 j)) = true) ∧
    (runFrom s p a i fuel < i + fuel →
      p (s.perm (a + BitVec.ofNat 64 (runFrom s p a i fuel))) = false)
  | 0, i => ⟨Nat.le_refl _, Nat.le_refl _, fun j h1 h2 => absurd h2 (by simp only [runFrom]; omega),
      fun h => absurd h (by simp only [runFrom]; omega)⟩
  | fuel + 1, i => by
    by_cases hw : p (s.perm (a + BitVec.ofNat 64 i)) = true
    · obtain ⟨h1, h2, h3, h4⟩ := runFrom_spec s p a fuel (i + 1)
      simp only [runFrom, hw, ↓reduceIte]
      refine ⟨by omega, by omega, fun j hj hlt => ?_, fun h => h4 (by omega)⟩
      by_cases hji : j = i
      · rw [hji]; exact hw
      · exact h3 j (by omega) hlt
    · simp only [runFrom, hw, Bool.false_eq_true, ↓reduceIte]
      exact ⟨Nat.le_refl _, by omega, fun j h1 h2 => absurd h2 (by omega),
        fun _ => trivial⟩

theorem writableRun_le (s : State) (a : BitVec 64) (n : Nat) : writableRun s a n ≤ n := by
  have := (runFrom_spec s Perm.writable a n 0).2.1
  simpa [writableRun] using this

theorem canWrite_writableRun (s : State) (a : BitVec 64) (n : Nat) :
    s.canWrite a (writableRun s a n) = true := by
  rw [State.canWrite_iff]
  exact fun i hi => (runFrom_spec s Perm.writable a n 0).2.2.1 i (Nat.zero_le _) hi

theorem canRead_readableRun (s : State) (a : BitVec 64) (n : Nat) :
    s.canRead a (readableRun s a n) = true := by
  rw [State.canRead_iff]
  exact fun i hi => (runFrom_spec s Perm.readable a n 0).2.2.1 i (Nat.zero_le _) hi

theorem readableRun_le (s : State) (a : BitVec 64) (n : Nat) : readableRun s a n ≤ n := by
  have := (runFrom_spec s Perm.readable a n 0).2.1
  simpa [readableRun] using this

/-- How many bytes a call hands over when it sets out to hand over `most`
and the kernel does `d` with it: all of them, or fewer if the kernel stops
early, but never none. -/
def taken (d : Fate) (most : Nat) : Nat :=
  match d with
  | .short k => if 0 < k then min k most else most
  | _ => most

theorem taken_le (d : Fate) (most : Nat) : taken d most ≤ most := by
  unfold taken
  split
  · split
    · exact Nat.min_le_right _ _
    · exact Nat.le_refl _
  · exact Nat.le_refl _

/-- A call that hands something over hands over at least one byte. -/
theorem taken_pos (d : Fate) {most : Nat} (h : 0 < most) : 0 < taken d most := by
  unfold taken
  split
  · split <;> omega
  · exact h

/-- `write(fd, buf, count)` when the kernel does `d` with it: append bytes
from `buf` to the output, or store them in a file at the descriptor's
position. The kernel takes as many bytes as it can read, up to its limit on
one call, or fewer if it stops early, and the result is how many: a program
that wants everything written must go round again. Or it fails, with
nothing written. -/
def writeBy (d : Fate) (s : State) : State :=
  let fd := fdArg s .rdi
  let buf := s.getReg .rsi
  let count := (s.getReg .rdx).toNat
  let most := readableRun s buf (min count 0x7ffff000)
  let n := taken d most
  match s.world.fd? fd with
  | some .stdout =>
    if 0 < count ∧ most = 0 then ret s (-14)
    else match d with
      | .fail e =>
        if e.ofWrite then ret s e.code
        else
          ret { s with world := { s.world with writes := s.loadBytes buf n :: s.world.writes } }
            (BitVec.ofNat 64 n)
      | _ =>
        ret { s with world := { s.world with writes := s.loadBytes buf n :: s.world.writes } }
          (BitVec.ofNat 64 n)
  | some (.file i pos r w app) =>
    if !w then ret s (-9)
    else if 0 < count ∧ most = 0 then ret s (-14)
    else
      match s.world.files[i]? with
      | none => ret s (-9)
      | some f =>
        let start := if app then f.size else pos
        match d with
        | .fail e =>
          if e.ofWrite then ret s e.code
          else
            ret { s with
                world := { s.world.setFd fd (.file i (start + n) r w app) with
                  files := s.world.files.setIfInBounds i (f.write start (s.loadBytes buf n)) } }
              (BitVec.ofNat 64 n)
        | _ =>
          ret { s with
              world := { s.world.setFd fd (.file i (start + n) r w app) with
                files := s.world.files.setIfInBounds i (f.write start (s.loadBytes buf n)) } }
            (BitVec.ofNat 64 n)
  | _ => ret s (-9)

/-- The kernel's decision for the call being made, and the state with that
decision used up. -/
def nextFate (s : State) : Fate × State :=
  (s.world.fates.head?.getD .full, { s with world := { s.world with fates := s.world.fates.tail } })

/-- `write(fd, buf, count)`, with the kernel doing what the world says. -/
def write (s : State) : State :=
  writeBy (nextFate s).1 (nextFate s).2

/-- `read(fd, buf, count)` when the kernel does `d` with it. The kernel
stores as far into the buffer as it can write, `room` bytes, and no further.
From the program's input: take the next input event; bytes are stored at
`buf`, at most `room` of them, and what does not fit stays for the next
call; with no input left the call returns 0. From a file: the bytes at the
descriptor's position, up to the end of the file, or fewer if the kernel
stops early; or the device fails, and nothing is stored. -/
def readBy (d : Fate) (s : State) : State :=
  let fd := fdArg s .rdi
  let buf := s.getReg .rsi
  let count := (s.getReg .rdx).toNat
  let room := writableRun s buf (min count 0x7ffff000)
  match s.world.fd? fd with
  | some .stdin =>
    if 0 < count ∧ room = 0 then ret s (-14)
    else
      match s.world.input with
      | [] => ret s 0
      | .error e :: rest => ret { s with world := { s.world with input := rest } } e.code
      | .bytes data :: rest =>
        let chunk := data.take room
        let left := data.drop room
        give s buf chunk (BitVec.ofNat 64 chunk.length)
          { s.world with input := if left.isEmpty then rest else .bytes left :: rest }
  | some (.file i pos r w app) =>
    if !r then ret s (-9)
    else if 0 < count ∧ room = 0 then ret s (-14)
    else
      match s.world.files[i]? with
      | none => ret s (-9)
      | some f =>
        match d with
        | .fail .io => ret s (-5)
        | _ =>
          let data := (f.read pos (taken d room)).take room
          give s buf data (BitVec.ofNat 64 data.length)
            (s.world.setFd fd (.file i (pos + data.length) r w app))
  | _ => ret s (-9)

/-- `read(fd, buf, count)`, with the kernel doing what the world says. A
read of the program's input has its answer in `World.input` and uses up no
decision. -/
def read (s : State) : State :=
  match s.world.fd? (fdArg s .rdi) with
  | some (.file ..) => readBy (nextFate s).1 (nextFate s).2
  | _ => readBy .full s

/-- The bytes of a zero-terminated string at `a`, without the zero: a name
as a program hands it to the kernel. It fails if a byte cannot be read, or
if no zero comes within `fuel` bytes. -/
def cstring (s : State) : Nat → BitVec 64 → Except (BitVec 64) (List (BitVec 8))
  | 0, _ => .error (-36)
  | fuel + 1, a =>
    if (s.perm a).readable then
      let b := s.mem a
      if b = 0 then .ok [] else (cstring s fuel (a + 1)).map (b :: ·)
    else .error (-14)

/-- `openat(dirfd, path, flags, mode)`: open the file with that name, making
it first if `O_CREAT` asks and there is none. The result is the lowest
descriptor not in use. There are no directories, so a file asked for as one
(`O_DIRECTORY`) is refused. A file opened only to name it (`O_PATH`) can be
neither read nor written. -/
def openatIn (s : State) : State :=
  match cstring s 4096 (s.getReg .rsi) with
  | .error e => ret s e
  | .ok path =>
    let flags := ((s.getReg .rdx).setWidth 32).toNat
    let access := flags % 4
    let creat := flags / 0x40 % 2 == 1
    let excl := flags / 0x80 % 2 == 1
    let trunc := flags / 0x200 % 2 == 1
    let app := flags / 0x400 % 2 == 1
    let dir := flags / 0x10000 % 2 == 1
    let named := flags / 0x200000 % 2 == 1
    let r := access != 1 && !named
    let w := access != 0 && !named
    let fd := s.world.freeFd
    if access == 3 && !named then ret s (-22)
    else if path.isEmpty then ret s (-2)
    else if path.head? != some 0x2f && (s.getReg .rdi).setWidth 32 != (-100 : BitVec 32) then
      ret s (-9)
    else
      match s.world.find? path with
      | some i =>
        match s.world.files[i]? with
        | none => ret s (-2)
        | some f =>
          if creat && excl then ret s (-17)
          else if dir then ret s (-20)
          else if (r && !f.mayRead) || (w && !f.mayWrite) then ret s (-13)
          else
            ret { s with
                world := { s.world.setFd fd (.file i 0 r w app) with
                  files := s.world.files.setIfInBounds i (if trunc && w then f.truncate else f) } }
              (BitVec.ofNat 64 fd)
      | none =>
        if creat then
          if dir then ret s (-22)
          else if s.world.mayCreate then
            ret { s with
                world := { s.world.setFd fd (.file s.world.files.size 0 r w app) with
                  files := s.world.files.push { path := path } } }
              (BitVec.ofNat 64 fd)
          else ret s (-13)
        else ret s (-2)

/-- `openat`, with the kernel doing what the world says: it may refuse for
want of memory, room, or descriptors, whatever was asked. -/
def openat (s : State) : State :=
  match (nextFate s).1 with
  | .fail e => if e.ofOpen then ret (nextFate s).2 e.code else openatIn (nextFate s).2
  | _ => openatIn (nextFate s).2

/-- `close(fd)` when the kernel does `d` with it. The descriptor is closed
even when the call reports that the device failed, as it may once what was
written has been sent on its way. -/
def closeBy (d : Fate) (s : State) : State :=
  let fd := fdArg s .rdi
  match s.world.fd? fd with
  | some _ =>
    ret { s with world := s.world.closeFd fd }
      (match d with
        | .fail .io => -5
        | _ => 0)
  | none => ret s (-9)

/-- `close(fd)`, with the kernel doing what the world says. -/
def close (s : State) : State :=
  closeBy (nextFate s).1 (nextFate s).2

/-- `lseek(fd, offset, whence)`: move a file descriptor's position, counted
from the start of the file, from where it is, or from the end. The result
is the new position. -/
def lseek (s : State) : State :=
  let fd := fdArg s .rdi
  let whence := s.getReg .rdx
  match s.world.fd? fd with
  | some (.file i pos r w app) =>
    let size := ((s.world.files[i]?).map (·.size)).getD 0
    let from? : Option Nat :=
      if whence = 0 then some 0 else if whence = 1 then some pos
      else if whence = 2 then some size else none
    match from? with
    | none => ret s (-22)
    | some b =>
      let to : Int := b + (s.getReg .rsi).toInt
      if to < 0 then ret s (-22)
      else
        ret { s with world := s.world.setFd fd (.file i to.toNat r w app) }
          (BitVec.ofNat 64 to.toNat)
  | some _ => ret s (-29)
  | none => ret s (-9)

/-- `fsync(fd)` and `fdatasync(fd)` when the kernel does `d` with it: have
what was written to a file put where it will last. Nothing the program can
see changes but the answer. On a file it is zero, or the failure of the
device or the want of room that the writing ran into. The program's input
and output are not files here, and for them the call is refused. -/
def fsyncBy (d : Fate) (s : State) : State :=
  match s.world.fd? (fdArg s .rdi) with
  | some (.file _ _ _ _ _) =>
    ret s (match d with
      | .fail .io => -5
      | .fail .nospc => -28
      | .fail .dquot => -122
      | _ => 0)
  | some _ => ret s (-22)
  | none => ret s (-9)

/-- `fsync(fd)`, with the kernel doing what the world says. -/
def fsync (s : State) : State :=
  fsyncBy (nextFate s).1 (nextFate s).2

/-- `getpid()`: the number of the process, which the world gives. It cannot
fail. -/
def getpid (s : State) : State :=
  ret s (BitVec.ofNat 64 s.world.pid)

/-- The low `n` bytes of a number, least significant first. -/
def leBytes (n v : Nat) : List (BitVec 8) :=
  (List.range n).map fun i => BitVec.ofNat 8 (v >>> (8 * i))

/-- `fstat(fd, buf)`: store a description of what the descriptor refers to,
144 bytes of it, at `buf`. -/
def fstat (s : State) : State :=
  let buf := s.getReg .rsi
  match s.world.fd? (fdArg s .rdi) with
  | none => ret s (-9)
  | some d =>
    -- a regular file that its owner may read and write, or a pipe
    let (mode, size) := match d with
      | .file i _ _ _ _ => (0x81a4, ((s.world.files[i]?).map (·.size)).getD 0)
      | _ => (0x1180, 0)
    let data :=
      leBytes 8 0 ++ leBytes 8 0 ++ leBytes 8 1 ++ leBytes 4 mode ++ leBytes 4 0 ++ leBytes 4 0 ++
      leBytes 4 0 ++ leBytes 8 0 ++ leBytes 8 size ++ leBytes 8 4096 ++
      leBytes 8 ((size + 511) / 512) ++ List.replicate 72 0
    -- into a buffer that is not all writable the kernel stores what it can
    -- before it reports the bad address
    if s.canWrite buf 144 then give s buf (data.take 144) 0 s.world
    else give s buf (data.take (writableRun s buf 144)) (-14) s.world

/-- The standard clocks, by number: 0 to 11, but for 10, which is none. -/
def standardClock (c : Nat) : Bool :=
  decide (c < 12) && c != 10

/-- The clocks that only go forward: `CLOCK_MONOTONIC` (1), the two that
count processor time (2, 3), `CLOCK_MONOTONIC_RAW` (4),
`CLOCK_MONOTONIC_COARSE` (6), `CLOCK_BOOTTIME` (7) and its alarm (9). The
others tell the time of day, which can be set back. -/
def forwardOnly (c : Nat) : Bool :=
  c == 1 || c == 2 || c == 3 || c == 4 || c == 6 || c == 7 || c == 9

/-- What clock `c` reads now, in nanoseconds. -/
def clockNow (w : World) (c : Nat) : Nat :=
  if forwardOnly c then w.moved c + w.time c w.asks else w.time c w.asks

/-- `clock_gettime(clock, buf)`: store the time by that clock, seconds then
nanoseconds, 16 bytes, at `buf`. A number that is not a standard clock's may
be the clock of some process or device, which there is or is not: the world
says. -/
def clockGettime (s : State) : State :=
  let buf := s.getReg .rsi
  let c := fdArg s .rdi
  if !(standardClock c || s.world.hasClock c) then ret s (-22)
  else
    let now := clockNow s.world c
    let data := leBytes 8 (now / 1000000000) ++ leBytes 8 (now % 1000000000)
    let w := { s.world with
      asks := s.world.asks + 1
      moved := fun k => if k = c ∧ forwardOnly c = true then now else s.world.moved k }
    -- the clock is read either way; into a buffer that is not all writable
    -- the kernel stores what it can before it reports the bad address
    if s.canWrite buf 16 then give s buf (data.take 16) 0 w
    else give s buf (data.take (writableRun s buf 16)) (-14) w

/-- **A clock that only goes forward never goes back**: what it reads at one
asking is no less than what it read at the last. -/
theorem clockGettime_forward (s : State) (c : Nat) :
    s.world.moved c ≤ (clockGettime s).world.moved c := by
  have key : s.world.moved c ≤ if c = fdArg s .rdi ∧ forwardOnly (fdArg s .rdi) = true
      then clockNow s.world (fdArg s .rdi) else s.world.moved c := by
    split
    · next h =>
      rw [h.1]
      simp only [clockNow, h.2, ↓reduceIte]
      omega
    · exact Nat.le_refl _
  simp only [clockGettime]
  split
  · exact Nat.le_refl _
  · split <;> exact key

/-- Whether the call number `318` was handed flags the kernel refuses: a bit
it does not know, or both `GRND_RANDOM` (2) and `GRND_INSECURE` (4). -/
def grndBad (s : State) : Bool :=
  let f := ((s.getReg .rdx).setWidth 32).toNat
  decide (8 ≤ f) || (f / 2 % 2 == 1 && f / 4 % 2 == 1)

/-- Whether a `getrandom` may answer that it would have to wait: it was
handed `GRND_NONBLOCK` (1), and not `GRND_INSECURE` (4), which never waits. -/
def grndMayRefuse (s : State) : Bool :=
  let f := ((s.getReg .rdx).setWidth 32).toNat
  f % 2 == 1 && !(f / 4 % 2 == 1)

/-- Whether a `getrandom` may stop before it has delivered everything: it
was asked for more than 256 bytes, or handed `GRND_RANDOM` (2). -/
def grndMayStop (s : State) : Bool :=
  decide (256 < (s.getReg .rsi).toNat) || ((s.getReg .rdx).setWidth 32).toNat / 2 % 2 == 1

/-- The most one `getrandom` delivers: what was asked for, up to the
kernel's limit on one call. -/
def grndMost (s : State) : Nat :=
  min (s.getReg .rsi).toNat 0x7ffff000

/-- A `getrandom` that sets out to deliver `want` bytes, in world `w`: it
stores as many as it can write, and fails only if it can write none. -/
def grndDeliver (s : State) (w : World) (want : Nat) : State :=
  let buf := s.getReg .rdi
  let n := writableRun s buf want
  if n = 0 ∧ 0 < want then ret { s with world := w } (-14)
  else
    give s buf ((List.range n).map fun i => s.world.random (s.world.drawn + i))
      (BitVec.ofNat 64 n) { w with drawn := s.world.drawn + n }

/-- `getrandom(buf, length, flags)`: store random bytes at `buf`. The result
is how many. Which bytes is the world's choice, and so is what the kernel
does where it has a choice (`World.fates`): deliver everything, stop early,
or say it would have to wait. `Getrandom` says what it may do. -/
def getrandom (s : State) : State :=
  if grndBad s then ret s (-22)
  else
    let w := { s.world with fates := s.world.fates.tail }
    match s.world.fates.head? with
    | some (.fail .again) =>
      if grndMayRefuse s then ret { s with world := w } (-11) else grndDeliver s w (grndMost s)
    | some (.short k) =>
      grndDeliver s w (if grndMayStop s && decide (0 < k) then min k (grndMost s) else grndMost s)
    | _ => grndDeliver s w (grndMost s)

/-- `mmap(addr, length, prot, flags, fd, offset)`, for fresh memory only:
`prot` must be 3 (read and write) and `flags` 0x22 (private, not backed by a
file). The kernel ignores `fd` in this form, and treats `addr` as a hint of
where the memory should go. Only zero is modelled, which leaves the choice
to the kernel, and `linux` says nothing of any other. A hint is how a
program gets memory where the kernel would not put it of its own accord:
above `addrTop`, on a processor with 57-bit addresses, or in the reach of
the stack, which the kernel keeps clear so that the stack can grow.
`offset` must be a multiple of the page size. The length
is rounded up to whole pages. The world proposes where the memory goes; a
place that is not page-aligned, not within reach of a program, or not
entirely inaccessible beforehand is not one the kernel would choose, and the
call fails instead. On success the pages are readable, writable and zero,
and the result is their address. -/
def mmap (s : State) : State :=
  let len := (s.getReg .rsi).toNat
  let size := (len + 4095) / 4096 * 4096
  let w := { s.world with asked := s.world.asked + 1 }
  if s.getReg .rdx ≠ 3 ∨ s.getReg .r10 ≠ 0x22 then ret s (-22)
  else if len = 0 ∨ (s.getReg .r9).toNat % 4096 ≠ 0 then ret s (-22)
  else match s.world.place s.world.asked with
    | none => ret { s with world := w } (-12)
    | some a =>
      if a.toNat % 4096 = 0 ∧ 0 < a.toNat ∧ a.toNat + size ≤ addrTop ∧
          s.unmapped a size = true then
        ret { s.mapZero a size with world := w } a
      else ret { s with world := w } (-12)

/-- `munmap(addr, length)`: give whole pages back. The model does so only
for memory that is writable or already inaccessible; asked to take away
anything else, such as the program's own code, it refuses, which the kernel
would not, so the call is typed only for memory the program owns. -/
def munmap (s : State) : State :=
  let a := s.getReg .rdi
  let len := (s.getReg .rsi).toNat
  let size := (len + 4095) / 4096 * 4096
  if a.toNat % 4096 = 0 ∧ len ≠ 0 ∧ a.toNat + size ≤ addrTop ∧
      State.allBelow (fun i =>
        decide ((s.perm (a + BitVec.ofNat 64 i)).writable = true ∨
          s.perm (a + BitVec.ofNat 64 i) = .none)) size = true then
    ret (s.unmap a size) 0
  else ret s (-22)

end Linux

/-- The calls, by number: `read` 0, `write` 1, `close` 3, `fstat` 5, `lseek`
8, `mmap` 9, `munmap` 11, `exit` 60, `clock_gettime` 228, `exit_group` 231, `openat` 257
and `getrandom` 318. -/
def linux : Syscall := fun s =>
  if s.getReg .rax = 60 then .exit (s.readReg .w32 .rdi)
  else if s.getReg .rax = 231 then .exit (s.readReg .w32 .rdi)
  else if s.getReg .rax = 1 then .next (Linux.write s)
  else if s.getReg .rax = 0 then .next (Linux.read s)
  else if s.getReg .rax = 9 then
    -- Only where the kernel chooses the place; see `Linux.mmap`.
    if s.getReg .rdi = 0 then .next (Linux.mmap s) else .stuck
  else if s.getReg .rax = 11 then .next (Linux.munmap s)
  else if s.getReg .rax = 3 then .next (Linux.close s)
  else if s.getReg .rax = 5 then .next (Linux.fstat s)
  else if s.getReg .rax = 8 then .next (Linux.lseek s)
  else if s.getReg .rax = 228 then .next (Linux.clockGettime s)
  else if s.getReg .rax = 257 then .next (Linux.openat s)
  else if s.getReg .rax = 74 then .next (Linux.fsync s)
  else if s.getReg .rax = 75 then .next (Linux.fsync s)
  else if s.getReg .rax = 39 then .next (Linux.getpid s)
  else if s.getReg .rax = 318 then .next (Linux.getrandom s)
  else .next (Linux.ret s (-38))

namespace Linux

variable {n : Nat} {s : State}

theorem ret_rax (s : State) (v : BitVec 64) : (ret s v).getReg .rax = v := by
  show (((s.setReg .rax v).setReg .rcx s.rip).setReg .r11 0).getReg .rax = v
  rw [State.getReg_setReg_other _ _ _ _ (by decide), State.getReg_setReg_other _ _ _ _ (by decide),
    State.getReg_setReg_same]

theorem mmap_rip (s : State) : (mmap s).rip = s.rip := by
  simp only [mmap]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split <;> rfl

/-- A byte in a range found inaccessible is inaccessible. -/
theorem perm_of_unmapped {a : BitVec 64} {size : Nat} (hal : a.toNat % 4096 = 0)
    (hfit : a.toNat + size ≤ addrTop) (h : s.unmapped a size = true)
    {x : BitVec 64} (hx : (x - a).toNat < size) : s.perm x = .none := by
  have := (State.unmapped_iff hal (Nat.le_trans hfit (by decide))).mp h _ hx
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq, show a + (x - a) = x by bv_omega] at this

/-! ## The two things a call can do to the program

Apart from `mmap`, every call either leaves the machine alone, changing only
the outside world and the registers a call always changes, or does that and
also stores bytes in a buffer it was handed. Each fact a call must satisfy
is proved once for each of the two. -/

/-- `t` is `s` after a call that touched nothing of the program's. -/
def OnlyWorld (s t : State) : Prop :=
  ∃ v w, t = ret { s with world := w } v

namespace OnlyWorld

variable {t : State}

theorem same (s : State) (v : BitVec 64) : OnlyWorld s (ret s v) :=
  ⟨v, s.world, rfl⟩

theorem intro (s : State) (v : BitVec 64) (w : World) :
    OnlyWorld s (ret { s with world := w } v) :=
  ⟨v, w, rfl⟩

theorem rip (hf : OnlyWorld s t) : t.rip = s.rip := by
  obtain ⟨v, w, rfl⟩ := hf
  rfl

theorem frame (hf : OnlyWorld s t) : Frame s t := by
  obtain ⟨v, w, rfl⟩ := hf
  exact Frame.of_eq rfl rfl

end OnlyWorld

/-- `t` is `s` after a call that at most stored up to `room` bytes at `buf`,
all of them in writable memory. -/
def Fills (s : State) (buf : BitVec 64) (room : Nat) (t : State) : Prop :=
  OnlyWorld s t ∨
    ∃ data v w, data.length ≤ room ∧ s.canWrite buf data.length = true ∧ t = give s buf data v w

theorem Fills.same (s : State) (buf : BitVec 64) (room : Nat) (v : BitVec 64) :
    Fills s buf room (ret s v) :=
  .inl (.same s v)

theorem Fills.only (s : State) (buf : BitVec 64) (room : Nat) (v : BitVec 64) (w : World) :
    Fills s buf room (ret { s with world := w } v) :=
  .inl (.intro s v w)

theorem canWrite_le {a : BitVec 64} {m k : Nat} (h : s.canWrite a m = true) (hle : k ≤ m) :
    s.canWrite a k = true := by
  rw [State.canWrite_iff] at h ⊢
  exact fun i hi => h i (by omega)

theorem fills_give {buf : BitVec 64} {room : Nat} {data : List (BitVec 8)} {v : BitVec 64}
    {w : World} (hw : s.canWrite buf room = true) (hlen : data.length ≤ room) :
    Fills s buf room (give s buf data v w) :=
  .inr ⟨data, v, w, hlen, canWrite_le hw hlen, rfl⟩

namespace Fills

variable {t : State} {r : Reg} {room : Nat}

theorem rip {buf : BitVec 64} (hf : Fills s buf room t) : t.rip = s.rip := by
  rcases hf with hf | ⟨data, v, w, -, -, rfl⟩
  · exact hf.rip
  · rfl

/-- Only bytes of the buffer change, and those were writable. -/
theorem frame {buf : BitVec 64} (hf : Fills s buf room t) (hroom : room ≤ 2 ^ 64) : Frame s t := by
  rcases hf with hf | ⟨data, v, w, hlen, hw, rfl⟩
  · exact hf.frame
  · refine .of_perm rfl (fun x hx => ?_)
    show (s.storeBytes buf data).mem x = s.mem x
    rw [State.mem_storeBytes s _ x _ (by omega)]
    by_cases hin : (x - buf).toNat < data.length
    · -- a byte inside the buffer is writable, so it is not one of these
      rw [State.canWrite_iff] at hw
      have := hw _ hin
      rw [show buf + BitVec.ofNat 64 (x - buf).toNat = x by bv_omega] at this
      rw [this] at hx
      cases hx
    · rw [List.getElem?_eq_none (by omega)]
      rfl

end Fills

/-! ## Each call is one of the two -/

/-- Settles a call that only changes the world: every way it can end is a
plain return. -/
local macro "only_world" : tactic =>
  `(tactic| repeat' (first
    | (with_reducible exact OnlyWorld.same _ _)
    | (with_reducible exact OnlyWorld.intro _ _ _)
    | split))

/-- Settles a call that fills a buffer: every way it can end is a plain
return, or a store of no more than was asked for into memory found writable. -/
local macro "fills" : tactic =>
  `(tactic| repeat' (first
    | (with_reducible exact Fills.same _ _ _ _)
    | (with_reducible exact Fills.only _ _ _ _ _)
    | (with_reducible exact fills_give (by assumption) (List.length_take_le _ _))
    | (with_reducible exact (fills_give (canWrite_writableRun _ _ _)
        (List.length_take_le _ _)).mono (writableRun_le _ _ _))
    | split))

theorem writeBy_only (d : Fate) (s : State) : OnlyWorld s (writeBy d s) := by
  simp only [writeBy]
  only_world

theorem write_only (s : State) : OnlyWorld s (write s) := by
  obtain ⟨v, w, e⟩ := writeBy_only (nextFate s).1 (nextFate s).2
  exact ⟨v, w, e⟩

/-- **What a program may conclude from the result of a `write` to its
output**, whatever the kernel did with it. Either the call failed, with an
error number, and nothing was written: the world is as it was, but for the
call having returned. Or it answered a count `n`, no more
than was asked for: then exactly the first `n` bytes of the buffer were
added to the output. Nothing says `n` is all that was asked for, only that
it is not zero when something was: a program that goes round again with the
rest gets somewhere each time. -/
theorem writeBy_stdout (d : Fate) (s : State)
    (hfd : s.world.fd? (fdArg s .rdi) = some .stdout) :
    (SysErr ((writeBy d s).getReg .rax) ∧ (writeBy d s).world = s.world.spent) ∨
    ∃ n, n ≤ (s.getReg .rdx).toNat ∧ (0 < (s.getReg .rdx).toNat → 0 < n) ∧
      (writeBy d s).getReg .rax = BitVec.ofNat 64 n ∧
      (writeBy d s).world.writes = s.loadBytes (s.getReg .rsi) n :: s.world.writes := by
  have hmost : readableRun s (s.getReg .rsi) (min (s.getReg .rdx).toNat 0x7ffff000)
      ≤ (s.getReg .rdx).toNat :=
    Nat.le_trans (readableRun_le _ _ _) (Nat.min_le_left _ _)
  simp only [writeBy, hfd]
  split
  · exact .inl ⟨by rw [ret_rax]; decide, rfl⟩
  · next h0 =>
    have hcount : ∀ d' : Fate, taken d' (readableRun s (s.getReg .rsi)
          (min (s.getReg .rdx).toNat 0x7ffff000)) ≤ (s.getReg .rdx).toNat ∧
        (0 < (s.getReg .rdx).toNat → 0 < taken d' (readableRun s (s.getReg .rsi)
          (min (s.getReg .rdx).toNat 0x7ffff000))) :=
      fun d' => ⟨Nat.le_trans (taken_le _ _) hmost, fun hpos => taken_pos _ (by omega)⟩
    cases d with
    | fail e =>
      by_cases hw : e.ofWrite = true
      · simp only [hw, ↓reduceIte]
        exact .inl ⟨by rw [ret_rax]; cases e <;> decide, rfl⟩
      · simp only [hw, Bool.false_eq_true, ↓reduceIte]
        exact .inr ⟨_, (hcount (.fail e)).1, (hcount (.fail e)).2, ret_rax _ _, rfl⟩
    | full => exact .inr ⟨_, (hcount .full).1, (hcount .full).2, ret_rax _ _, rfl⟩
    | short k => exact .inr ⟨_, (hcount (.short k)).1, (hcount (.short k)).2, ret_rax _ _, rfl⟩

theorem openatIn_only (s : State) : OnlyWorld s (openatIn s) := by
  simp only [openatIn]
  only_world

theorem openat_only (s : State) : OnlyWorld s (openat s) := by
  have key : ∀ t, OnlyWorld (nextFate s).2 t → OnlyWorld s t := fun t ⟨v, w, e⟩ => ⟨v, w, e⟩
  simp only [openat]
  split
  · split
    · exact key _ (OnlyWorld.same _ _)
    · exact key _ (openatIn_only _)
  · exact key _ (openatIn_only _)

theorem closeBy_only (d : Fate) (s : State) : OnlyWorld s (closeBy d s) := by
  simp only [closeBy]
  only_world

theorem close_only (s : State) : OnlyWorld s (close s) := by
  obtain ⟨v, w, e⟩ := closeBy_only (nextFate s).1 (nextFate s).2
  exact ⟨v, w, e⟩

theorem lseek_only (s : State) : OnlyWorld s (lseek s) := by
  simp only [lseek]
  only_world

theorem fsyncBy_only (d : Fate) (s : State) : OnlyWorld s (fsyncBy d s) := by
  simp only [fsyncBy]
  only_world

theorem fsync_only (s : State) : OnlyWorld s (fsync s) := by
  obtain ⟨v, w, e⟩ := fsyncBy_only (nextFate s).1 (nextFate s).2
  exact ⟨v, w, e⟩

theorem getpid_only (s : State) : OnlyWorld s (getpid s) := .same s _

/-- A call that stored within a smaller room stored within a larger one. -/
theorem Fills.mono {buf : BitVec 64} {room room' : Nat} {t : State} (hf : Fills s buf room t)
    (h : room ≤ room') : Fills s buf room' t := by
  rcases hf with hf | ⟨data, v, w, hlen, hcan, rfl⟩
  · exact .inl hf
  · exact .inr ⟨data, v, w, Nat.le_trans hlen h, hcan, rfl⟩

/-- A call made in a state that differs only in its world fills what it
would have filled. -/
theorem Fills.ofWorld {buf : BitVec 64} {room : Nat} {t : State} {w₀ : World}
    (hf : Fills { s with world := w₀ } buf room t) : Fills s buf room t := by
  rcases hf with ⟨v, w, rfl⟩ | ⟨data, v, w, hlen, hcan, rfl⟩
  · exact .inl ⟨v, w, rfl⟩
  · exact .inr ⟨data, v, w, hlen, hcan, rfl⟩

theorem readBy_fills (d : Fate) (s : State) :
    Fills s (s.getReg .rsi) (s.getReg .rdx).toNat (readBy d s) := by
  have hroom : writableRun s (s.getReg .rsi) (min (s.getReg .rdx).toNat 0x7ffff000)
      ≤ (s.getReg .rdx).toNat :=
    Nat.le_trans (writableRun_le _ _ _) (Nat.min_le_left _ _)
  simp only [readBy]
  repeat' (first
    | (with_reducible exact Fills.same _ _ _ _)
    | (with_reducible exact Fills.only _ _ _ _ _)
    | exact (fills_give (canWrite_writableRun _ _ _) (List.length_take_le _ _)).mono hroom
    | split)

/-- What a program may conclude from the result of a call that stores up to
`count` bytes at `buf`. Either the call failed, with an error number, and
memory is as it was. Or it answered a count, no more than `count`: then that
many bytes at the start of the buffer are the ones the kernel supplied, and
every other byte of memory is as it was. A count of zero is the end of what
there is to read. -/
def Stored (s : State) (buf : BitVec 64) (count : Nat) (t : State) : Prop :=
  (SysErr (t.getReg .rax) ∧ t.mem = s.mem) ∨
  ∃ data : List (BitVec 8), data.length ≤ count ∧
    t.getReg .rax = BitVec.ofNat 64 data.length ∧
    (∀ i (hi : i < data.length), t.mem (buf + BitVec.ofNat 64 i) = data[i]) ∧
    ∀ x : BitVec 64, data.length ≤ (x - buf).toNat → t.mem x = s.mem x

theorem Errno.code_err (e : Errno) : SysErr e.code := by
  cases e <;> decide

theorem Stored.err {buf : BitVec 64} {count : Nat} {v : BitVec 64} (w : World) (hv : SysErr v) :
    Stored s buf count (ret { s with world := w } v) :=
  .inl ⟨by rw [ret_rax]; exact hv, rfl⟩

theorem Stored.err' {buf : BitVec 64} {count : Nat} {v : BitVec 64} (hv : SysErr v) :
    Stored s buf count (ret s v) :=
  .inl ⟨by rw [ret_rax]; exact hv, rfl⟩

theorem Stored.none {buf : BitVec 64} {count : Nat} : Stored s buf count (ret s 0) :=
  .inr ⟨[], Nat.zero_le _, ret_rax _ _, fun i hi => absurd hi (by simp), fun _ _ => rfl⟩

theorem Stored.give {buf : BitVec 64} {count : Nat} {data : List (BitVec 8)} (w : World)
    (hlen : data.length ≤ count) (hc : count < 2 ^ 64) :
    Stored s buf count (give s buf data (BitVec.ofNat 64 data.length) w) := by
  refine .inr ⟨data, hlen, ret_rax _ _, fun i hi => ?_, fun x hx => ?_⟩
  · show (s.storeBytes buf data).mem _ = _
    rw [State.mem_storeBytes _ _ _ _ (by omega)]
    have e : (buf + BitVec.ofNat 64 i - buf).toNat = i := by bv_omega
    rw [e, List.getElem?_eq_getElem hi]
    rfl
  · show (s.storeBytes buf data).mem x = _
    rw [State.mem_storeBytes _ _ _ _ (by omega), List.getElem?_eq_none hx]
    rfl

/-- **What a program may conclude from the result of a `read`**, whatever the
kernel did with it and whatever there was to read. -/
theorem readBy_stored (d : Fate) (s : State) :
    Stored s (s.getReg .rsi) (s.getReg .rdx).toNat (readBy d s) := by
  have hroom : writableRun s (s.getReg .rsi) (min (s.getReg .rdx).toNat 0x7ffff000)
      ≤ (s.getReg .rdx).toNat :=
    Nat.le_trans (writableRun_le _ _ _) (Nat.min_le_left _ _)
  have hlt := (s.getReg .rdx).isLt
  simp only [readBy]
  repeat' (first
    | (with_reducible exact Stored.none)
    | ((with_reducible refine Stored.err' ?_); first | decide | exact Errno.code_err _)
    | ((with_reducible refine Stored.err _ ?_); first | decide | exact Errno.code_err _)
    | ((with_reducible refine Stored.give _ ?_ hlt);
        exact Nat.le_trans (List.length_take_le _ _) hroom)
    | split)

theorem read_stored (s : State) :
    Stored s (s.getReg .rsi) (s.getReg .rdx).toNat (read s) := by
  simp only [read]
  split
  · exact readBy_stored (nextFate s).1 (nextFate s).2
  · exact readBy_stored _ s

theorem read_fills (s : State) : Fills s (s.getReg .rsi) (s.getReg .rdx).toNat (read s) := by
  simp only [read]
  split
  · exact (readBy_fills (nextFate s).1 (nextFate s).2).ofWorld
  · exact readBy_fills _ s

theorem fstat_fills (s : State) : Fills s (s.getReg .rsi) 144 (fstat s) := by
  simp only [fstat]
  fills

theorem clockGettime_fills (s : State) : Fills s (s.getReg .rsi) 16 (clockGettime s) := by
  simp only [clockGettime]
  fills

/-! ## What `getrandom` may answer

The contract of `getrandom(buf, len, flags)` with Linux, for a process
without signal handlers, which is every process of the model: it has no way
to install one. A signal whose action is to end or stop the process does so
from outside, and is not an answer to the call.

* Flags the kernel does not know, or `GRND_RANDOM` with `GRND_INSECURE`:
  `EINVAL`, and nothing else happens.
* With `GRND_NONBLOCK` and without `GRND_INSECURE`: it may answer `EAGAIN`,
  having stored nothing.
* Otherwise it stores some number of bytes at the start of the buffer and
  answers with that number, leaving every other byte of memory as it was.
  The number is everything asked for, up to the kernel's limit on one call,
  with two exceptions. A call for more than 256 bytes, or with
  `GRND_RANDOM`, may stop early after at least one byte. And a call whose
  buffer is not all writable stops at the first byte it cannot write.
* If it cannot write even the first byte, `EFAULT`.

`EINTR` is not among the answers: without a handler, the kernel starts an
interrupted call again by itself. -/

/-- The worlds that differ from `w` only in how much randomness has been
drawn and in what the kernel is still to decide. -/
def SameBut (w w' : World) : Prop :=
  ∃ fates drawn, w' = { w with fates := fates, drawn := drawn }

/-- `Getrandom s t`: `t` is a state Linux may return to from a `getrandom`
called in `s`. -/
inductive Getrandom (s : State) : State → Prop
  | invalid : grndBad s = true → Getrandom s (ret s (-22))
  | again (w : World) : grndBad s = false → SameBut s.world w → grndMayRefuse s = true →
    Getrandom s (ret { s with world := w } (-11))
  | fault (w : World) : grndBad s = false → SameBut s.world w → 0 < grndMost s →
    (s.perm (s.getReg .rdi)).writable = false → Getrandom s (ret { s with world := w } (-14))
  | filled (data : List (BitVec 8)) (w : World) : grndBad s = false → SameBut s.world w →
    data.length ≤ grndMost s → s.canWrite (s.getReg .rdi) data.length = true →
    (data.length = grndMost s ∨ (grndMayStop s = true ∧ 0 < data.length) ∨
      (0 < data.length ∧ data.length < grndMost s ∧
        (s.perm (s.getReg .rdi + BitVec.ofNat 64 data.length)).writable = false)) →
    Getrandom s (give s (s.getReg .rdi) data (BitVec.ofNat 64 data.length) w)

/-- A delivery of an amount the call may deliver is an answer the contract allows. -/
theorem grndDeliver_allowed (s : State) (w : World) (want : Nat) (hbad : grndBad s = false)
    (hw : SameBut s.world w) (hle : want ≤ grndMost s)
    (hwant : want = grndMost s ∨ (grndMayStop s = true ∧ 0 < want)) :
    Getrandom s (grndDeliver s w want) := by
  have hrun := runFrom_spec s Perm.writable (s.getReg .rdi) want 0
  have hn : writableRun s (s.getReg .rdi) want ≤ want := writableRun_le _ _ _
  simp only [grndDeliver]
  split
  · next h0 =>
    refine .fault w hbad hw (by omega) ?_
    have := hrun.2.2.2 (by show writableRun s _ want < 0 + want; omega)
    rw [show runFrom s Perm.writable (s.getReg .rdi) 0 want = 0 from h0.1] at this
    simpa using this
  · next h0 =>
    obtain ⟨fates, drawn, rfl⟩ := hw
    have hlen : ((List.range (writableRun s (s.getReg .rdi) want)).map
        fun i => s.world.random (s.world.drawn + i)).length
          = writableRun s (s.getReg .rdi) want := by simp
    have key := Getrandom.filled (s := s)
      ((List.range (writableRun s (s.getReg .rdi) want)).map
        fun i => s.world.random (s.world.drawn + i))
      { s.world with fates := fates, drawn := s.world.drawn + writableRun s (s.getReg .rdi) want }
      hbad ⟨fates, _, rfl⟩ (by rw [hlen]; omega) (by rw [hlen]; exact canWrite_writableRun _ _ _)
      (by
        rw [hlen]
        by_cases hfull : writableRun s (s.getReg .rdi) want = want
        · rcases hwant with h | h
          · exact .inl (by omega)
          · exact .inr (.inl ⟨h.1, by omega⟩)
        · refine .inr (.inr ⟨by omega, by omega, ?_⟩)
          exact hrun.2.2.2 (by show writableRun s _ want < 0 + want; omega))
    rw [hlen] at key
    exact key

/-- **The model's `getrandom` does only what the contract allows**, whatever
the world. -/
theorem getrandom_allowed (s : State) : Getrandom s (getrandom s) := by
  simp only [getrandom]
  split
  · next hbad => exact .invalid hbad
  · next hbad =>
    have hbad' : grndBad s = false := (Bool.not_eq_true _).mp hbad
    have hw : SameBut s.world { s.world with fates := s.world.fates.tail } :=
      ⟨_, s.world.drawn, rfl⟩
    split
    · split
      · next hr => exact .again _ hbad' hw hr
      · exact grndDeliver_allowed s _ _ hbad' hw (Nat.le_refl _) (.inl rfl)
    · next k _ =>
      split
      · next hk =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
        by_cases hmin : min k (grndMost s) = grndMost s
        · exact grndDeliver_allowed s _ _ hbad' hw (Nat.min_le_right _ _) (.inl hmin)
        · exact grndDeliver_allowed s _ _ hbad' hw (Nat.min_le_right _ _)
            (.inr ⟨hk.1, by omega⟩)
      · exact grndDeliver_allowed s _ _ hbad' hw (Nat.le_refl _) (.inl rfl)
    · exact grndDeliver_allowed s _ _ hbad' hw (Nat.le_refl _) (.inl rfl)

/-- **Every answer the contract allows stores only in the buffer**, in bytes
that were writable, and no more than was asked for: so every one of them
keeps the typing and changes nothing the program cannot write. -/
theorem Getrandom.fills {s t : State} (h : Getrandom s t) :
    Fills s (s.getReg .rdi) (s.getReg .rsi).toNat t := by
  cases h with
  | invalid => exact Fills.same _ _ _ _
  | again w => exact Fills.only _ _ _ _ _
  | fault w => exact Fills.only _ _ _ _ _
  | filled data w _ _ hle hcan =>
    exact .inr ⟨data, _, w, Nat.le_trans hle (Nat.min_le_left _ _), hcan, rfl⟩

/-- **What a program may conclude from the result.** Either the call failed,
with one of three error numbers, and memory is as it was. Or it answered a
count `k`, no more than was asked for: then the first `k` bytes of the
buffer are the ones the kernel supplied, and every other byte of memory is
as it was. Nothing says that `k` is all that was asked for. -/
theorem Getrandom.effect {s t : State} (h : Getrandom s t) :
    (t.mem = s.mem ∧
      (t.getReg .rax = -22 ∨ t.getReg .rax = -11 ∨ t.getReg .rax = -14)) ∨
    ∃ data : List (BitVec 8), data.length ≤ (s.getReg .rsi).toNat ∧
      t.getReg .rax = BitVec.ofNat 64 data.length ∧
      (∀ i (hi : i < data.length), t.mem (s.getReg .rdi + BitVec.ofNat 64 i) = data[i]) ∧
      ∀ x : BitVec 64, data.length ≤ (x - s.getReg .rdi).toNat → t.mem x = s.mem x := by
  cases h with
  | invalid => exact .inl ⟨rfl, .inl (ret_rax _ _)⟩
  | again w => exact .inl ⟨rfl, .inr (.inl (ret_rax _ _))⟩
  | fault w => exact .inl ⟨rfl, .inr (.inr (ret_rax _ _))⟩
  | filled data w _ _ hle hcan =>
    have hlen : data.length ≤ (s.getReg .rsi).toNat := Nat.le_trans hle (Nat.min_le_left _ _)
    have hlt := (s.getReg .rsi).isLt
    refine .inr ⟨data, hlen, ret_rax _ _, fun i hi => ?_, fun x hx => ?_⟩
    · show (s.storeBytes (s.getReg .rdi) data).mem _ = _
      rw [State.mem_storeBytes _ _ _ _ (by omega)]
      have e : (s.getReg .rdi + BitVec.ofNat 64 i - s.getReg .rdi).toNat = i := by bv_omega
      rw [e, List.getElem?_eq_getElem hi]
      rfl
    · show (s.storeBytes (s.getReg .rdi) data).mem x = _
      rw [State.mem_storeBytes _ _ _ _ (by omega), List.getElem?_eq_none hx]
      rfl

theorem getrandom_fills (s : State) :
    Fills s (s.getReg .rdi) (s.getReg .rsi).toNat (getrandom s) :=
  (getrandom_allowed s).fills

/-! ## What a call that stores bytes answers

Each of them answers an error number, or a number no more than the bytes it
was given room for: how many it stored, or nought. -/

/-- A call's answer, with room for so many bytes: an error number, or no
more than that. -/
def Answered (room : Nat) (v : BitVec 64) : Prop := SysErr v ∨ v.toNat ≤ room

theorem give_rax (s : State) (buf : BitVec 64) (data : List (BitVec 8)) (v : BitVec 64)
    (w : World) : (give s buf data v w).getReg .rax = v :=
  ret_rax _ _

theorem Answered.of_stored {buf : BitVec 64} {count : Nat} {t : State} (hc : count < 2 ^ 64)
    (h : Stored s buf count t) : Answered count (t.getReg .rax) := by
  rcases h with ⟨he, -⟩ | ⟨data, hlen, hrax, -, -⟩
  · exact .inl he
  · refine .inr ?_
    rw [hrax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hlen

/-- What `write` answers is an error number, or no more than it was
offered. -/
theorem writeBy_answered (d : Fate) (s : State) :
    Answered (s.getReg .rdx).toNat ((writeBy d s).getReg .rax) := by
  have hn : (BitVec.ofNat 64 (taken d (readableRun s (s.getReg .rsi)
      (min (s.getReg .rdx).toNat 0x7ffff000)))).toNat ≤ (s.getReg .rdx).toNat := by
    rw [BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le _ _) (Nat.le_trans (taken_le _ _)
      (Nat.le_trans (readableRun_le _ _ _) (Nat.min_le_left _ _)))
  simp only [writeBy]
  repeat' (first
    | (rw [ret_rax]; first
        | exact .inl (by decide) | exact .inl (Errno.code_err _) | exact .inr hn)
    | split)

theorem write_answered (s : State) : Answered (s.getReg .rdx).toNat ((write s).getReg .rax) :=
  writeBy_answered (nextFate s).1 (nextFate s).2

theorem read_answered (s : State) : Answered (s.getReg .rdx).toNat ((read s).getReg .rax) :=
  .of_stored (s.getReg .rdx).isLt (read_stored s)

theorem getrandom_answered (s : State) :
    Answered (s.getReg .rsi).toNat ((getrandom s).getReg .rax) := by
  rcases (getrandom_allowed s).effect with ⟨-, h | h | h⟩ | ⟨data, hlen, hrax, -, -⟩
  · rw [h]; exact .inl (by decide)
  · rw [h]; exact .inl (by decide)
  · rw [h]; exact .inl (by decide)
  · refine .inr ?_
    have := (s.getReg .rsi).isLt
    rw [hrax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hlen

theorem fstat_answered (s : State) : Answered 144 ((fstat s).getReg .rax) := by
  simp only [fstat]
  repeat' (first
    | (rw [ret_rax]; first | exact .inl (by decide) | exact .inr (by decide))
    | (rw [give_rax]; first | exact .inl (by decide) | exact .inr (by decide))
    | split)

theorem clockGettime_answered (s : State) : Answered 16 ((clockGettime s).getReg .rax) := by
  simp only [clockGettime]
  repeat' (first
    | (rw [ret_rax]; first | exact .inl (by decide) | exact .inr (by decide))
    | (rw [give_rax]; first | exact .inl (by decide) | exact .inr (by decide))
    | split)

/-- **What a program may conclude from the result of a `getrandom`**, in the
same words as for a `read`. -/
theorem getrandom_stored (s : State) :
    Stored s (s.getReg .rdi) (s.getReg .rsi).toNat (getrandom s) := by
  rcases (getrandom_allowed s).effect with ⟨hm, he⟩ | h
  · refine .inl ⟨?_, hm⟩
    rcases he with e | e | e <;> rw [e] <;> decide
  · exact .inr h

/-- The kernel gets exactly as far as the bytes that can be written. -/
theorem writableRun_eq {s : State} {a : BitVec 64} {k n : Nat} (hcan : s.canWrite a k = true)
    (hstop : k = n ∨ (k < n ∧ (s.perm (a + BitVec.ofNat 64 k)).writable = false)) :
    writableRun s a n = k := by
  obtain ⟨-, h2, h3, h4⟩ := runFrom_spec s Perm.writable a n 0
  rw [State.canWrite_iff] at hcan
  show runFrom s Perm.writable a 0 n = k
  apply Nat.le_antisymm
  · apply Nat.le_of_not_lt
    intro hgt
    rcases hstop with h | h
    · omega
    · have := h3 k (Nat.zero_le _) hgt
      rw [h.2] at this
      cases this
  · apply Nat.le_of_not_lt
    intro hlt
    have := h4 (by omega)
    rw [hcan _ hlt] at this
    cases this

/-- The state with the kernel's coming decisions and the bytes it supplies
chosen afresh. -/
def withChoices (s : State) (fates : List Fate) (random : Nat → BitVec 8) : State :=
  { s with world := { s.world with fates := fates, random := random, drawn := 0 } }

theorem getrandom_of_bad {s : State} (h : grndBad s = true) : getrandom s = ret s (-22) := by
  simp [getrandom, h]

theorem getrandom_of_again {s : State} (h : grndBad s = false) (hf : s.world.fates = [.fail .again])
    (hr : grndMayRefuse s = true) : ∃ w, getrandom s = ret { s with world := w } (-11) := by
  simp only [getrandom, h, hf, hr, Bool.false_eq_true, ↓reduceIte, List.head?_cons]
  exact ⟨_, rfl⟩

theorem getrandom_of_none {s : State} (h : grndBad s = false) (hf : s.world.fates = []) :
    ∃ w, getrandom s = grndDeliver s w (grndMost s) := by
  simp only [getrandom, h, hf, Bool.false_eq_true, ↓reduceIte, List.head?_nil]
  exact ⟨_, rfl⟩

theorem getrandom_of_short {s : State} {k : Nat} (h : grndBad s = false)
    (hf : s.world.fates = [.short k]) (hs : grndMayStop s = true) (hk : 0 < k) :
    ∃ w, getrandom s = grndDeliver s w (min k (grndMost s)) := by
  simp only [getrandom, h, hf, hs, hk, Bool.false_eq_true, ↓reduceIte, List.head?_cons,
    Bool.true_and, decide_true]
  exact ⟨_, rfl⟩

/-- **Every answer the contract allows is one the model gives in some
world.** The world differs from the state's own only in the bytes the kernel
supplies and in what it decides. So a statement proved of the model for
every world is proved for every answer Linux may give, as far as a program
can observe it: the result, and all of memory. -/
theorem Getrandom.realized {s t : State} (h : Getrandom s t) :
    ∃ (fates : List Fate) (random : Nat → BitVec 8),
      (getrandom (withChoices s fates random)).getReg .rax = t.getReg .rax ∧
      (getrandom (withChoices s fates random)).mem = t.mem := by
  cases h with
  | invalid hbad =>
    refine ⟨[], fun _ => 0, ?_⟩
    rw [getrandom_of_bad (s := withChoices s [] fun _ => 0) hbad]
    exact ⟨by rw [ret_rax, ret_rax], rfl⟩
  | again w hbad _ hr =>
    refine ⟨[.fail .again], fun _ => 0, ?_⟩
    obtain ⟨w', e⟩ := getrandom_of_again (s := withChoices s [.fail .again] fun _ => 0) hbad rfl hr
    rw [e]
    exact ⟨by rw [ret_rax, ret_rax], rfl⟩
  | fault w hbad _ hpos hperm =>
    refine ⟨[], fun _ => 0, ?_⟩
    obtain ⟨w', e⟩ := getrandom_of_none (s := withChoices s [] fun _ => 0) hbad rfl
    have hp : (withChoices s [] fun _ => 0).perm = s.perm := rfl
    have hrun : writableRun (withChoices s [] fun _ => 0)
        ((withChoices s [] fun _ => 0).getReg .rdi) (grndMost (withChoices s [] fun _ => 0)) = 0 :=
      writableRun_eq (State.canWrite_iff.mpr fun i hi => absurd hi (by omega))
        (.inr ⟨hpos, by
          rw [hp]
          show (s.perm (s.getReg .rdi + BitVec.ofNat 64 0)).writable = false
          simpa using hperm⟩)
    have hpos' : 0 < grndMost (withChoices s [] fun _ => 0) := hpos
    rw [e]
    simp only [grndDeliver, hrun, hpos', and_self, ↓reduceIte]
    exact ⟨by rw [ret_rax, ret_rax], rfl⟩
  | filled data w hbad _ hle hcan hwhy =>
    -- the kernel's decision: stop early where that is why the count is short
    let fates : List Fate :=
      if data.length = grndMost s then []
      else if grndMayStop s = true ∧ 0 < data.length then [.short data.length] else []
    refine ⟨fates, fun i => data.getD i 0, ?_⟩
    generalize hs' : withChoices s fates (fun i => data.getD i 0) = s'
    have hfates : s'.world.fates = fates := by rw [← hs']; rfl
    have hreg : ∀ r, s'.getReg r = s.getReg r := fun r => by rw [← hs']; rfl
    have hperm : s'.perm = s.perm := by rw [← hs']; rfl
    have hbad' : grndBad s' = false := by rw [← hs']; exact hbad
    have hmost : grndMost s' = grndMost s := by rw [← hs']; rfl
    have hstop : grndMayStop s' = grndMayStop s := by rw [← hs']; rfl
    have hcan' : s'.canWrite (s'.getReg .rdi) data.length = true := by
      rw [State.canWrite_iff] at hcan ⊢
      rw [hperm, hreg]; exact hcan
    have hdata : (List.range data.length).map (fun i => s'.world.random (s'.world.drawn + i))
        = data := by
      rw [← hs']
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_map, List.getElem_range]
        show data.getD (0 + i) 0 = data[i]
        rw [Nat.zero_add]
        simp [List.getD, List.getElem?_eq_getElem h2]
    -- what the model sets out to deliver, and that it gets exactly that far
    have hdeliver : ∀ (w' : World) (want : Nat), want ≤ grndMost s →
        writableRun s' (s'.getReg .rdi) want = data.length →
        (grndDeliver s' w' want).getReg .rax = BitVec.ofNat 64 data.length ∧
        (grndDeliver s' w' want).mem = (s.storeBytes (s.getReg .rdi) data).mem := by
      intro w' want hwle hrun
      simp only [grndDeliver, hrun, hdata]
      split
      · next h0 =>
        -- nothing delivered though something was wanted: no answer of this kind allows it
        rcases hwhy with h | h | h <;> omega
      · exact ⟨ret_rax _ _, by rw [← hs']; rfl⟩
    have goal : (getrandom s').getReg .rax = BitVec.ofNat 64 data.length ∧
        (getrandom s').mem = (s.storeBytes (s.getReg .rdi) data).mem := by
      by_cases h1 : data.length = grndMost s
      · have hf : fates = [] := by simp [fates, h1]
        obtain ⟨w', e⟩ := getrandom_of_none hbad' (hfates.trans hf)
        rw [e, hmost]
        exact hdeliver _ _ (Nat.le_refl _) (writableRun_eq hcan' (.inl h1))
      · by_cases h2 : grndMayStop s = true ∧ 0 < data.length
        · have hf : fates = [.short data.length] := by simp [fates, h1, h2]
          obtain ⟨w', e⟩ := getrandom_of_short hbad' (hfates.trans hf) (hstop.trans h2.1) h2.2
          rw [e, hmost]
          exact hdeliver _ _ (Nat.min_le_right _ _) (writableRun_eq hcan' (.inl (by omega)))
        · have hf : fates = [] := by simp [fates, h1, h2]
          obtain ⟨w', e⟩ := getrandom_of_none hbad' (hfates.trans hf)
          rw [e, hmost]
          rcases hwhy with h | h | h
          · exact absurd h h1
          · exact absurd h h2
          · refine hdeliver _ _ (Nat.le_refl _) (writableRun_eq hcan' (.inr ⟨h.2.1, ?_⟩))
            rw [hperm, hreg]; exact h.2.2
    exact ⟨goal.1.trans (show (ret _ _).getReg .rax = _ from ret_rax _ _).symm, goal.2⟩

/-- **A full buffer is not promised.** There is a state in which `getrandom`,
asked for 512 bytes with every one of them writable, may answer that it
stored one. A program that goes on to use all 512 uses 511 that the call
left as they were. -/
theorem Getrandom.may_stop_early :
    ∃ s t : State, Getrandom s t ∧ (s.getReg .rsi).toNat = 512 ∧
      s.canWrite (s.getReg .rdi) 512 = true ∧ t.getReg .rax = 1 ∧
      ∀ x : BitVec 64, 1 ≤ (x - s.getReg .rdi).toNat → t.mem x = s.mem x := by
  let s : State := ((State.init.setPerm 0x10000 512 .rw).setReg .rdi 0x10000).setReg .rsi 512
  have h : Getrandom s (give s (s.getReg .rdi) [0] (BitVec.ofNat 64 1) s.world) :=
    .filled (s := s) [0] s.world (by decide) ⟨_, _, rfl⟩ (by decide) (by decide)
      (.inr (.inl ⟨by decide, by decide⟩))
  refine ⟨s, _, h, by decide, by decide +kernel, ret_rax _ _, fun x hx => ?_⟩
  show (s.storeBytes (s.getReg .rdi) [0]).mem x = s.mem x
  rw [State.mem_storeBytes _ _ _ _ (by decide), List.getElem?_eq_none (by simpa using hx)]
  rfl

/-- Only bytes that were not accessible change. -/
theorem mmap_frame (s : State) : Frame s (mmap s) := by
  simp only [mmap]
  split
  · exact Frame.of_eq rfl rfl
  · split
    · exact Frame.of_eq rfl rfl
    · split
      · exact Frame.of_eq rfl rfl
      · split
        · next a _ hok =>
          obtain ⟨hal, -, htop, hun⟩ := hok
          have hsz4 : ((s.getReg .rsi).toNat + 4095) / 4096 * 4096 % 4096 = 0 := by omega
          generalize ((s.getReg .rsi).toNat + 4095) / 4096 * 4096 = size at htop hun hsz4 ⊢
          have hT : addrTop = 0x7ffffffff000 := rfl
          have hfit64 : a.toNat + size ≤ addrTop := by omega
          refine ⟨fun x hx _ => ?_, fun x hx _ => ?_⟩
          · show (s.mapZero a size).perm x = s.perm x
            rw [State.perm_mapZero s hal hsz4 hfit64]
            split
            · next hin => exact absurd (perm_of_unmapped hal hfit64 hun hin) hx
            · rfl
          · show (s.mapZero a size).mem x = s.mem x
            rw [State.mem_mapZero s hal hsz4 hfit64]
            split
            · next hin => exact absurd (perm_of_unmapped hal hfit64 hun hin) hx
            · rfl
        · exact Frame.of_eq rfl rfl

/-! ## Memory the program owns -/

/-- Anything readable lies apart from a range found inaccessible. -/
theorem disjoint_of_unmapped {a b : BitVec 64} {size m k : Nat}
    (hU : ∀ x : BitVec 64, (x - a).toNat < size → s.perm x = .none) (hsize : size < 2 ^ 64)
    (hk : k ≤ size) (hm : m < 2 ^ 64) (hr : s.canRead b m = true) : Disjoint a k b m := by
  rw [State.canRead_iff] at hr
  refine ⟨fun hm0 => ?_, fun hk0 => ?_⟩
  · apply Classical.byContradiction
    intro hlt
    have hb := hr 0 (by omega)
    rw [show b + BitVec.ofNat 64 0 = b by simp, hU b (by bv_omega)] at hb
    exact absurd hb (by decide)
  · apply Classical.byContradiction
    intro hlt
    have hb := hr (a - b).toNat (by bv_omega)
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, show b + (a - b) = a by bv_omega,
      hU a (by simp; omega)] at hb
    exact absurd hb (by decide)

theorem munmap_rip (s : State) : (munmap s).rip = s.rip := by
  simp only [munmap]
  split <;> rfl

/-- Only writable memory is given back. -/
theorem munmap_frame (s : State) : Frame s (munmap s) := by
  simp only [munmap]
  split
  · next hok =>
    obtain ⟨hal, -, htop, hall⟩ := hok
    have hsz4 : ((s.getReg .rsi).toNat + 4095) / 4096 * 4096 % 4096 = 0 := by omega
    generalize ((s.getReg .rsi).toNat + 4095) / 4096 * 4096 = size at htop hall hsz4 ⊢
    have hT : addrTop = 0x7ffffffff000 := rfl
    have hfit : (s.getReg .rdi).toNat + size ≤ addrTop := by omega
    refine ⟨fun x hx hw => ?_, fun x _ _ => rfl⟩
    show (s.unmap _ size).perm x = s.perm x
    rw [State.perm_unmap s hal hsz4 hfit]
    split
    · next hin =>
      have := State.allBelow_iff.mp hall _ hin
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq,
        show s.getReg .rdi + (x - s.getReg .rdi) = x by bv_omega] at this
      rcases of_decide_eq_true this with hwr | hnone
      · rw [hwr] at hw; cases hw
      · exact absurd hnone hx
    · rfl
  · exact Frame.of_eq rfl rfl

end Linux

/-! ## The calls, as the type system sees them -/

/-- An operating system that does what `linux` does wherever `linux` lets
the program go on. The rules for the calls that return hold for any such:
for `linux` itself, and for `linux` made to refuse some exits. -/
class LikeLinux (sys : Syscall) : Prop where
  next : ∀ {s t : State}, linux s = .next t → sys s = .next t

instance : LikeLinux linux := ⟨id⟩

instance (Q : BitVec 32 → Prop) : LikeLinux (linux.exitsOnly Q) := ⟨Syscall.exitsOnly_next⟩

/-- An operating system that does what `linux` does wherever `linux` lets
the program go on, for every call but `write`. The rules for the other
calls that return hold for any such: also for a system made to refuse some
writes. -/
class LikeLinuxNW (sys : Syscall) : Prop where
  next : ∀ {s t : State}, s.getReg .rax ≠ 1 → linux s = .next t → sys s = .next t

instance {sys : Syscall} [LikeLinux sys] : LikeLinuxNW sys := ⟨fun _ h => LikeLinux.next h⟩

instance {sys : Syscall} [LikeLinuxNW sys] (R : BitVec 64 → List (BitVec 8) → Prop) :
    LikeLinuxNW (sys.writesOnly R) :=
  ⟨fun hne h => (Syscall.writesOnly_eq (fun e => absurd e hne)).trans (LikeLinuxNW.next hne h)⟩

variable {sys : Syscall} [LikeLinuxNW sys]

/-! ## Ending, for the checker

One statement of when a call ends the program, for each system a program is
typed against: the checker's walk ends a block at such a call. -/

/-! ## Memory the program cannot write stays as it was -/

/-- No system call changes a byte that is accessible but not writable, in
permission or in contents. -/
theorem linux_frame (s : State) : (linux s).All (Frame s) := by
  unfold linux
  by_cases h : s.getReg .rax = 60
  · rw [h]
    simp only [↓reduceIte]
    trivial
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 231
  · rw [h]
    simp only [↓reduceIte]
    trivial
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 1
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.write_only s).frame
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 0
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.read_fills s).frame (Nat.le_of_lt (s.getReg .rdx).isLt)
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 9
  · rw [h]
    simp only [↓reduceIte]
    split
    · exact Linux.mmap_frame s
    · trivial
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 11
  · rw [h]
    simp only [↓reduceIte]
    exact Linux.munmap_frame s
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 3
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.close_only s).frame
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 5
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.fstat_fills s).frame (by decide)
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 8
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.lseek_only s).frame
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 228
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.clockGettime_fills s).frame (by decide)
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 257
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.openat_only s).frame
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 74
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.fsync_only s).frame
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 75
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.fsync_only s).frame
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 39
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.getpid_only s).frame
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 318
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.getrandom_fills s).frame (Nat.le_of_lt (s.getReg .rsi).isLt)
  simp only [h, ↓reduceIte]
  clear h
  exact Frame.of_eq rfl rfl

namespace Linux

/-- **What a call that returns leaves of the registers**: all but `rax`,
which has its answer, and `rcx` and `r11`, which the kernel uses. -/
def Keeps (s t : State) : Prop :=
  ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r11 → t.getReg r = s.getReg r

theorem ret_keeps (s : State) (v : BitVec 64) : Keeps s (ret s v) := by
  intro r h1 h2 h3
  show (((s.setReg .rax v).setReg .rcx s.rip).setReg .r11 (s.world.saved 0)).getReg r = _
  rw [State.getReg_setReg_other _ _ _ _ h3, State.getReg_setReg_other _ _ _ _ h2,
    State.getReg_setReg_other _ _ _ _ h1]

theorem OnlyWorld.keeps {s t : State} (h : OnlyWorld s t) : Keeps s t := by
  obtain ⟨v, w, rfl⟩ := h
  exact ret_keeps { s with world := w } v

theorem Fills.keeps {s t : State} {buf : BitVec 64} {room : Nat} (h : Fills s buf room t) :
    Keeps s t := by
  rcases h with h | ⟨data, v, w, -, -, rfl⟩
  · exact h.keeps
  · exact ret_keeps { s.storeBytes buf data with world := w } v

theorem mmap_keeps (s : State) : Keeps s (mmap s) := by
  simp only [mmap]
  repeat' split
  all_goals exact ret_keeps _ _

theorem munmap_keeps (s : State) : Keeps s (munmap s) := by
  simp only [munmap]
  split <;> exact ret_keeps _ _

end Linux

/-- **A system call that returns changes no register but `rax`, `rcx` and
`r11`.** -/
theorem linux_keeps (s : State) : (linux s).All (Linux.Keeps s) := by
  unfold linux
  by_cases h : s.getReg .rax = 60
  · rw [h]
    simp only [↓reduceIte]
    trivial
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 231
  · rw [h]
    simp only [↓reduceIte]
    trivial
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 1
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.write_only s).keeps
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 0
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.read_fills s).keeps
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 9
  · rw [h]
    simp only [↓reduceIte]
    split
    · exact Linux.mmap_keeps s
    · trivial
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 11
  · rw [h]
    simp only [↓reduceIte]
    exact Linux.munmap_keeps s
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 3
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.close_only s).keeps
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 5
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.fstat_fills s).keeps
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 8
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.lseek_only s).keeps
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 228
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.clockGettime_fills s).keeps
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 257
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.openat_only s).keeps
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 74
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.fsync_only s).keeps
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 75
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.fsync_only s).keeps
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 39
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.getpid_only s).keeps
  simp only [h, ↓reduceIte]
  clear h
  by_cases h : s.getReg .rax = 318
  · rw [h]
    simp only [↓reduceIte]
    exact (Linux.getrandom_fills s).keeps
  simp only [h, ↓reduceIte]
  clear h
  exact Linux.ret_keeps s _


end TypedAsm

