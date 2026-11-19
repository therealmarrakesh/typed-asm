import TypedAsm.Instr
import Std.Data.TreeMap

/-!
# Machine state

The registers, flags, instruction pointer and memory, with the basic operations
for reading and writing registers.

Memory has a byte at every address, and separately a permission for every
page that says whether programs may read or write its bytes. Only addresses
below `addrTop` can be accessible: the rest are ones no program can have
memory at.

The registers and memory are stored so that the model runs at a steady
speed however long the run: the registers as sixteen fields, memory as an
ordered table of the bytes written so far. Both keep their cost when an
older state is still in use, which a run that reports where it stopped needs. Everything else sees them only as
the functions `State.regs` and `State.mem`, and the two facts about writing
them, `State.regs_setReg` and `State.mem_store8` (in `Memory`).
-/

namespace TypedAsm

/-- The number of bits in an operand of the given width. It is reducible so
that `BitVec Width.w64.bits` and `BitVec 64` are interchangeable in proofs. -/
@[reducible] def Width.bits : Width → Nat
  | .w32 => 32
  | .w64 => 64

/-- The four modelled status flags. `none` means the value is unknown, which is
how flags the hardware leaves undefined are represented. -/
structure Flags where
  cf : Option Bool
  zf : Option Bool
  sf : Option Bool
  of : Option Bool
  deriving DecidableEq, Repr

/-- What a program may do with a byte of memory. -/
inductive Perm
  /-- Not accessible. -/
  | none
  /-- Readable only. -/
  | ro
  /-- Readable and writable. -/
  | rw
  /-- Readable and executable: this is where code lives. There is no
  permission that is both writable and executable, so code cannot be changed. -/
  | rx
  deriving DecidableEq, Repr

def Perm.readable : Perm → Bool
  | .none => false
  | _ => true

def Perm.writable : Perm → Bool
  | .rw => true
  | _ => false

def Perm.executable : Perm → Bool
  | .rx => true
  | _ => false

theorem Perm.readable_of_writable {p : Perm} (h : p.writable = true) : p.readable = true := by
  cases p <;> simp_all [Perm.readable, Perm.writable]

/-- The errors a call may answer with where the choice is the kernel's and
not settled by what the program asked: the call would have to wait and was
asked not to, the device failed, there is no room left, the reader of a pipe
has gone, the file would grow past a limit, or past the user's quota, the
process or the system has too many files open, or there is no memory. -/
inductive Errno
  | again | io | nospc | pipe | fbig | dquot | mfile | nfile | nomem
  deriving DecidableEq

/-- The number a call hands back for an error: the negated error number. -/
def Errno.code : Errno → BitVec 64
  | .again => -11
  | .io => -5
  | .nospc => -28
  | .pipe => -32
  | .fbig => -27
  | .dquot => -122
  | .mfile => -24
  | .nfile => -23
  | .nomem => -12

/-- The errors a `write` may fail with by the kernel's choice. -/
def Errno.ofWrite : Errno → Bool
  | .again | .io | .nospc | .pipe | .fbig | .dquot => true
  | _ => false

/-- The errors an `openat` may fail with by the kernel's choice. -/
def Errno.ofOpen : Errno → Bool
  | .mfile | .nfile | .nomem | .io | .nospc | .dquot => true
  | _ => false

/-- What one `read` from the outside world delivers: some bytes, or an
error. -/
inductive ReadEvent
  | bytes (data : List (BitVec 8))
  | error (e : Errno)

/-- What the kernel does with one call, where the choice is its own and not
settled by what the program asked. -/
inductive Fate
  /-- Everything that was asked for. -/
  | full
  /-- At most this many bytes, where the call is one that may stop early. -/
  | short (n : Nat)
  /-- Nothing, and this error, where the call is one that may fail with it. -/
  | fail (e : Errno)

/-- A file: its name, and its bytes. The bytes are what it held to begin
with, overlaid by what has been written to it since, so that writing costs
the same however large the file. -/
structure File where
  /-- The name, exactly as a program must spell it to open the file. -/
  path : List (BitVec 8)
  base : Array (BitVec 8) := #[]
  over : Std.TreeMap Nat (BitVec 8) := {}
  size : Nat := base.size
  /-- Whether the program is allowed to open it for reading, and for writing. -/
  mayRead : Bool := true
  mayWrite : Bool := true

namespace File

/-- The byte at a position; zero where nothing was ever written. -/
def byte (f : File) (i : Nat) : BitVec 8 :=
  f.over.getD i (f.base.getD i 0)

/-- Up to `n` bytes from position `pos`, stopping at the end of the file. -/
def read (f : File) (pos n : Nat) : List (BitVec 8) :=
  (List.range (min n (f.size - pos))).map fun i => f.byte (pos + i)

/-- The file with `data` written at position `pos`. Writing past the end
makes the file longer; any gap reads as zero. -/
def write (f : File) (pos : Nat) (data : List (BitVec 8)) : File :=
  { f with
    over := (data.zipIdx).foldl (fun t x => t.insert (pos + x.2) x.1) f.over
    size := max f.size (pos + data.length) }

/-- The file made empty. -/
def truncate (f : File) : File :=
  { f with base := #[], over := {}, size := 0 }

/-- Everything in the file. -/
def contents (f : File) : List (BitVec 8) :=
  f.read 0 f.size

end File

/-- What a file descriptor refers to. -/
inductive Fd
  /-- The input the program is given: descriptor 0 to begin with. -/
  | stdin
  /-- The program's output: descriptors 1 and 2 to begin with. -/
  | stdout
  /-- An open file: which one, the position of the next read or write, what
  it was opened for, and whether every write goes to the end. -/
  | file (index pos : Nat) (canRead canWrite append : Bool)

/-- The world outside the machine, as far as a program can observe it: what
is still to be read, one event per `read`, everything written so far, the
files there are, and which descriptors are open. Only system calls touch it.
Nothing is assumed about it, so a result proved for every state holds
whatever the program is given to read and whatever files it finds. -/
structure World where
  input : List ReadEvent := []
  /-- The bytes of each `write` so far, most recent first. -/
  writes : List (List (BitVec 8)) := []
  /-- Where the kernel would put the memory of each request for some, by the
  number of the request, or `none` to refuse it. Nothing is assumed about
  the choice; the model of `mmap` refuses a place that is not free. -/
  place : Nat → Option (BitVec 64) := fun _ => none
  /-- How many requests for memory have been made. -/
  asked : Nat := 0
  /-- The open file descriptors, by number. -/
  fds : List (Nat × Fd) := [(0, .stdin), (1, .stdout), (2, .stdout)]
  /-- The files there are. There are no directories: a file is found by its
  whole name, spelled exactly. -/
  files : Array File := #[]
  /-- Whether the program may create files. -/
  mayCreate : Bool := true
  /-- The random bytes the kernel would hand out, in order, and how many
  have been handed out. -/
  random : Nat → BitVec 8 := fun _ => 0
  drawn : Nat := 0
  /-- What the kernel does with each coming call in which it has a choice:
  one entry for each `write`, each `openat`, each `close`, each `fsync`,
  each `read` of a file, and each `getrandom` whose flags it accepts, in the
  order they are made. A choice the call does
  not allow counts as `full`, and so does having none left. What a `read` of
  the program's input delivers is in `input`. -/
  fates : List Fate := []
  /-- The clocks, by number, at each successive asking, in nanoseconds: what
  a clock that can be set reads, or how far a clock that only goes forward
  has moved on since it was last read. -/
  time : Nat → Nat → Nat := fun _ _ => 0
  /-- How many times the time has been asked. -/
  asks : Nat := 0
  /-- What each clock that only goes forward read when it was last read. -/
  moved : Nat → Nat := fun _ => 0
  /-- Whether there is a clock with a number other than the standard ones:
  the clock of some process, or of a device. -/
  hasClock : Nat → Bool := fun _ => false
  /-- The number of the process. -/
  pid : Nat := 1
  /-- What the kernel leaves in `r11` at each call that returns, the next
  first: the flags it saved when the call was made, which the program's
  own flags do not say in full. -/
  saved : Nat → BitVec 64 := fun _ => 0

namespace World

/-- The world once a call has returned: what the kernel leaves in `r11` is
used, and the next call has the next. Nothing else of the world differs. -/
def spent (w : World) : World := { w with saved := fun n => w.saved (n + 1) }

/-- What a descriptor refers to, if it is open. -/
def fd? (w : World) (n : Nat) : Option Fd :=
  w.fds.lookup n

/-- Make a descriptor refer to something. -/
def setFd (w : World) (n : Nat) (fd : Fd) : World :=
  { w with fds := (n, fd) :: w.fds.filter (·.1 != n) }

/-- Close a descriptor. -/
def closeFd (w : World) (n : Nat) : World :=
  { w with fds := w.fds.filter (·.1 != n) }

/-- The lowest descriptor number not in use, which is the one the kernel
gives out next. -/
def freeFd (w : World) : Nat :=
  ((List.range (w.fds.length + 1)).find? fun i => (w.fds.lookup i).isNone).getD w.fds.length

/-- The file with a given name, if there is one. -/
def find? (w : World) (path : List (BitVec 8)) : Option Nat :=
  w.files.findIdx? (·.path == path)

end World

/-- Everything written so far, in the order it was written. -/
def World.output (w : World) : List (BitVec 8) :=
  w.writes.reverse.flatten

/-- The values of the sixteen registers. -/
structure RegFile where
  (rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64)

namespace RegFile

def get (f : RegFile) : Reg → BitVec 64
  | .rax => f.rax
  | .rcx => f.rcx
  | .rdx => f.rdx
  | .rbx => f.rbx
  | .rsp => f.rsp
  | .rbp => f.rbp
  | .rsi => f.rsi
  | .rdi => f.rdi
  | .r8 => f.r8
  | .r9 => f.r9
  | .r10 => f.r10
  | .r11 => f.r11
  | .r12 => f.r12
  | .r13 => f.r13
  | .r14 => f.r14
  | .r15 => f.r15

def set (f : RegFile) (r : Reg) (v : BitVec 64) : RegFile :=
  match r with
  | .rax => { f with rax := v }
  | .rcx => { f with rcx := v }
  | .rdx => { f with rdx := v }
  | .rbx => { f with rbx := v }
  | .rsp => { f with rsp := v }
  | .rbp => { f with rbp := v }
  | .rsi => { f with rsi := v }
  | .rdi => { f with rdi := v }
  | .r8 => { f with r8 := v }
  | .r9 => { f with r9 := v }
  | .r10 => { f with r10 := v }
  | .r11 => { f with r11 := v }
  | .r12 => { f with r12 := v }
  | .r13 => { f with r13 := v }
  | .r14 => { f with r14 := v }
  | .r15 => { f with r15 := v }

theorem get_set (f : RegFile) (r r' : Reg) (v : BitVec 64) :
    (f.set r v).get r' = if r' = r then v else f.get r' := by
  cases r <;> cases r' <;> rfl

end RegFile

/-! ## Sets of pages

Memory that a program is given while it runs comes in whole pages. Which
pages those are is kept as an ordered set of page numbers, so that asking
about one costs the same however many there are. -/

/-- The number of bytes in a page. -/
def pageSize : Nat := 4096

namespace Pages

/-- Add the numbers `first`, …, `first + count - 1`. -/
def insertRange (t : Std.TreeMap Nat Unit) (first : Nat) : Nat → Std.TreeMap Nat Unit
  | 0 => t
  | n + 1 => insertRange (t.insert (first + n) ()) first n

theorem contains_insertRange (t : Std.TreeMap Nat Unit) (first n k : Nat) :
    (insertRange t first n).contains k = (t.contains k || decide (first ≤ k ∧ k < first + n)) := by
  induction n generalizing t with
  | zero =>
    have h0 : ¬ (first ≤ k ∧ k < first + 0) := by omega
    show t.contains k = _
    rw [decide_eq_false h0, Bool.or_false]
  | succ n ih =>
    rw [insertRange, ih, Std.TreeMap.contains_insert]
    by_cases h : first + n = k
    · subst h
      simp
    · have hc : (compare (first + n) k == Ordering.eq) = false := by
        simp [h]
      rw [hc, Bool.false_or]
      congr 1
      apply decide_eq_decide.mpr
      omega

/-- Whether none of the numbers `first`, …, `first + count - 1` is there. -/
def noneIn (t : Std.TreeMap Nat Unit) (first : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => if t.contains (first + n) then false else noneIn t first n

theorem noneIn_iff (t : Std.TreeMap Nat Unit) (first n : Nat) :
    noneIn t first n = true ↔ ∀ j, j < n → t.contains (first + j) = false := by
  induction n with
  | zero => simp [noneIn]
  | succ n ih =>
    simp only [noneIn]
    constructor
    · intro h j hj
      split at h
      · cases h
      · next hc =>
        by_cases hjn : j = n
        · rw [hjn]; exact (Bool.not_eq_true _).mp hc
        · exact ih.mp h j (by omega)
    · intro h
      simp only [h n (by omega), Bool.false_eq_true, ↓reduceIte]
      exact ih.mpr (fun j hj => h j (by omega))

/-- Remove the keys `first`, …, `first + count - 1`. -/
def eraseRange (t : Std.TreeMap Nat (BitVec 8)) (first : Nat) : Nat → Std.TreeMap Nat (BitVec 8)
  | 0 => t
  | n + 1 => eraseRange (t.erase (first + n)) first n

theorem contains_eraseRange (t : Std.TreeMap Nat (BitVec 8)) (first n k : Nat) :
    (eraseRange t first n).contains k = (t.contains k && !decide (first ≤ k ∧ k < first + n)) := by
  induction n generalizing t with
  | zero =>
    have h0 : ¬ (first ≤ k ∧ k < first + 0) := by omega
    show t.contains k = _
    rw [decide_eq_false h0, Bool.not_false, Bool.and_true]
  | succ n ih =>
    rw [eraseRange, ih, Std.TreeMap.contains_erase]
    by_cases h : first + n = k
    · subst h
      simp
    · have hc : (compare (first + n) k != Ordering.eq) = true := by
        simp [h]
      rw [hc, Bool.true_and]
      congr 2
      apply decide_eq_decide.mpr
      omega

theorem getD_eraseRange (t : Std.TreeMap Nat (BitVec 8)) (first n k : Nat) (d : BitVec 8) :
    (eraseRange t first n).getD k d = if first ≤ k ∧ k < first + n then d else t.getD k d := by
  induction n generalizing t with
  | zero =>
    have h0 : ¬ (first ≤ k ∧ k < first + 0) := by omega
    show t.getD k d = _
    simp only [h0, ↓reduceIte]
  | succ n ih =>
    rw [eraseRange, ih, Std.TreeMap.getD_erase]
    by_cases h : first + n = k
    · subst h
      simp
    · have hc : ¬ compare (first + n) k = Ordering.eq := by
        simp [h]
      simp only [hc, ↓reduceIte]
      by_cases h1 : first ≤ k ∧ k < first + n
      · simp only [h1, and_self, ↓reduceIte, show first ≤ k ∧ k < first + (n + 1) from ⟨h1.1, by omega⟩]
      · have h2 : ¬ (first ≤ k ∧ k < first + (n + 1)) := by omega
        simp only [h1, h2, ↓reduceIte]

/-- Give the pages `first`, …, `first + count - 1` the permission `q`. -/
def setRange (t : Std.TreeMap Nat Perm) (first : Nat) (q : Perm) : Nat → Std.TreeMap Nat Perm
  | 0 => t
  | n + 1 => setRange (t.insert (first + n) q) first q n

theorem getElem?_setRange (t : Std.TreeMap Nat Perm) (first : Nat) (q : Perm) (n k : Nat) :
    (setRange t first q n)[k]? = if first ≤ k ∧ k < first + n then some q else t[k]? := by
  induction n generalizing t with
  | zero =>
    have h0 : ¬ (first ≤ k ∧ k < first + 0) := by omega
    show t[k]? = _
    simp only [h0, ↓reduceIte]
  | succ n ih =>
    rw [setRange, ih, Std.TreeMap.getElem?_insert]
    by_cases h : first + n = k
    · subst h
      simp
    · have hc : ¬ compare (first + n) k = Ordering.eq := by
        simp [h]
      simp only [hc, ↓reduceIte]
      by_cases h1 : first ≤ k ∧ k < first + n
      · simp only [h1, and_self, ↓reduceIte, show first ≤ k ∧ k < first + (n + 1) from ⟨h1.1, by omega⟩]
      · have h2 : ¬ (first ≤ k ∧ k < first + (n + 1)) := by omega
        simp only [h1, h2, ↓reduceIte]

/-- A byte is among the `size` bytes from `a` exactly when its page is among
the pages from `a`'s, provided the range is whole pages and does not wrap. -/
theorem in_range_iff {a x : BitVec 64} {size : Nat} (hal : a.toNat % 4096 = 0)
    (hsz : size % 4096 = 0) (hfit : a.toNat + size ≤ 2 ^ 64) :
    (a.toNat / 4096 ≤ x.toNat / 4096 ∧ x.toNat / 4096 < a.toNat / 4096 + size / 4096) ↔
      (x - a).toNat < size := by
  have := x.isLt
  have := a.isLt
  rw [BitVec.toNat_sub]
  omega

end Pages

/-! ## The addresses a program can use

Not every 64-bit number is an address a program can have memory at. A
processor with 48-bit addresses faults on any access from `2 ^ 47` up to
`2 ^ 64 - 2 ^ 47`, whatever the page tables say, and the addresses above
that belong to the kernel. Linux also keeps the last page below `2 ^ 47`
from programs, so that no instruction can end exactly there. A processor
with 57-bit addresses has more, but Linux gives a program none of it unless
the program asks for an address up there.

So a permission is only ever looked up below `addrTop`; from there on every
byte is inaccessible, whatever is recorded for it. No state has readable,
writable or executable memory at an address the hardware would refuse. -/

/-- One past the highest address a program can have memory at. -/
def addrTop : Nat := 0x7ffffffff000

/-- The permission of every page: what it was to begin with, and what
pages have been given since, when memory was handed to the program or taken
back. A processor protects memory a page at a time, so that is what is
recorded: no state has two permissions inside one page. `clearFrom` is a
page from which nothing was accessible to begin with; knowing one lets a
whole range be found free without asking about each of its pages. -/
structure Perms where
  /-- The permission of each page to begin with, by page number. -/
  initial : Nat → Perm
  pages : Std.TreeMap Nat Perm := {}
  clearFrom : Nat := addrTop / 4096
  clear : ∀ k, clearFrom ≤ k → k < addrTop / 4096 → initial k = .none := by
    intro k h h'; exact absurd h' (by omega)

namespace Perms

/-- The permission of a page, by its number. -/
@[inline] def page (p : Perms) (k : Nat) : Perm :=
  (p.pages[k]?).getD (p.initial k)

@[inline] def get (p : Perms) (x : BitVec 64) : Perm :=
  if x.toNat < addrTop then p.page (x.toNat / 4096) else .none

/-- **No memory at or above `addrTop` is accessible**, in any state. -/
theorem get_top (p : Perms) {x : BitVec 64} (h : addrTop ≤ x.toNat) : p.get x = .none := by
  simp only [get, Nat.not_lt.mpr h, ↓reduceIte]

theorem lt_top_of_get (p : Perms) {x : BitVec 64} (h : p.get x ≠ .none) : x.toNat < addrTop :=
  Nat.lt_of_not_le fun hle => h (p.get_top hle)

/-- **The bytes of a page all have one permission**, in any state. -/
theorem get_page (p : Perms) {x y : BitVec 64} (h : x.toNat / 4096 = y.toNat / 4096) :
    p.get x = p.get y := by
  have hT : addrTop = 0x7ffffffff000 := rfl
  simp only [get, h]
  by_cases hx : x.toNat < addrTop
  · have hy : y.toNat < addrTop := by omega
    simp only [hx, hy, ↓reduceIte]
  · have hy : ¬ y.toNat < addrTop := by omega
    simp only [hx, hy, ↓reduceIte]

/-- The permissions given by a function of the page number. -/
def ofFun (f : Nat → Perm) : Perms :=
  { initial := f }

@[simp] theorem get_ofFun (f : Nat → Perm) (x : BitVec 64) :
    (ofFun f).get x = if x.toNat < addrTop then f (x.toNat / 4096) else .none := by
  simp [get, page, ofFun]

/-- No byte is accessible. -/
def none : Perms :=
  { initial := fun _ => .none, clearFrom := 0, clear := fun _ _ _ => rfl }

@[simp] theorem get_none (x : BitVec 64) : none.get x = .none := by
  simp [get, page, none]

/-- Give the `count` pages from page `first` on the permission `q`. -/
@[inline] def override (p : Perms) (first count : Nat) (q : Perm) : Perms :=
  if p.pages.isEmpty then
    { initial := fun k => if first ≤ k ∧ k < first + count then q else p.initial k
      clearFrom := max p.clearFrom (first + count)
      clear := fun k hk hk' => by
        have h1 : ¬ (first ≤ k ∧ k < first + count) := by omega
        simp only [h1, ↓reduceIte]
        exact p.clear k (by omega) hk' }
  else ofFun fun k => if first ≤ k ∧ k < first + count then q else p.page k

theorem get_override (p : Perms) (first count : Nat) (q : Perm) (x : BitVec 64) :
    (p.override first count q).get x =
      if x.toNat < addrTop ∧ first ≤ x.toNat / 4096 ∧ x.toNat / 4096 < first + count then q
      else p.get x := by
  by_cases hx : x.toNat < addrTop
  · unfold override
    split
    · next he =>
      have hc : ∀ k, p.pages[k]? = Option.none := fun k =>
        Std.TreeMap.getElem?_eq_none_of_contains_eq_false (Std.TreeMap.contains_of_isEmpty he)
      simp only [get, page, hc, Std.TreeMap.getElem?_emptyc, Option.getD_none, hx, true_and,
        ↓reduceIte]
    · rw [get_ofFun]
      simp only [get, hx, true_and, ↓reduceIte]
  · rw [get_top _ (Nat.le_of_not_lt hx), get_top _ (Nat.le_of_not_lt hx)]
    simp only [hx, false_and, ↓reduceIte]

/-- Give the pages of the `size` bytes starting at `a` the permission `q`. -/
def setRange (p : Perms) (a : BitVec 64) (size : Nat) (q : Perm) : Perms :=
  { p with pages := Pages.setRange p.pages (a.toNat / 4096) q (size / 4096) }

theorem get_setRange (p : Perms) {a : BitVec 64} {size : Nat} (q : Perm) (x : BitVec 64)
    (hal : a.toNat % 4096 = 0) (hsz : size % 4096 = 0) (hfit : a.toNat + size ≤ addrTop) :
    (p.setRange a size q).get x = if (x - a).toNat < size then q else p.get x := by
  have htop : addrTop = 0x7ffffffff000 := rfl
  have key := Pages.in_range_iff (x := x) hal hsz (by omega)
  simp only [get, page, setRange, Pages.getElem?_setRange]
  by_cases h : (x - a).toNat < size
  · have hp := key.mpr h
    have hx : x.toNat < addrTop := by
      rw [BitVec.toNat_sub] at h
      have := x.isLt
      have := a.isLt
      omega
    simp only [hp, and_self, ↓reduceIte, h, Option.getD_some, hx]
  · have h' := mt key.mp h
    simp only [h', ↓reduceIte, h]

/-- Make the pages of the `size` bytes starting at `a` readable and writable. -/
def mapRange (p : Perms) (a : BitVec 64) (size : Nat) : Perms :=
  p.setRange a size .rw

theorem get_mapRange (p : Perms) {a : BitVec 64} {size : Nat} (x : BitVec 64)
    (hal : a.toNat % 4096 = 0) (hsz : size % 4096 = 0) (hfit : a.toNat + size ≤ addrTop) :
    (p.mapRange a size).get x = if (x - a).toNat < size then .rw else p.get x :=
  get_setRange p .rw x hal hsz hfit

end Perms

/-- The contents of memory: the bytes written so far, over what was there to
begin with. Pages handed out fresh are kept apart: they start as zero, and
what is written to them goes in a table of its own, so that making a page
fresh never has to look for bytes written there before. -/
structure Memory where
  initial : BitVec 64 → BitVec 8
  written : Std.TreeMap Nat (BitVec 8) := {}
  /-- The pages handed out fresh. -/
  zeroed : Std.TreeMap Nat Unit := {}
  /-- The bytes written to fresh pages. -/
  fresh : Std.TreeMap Nat (BitVec 8) := {}
  /-- Only fresh pages have bytes in `fresh`. -/
  inv : ∀ k, fresh.contains k = true → zeroed.contains (k / 4096) = true := by
    intro k h; simp at h

namespace Memory

def get (m : Memory) (x : BitVec 64) : BitVec 8 :=
  if m.zeroed.contains (x.toNat / 4096) then m.fresh.getD x.toNat 0
  else m.written.getD x.toNat (m.initial x)

def set (m : Memory) (a : BitVec 64) (v : BitVec 8) : Memory :=
  if h : m.zeroed.contains (a.toNat / 4096) = true then
    { m with
      fresh := m.fresh.insert a.toNat v
      inv := fun k hk => by
        rw [Std.TreeMap.contains_insert] at hk
        by_cases hka : a.toNat = k
        · rw [← hka]; exact h
        · have hc : (compare a.toNat k == Ordering.eq) = false := by
            simp [hka]
          rw [hc, Bool.false_or] at hk
          exact m.inv k hk }
  else { m with written := m.written.insert a.toNat v }

theorem get_set (m : Memory) (a x : BitVec 64) (v : BitVec 8) :
    (m.set a v).get x = if x = a then v else m.get x := by
  have hne : x ≠ a → ¬ a.toNat = x.toNat := fun h e => h (BitVec.eq_of_toNat_eq e.symm)
  unfold set
  split
  · next hz =>
    simp only [get, Std.TreeMap.getD_insert]
    by_cases h : x = a
    · subst h
      simp [hz]
    · simp [h, hne h]
  · next hz =>
    simp only [get, Std.TreeMap.getD_insert]
    by_cases h : x = a
    · subst h
      simp [hz]
    · simp [h, hne h]

/-- Write a list of bytes at consecutive addresses. -/
def setBytes (m : Memory) (a : BitVec 64) : List (BitVec 8) → Memory
  | [] => m
  | b :: bs => (m.set a b).setBytes (a + 1) bs

theorem setBytes_nil (m : Memory) (a : BitVec 64) : m.setBytes a [] = m :=
  rfl

theorem get_setBytes (m : Memory) (a x : BitVec 64) (l : List (BitVec 8)) (hlen : l.length ≤ 2 ^ 64) :
    (m.setBytes a l).get x = (l[(x - a).toNat]?).getD (m.get x) := by
  induction l generalizing m a with
  | nil => simp [setBytes]
  | cons b bs ih =>
    simp only [List.length_cons] at hlen
    simp only [setBytes]
    rw [ih _ _ (by omega), get_set]
    by_cases hxa : x = a
    · subst hxa
      have h1 : (x - (x + 1)).toNat = 2 ^ 64 - 1 := by bv_omega
      have h2 : bs[(x - (x + 1)).toNat]? = none := by
        rw [h1]; exact List.getElem?_eq_none (by omega)
      rw [h2]
      simp
    · have h1 : (x - a).toNat = (x - (a + 1)).toNat + 1 := by bv_omega
      rw [h1]
      simp [hxa]

/-- Make the pages of the `size` bytes starting at `a` fresh: all zero. Bytes
written to a page that was already fresh are removed; for a page that was
not, there are none to remove. -/
def zero (m : Memory) (a : BitVec 64) (size : Nat) : Memory :=
  { m with
    zeroed := Pages.insertRange m.zeroed (a.toNat / 4096) (size / 4096)
    fresh :=
      if Pages.noneIn m.zeroed (a.toNat / 4096) (size / 4096) then m.fresh
      else Pages.eraseRange m.fresh a.toNat size
    inv := fun k hk => by
      rw [Pages.contains_insertRange]
      have hold : m.fresh.contains k = true := by
        split at hk
        · exact hk
        · rw [Pages.contains_eraseRange] at hk
          exact (Bool.and_eq_true _ _ ▸ hk).1
      simp [m.inv k hold] }

theorem get_zero (m : Memory) {a : BitVec 64} {size : Nat} (x : BitVec 64)
    (hal : a.toNat % 4096 = 0) (hsz : size % 4096 = 0) (hfit : a.toNat + size ≤ 2 ^ 64) :
    (m.zero a size).get x = if (x - a).toNat < size then 0 else m.get x := by
  have key := Pages.in_range_iff (x := x) hal hsz hfit
  have hx := x.isLt
  have ha := a.isLt
  simp only [get, zero, Pages.contains_insertRange]
  by_cases h : (x - a).toNat < size
  · -- a byte of the range: its page is fresh, and nothing is written there
    have hpage := key.mpr h
    have hin : a.toNat ≤ x.toNat ∧ x.toNat < a.toNat + size := by
      rw [BitVec.toNat_sub] at h
      omega
    simp only [hpage, and_self, decide_true, Bool.or_true, ↓reduceIte, h]
    split
    · next hnone =>
      -- the page was not fresh before, so it had no bytes in `fresh`
      have hz := (Pages.noneIn_iff _ _ _).mp hnone (x.toNat / 4096 - a.toNat / 4096) (by omega)
      rw [show a.toNat / 4096 + (x.toNat / 4096 - a.toNat / 4096) = x.toNat / 4096 by omega] at hz
      apply Std.TreeMap.getD_eq_fallback_of_contains_eq_false
      cases hc : m.fresh.contains x.toNat with
      | false => rfl
      | true => rw [m.inv _ hc] at hz; cases hz
    · rw [Pages.getD_eraseRange]
      simp only [hin, and_self, ↓reduceIte]
  · have hpage := mt key.mp h
    have hout : ¬ (a.toNat ≤ x.toNat ∧ x.toNat < a.toNat + size) := by
      rw [BitVec.toNat_sub] at h
      omega
    simp only [hpage, decide_false, Bool.or_false, h, ↓reduceIte]
    by_cases hz : m.zeroed.contains (x.toNat / 4096) = true
    · simp only [hz, ↓reduceIte]
      split
      · rfl
      · rw [Pages.getD_eraseRange]
        simp only [hout, ↓reduceIte]
    · simp only [hz, Bool.false_eq_true, ↓reduceIte]

end Memory

-- How memory is stored is nobody's business but the facts above:
-- sealing it keeps proofs from wandering into the tables.
attribute [irreducible] Memory.get Memory.set Memory.setBytes Memory.zero


structure State where
  regFile : RegFile
  flags : Flags
  rip : BitVec 64
  memory : Memory
  perms : Perms
  world : World := {}
  /-- Whether the processor has 57-bit addresses, not 48-bit. It decides
  only which fault an address in between raises. -/
  wide : Bool := false

/-- The value of each register. -/
def State.regs (s : State) : Reg → BitVec 64 :=
  s.regFile.get

/-- The byte at each address. -/
def State.mem (s : State) : BitVec 64 → BitVec 8 :=
  s.memory.get

/-- What a program may do with the byte at each address. -/
def State.perm (s : State) : BitVec 64 → Perm :=
  s.perms.get

namespace State

/-- A state with every register and memory byte zero, every flag clear, and
no accessible memory. -/
def init : State where
  regFile := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  flags := ⟨some false, some false, some false, some false⟩
  rip := 0
  memory := { initial := fun _ => 0 }
  perms := .none

/-- The number of the first page the `len` bytes at `base` touch, and how
many pages they touch. -/
def pagesOf (base len : Nat) : Nat × Nat :=
  (base / 4096, if len = 0 then 0 else (base + len - 1) / 4096 - base / 4096 + 1)

/-- Set the permission of the `len` bytes starting at `base`, which is to
say of every page they touch: a permission is a page's. -/
def setPerm (s : State) (base len : BitVec 64) (p : Perm) : State :=
  { s with
    perms := s.perms.override (pagesOf base.toNat len.toNat).1 (pagesOf base.toNat len.toNat).2 p }

theorem perm_setPerm (s : State) (base len x : BitVec 64) (p : Perm) :
    (s.setPerm base len p).perm x =
      if x.toNat < addrTop ∧ (pagesOf base.toNat len.toNat).1 ≤ x.toNat / 4096 ∧
          x.toNat / 4096 < (pagesOf base.toNat len.toNat).1 + (pagesOf base.toNat len.toNat).2
      then p else s.perm x := by
  simp only [State.perm, setPerm, Perms.get_override]

/-- The bytes named get the permission, where they are addresses a program
can have memory at. -/
theorem perm_setPerm_in (s : State) {base len x : BitVec 64} (p : Perm) (hx : x.toNat < addrTop)
    (hin : base.toNat ≤ x.toNat ∧ x.toNat < base.toNat + len.toNat) :
    (s.setPerm base len p).perm x = p := by
  rw [perm_setPerm]
  have h : (pagesOf base.toNat len.toNat).1 ≤ x.toNat / 4096 ∧
      x.toNat / 4096 < (pagesOf base.toNat len.toNat).1 + (pagesOf base.toNat len.toNat).2 := by
    simp only [pagesOf]
    split <;> omega
  simp only [hx, h, and_self, ↓reduceIte]

/-- A byte whose page none of the bytes named are in keeps its permission. -/
theorem perm_setPerm_out (s : State) {base len x : BitVec 64} (p : Perm)
    (hout : x.toNat / 4096 < base.toNat / 4096 ∨
      (base.toNat + len.toNat - 1) / 4096 < x.toNat / 4096) :
    (s.setPerm base len p).perm x = s.perm x := by
  rw [perm_setPerm]
  have h : ¬ ((pagesOf base.toNat len.toNat).1 ≤ x.toNat / 4096 ∧
      x.toNat / 4096 < (pagesOf base.toNat len.toNat).1 + (pagesOf base.toNat len.toNat).2) := by
    simp only [pagesOf]
    split <;> omega
  simp only [h, and_false, ↓reduceIte]

/-- **The bytes of a page all have one permission**, in any state. -/
theorem perm_page (s : State) {x y : BitVec 64} (h : x.toNat / 4096 = y.toNat / 4096) :
    s.perm x = s.perm y :=
  s.perms.get_page h

/-- **No memory at or above `addrTop` is accessible**, in any state. -/
theorem perm_top (s : State) {x : BitVec 64} (h : addrTop ≤ x.toNat) : s.perm x = .none :=
  s.perms.get_top h

/-- A byte that is accessible in any way is below `addrTop`. -/
theorem lt_top_of_perm (s : State) {x : BitVec 64} (h : s.perm x ≠ .none) : x.toNat < addrTop :=
  s.perms.lt_top_of_get h

/-- Read a full 64-bit register. -/
def getReg (s : State) (r : Reg) : BitVec 64 :=
  s.regs r

/-- Overwrite a full 64-bit register. -/
def setReg (s : State) (r : Reg) (v : BitVec 64) : State :=
  { s with regFile := s.regFile.set r v }

/-- Writing a register changes that register and no other. -/
theorem regs_setReg (s : State) (r r' : Reg) (v : BitVec 64) :
    (s.setReg r v).regs r' = if r' = r then v else s.regs r' :=
  RegFile.get_set _ _ _ _

/-- Read a register at the given width. The width of the result depends on `w`. -/
def readReg (s : State) (w : Width) (r : Reg) : BitVec w.bits :=
  (s.getReg r).setWidth w.bits

/-- Write a register at the given width. A 32-bit write clears the upper half. -/
def writeReg (s : State) (w : Width) (r : Reg) (v : BitVec w.bits) : State :=
  s.setReg r (v.setWidth 64)

/-- Reading a register just written gives the written value. -/
theorem getReg_setReg_same (s : State) (r : Reg) (v : BitVec 64) :
    (s.setReg r v).getReg r = v := by
  simp [getReg, regs_setReg]

/-- Writing one register leaves every other register unchanged. -/
theorem getReg_setReg_other (s : State) (r r' : Reg) (v : BitVec 64) (h : r' ≠ r) :
    (s.setReg r v).getReg r' = s.getReg r' := by
  simp [getReg, regs_setReg, h]

/-- After a 32-bit write, the upper 32 bits of the register are zero,
whatever the register held before and whatever value was written. -/
theorem writeReg_w32_upper_zero (s : State) (r : Reg) (v : BitVec 32) :
    ((s.writeReg .w32 r v).getReg r).extractLsb 63 32 = 0 := by
  simp only [writeReg, getReg_setReg_same]
  show (BitVec.setWidth 64 v).extractLsb 63 32 = 0
  apply BitVec.eq_of_toNat_eq
  have := v.isLt
  have h0 : (0 : BitVec (63 - 32 + 1)).toNat = 0 := rfl
  rw [h0, BitVec.extractLsb_toNat, BitVec.toNat_setWidth]
  omega

end State

end TypedAsm
