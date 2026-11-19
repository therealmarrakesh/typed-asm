import TypedAsm
import TypedAsm.U.Checked

/-!
# A store into the middle of a row of values

```asm
_start:
     sub   rsp, 8
     mov   rdi, rsp
     call  fill
     movzx eax, byte [rsp + k]   ; one of the bytes fill left as they were
     lea   rbx, [table]
     movzx edx, byte [rbx + rax]
     xor   edi, edi
     mov   eax, 60
     syscall
fill:                            ; rdi: eight bytes lent
     mov   eax, 7                ; six bytes, each at most seven
     mov   [rdi], al
     ...
     mov   [rdi + 5], al
     mov   eax, 0xC8C8C8C8
     mov   [rdi + 1], eax        ; four bytes over the second to the fifth
     mov   eax, 2
     mov   [rdi + 5], al         ; a byte of the row's kind over its last
     ret
table: 8 bytes
```

The four bytes stored over the middle of the row leave the byte before
them and the byte after them known as they were, each a row of its own; and
the byte then stored over the last is of the row's kind, so that row stays.
The function's type says so of the first byte and the sixth, and the read
through the table is typed from either; from a byte stored over it is not.
-/

open TypedAsm TypedAsm.U

namespace Tests.Written.Middle

inductive L
  | start | fill | table
  deriving DecidableEq, Hashable

/-- A number put in `eax`, and its low byte stored so far past `rdi`. -/
def st (o : BitVec 32) (v : BitVec 32) : List (Asm L) :=
  [.ins (.mov .w32 (.rm_i (.reg .rax) v)), .ins (.store8 (.sib (some .rdi) none o) .rax)]

/-- The program, reading the byte so far into what the function filled. -/
def codeOf (k : BitVec 32) : List (Asm L) := [
  .label .start,
  .ins (.alu .sub .w64 (.rm_i (.reg .rsp) 8)),
  .ins (.mov .w64 (.rm_r (.reg .rdi) .rsp)),
  .call .fill,
  .ins (.movzx .w32 .rax .w8 (.mem (.sib (some .rsp) none k))),
  .ref (.lea .w64 .rbx (.rip 0)) .table,
  .ins (.movzx .w32 .rdx .w8 (.mem (.sib (some .rbx) (some (.rax, .s1)) 0))),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .fill] ++ st 0 7 ++ st 1 3 ++ st 2 5 ++ st 3 1 ++ st 4 6 ++ st 5 4 ++ [
  .ins (.mov .w32 (.rm_i (.reg .rax) 0xC8C8C8C8)),
  .ins (.mov .w32 (.rm_r (.mem (.sib (some .rdi) none 1)) .rax))] ++ st 5 2 ++ [
  .ins .ret,
  .segment .ro,
  .label .table, .bytes (List.replicate 8 0)]

def code : List (Asm L) := codeOf 0

asm_program code start .start stack 2

#guard exitsWith 0 (runMem linux 1000 start)

def blocksOn (c : List (Asm L)) : List (BitVec 64 × U.LayoutS) :=
  blocksWith c .start [(Asm.addr c (Asm.base c) .table, plainBlock 8 false)]

def pgOf (c : List (Asm L)) : Prog :=
  { code := progCode (Asm.table (Asm.base c) c), pre := preExits (· == 0)
    statics := staticIn (blocksOn c) (Asm.addr c (Asm.base c) .table) }

/-- The labels, the function said to leave the first byte and the sixth
each at most seven. -/
def labelsOf (c : List (Asm L)) : List U.Label :=
  [⟨Asm.addr c (Asm.base c) .start, inProgram 2⟩,
   ⟨Asm.addr c (Asm.base c) .fill,
     inFunction (takes := [(.was .rdi, 8)])
       (returnRows := [bytesAt (.was .rdi) 1 (.range 0 7),
         bytesAt (.was .rdi + .lit 5) 1 (.range 0 7)])⟩]

/-- Whether the program is typed, reading the byte so far in. -/
def typed (k : BitVec 32) : Bool :=
  wholeOkWith (codeOf k) .start 2 [] (blocksOn (codeOf k)) (pgOf (codeOf k)) (labelsOf (codeOf k))
    (needFuel (pgOf (codeOf k)) (labelsOf (codeOf k)) [])

#guard typed 0
#guard typed 5
-- the second byte, and the fifth: stored over. Refused
#guard !typed 1
#guard !typed 4

def blocks : List (BitVec 64 × U.LayoutS) := blocksOn code
def pg : Prog := pgOf code
def labels : List U.Label := labelsOf code

asm_checked code start .start stack 2 program pg labels labels blocks blocks exits (· == 0)

/-! ## Stored over a value whose place is not written out

```asm
_start:
     sub   rsp, 32
     mov   rdi, rsp
     call  fill                  ; four values of eight bytes, each at most seven
     mov   eax, 39
     syscall                     ; getpid: any number
     and   eax, 3
     cmp   rax, 3
     je    done                  ; so nought, one or two
     mov   qword [rsp + rax*8], 200
     mov   rax, [rsp + rax*8 + d]
     lea   rbx, [table]
     movzx edx, byte [rbx + rax]
done: ...
```

Which value is stored over is not known as a number; the values before it
are a row of as many as its place, and those after it a row of the rest.
The value next after it is one of those, whichever it was.
-/

namespace Place

inductive L
  | start | fill | done | table
  deriving DecidableEq, Hashable
/-- A number stored, all eight bytes of it, so far past `rdi`. -/
def st (o : BitVec 32) (v : BitVec 32) : List (Asm L) :=
  [.ins (.mov .w64 (.rm_i (.mem (.sib (some .rdi) none o)) v))]
/-- The program, reading the value so far past the one it stored over; and,
where that is asked, not storing over the first. -/
def codeOf (d : BitVec 32) (notFirst : Bool := false) : List (Asm L) := [
  .label .start,
  .ins (.alu .sub .w64 (.rm_i (.reg .rsp) 32)),
  .ins (.mov .w64 (.rm_r (.reg .rdi) .rsp)),
  .call .fill,
  .ins (.mov .w32 (.rm_i (.reg .rax) 39)),
  .ins .syscall,
  .ins (.alu .and .w32 (.rm_i (.reg .rax) 3)),
  .ins (.alu .cmp .w64 (.rm_i (.reg .rax) 3)),
  .jcc .e .done] ++
  (if notFirst then [.ins (.test .w64 (.reg .rax) (.reg .rax)), .jcc .e .done] else []) ++ [
  .ins (.mov .w64 (.rm_i (.mem (.sib (some .rsp) (some (.rax, .s8)) 0)) 200)),
  .ins (.mov .w64 (.r_m .rax (.sib (some .rsp) (some (.rax, .s8)) d))),
  .ref (.lea .w64 .rbx (.rip 0)) .table,
  .ins (.movzx .w32 .rdx .w8 (.mem (.sib (some .rbx) (some (.rax, .s1)) 0))),
  .label .done,
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .fill] ++ st 0 7 ++ st 8 3 ++ st 16 5 ++ st 24 1 ++ [
  .ins .ret,
  .segment .ro,
  .label .table, .bytes (List.replicate 8 0)]
def blocksOn (c : List (Asm L)) : List (BitVec 64 × U.LayoutS) :=
  blocksWith c .start [(Asm.addr c (Asm.base c) .table, plainBlock 8 false)]
def pgOf (c : List (Asm L)) : Prog :=
  { code := progCode (Asm.table (Asm.base c) c), pre := preExits (· == 0)
    statics := staticIn (blocksOn c) (Asm.addr c (Asm.base c) .table) }
/-- The labels, the function said to leave four values each at most seven. -/
def labelsOf (c : List (Asm L)) : List U.Label :=
  [⟨Asm.addr c (Asm.base c) .start, inProgram 6⟩,
   ⟨Asm.addr c (Asm.base c) .fill,
     inFunction (takes := [(.was .rdi, 32)])
       (returnRows := [cellsAt (.was .rdi) (.lit 4) (.range 0 7)])⟩]

def typed (d : BitVec 32) (notFirst : Bool := false) : Bool :=
  wholeOkWith (codeOf d notFirst) .start 6 [] (blocksOn (codeOf d notFirst))
    (pgOf (codeOf d notFirst)) (labelsOf (codeOf d notFirst))
    (needFuel (pgOf (codeOf d notFirst)) (labelsOf (codeOf d notFirst)) [])

#guard typed 8
-- the value stored itself: two hundred, past the table. Refused
#guard !typed 0
-- two values on: there may be none there. Refused
#guard !typed 16
-- the value before: there may be none. Refused
#guard !typed (-8)
-- the value before, where the one stored over is not the first: its place is
-- that of the one stored over with one taken away
#guard typed (-8) true

end Place

/-! ## A store into other memory than the row is in

```asm
_start:
     sub   rsp, 16
     mov   rdi, rsp
     lea   rsi, [rsp + 8]
     call  fill
     movzx eax, byte [rsp + 2]
     ...
fill:                            ; rdi, rsi: eight bytes lent, each
     mov   eax, 7                ; four bytes into the first, each at most seven
     mov   [rdi], al
     ...
     mov   eax, 200
     mov   [rsi + 2], al         ; and one into the second
     ret
```

What the function is lent are two pieces of memory, apart; a store into
the second leaves what is said of the first. The same store into the first
is over one of the row's bytes, and the row is no longer as said.
-/

namespace Elsewhere

inductive L
  | start | fill | table
  deriving DecidableEq, Hashable
/-- A number put in `eax`, and its low byte stored so far past `rdi`. -/
def st (o : BitVec 32) (v : BitVec 32) : List (Asm L) :=
  [.ins (.mov .w32 (.rm_i (.reg .rax) v)), .ins (.store8 (.sib (some .rdi) none o) .rax)]
/-- The program, the function's last store through such a register. -/
def codeOf (other : Reg) : List (Asm L) := [
  .label .start,
  .ins (.alu .sub .w64 (.rm_i (.reg .rsp) 16)),
  .ins (.mov .w64 (.rm_r (.reg .rdi) .rsp)),
  .ins (.lea .w64 .rsi (.sib (some .rsp) none 8)),
  .call .fill,
  .ins (.movzx .w32 .rax .w8 (.mem (.sib (some .rsp) none 2))),
  .ref (.lea .w64 .rbx (.rip 0)) .table,
  .ins (.movzx .w32 .rdx .w8 (.mem (.sib (some .rbx) (some (.rax, .s1)) 0))),
  .ins (.alu .xor .w32 (.rm_r (.reg .rdi) .rdi)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .fill] ++ st 0 7 ++ st 1 3 ++ st 2 5 ++ st 3 1 ++ [
  .ins (.mov .w32 (.rm_i (.reg .rax) 200)),
  .ins (.store8 (.sib (some other) none 2) .rax),
  .ins .ret,
  .segment .ro,
  .label .table, .bytes (List.replicate 8 0)]
def blocksOn (c : List (Asm L)) : List (BitVec 64 × U.LayoutS) :=
  blocksWith c .start [(Asm.addr c (Asm.base c) .table, plainBlock 8 false)]
def pgOf (c : List (Asm L)) : Prog :=
  { code := progCode (Asm.table (Asm.base c) c), pre := preExits (· == 0)
    statics := staticIn (blocksOn c) (Asm.addr c (Asm.base c) .table) }
/-- The labels, the function lent two buffers and said to leave the first
four bytes of the first each at most seven. -/
def labelsOf (c : List (Asm L)) : List U.Label :=
  [⟨Asm.addr c (Asm.base c) .start, inProgram 3⟩,
   ⟨Asm.addr c (Asm.base c) .fill,
     inFunction (takes := [(.was .rdi, 8), (.was .rsi, 8)])
       (returnRows := [bytesAt (.was .rdi) 4 (.range 0 7)])⟩]

def typed (other : Reg) : Bool :=
  wholeOkWith (codeOf other) .start 3 [] (blocksOn (codeOf other)) (pgOf (codeOf other))
    (labelsOf (codeOf other)) (needFuel (pgOf (codeOf other)) (labelsOf (codeOf other)) [])

#guard typed .rsi
-- the store through `rdi`: over the third byte of the row. Refused
#guard !typed .rdi

end Elsewhere

end Tests.Written.Middle
