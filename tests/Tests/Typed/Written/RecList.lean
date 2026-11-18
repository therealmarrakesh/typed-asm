import TypedAsm
import TypedAsm.U.Checked

/-!
# A function that goes down a list by calling itself

```asm
_start:  lea  rdi, [first]
         call sumlist
         mov  edi, eax
         mov  eax, 60
         syscall
sumlist: test rdi, rdi          ; rdi: a list of n nodes
         jne  recur
         xor  eax, eax
         ret
recur:   push rbx
         mov  rbx, [rdi]
         mov  rdi, [rdi + 8]    ; a list of n - 1
         call sumlist
         add  rax, rbx
         pop  rbx
         ret
first:   3, second    second: 4, third    third: 5, 0
```

The stack the function needs is by how long the list is: sixteen bytes a
node. A link is said with how many nodes the list it leads to has: it is
nought exactly when that is none, and else the address of a node whose own
link leads to a list of one fewer. The function is typed for a list of any
length; the three nodes of the program are said to be lists of three, two
and one, and their links are read from the program's bytes to be so.
-/

open TypedAsm TypedAsm.U

namespace Tests.Written.RecList

inductive L
  | start | sumlist | recur | first | second | third
  deriving DecidableEq, Hashable

def code : List (Asm L) := [
  .label .start,
  .ref (.lea .w64 .rdi (.rip 0)) .first,
  .call .sumlist,
  .ins (.mov .w32 (.rm_r (.reg .rdi) .rax)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .sumlist,
  .ins (.test .w64 (.reg .rdi) (.reg .rdi)),
  .jcc .ne .recur,
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .ins .ret,
  .label .recur,
  .ins (.push .rbx),
  .ins (.mov .w64 (.r_m .rbx (.sib (some .rdi) none 0))),
  .ins (.mov .w64 (.r_m .rdi (.sib (some .rdi) none 8))),
  .call .sumlist,
  .ins (.alu .add .w64 (.rm_r (.reg .rax) .rbx)),
  .ins (.pop .rbx),
  .ins .ret,
  .segment .ro,
  .label .first, .bytes (le64 3), .quad .second,
  .label .second, .bytes (le64 4), .quad .third,
  .label .third, .bytes (le64 5 ++ le64 0)]

asm_program code start .start stack 9

#guard exitsWith 12 (runMem linux 1000 start)


/-- A link to a list of so many nodes: nought exactly when there are none;
else the address of a node of the kind that many numbers. -/
def listOf (n : Val) : TyS := .zeroIff n (.refN 1 n false 0)

/-- A node of a list: a number, then a link to a list of fewer by so many
than the node's own list has; one fewer, as it should be said. -/
def node (fewer : BitVec 64) : ShapeS :=
  .mk 16 (.cons 8 (listOf (.add (.bvar 0 0) (.lit (-fewer)))) .nil)

def kindsFor (fewer : BitVec 64) : List (Nat × ShapeS) := [(1, node fewer)]

/-- A node at a label of the data, the first of a list of so many. -/
def nodeAt (fewer : BitVec 64) (l : L) (k : Nat) : BitVec 64 × U.LayoutS :=
  (Asm.addr code base l,
    { shape := (node fewer).atIdx (.lit (BitVec.ofNat 64 k)), writable := false, tag := some 1,
      idx := k })

def blocksFor (fewer : BitVec 64) : List (BitVec 64 × U.LayoutS) :=
  blocksWith code .start [nodeAt fewer .first 3, nodeAt fewer .second 2, nodeAt fewer .third 1]

def pgFor (fewer : BitVec 64) : Prog :=
  { code := progCode (Asm.table base code)
    kinds := kindsOf (kindsFor fewer)
    statics := staticIn (blocksFor fewer) (Asm.addr code base .first) }

/-- The labels: the function takes a list of some number of nodes, at most
so many, and asks for stack by that number, shifted so many bits. -/
def labelsFor (shift : Nat) : List U.Label :=
  [⟨entry, inProgram 9⟩,
   ⟨Asm.addr code base .sumlist,
     inFunction (known := [(.was .rdi, listOf (.named 0)), (.named 0, .range 0 0xFFFFFFF)])
       (room := (Val.named 0) <<< shift)⟩]

/-- Whether the program is typed, a node's link said to lead to a list of
so many fewer, and the stack asked for by the length shifted so far. -/
def typed (fewer : BitVec 64) (shift : Nat) : Bool :=
  wholeOkWith code .start 9 (kindsFor fewer) (blocksFor fewer) (pgFor fewer) (labelsFor shift)
    (needFuel (pgFor fewer) (labelsFor shift) (kindsFor fewer))

#guard typed 1 4
-- eight bytes a node asked for: each call uses sixteen. Refused
#guard !typed 1 3
-- a node's link said to lead to a list as long as the node's own: the data's
-- last link is nought, which a list of one is not. Refused
#guard !typed 0 4

def pg : Prog := pgFor 1

def labels : List U.Label := labelsFor 4

def blocks : List (BitVec 64 × U.LayoutS) := blocksFor 1

def kinds : List (Nat × ShapeS) := kindsFor 1

asm_checked code start .start stack 9 program pg labels labels blocks blocks kinds kinds

end Tests.Written.RecList
