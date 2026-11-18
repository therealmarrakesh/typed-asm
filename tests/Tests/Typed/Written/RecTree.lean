import TypedAsm
import TypedAsm.U.Checked

/-!
# A function that goes down a tree by calling itself

```asm
_start:  lea  rdi, [root]
         call sumtree
         mov  edi, eax
         mov  eax, 60
         syscall
sumtree: test rdi, rdi          ; rdi: nought, or a tree no deeper than n
         jne  rec
         xor  eax, eax
         ret
rec:     push rbx
         push r12
         mov  rbx, rdi
         mov  r12, [rbx]        ; the node's number
         mov  rdi, [rbx + 8]    ; its left: no deeper than n - 1
         call sumtree
         add  r12, rax
         mov  rdi, [rbx + 16]   ; its right, likewise
         call sumtree
         add  rax, r12
         pop  r12
         pop  rbx
         ret
root:    1, left, right     left: 2, 0, 0     right: 3, 0, 0
```

The stack the function needs is by how deep the tree is: twenty-four bytes
a level. A link is nought, or the address of a node of a tree no deeper
than a number; and that number is not nought where the link is not, for a
tree no deeper than nought has no node. Either link of a node of a tree no
deeper than `n` is such a link for `n - 1`.
-/

open TypedAsm TypedAsm.U

namespace Tests.Written.RecTree

inductive L
  | start | sumtree | recur | root | left | right
  deriving DecidableEq, Hashable

def code : List (Asm L) := [
  .label .start,
  .ref (.lea .w64 .rdi (.rip 0)) .root,
  .call .sumtree,
  .ins (.mov .w32 (.rm_r (.reg .rdi) .rax)),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .label .sumtree,
  .ins (.test .w64 (.reg .rdi) (.reg .rdi)),
  .jcc .ne .recur,
  .ins (.alu .xor .w32 (.rm_r (.reg .rax) .rax)),
  .ins .ret,
  .label .recur,
  .ins (.push .rbx),
  .ins (.push .r12),
  .ins (.mov .w64 (.rm_r (.reg .rbx) .rdi)),
  .ins (.mov .w64 (.r_m .r12 (.sib (some .rbx) none 0))),
  .ins (.mov .w64 (.r_m .rdi (.sib (some .rbx) none 8))),
  .call .sumtree,
  .ins (.alu .add .w64 (.rm_r (.reg .r12) .rax)),
  .ins (.mov .w64 (.r_m .rdi (.sib (some .rbx) none 16))),
  .call .sumtree,
  .ins (.alu .add .w64 (.rm_r (.reg .rax) .r12)),
  .ins (.pop .r12),
  .ins (.pop .rbx),
  .ins .ret,
  .segment .ro,
  .label .root, .bytes (le64 1), .quad .left, .quad .right,
  .label .left, .bytes (le64 2 ++ le64 0 ++ le64 0),
  .label .right, .bytes (le64 3 ++ le64 0 ++ le64 0)]

asm_program code start .start stack 12

#guard exitsWith 6 (runMem linux 1000 start)

/-- A link to a tree no deeper than so much: nought; or, that not being
nought, the address of a node of the kind that number numbers. -/
def treeOf (n : Val) : TyS := .nullable (.zeroIff n (.refN 1 n false 0))

/-- A node: a number, then two links, each to a tree shallower by so much
than the node's own; by one, as it should be said. -/
def node (less : BitVec 64) : ShapeS :=
  .mk 24 (.cons 8 (treeOf (.add (.bvar 0 0) (.lit (-less))))
    (.cons 16 (treeOf (.add (.bvar 0 0) (.lit (-less)))) .nil))

def kindsFor (less : BitVec 64) : List (Nat × ShapeS) := [(1, node less)]

def nodeAt (less : BitVec 64) (l : L) (k : Nat) : BitVec 64 × U.LayoutS :=
  (Asm.addr code base l,
    { shape := (node less).atIdx (.lit (BitVec.ofNat 64 k)), writable := false, tag := some 1,
      idx := k })

def blocksFor (less : BitVec 64) : List (BitVec 64 × U.LayoutS) :=
  blocksWith code .start [nodeAt less .root 2, nodeAt less .left 1, nodeAt less .right 1]

def pgFor (less : BitVec 64) : Prog :=
  { code := progCode (Asm.table base code)
    kinds := kindsOf (kindsFor less)
    statics := staticIn (blocksFor less) (Asm.addr code base .root) }

/-- The labels: the function takes a tree no deeper than some number, and
asks for stack by that number: so many bytes a level. -/
def labelsFor (a b : Nat) : List U.Label :=
  [⟨entry, inProgram 12⟩,
   ⟨Asm.addr code base .sumtree,
     inFunction (known := [(.was .rdi, treeOf (.named 0)), (.named 0, .range 0 0xFFFFFF)])
       (room := ((Val.named 0) <<< a) + ((Val.named 0) <<< b))⟩]

def typed (less : BitVec 64) (a b : Nat) : Bool :=
  wholeOkWith code .start 12 (kindsFor less) (blocksFor less) (pgFor less) (labelsFor a b)
    (needFuel (pgFor less) (labelsFor a b) (kindsFor less))

#guard typed 1 4 3
-- sixteen bytes a level asked for: each level uses twenty-four. Refused
#guard !typed 1 3 3
-- a node's links said to lead to trees as deep as its own: the function then
-- asks of each call as much stack as it was given. Refused
#guard !typed 0 4 3

def pg : Prog := pgFor 1
def labels : List U.Label := labelsFor 4 3
def blocks : List (BitVec 64 × U.LayoutS) := blocksFor 1
def kinds : List (Nat × ShapeS) := kindsFor 1

asm_checked code start .start stack 12 program pg labels labels blocks blocks kinds kinds

end Tests.Written.RecTree
