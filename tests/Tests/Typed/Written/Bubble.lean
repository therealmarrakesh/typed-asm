import TypedAsm
import TypedAsm.U.Checked

/-!
Bubble sort of eight numbers in a static writable array, in place; exit
with the smallest (arr[0] after sorting) = 1.
-/

open TypedAsm TypedAsm.U

namespace Tests.Written.Bubble

inductive L
  | start | outer | inner | noswap | arr
  deriving DecidableEq, Hashable

def nums : List (BitVec 64) := [5, 3, 8, 1, 9, 2, 7, 4]

def code : List (Asm L) := [
  .label .start,
  .ref (.lea .w64 .rdi (.rip 0)) .arr,
  .ins (.mov .w32 (.rm_i (.reg .rcx) 7)),          -- pairs to look at in this pass
  .label .outer,
  .ins (.alu .xor .w32 (.rm_r (.reg .rdx) .rdx)),  -- j = 0
  .label .inner,
  .ins (.mov .w64 (.r_m .rax (.sib (some .rdi) (some (.rdx, .s8)) 0))),
  .ins (.mov .w64 (.r_m .r8 (.sib (some .rdi) (some (.rdx, .s8)) 8))),
  .ins (.alu .cmp .w64 (.rm_r (.reg .rax) .r8)),
  .jcc .be .noswap,
  .ins (.mov .w64 (.rm_r (.mem (.sib (some .rdi) (some (.rdx, .s8)) 0)) .r8)),
  .ins (.mov .w64 (.rm_r (.mem (.sib (some .rdi) (some (.rdx, .s8)) 8)) .rax)),
  .label .noswap,
  .ins (.alu .add .w64 (.rm_i (.reg .rdx) 1)),
  .ins (.alu .cmp .w64 (.rm_r (.reg .rdx) .rcx)),
  .jcc .b .inner,
  .ins (.alu .sub .w64 (.rm_i (.reg .rcx) 1)),
  .jcc .ne .outer,
  .ins (.mov .w64 (.r_m .rdi (.sib (some .rdi) none 0))),
  .ins (.mov .w32 (.rm_i (.reg .rax) 60)),
  .ins .syscall,
  .segment .rw,
  .label .arr, .bytes (nums.flatMap le64)]

asm_program code start .start stack 0

#guard exitsWith 1 (runMem linux 10000 start)

def arrAddr : BitVec 64 := Asm.addr code base .arr

def blocks : List (BitVec 64 × U.LayoutS) :=
  blocksWith code .start [(arrAddr, rowBlock 8 .any true)]

def pg : Prog :=
  { code := progCode (Asm.table base code)
    statics := staticIn blocks arrAddr }

/-- At the outer loop: rdi is the array, rcx is from 1 to 7.  At the inner
loop besides: rdx is below rcx. -/
def labels : List U.Label :=
  [⟨entry, inProgram 0⟩,
   ⟨Asm.addr code base .outer,
     inProgram 0 (regs := [(.rdi, .lit arrAddr)]) (known := [(.was .rcx, .range 1 7)])⟩,
   ⟨Asm.addr code base .inner,
     inProgram 0 (regs := [(.rdi, .lit arrAddr)])
       (known := [(.was .rcx, .range 1 7), (.was .rdx, .upTo (.was .rcx) true)])⟩]

asm_checked code start .start stack 0 program pg labels labels blocks blocks

/-- The labels, the inner loop's index said to be at most the count of pairs
and not below it. -/
def labelsLoose : List U.Label :=
  [⟨entry, inProgram 0⟩,
   ⟨Asm.addr code base .outer,
     inProgram 0 (regs := [(.rdi, .lit arrAddr)]) (known := [(.was .rcx, .range 1 7)])⟩,
   ⟨Asm.addr code base .inner,
     inProgram 0 (regs := [(.rdi, .lit arrAddr)])
       (known := [(.was .rcx, .range 1 7), (.was .rdx, .upTo (.was .rcx) false)])⟩]

-- the second of a pair may then be one past the last of the eight. Refused
#guard !wholeOkWith code .start 0 [] blocks pg labelsLoose (needFuel pg labelsLoose [])

end Tests.Written.Bubble
