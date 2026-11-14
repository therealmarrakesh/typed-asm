import Core

/-!
# Summing an array

A complete program: it sums five 64-bit integers stored in read-only memory
and exits with the total as its status.

```asm
_start:
  400000  lea   rdi, [rip + array]
  400007  mov   esi, 5
  40000c  call  sum
  400011  mov   edi, eax
  400013  mov   eax, 60          ; Linux `exit`
  400018  syscall
sum:                             ; rdi = pointer, rsi = count, result in rax
  40001a  xor   eax, eax
  40001c  test  rsi, rsi
  40001f  je    done
loop:
  400025  add   rax, [rdi]
  400028  add   rdi, 8
  40002c  sub   rsi, 1
  400030  jne   loop
done:
  400036  ret
```

Instruction lengths are those of the real encodings. Jump and call offsets are
relative to the address of the following instruction.
-/

open Core

namespace Sum

def codeBase : BitVec 64 := 0x400000
def arrayBase : BitVec 64 := 0x600000
def stackTop : BitVec 64 := 0x800000

/-- The program as (instruction, length in bytes) pairs, in address order. -/
def code : List (Instr × BitVec 64) := [
  -- _start
  (.lea .w64 .rdi (.rip 0x1ffff9), 7),
  (.mov .w32 (.rm_i (.reg .rsi) 5), 5),
  (.call (.rel 9), 5),
  (.mov .w32 (.rm_r (.reg .rdi) .rax), 2),
  (.mov .w32 (.rm_i (.reg .rax) 60), 5),
  (.syscall, 2),
  -- sum
  (.alu .xor .w32 (.rm_r (.reg .rax) .rax), 2),
  (.test .w64 (.reg .rsi) (.reg .rsi), 3),
  (.jcc .e 17, 6),
  -- loop
  (.alu .add .w64 (.r_m .rax (.sib (some .rdi) none 0)), 3),
  (.alu .add .w64 (.rm_i (.reg .rdi) 8), 4),
  (.alu .sub .w64 (.rm_i (.reg .rsi) 1), 4),
  (.jcc .ne (-17), 6),
  -- done
  (.ret, 1)]

/-- Lay instructions out one after another starting at `base`. -/
def layout (base : BitVec 64) : List (Instr × BitVec 64) → Fetch
  | [], _ => none
  | (i, len) :: rest, a => if a = base then some (i, len) else layout (base + len) rest a

def fetch : Fetch := layout codeBase code

/-- The one system call this program uses: `exit`, number 60 on Linux. -/
def linux : Syscall := fun s =>
  if s.getReg .rax = 60 then .exit (s.readReg .w32 .rdi) else .stuck

def array : List (BitVec 64) := [3, 1, 4, 1, 5]

/-- The starting state: the array in read-only memory, a writable 4 KiB stack,
`rsp` at the top of the stack and `rip` at `_start`. -/
def start : State :=
  let s := State.init
  let s := (array.zipIdx).foldl (fun s (v, i) => s.store64 (arrayBase + 8 * BitVec.ofNat 64 i) v) s
  let s := s.setPerm arrayBase 40 .ro
  let s := s.setPerm (stackTop - 0x1000) 0x1000 .rw
  let s := s.setReg .rsp stackTop
  { s with rip := codeBase }

def describe : Outcome → String
  | .next s => s!"still running at rip = {s.rip.toHex}"
  | .fault f => s!"fault: {repr f}"
  | .exit code => s!"exit {code.toNat}"
  | .stuck => "stuck"

/-- The program exits with status 14 = 3 + 1 + 4 + 1 + 5. Checked when this file is built. -/
def exitsWith (code : BitVec 32) : Outcome → Bool
  | .exit c => c == code
  | _ => false

#guard exitsWith 14 (run fetch linux 100 start)

end Sum

def main : IO Unit :=
  IO.println (Sum.describe (run Sum.fetch Sum.linux 100 Sum.start))
