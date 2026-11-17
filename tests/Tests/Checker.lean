import TypedAsm.Sym

/-!
# What the checker answers

Each check gives the checker one instruction in one context and looks at
what it says: the type a register has afterwards, what the stack or an owned
block holds, what is left to be shown, or that it has no answer. They are
checked as this file is compiled. The contexts are terms, as the checker
takes them; `v n` is a value the context says nothing more of.
-/

open TypedAsm TypedAsm.Sym

namespace Tests.Checker

def v (n : Nat) : Val := .var n

/-- Nothing known of any register, an empty stack with 64 bytes of room. -/
def base : CtxS :=
  { regs := ⟨.int, .int, .int, .int, .int, .int, .int, .int, .int, .int, .int, .int, .int, .int,
      .int, .int⟩,
    stack := [], room := .lit 64, flags := .any }

def reg (Γ : CtxS) (r : Reg) (τ : TyS) : CtxS := Γ.setReg r τ

/-- The type a register has after a step, if the checker has an answer. -/
def after (Γ : CtxS) (i : Instr) (r : Reg) : Option TyS :=
  (step 0x1000 Γ i).map (·.1.regs.get r)

/-- How many things a step leaves to be shown, if the checker has an answer. -/
def left (Γ : CtxS) (i : Instr) : Option Nat := (step 0x1000 Γ i).map (·.2.length)

def refused (Γ : CtxS) (i : Instr) : Bool := (step 0x1000 Γ i).isNone

def mem (b : Reg) (d : BitVec 32) : Mem := .sib (some b) none d
def idx (b : Reg) (x : IndexReg) (sc : Scale) (d : BitVec 32) : Mem := .sib (some b) (some (x, sc)) d

/-! ## Registers -/

-- a constant, then arithmetic on it, is worked out
example : after base (.mov .w64 (.rm_i (.reg .rax) 5)) .rax = some (.eq (.lit 5)) := by decide
example : after (reg base .rax (.eq (.lit 5))) (.alu .add .w64 (.rm_i (.reg .rax) 3)) .rax
    = some (.eq (.lit 8)) := by decide
-- arithmetic on a value that is not a number is kept as the operation
example : after (reg base .rax (.eq (v 0))) (.alu .add .w64 (.rm_i (.reg .rax) 3)) .rax
    = some (.eq (.app2 (.alu .add .w64) (v 0) (.lit 3))) := by decide
-- on a number nothing is known, and nothing is left to be shown
example : after base (.alu .add .w64 (.rm_i (.reg .rax) 3)) .rax = some .int := by decide
example : left base (.alu .add .w64 (.rm_i (.reg .rax) 3)) = some 0 := by decide
-- reading the carry flag where nothing is known of the flags is left to be shown
example : left base (.alu .adc .w64 (.rm_i (.reg .rax) 3)) = some 1 := by decide
example : left { base with flags := .known } (.alu .adc .w64 (.rm_i (.reg .rax) 3)) = some 0 := by
  decide
-- the stack pointer is not written by ordinary instructions
example : refused base (.mov .w64 (.rm_i (.reg .rsp) 5)) = true := by decide
-- a pointer moved on stays a pointer, that much further in
example : after (reg base .rdi (.ptr (.mk (.lit 64) .nil) false (.lit 8)))
    (.alu .add .w64 (.rm_i (.reg .rdi) 8)) .rdi
    = some (.ptr (.mk (.lit 64) .nil) false (.lit 16)) := by decide
-- any other arithmetic on it leaves a number
example : after (reg base .rdi (.ptr (.mk (.lit 64) .nil) false (.lit 8)))
    (.alu .sub .w64 (.rm_i (.reg .rdi) 8)) .rdi = some .int := by decide
-- shifts, extensions and the rest are worked out on numbers
example : after (reg base .rax (.eq (.lit 3))) (.shift .shl .w64 (.reg .rax) (.imm 4)) .rax
    = some (.eq (.lit 48)) := by decide
example : after (reg base .rax (.eq (.lit 0xffffffff))) (.movsxd .rcx (.reg .rax)) .rcx
    = some (.eq (.lit 0xffffffffffffffff)) := by decide
example : after (reg base .rax (.eq (.lit 7))) (.unary .neg .w64 (.reg .rax)) .rax
    = some (.eq (.lit 0xfffffffffffffff9)) := by decide

/-! ## The stack -/

-- a push needs room: seen where the room is a number
example : left base (.push .rax) = some 0 := by decide
example : left { base with room := .var 0 } (.push .rax) = some 1 := by decide
example : (step 0x1000 base (.push .rax)).map (·.1.room) = some (.lit 56) := by decide
-- what is pushed comes back with its type
example : after { (reg base .rcx .int) with stack := [.mk (.lit 8) (.cons 0 (.eq (v 3)) .nil)] }
    (.pop .rcx) .rcx = some (.eq (v 3)) := by decide
example : refused base (.pop .rcx) = true := by decide
-- a load from a slot keeps its type; from plain bytes it is a number
example : after { base with stack := [.mk (.lit 16) (.cons 8 (.eq (v 1)) .nil)] }
    (.mov .w64 (.r_m .rax (mem .rsp 8))) .rax = some (.eq (v 1)) := by decide
example : after { base with stack := [.mk (.lit 16) (.cons 8 (.eq (v 1)) .nil)] }
    (.mov .w64 (.r_m .rax (mem .rsp 0))) .rax = some .int := by decide
-- past the pieces the stack has, there is no answer
example : refused { base with stack := [.mk (.lit 16) .nil] }
    (.mov .w64 (.r_m .rax (mem .rsp 16))) = true := by decide
-- eight bytes that straddle a piece's end are refused
example : refused { base with stack := [.mk (.lit 16) .nil, .mk (.lit 16) .nil] }
    (.mov .w64 (.r_m .rax (mem .rsp 12))) = true := by decide

/-! ## Through a pointer -/

def rec2 : ShapeS := .mk (.lit 16) (.cons 8 (.eq (v 9)) .nil)

example : after (reg base .rdi (.ptr rec2 false (.lit 0))) (.mov .w64 (.r_m .rax (mem .rdi 8))) .rax
    = some (.eq (v 9)) := by decide
example : after (reg base .rdi (.ptr rec2 false (.lit 0))) (.mov .w64 (.r_m .rax (mem .rdi 0))) .rax
    = some .int := by decide
-- outside the block
example : refused (reg base .rdi (.ptr rec2 false (.lit 0)))
    (.mov .w64 (.r_m .rax (mem .rdi 16))) = true := by decide
-- a store through a pointer that may not be written
example : refused (reg base .rdi (.ptr rec2 false (.lit 0)))
    (.mov .w64 (.rm_r (.mem (mem .rdi 0)) .rax)) = true := by decide
-- a store over a typed value leaves it to be shown that the value has its type,
-- unless the terms show it
example : left (reg (reg base .rdi (.ptr rec2 true (.lit 0))) .rax .int)
    (.mov .w64 (.rm_r (.mem (mem .rdi 8)) .rax)) = some 1 := by decide
example : left (reg (reg base .rdi (.ptr rec2 true (.lit 0))) .rax (.eq (v 9)))
    (.mov .w64 (.rm_r (.mem (mem .rdi 8)) .rax)) = some 0 := by decide
-- an index that is not a number: the bound is left to be shown
example : left (reg (reg base .rdi (.ptr (.mk (.var 0) .nil) false (.lit 0))) .rcx (.eq (v 1)))
    (.mov .w64 (.r_m .rax (idx .rdi .rcx .s8 0))) = some 1 := by decide
-- an element of an array: its type, and that there is such an element
def arr : ShapeS := .rep (.var 0) (.mk (.lit 8) (.cons 0 (.str false) .nil))
example : after (reg (reg base .rdi (.ptr arr false (.lit 0))) .rcx (.eq (v 1)))
    (.mov .w64 (.r_m .rax (idx .rdi .rcx .s8 0))) .rax = some (.str false) := by decide
example : left (reg (reg base .rdi (.ptr arr false (.lit 0))) .rcx (.eq (v 1)))
    (.mov .w64 (.r_m .rax (idx .rdi .rcx .s8 0))) = some 1 := by decide
-- a store into an element of an array that may be written
example : left (reg (reg (reg base .rdi (.ptr arr true (.lit 0))) .rcx (.eq (v 1))) .rax
    (.str false)) (.mov .w64 (.rm_r (.mem (idx .rdi .rcx .s8 0)) .rax)) = some 1 := by decide

/-! ## Blocks the context owns -/

/-- A block of 32 plain bytes at `v 5`, with `rbx` holding its address. -/
def owner : CtxS := { reg base .rbx (.eq (v 5)) with owned := [(v 5, .mk (.lit 32) .nil)] }

-- the block is found from the address, with nothing told
example : after owner (.mov .w64 (.r_m .rax (mem .rbx 8))) .rax = some .int := by decide
example : refused owner (.mov .w64 (.r_m .rax (mem .rbx 32))) = true := by decide
-- an address that is not the block's is in no block
example : refused (reg owner .rbx (.eq (v 6))) (.mov .w64 (.r_m .rax (mem .rbx 8))) = true := by
  decide
-- a typed value stored gives the bytes its type; a number leaves them plain
example : (step 0x1000 (reg owner .rax (.eq (v 2))) (.mov .w64 (.rm_r (.mem (mem .rbx 8)) .rax))).map
    (·.1.owned) = some [(v 5, .mk (.lit 32) (.cons 8 (.eq (v 2)) .nil))] := by decide
example : (step 0x1000 owner (.mov .w64 (.rm_r (.mem (mem .rbx 8)) .rax))).map (·.1.owned)
    = some [(v 5, .mk (.lit 32) .nil)] := by decide
-- storing again a value of the type that is there changes nothing
example : (step 0x1000
      { reg (reg base .rbx (.eq (v 5))) .rax (.eq (v 2)) with
        owned := [(v 5, .mk (.lit 32) (.cons 8 (.eq (v 2)) (.cons 0 (.str false) .nil)))] }
      (.mov .w64 (.rm_r (.mem (mem .rbx 8)) .rax))).map (·.1.owned)
    = some [(v 5, .mk (.lit 32) (.cons 8 (.eq (v 2)) (.cons 0 (.str false) .nil)))] := by decide
-- of two blocks one after the other, the address picks the one it is in
example : (step 0x1000
      { reg (reg base .rbx (.eq (.add (v 5) (.lit 16)))) .rax (.eq (v 2)) with
        owned := [(v 5, .mk (.lit 16) .nil), (.add (v 5) (.lit 16), .mk (.lit 16) .nil)] }
      (.mov .w64 (.rm_r (.mem (mem .rbx 0)) .rax))).map (·.1.owned)
    = some [(v 5, .mk (.lit 16) .nil),
        (.add (v 5) (.lit 16), .mk (.lit 16) (.cons 0 (.eq (v 2)) .nil))] := by decide

/-! ## The program's blocks -/

/-- A writable block of 16 bytes at `0x2000` with a typed value at byte 8. -/
def prog : CtxS := { base with blocks := [(0x2000, rec2, true)] }

-- reached from the next instruction, which is at `0x1000`
example : after prog (.mov .w64 (.r_m .rax (.rip 0x1008))) .rax = some (.eq (v 9)) := by decide
example : refused prog (.mov .w64 (.r_m .rax (.rip 0x1010))) = true := by decide
-- at a fixed address, and through an index from one
example : after prog (.mov .w64 (.r_m .rax (.sib none none 0x2008))) .rax = some (.eq (v 9)) := by
  decide
example : left (reg prog .rcx (.eq (v 1)))
    (.mov .w32 (.r_m .rax (.sib none (some (.rcx, .s1)) 0x2000))) = some 1 := by decide
-- a store over the typed value at a fixed address, and into the plain bytes
example : left (reg prog .rax (.eq (v 9)))
    (.mov .w64 (.rm_r (.mem (.sib none none 0x2008)) .rax)) = some 0 := by decide
example : left prog (.mov .w64 (.rm_r (.mem (.sib none none 0x2000)) .rax)) = some 0 := by decide
-- a block that may not be written
example : refused { base with blocks := [(0x2000, rec2, false)] }
    (.mov .w64 (.rm_r (.mem (.sib none none 0x2000)) .rax)) = true := by decide

/-! ## Divides -/

def dividing (a d b : TyS) : CtxS := reg (reg (reg base .rax a) .rdx d) .rcx b

-- numbers are divided at once, and a divide by zero is refused
example : after (dividing (.eq (.lit 17)) (.eq (.lit 0)) (.eq (.lit 5))) (.mulDiv .div .w64 (.reg .rcx))
    .rax = some (.eq (.lit 3)) := by decide
example : after (dividing (.eq (.lit 17)) (.eq (.lit 0)) (.eq (.lit 5))) (.mulDiv .div .w64 (.reg .rcx))
    .rdx = some (.eq (.lit 2)) := by decide
example : refused (dividing (.eq (.lit 17)) (.eq (.lit 0)) (.eq (.lit 0)))
    (.mulDiv .div .w64 (.reg .rcx)) = true := by decide
-- of a value that is not a number: that the divisor is not zero is left to be shown
example : left (dividing (.eq (v 0)) (.eq (.lit 0)) (.eq (v 1))) (.mulDiv .div .w64 (.reg .rcx))
    = some 1 := by decide
-- a divisor only known to be a number is refused
example : refused (dividing (.eq (v 0)) (.eq (.lit 0)) .int) (.mulDiv .div .w64 (.reg .rcx)) = true := by
  decide
-- by an exactly known value held on the stack
example : left { dividing (.eq (v 0)) (.eq (.lit 0)) .int with
      stack := [.mk (.lit 8) (.cons 0 (.eq (v 1)) .nil)] }
    (.mulDiv .div .w64 (.mem (mem .rsp 0))) = some 1 := by decide

/-! ## Conditions -/

-- exactly known flags say which way a conditional move goes
example : after { reg (reg base .rax (.eq (.lit 1))) .rcx (.eq (.lit 2)) with
      flags := .alu .cmp .w64 (.lit 3) (.lit 3) }
    (.cmov .e .w64 .rax (.reg .rcx)) .rax = some (.eq (.lit 2)) := by decide
example : after { reg (reg base .rax (.eq (.lit 1))) .rcx (.eq (.lit 2)) with
      flags := .alu .cmp .w64 (.lit 3) (.lit 4) }
    (.cmov .e .w64 .rax (.reg .rcx)) .rax = some (.eq (.lit 1)) := by decide
-- flags not known to be defined: that they decide the condition is left to be shown
example : left (reg (reg base .rax (.eq (.lit 1))) .rcx (.eq (.lit 2)))
    (.cmov .e .w64 .rax (.reg .rcx)) = some 1 := by decide
example : left { reg (reg base .rax (.eq (.lit 1))) .rcx (.eq (.lit 2)) with flags := .known }
    (.cmov .e .w64 .rax (.reg .rcx)) = some 0 := by decide

/-! ## One context standing for another -/

def needs (Γ Δ : CtxS) : Option Nat := (subCtx Γ Δ).map (·.length)

-- a context stands for itself, and for one that knows less of a register
example : needs base base = some 0 := by decide
example : needs (reg base .rax (.eq (v 1))) base = some 0 := by decide
-- not the other way round without its being shown
example : needs base (reg base .rax (.eq (v 1))) = some 1 := by decide
-- exactly known flags stand for defined ones, and anything for none known
example : needs { base with flags := .alu .cmp .w64 (v 0) (v 1) } { base with flags := .known }
    = some 0 := by decide
example : needs base { base with flags := .known } = some 1 := by decide
-- a slot stands for one of a type its value may be taken at
example : needs { base with stack := [.mk (.lit 8) (.cons 0 (.eq (v 1)) .nil)] }
    { base with stack := [.mk (.lit 8) (.cons 0 .int .nil)] } = some 0 := by decide
-- and for plain bytes, but stacks cut differently do not compare
example : needs { base with stack := [.mk (.lit 8) (.cons 0 (.eq (v 1)) .nil)] }
    { base with stack := [.mk (.lit 8) .nil] } = some 0 := by decide
example : needs { base with stack := [.mk (.lit 16) .nil] }
    { base with stack := [.mk (.lit 8) .nil, .mk (.lit 8) .nil] } = none := by decide
-- room that is written differently is left to be shown the same
example : needs { base with room := .var 0 } { base with room := .add (.var 1) (.lit 8) }
    = some 1 := by decide
-- owned blocks written differently are left to be shown the same
example : needs { base with owned := [(v 5, .mk (.lit 32) .nil)] } base = some 1 := by decide

/-! ## Past a piece of the stack whose length is not a number written out -/

/-- A count, that many slots, and 32 plain bytes; `rax` holds the count. -/
def counted : CtxS :=
  { reg base .rax (.eq (v 0)) with
    stack := [.mk (.lit 8) (.cons 0 (.eq (v 0)) .nil),
      .rep (.toNat (v 0)) (.mk (.lit 8) (.cons 0 (.str false) .nil)), .mk (.lit 32) .nil] }

-- indexed by the count itself, the access is in what follows the slots
example : after counted (.mov .w64 (.r_m .rcx (idx .rsp .rax .s8 8))) .rcx = some .int := by
  decide
example : left counted (.mov .w64 (.r_m .rcx (idx .rsp .rax .s8 8))) = some 0 := by decide
-- and is held to that piece's length
example : refused counted (.mov .w64 (.r_m .rcx (idx .rsp .rax .s8 36))) = true := by decide
-- indexed by anything else it is in the slots, within bounds to be shown
example : left (reg counted .rax (.eq (v 1))) (.mov .w64 (.r_m .rcx (idx .rsp .rax .s8 8)))
    = some 1 := by decide

/-! ## System calls that return -/

def sysLeft (Γ : CtxS) : Option Nat := (stepSys Γ).map (·.2.length)

-- `write`, by its number, whatever its arguments; and what it leaves in `rax`
example : sysLeft (reg base .rax (.eq (.lit 1))) = some 0 := by decide
example : ((stepSys (reg base .rax (.eq (.lit 1)))).map (·.1.regs.get .rax)) = some .int := by
  decide
-- a number that is not written out says nothing of which call it is
example : sysLeft base = none := by decide
example : sysLeft (reg base .rax (.eq (v 1))) = none := by decide
-- `fstat` needs 144 plain bytes that may be written
example : sysLeft (reg (reg base .rax (.eq (.lit 5))) .rsi (.ptr (.mk (.lit 144) .nil) true (.lit 0)))
    = some 0 := by decide
example : sysLeft (reg (reg base .rax (.eq (.lit 5))) .rsi (.ptr (.mk (.lit 143) .nil) true (.lit 0)))
    = none := by decide
example : sysLeft (reg (reg base .rax (.eq (.lit 5))) .rsi (.ptr (.mk (.lit 144) .nil) false (.lit 0)))
    = none := by decide
-- `read` of a count in a register: within the buffer, to be shown
example : sysLeft (reg (reg (reg base .rax (.eq (.lit 0))) .rsi
    (.ptr (.mk (.lit 64) .nil) true (.lit 0))) .rdx (.eq (v 2))) = some 1 := by decide
-- and not over a typed value
example : sysLeft (reg (reg (reg base .rax (.eq (.lit 0))) .rsi (.ptr rec2 true (.lit 0))) .rdx
    (.eq (v 2))) = none := by decide

/-! ## An address kept as a number until a pointer is needed -/

/-- A program with one block, whose address is kept. -/
def kept : Prog := { blocks := [(0x2000, rec2, true)], keep := [0x2000] }

/-- `rbx` holds exactly the block's address. -/
def holding : CtxS := reg base .rbx (.eq (.lit 0x2000))

-- taking the address leaves the number it is
example : (castData kept (reg base .rsi (.eq (.lit 0x2000))) (.lea .w64 .rsi (.rip 0))).regs.get .rsi
    = .eq (.lit 0x2000) := by decide
-- memory is reached through it as it is: the typed value there is loaded,
-- and the register still holds the number
example : after { holding with blocks := kept.blocks } (.mov .w64 (.r_m .rax (mem .rbx 8))) .rax
    = some (.eq (v 9)) := by decide
example : after { holding with blocks := kept.blocks } (.mov .w64 (.r_m .rax (mem .rbx 8))) .rbx
    = some (.eq (.lit 0x2000)) := by decide
-- and not past the block
example : refused { holding with blocks := kept.blocks } (.mov .w64 (.r_m .rax (mem .rbx 16)))
    = true := by decide
-- where a context to be compared with wants a pointer, it is made one
example : ((castWanted kept (reg base .rbx (.ptr rec2 true (.lit 0))) regList holding false).map
    (·.regs.get .rbx)) = some (.ptr rec2 true (.lit 0)) := by decide
-- and left alone where that context wants the number
example : (castWanted kept holding regList holding false).isNone = true := by decide

/-! ## A call that ends the program -/

/-- Whether the walk ends the program at a `syscall`, and with what status. -/
def ends (Γ : CtxS) : Option (Option Val) :=
  match exitAt Γ .syscall with
  | some (.exit v) => some v
  | _ => none

-- `exit` and `exit_group` end the walk, with the status where it is exactly known
example : ends (reg (reg base .rax (.eq (.lit 60))) .rdi (.eq (.lit 3))) = some (some (.lit 3)) := by
  decide
example : ends (reg base .rax (.eq (.lit 231))) = some none := by decide
-- another call does not, nor does a number that is not known
example : ends (reg base .rax (.eq (.lit 1))) = none := by decide
example : ends base = none := by decide
-- and no other instruction does
example : (exitAt (reg base .rax (.eq (.lit 60))) .nop).isNone = true := by decide

/-! ## The stack pointer where a function keeps it

Its type is then one the terms have no form for, and moving the stack
pointer gives that type shifted: by all the moves together. -/

example : (TyS.atom 3).shift? 8 = some (.shifted 3 8) := by decide
example : (TyS.shifted 3 8).shift? 16 = some (.shifted 3 24) := by decide
-- a return is seen through it
example : ((afterRet { reg base .rsp (.atom 3) with
    stack := [.mk (.lit 8) (.cons 0 (.atom 5) .nil)] }).map fun x => (x.1, x.2.regs.get .rsp))
    = some (5, .shifted 3 8) := by decide

/-! ## Memory asked of the kernel and given back -/

/-- The registers set for an `mmap` of one page that the program is to own. -/
def asking : CtxS :=
  reg (reg (reg (reg (reg base .rax (.eq (.lit 9))) .rsi (.eq (.lit 100))) .rdx (.eq (.lit 3)))
    .r10 (.eq (.lit 0x22))) .rdi (.eq (.lit 0))

/-- What the context owns on the side of an `mmap` where it gave memory. -/
def got (Γ : CtxS) : Option (List (Val × ShapeS)) :=
  match mmapAt { linux := true } 0 0x1000 Γ .syscall with
  | some (.fresh _ _ (.stop _ Δ)) => some Δ.owned
  | _ => none

-- whole pages, at an address the walk names
example : got asking = some [(.var 0, .mk (.lit 4096) .nil)] := by decide
-- not for memory that is a file's, nor at a place the program chooses
example : got (reg asking .r10 (.eq (.lit 0x21))) = none := by decide
example : got (reg asking .rdi (.eq (.lit 0x10000))) = none := by decide
-- nor where the system is not known to be like Linux
example : (mmapAt {} 0 0x1000 asking .syscall).isNone = true := by decide

/-- A page owned at the address in `rdi`, and the registers set to give back `len` bytes. -/
def giving (len : BitVec 64) : CtxS :=
  { reg (reg (reg base .rax (.eq (.lit 11))) .rdi (.eq (.var 0))) .rsi (.eq (.lit len)) with
    owned := [(.var 0, .mk (.lit 4096) .nil)] }

-- given back whole: the context owns nothing, and nothing is left to show
example : (stepSys (giving 4096)).map (fun x => (x.1.owned, x.2.length)) = some ([], 0) := by
  decide
-- a length that does not cover exactly the block is left as something false to show
example : (stepSys (giving 8192)).map (·.2.length) = some 1 := by decide
-- and an address that is not a block's own is refused
example : (stepSys (reg (giving 4096) .rdi (.eq (.lit 5)))).isNone = true := by decide

/-! ## Jumps and calls through a value -/

/-- A table of two values of a type the terms have no form for, as a
function pointer's is. -/
def fns : ShapeS := .mk (.lit 16) (.cons 0 (.atom 4) (.cons 8 (.atom 4) .nil))

/-- `rbx` points to the table, and `rcx` holds an index. -/
def atTable (i : BitVec 64) : CtxS :=
  reg (reg base .rbx (.ptr fns false (.lit 0))) .rcx (.eq (.lit i))

-- what a register holds, and what a field does, an index worked out
example : (held 0x1000 (reg base .r12 (.atom 4)) (.reg .r12)).map (·.1) = some (.atom 4) := by
  decide
example : (held 0x1000 (atTable 1) (.mem (idx .rbx .rcx .s8 0))).map (·.1) = some (.atom 4) := by
  decide
-- not past the table, and not the stack pointer
example : (held 0x1000 (atTable 2) (.mem (idx .rbx .rcx .s8 0))).isNone = true := by decide
example : (held 0x1000 base (.reg .rsp)).isNone = true := by decide
-- a number with no variable in it is worked out
example : (Num.add (.mul (.toNat (.lit 3)) (.lit 8)) (.lit 4)).folded = .lit 28 := by decide
example : (Num.add (.var 0) (.lit 4)).folded = .add (.var 0) (.lit 4) := by decide

/-- A program that says where a jump through `rcx` at 0x1000 goes, and that
0x2000 is the address of code. -/
def jumping : Prog := { enters := [(0x1000, 0, base)], codes := [(0x2000, 4)] }

-- the jump is typed through the value's type, whatever it is: that the type
-- enters the context is what is left to be shown
example : (match viaAt jumping 0x1000 2 (reg base .rcx (.atom 4)) (.jmp (.ind (.reg .rcx))) with
    | some (.jumpVia τ _ cs) => some (τ, cs.length)
    | _ => none) = some (.atom 4, 0) := by decide
-- nothing is said where no context was given for the instruction
example : (viaAt {} 0x1000 2 (reg base .rcx (.atom 4)) (.jmp (.ind (.reg .rcx)))).isNone = true := by
  decide
-- a register given the address of code is made a pointer to it; another address is not
example : codeCast jumping (reg base .rax (.eq (.lit 0x2000))) (.lea .w64 .rax (.rip 0))
    = some (.rax, 0x2000, 4) := by decide
example : (codeCast jumping (reg base .rax (.eq (.lit 0x3000))) (.lea .w64 .rax (.rip 0))).isNone
    = true := by decide

/-! ## What a `write` offers -/

/-- A value pushed, and the registers set to write `n` bytes from where the
stack pointer is. -/
def pushed (n : BitVec 64) : CtxS :=
  { reg (reg (reg (reg (reg base .rsp (.eq (v 0))) .rax (.eq (.lit 1))) .rdi (.eq (.lit 1)))
      .rsi (.eq (v 0))) .rdx (.eq (.lit n)) with
    stack := [.mk (.lit 8) (.cons 0 (.eq (.lit 0x0a216948)) .nil), .mk (.lit 8) (.cons 0 (.eq (v 5)) .nil)] }

/-- What is offered, where a `write` is typed for it. -/
def offered (Γ : CtxS) : Option (List Val × Nat) :=
  match offerAt { offers := true } Γ .syscall with
  | some (_, .fields vs n) => some (vs, n)
  | _ => none

-- four bytes of the value on top of the stack
example : offered (pushed 4) = some ([.lit 0x0a216948], 4) := by decide
-- twelve bytes reach into the next field: both values
example : offered (pushed 12) = some ([.lit 0x0a216948, v 5], 12) := by decide
-- more than is there is not offered as anything known
example : offered (pushed 24) = none := by decide
-- and nothing is said where what the program writes is not being shown
example : (offerAt {} (pushed 4) .syscall).isNone = true := by decide
-- a block the context owns: the fields from the byte the buffer is at
example : offered { reg (pushed 8) .rsi (.eq (.add (v 7) (.lit 8))) with
    owned := [(v 7, .mk (.lit 24) (.cons 8 (.eq (v 2)) (.cons 16 (.eq (v 3)) .nil)))] }
    = some ([v 2], 8) := by decide
-- a field that holds no exactly known value is not known bytes
example : offered { reg (pushed 8) .rsi (.eq (v 7)) with
    owned := [(v 7, .mk (.lit 24) (.cons 8 (.eq (v 2)) .nil))] } = none := by decide

/-! ## A byte stored into a field that holds an exactly known value -/

/-- A pushed word on top of the stack, `rcx` holding exactly a value. -/
def word : CtxS :=
  { reg (reg base .rsp (.eq (v 0))) .rcx (.eq (.lit 0x21)) with
    stack := [.mk (.lit 8) (.cons 0 (.eq (.lit 0x0a3f6948)) .nil)] }

/-- What the top piece of the stack holds after a step. -/
def top (Γ : CtxS) (i : Instr) : Option (List ShapeS) := (step 0x1000 Γ i).map (·.1.stack)

-- the third byte replaced: the word is still exactly known, and worked out
example : top word (.store8 (.sib (some .rsp) none 2) .rcx)
    = some [.mk (.lit 8) (.cons 0 (.eq (.lit 0x0a216948)) .nil)] := by decide
-- from a register whose value is not written out, the word is known as a term
example : top (reg word .rcx (.eq (v 4))) (.store8 (.sib (some .rsp) none 0) .rcx)
    = some [.mk (.lit 8) (.cons 0 (.eq (.app2 (.setByte 0) (.lit 0x0a3f6948) (v 4))) .nil)] := by
  decide
-- from a register that holds no exactly known value, the word is forgotten
example : top (reg word .rcx .int) (.store8 (.sib (some .rsp) none 2) .rcx)
    = some [.mk (.lit 8) .nil] := by decide

/-! ## Memory asked for as a new block of a declared kind -/

/-- A kind of block: 80 bytes, a link that may be null first. -/
def node : ShapeS := .mk (.lit 80) (.cons 0 (.nullable (.ref 1 true (.lit 0))) .nil)

/-- What `rax` holds after an `mmap` of `len` bytes tried as a block of kind 1. -/
def asKind (kinds : List (Nat × ShapeS)) (len : BitVec 64) : Option TyS :=
  (sysMmapKind { kinds := kinds } (reg asking .rsi (.eq (.lit len))) 1).map (·.1.regs.get .rax)

-- an error number, or a writable pointer to a block of the kind
example : asKind [(1, node)] 80 = some (.orErr (.ref 1 true (.lit 0))) := by decide
-- not where the kind does not fit in what was asked for
example : asKind [(1, node)] 64 = none := by decide
-- nor where a typed value of the kind does not admit zero, which is what fresh memory holds
example : asKind [(1, .mk (.lit 80) (.cons 0 (.ref 1 true (.lit 0)) .nil))] 80 = none := by decide
-- nor for a kind that is not declared
example : asKind [] 80 = none := by decide

/-! ## Part of an owned block given back -/

/-- Two pages owned as one block at the address `v 0`, and the registers set
to give back `len` bytes from `p`. -/
def twoPages (p : Val) (len : BitVec 64) : CtxS :=
  { reg (reg (reg base .rax (.eq (.lit 11))) .rdi (.eq p)) .rsi (.eq (.lit len)) with
    owned := [(v 0, .mk (.lit 8192) (.cons 0 (.eq (v 3)) (.cons 4096 (.eq (v 4)) .nil)))] }

-- the second page: the block is regarded as two, each keeping what it holds
example : (unmapSplit (twoPages (.add (v 0) (.lit 4096)) 4096) .syscall).map (·.owned)
    = some [(.add (v 0) (.lit 4096), .mk (.lit 4096) (.cons 0 (.eq (v 4)) .nil)),
            (v 0, .mk (.lit 4096) (.cons 0 (.eq (v 3)) .nil))] := by decide
-- the first page: likewise, from the other end
example : ((unmapSplit (twoPages (v 0) 4096) .syscall).map (·.owned.map (·.2.size)))
    = some [.lit 4096, .lit 4096] := by decide
-- the whole block needs no regarding as two
example : (unmapSplit (twoPages (v 0) 8192) .syscall).isNone = true := by decide
-- and it is then given back: after the split, the call is a step
example : ((unmapSplit (twoPages (.add (v 0) (.lit 4096)) 4096) .syscall).bind
    (stepSys ·)).map (·.1.owned.length) = some 1 := by decide

/-! ## Which part of a context a comparison is about -/

-- a register that does not compare is the part named, and there is a part
-- for each condition
example : subParts (reg base .rdi .int) (reg base .rdi (.eq (v 0))) = some [.reg .rdi] := by decide
example : (subCtx (reg base .rdi .int) (reg base .rdi (.eq (v 0)))).map (·.length) = some 1 := by
  decide
-- room that differs is the room
example : subParts { base with room := .lit 8 } { base with room := .lit 16 } = some [.room] := by
  decide
-- the same context: nothing to show, and nothing to say
example : subParts base base = some [] := by decide
example : (subWhy base base).isNone = true := by decide
-- a stack with a piece too many does not compare, and that is why
example : (subCtx { base with stack := [.mk (.lit 8) .nil] } base).isNone = true := by decide
example : (match subWhy { base with stack := [.mk (.lit 8) .nil] } base with
    | some (.stackPieces 1 0) => true
    | _ => false) = true := by decide
-- bytes detached on one side only: that is the reason given, before the stack
example : (match subWhy { base with above := .lit 16, stackRest := some 1 } base with
    | some .detached => true
    | _ => false) = true := by decide

/-! ## Why an instruction is refused -/

def isReason (Γ : CtxS) (i : Instr) (p : Reject → Bool) : Bool :=
  refused Γ i && p (why 0x1000 Γ i)

-- a number used as an address, and which register
example : isReason base (.mov .w64 (.r_m .rax (mem .rdi 0)))
    (fun | .notPointer .rdi .int false => true | _ => false) = true := by decide
-- a store through a pointer that may only be read through
example : isReason (reg base .rdi (.ptr (.mk (.lit 16) .nil) false (.lit 0)))
    (.mov .w64 (.rm_r (.mem (mem .rdi 0)) .rax))
    (fun | .readOnly .rdi _ => true | _ => false) = true := by decide
-- past the end of the block
example : isReason (reg base .rdi (.ptr (.mk (.lit 16) .nil) true (.lit 0)))
    (.mov .w64 (.r_m .rax (mem .rdi 12)))
    (fun | .pastBlock => true | _ => false) = true := by decide
-- plain bytes over a typed value
example : isReason (reg base .rdi (.ptr rec2 true (.lit 0)))
    (.unary .not .w64 (.mem (mem .rdi 8)))
    (fun | .typedThere => true | _ => false) = true := by decide
-- an index that is not exactly known
example : isReason (reg base .rdi (.ptr (.mk (.lit 16) .nil) true (.lit 0)))
    (.mov .w64 (.r_m .rax (idx .rdi .rcx .s8 0)))
    (fun | .indexUnknown .rcx .int => true | _ => false) = true := by decide
-- bytes of the stack that are in no piece
example : isReason base (.mov .w64 (.r_m .rax (mem .rsp 8)))
    (fun | .noPiece => true | _ => false) = true := by decide
-- the stack pointer as the register written
example : isReason base (.mov .w64 (.rm_i (.reg .rsp) 5))
    (fun | .spOperand => true | _ => false) = true := by decide
-- a divide whose dividend is not exactly known
example : isReason (dividing .int (.eq (.lit 0)) (.eq (.lit 2))) (.mulDiv .div .w64 (.reg .rcx))
    (fun | .divUnknown .rax .int => true | _ => false) = true := by decide

end Tests.Checker
