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
