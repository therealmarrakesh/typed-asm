import TypedAsm.U.Fill

/-!
# Each instruction, as data

One table: for each instruction, the registers it computes with, the
memory it touches, what must hold for it not to fault of itself, and what
it leaves: in each register it writes, in the flags, in the bytes it
writes, and where it sends control. Each of those is a term built of
operators on the things it computes with.

Nothing else is said of any instruction anywhere. Which registers it
writes, whether its flags are defined, what a condition on them says of its
operands, how its result reads: all of that is read off these terms.
-/

namespace TypedAsm.U

open TypedAsm

/-- An instruction, as data. -/
structure Sem where
  /-- The registers whose values it computes with. -/
  srcs : List Reg
  /-- A memory operand whose address it uses as a number. -/
  ea : Option Mem := none
  /-- The bytes it reads: where, and how many. -/
  rd : Option (Mem × Nat) := none
  /-- The bytes it writes. -/
  wr : Option (Mem × Nat) := none
  /-- What must hold for it not to fault of itself, and of what values. -/
  guard : GuardE := .none
  ga : Val := .lit 0
  gb : Val := .lit 0
  gc : Val := .lit 0
  /-- What it leaves in each register it writes, the later winning. -/
  outs : List (Reg × Val) := []
  /-- The flags it leaves. -/
  flags : FlagsT := .old
  /-- What it gives the bytes it writes. -/
  store : Val := .lit 0
  /-- Where it sends control, if not to the instruction after it. -/
  goes : Option Val := none

/-- Whether an instruction's terms speak only of what it computes with. -/
def Sem.slotOnly (s : Sem) : Bool :=
  s.ga.slotOnly && s.gb.slotOnly && s.gc.slotOnly && s.outs.all (fun p => p.2.slotOnly) &&
    s.flags.slotOnly && s.store.slotOnly &&
    (match s.goes with
     | some t => t.slotOnly
     | none => true)

/-- The setting in which an instruction's terms stand for given inputs. -/
def slotEnv (vals : List (BitVec 64)) (fl : Flags) (next ea cell : BitVec 64) : Env where
  slot
    | .arg j => vals.getD j 0
    | .cell => cell
    | .ea => ea
    | .next => next
  old := fl

/-- The value of a register an instruction uses, by position. -/
abbrev A (j : Nat) : Val := .slot (.arg j)

/-- An operand: the register's value, the `k`th used, or the bytes read. -/
def rmV (x : RM) (k : Nat) : Val :=
  match x with
  | .reg _ => A k
  | .mem _ => .slot .cell

/-- A number written in an instruction, at a width. -/
def immV (w : Width) (imm : BitVec 32) : Val := .lit (wide (imm.signExtend w.bits))

/-- The source of a two-operand form. -/
def srcV (w : Width) : Operands → Val
  | .rm_r d _ => A (rmRegs d).length
  | .r_m _ _ => .slot .cell
  | .rm_i _ imm => immV w imm

/-- A count: written in the instruction, or the register that holds it, the
`k`th used. -/
def countV (c : Count) (k : Nat) : Val :=
  match c with
  | .imm n => .lit (BitVec.ofNat 64 n.toNat)
  | .cl => A k

/-- What is left where an operand is given a value: the register, with any
others; or the bytes written. -/
def Sem.give (s : Sem) (x : RM) (v : Val) : Sem :=
  match x with
  | .reg r => { s with outs := (r, v) :: s.outs }
  | .mem _ => { s with store := v }

/-- **Each instruction, as data.** Nothing for a system call, which is
described by the system, or for what is not to be reached. -/
def _root_.TypedAsm.Instr.sem : Instr → Option Sem
  | .alu op w ops =>
    let d := ops.dst
    let s : Sem :=
      { srcs := rmRegs d ++ srcRegs ops, ea := opsMem ops
        rd := if (opsMem ops).isSome then (opsMem ops).map (·, wbytes w) else none
        wr := if (rmMem d).isSome && op.writesDst then (opsMem ops).map (·, wbytes w) else none
        guard := .alu op w, ga := rmV d 0, gb := srcV w ops
        flags := .src (.alu op w) .old (rmV d 0) (srcV w ops) (.lit 0) }
    some (if op.writesDst then s.give d (.fop (.alu op w) .old (rmV d 0) (srcV w ops)) else s)
  | .test w dst src =>
    some
      { srcs := rmRegs dst ++ (match src with | .reg r => [r] | .imm _ => [])
        ea := rmMem dst
        rd := if (rmMem dst).isSome then (rmMem dst).map (·, wbytes w) else none
        flags := .src (.test w) .old (rmV dst 0)
          (match src with
           | .reg _ => A (rmRegs dst).length
           | .imm i => immV w i) (.lit 0) }
  | .unary .neg w dst =>
    some (Sem.give
      { srcs := rmRegs dst, ea := rmMem dst
        rd := if (rmMem dst).isSome then (rmMem dst).map (·, wbytes w) else none
        wr := if (rmMem dst).isSome then (rmMem dst).map (·, wbytes w) else none
        flags := .src (.neg w) .old (rmV dst 0) (.lit 0) (.lit 0) }
      dst (.un (.neg w) (rmV dst 0)))
  | .unary .not w dst =>
    some (Sem.give
      { srcs := rmRegs dst, ea := rmMem dst
        rd := if (rmMem dst).isSome then (rmMem dst).map (·, wbytes w) else none
        wr := if (rmMem dst).isSome then (rmMem dst).map (·, wbytes w) else none }
      dst (.un (.not w) (rmV dst 0)))
  | .shift op w dst c =>
    some (Sem.give
      { srcs := rmRegs dst ++ (match c with | .cl => [.rcx] | .imm _ => [])
        ea := rmMem dst
        rd := if (rmMem dst).isSome then (rmMem dst).map (·, wbytes w) else none
        wr := if (rmMem dst).isSome then (rmMem dst).map (·, wbytes w) else none
        flags := .src (.shift op w) .old (rmV dst 0) (countV c (rmRegs dst).length) (.lit 0) }
      dst (.bin (.shift op w) (rmV dst 0) (countV c (rmRegs dst).length)))
  | .mulDiv op w src =>
    some
      { srcs := [.rdx, .rax] ++ rmRegs src, ea := rmMem src
        rd := if (rmMem src).isSome then (rmMem src).map (·, wbytes w) else none
        guard := .mul op w, ga := A 0, gb := A 1, gc := rmV src 2
        outs := [(.rax, .tri (.mulLo op w) (A 0) (A 1) (rmV src 2)),
                 (.rdx, .tri (.mulHi op w) (A 0) (A 1) (rmV src 2))]
        flags := .src (.mul op w) .old (A 0) (A 1) (rmV src 2) }
  | .imul2 w dst src =>
    some
      { srcs := dst :: rmRegs src, ea := rmMem src
        rd := if (rmMem src).isSome then (rmMem src).map (·, wbytes w) else none
        outs := [(dst, .bin (.imul w) (A 0) (rmV src 1))]
        flags := .src (.imul w) .old (A 0) (rmV src 1) (.lit 0) }
  | .imul3 w dst src imm =>
    some
      { srcs := rmRegs src, ea := rmMem src
        rd := if (rmMem src).isSome then (rmMem src).map (·, wbytes w) else none
        outs := [(dst, .bin (.imul w) (rmV src 0) (immV w imm))]
        flags := .src (.imul w) .old (rmV src 0) (immV w imm) (.lit 0) }
  | .popcnt w dst src =>
    some
      { srcs := rmRegs src, ea := rmMem src
        rd := if (rmMem src).isSome then (rmMem src).map (·, wbytes w) else none
        outs := [(dst, .un (.popcnt w) (rmV src 0))]
        flags := .src (.popcnt w) .old (rmV src 0) (.lit 0) (.lit 0) }
  | .bswap w r => some { srcs := [r], outs := [(r, .un (.bswap w) (A 0))] }
  | .cdq => some { srcs := [.rax], outs := [(.rdx, .un (.signFill .w32) (A 0))] }
  | .cqo => some { srcs := [.rax], outs := [(.rdx, .un (.signFill .w64) (A 0))] }
  | .mov w ops =>
    let d := ops.dst
    some (Sem.give
      { srcs := srcRegs ops, ea := opsMem ops
        rd := if (match ops with | .r_m _ _ => true | _ => false) then
            (opsMem ops).map (·, wbytes w) else none
        wr := if (rmMem d).isSome then (opsMem ops).map (·, wbytes w) else none }
      d (match ops with
         | .rm_r _ _ => .un (.trunc w) (A 0)
         | .r_m _ _ => .un (.trunc w) (.slot .cell)
         | .rm_i _ imm => immV w imm))
  | .movAbs dst imm => some { srcs := [], outs := [(dst, .lit imm)] }
  | .store8 dst src =>
    some { srcs := [src], ea := some dst, wr := some (dst, 1), store := .un .low8 (A 0) }
  | .store16 dst src =>
    some { srcs := [src], ea := some dst, wr := some (dst, 2), store := .un .low16 (A 0) }
  | .movzx w dst sw src =>
    some
      { srcs := rmRegs src, ea := rmMem src
        rd := if (rmMem src).isSome then (rmMem src).map (·, nbytes sw) else none
        outs := [(dst, .un (.zx w sw) (rmV src 0))] }
  | .movsx w dst sw src =>
    some
      { srcs := rmRegs src, ea := rmMem src
        rd := if (rmMem src).isSome then (rmMem src).map (·, nbytes sw) else none
        outs := [(dst, .un (.sx w sw) (rmV src 0))] }
  | .movsxd dst src =>
    some
      { srcs := rmRegs src, ea := rmMem src
        rd := if (rmMem src).isSome then (rmMem src).map (·, 4) else none
        outs := [(dst, .un .sxd (rmV src 0))] }
  | .lea w dst addr =>
    some { srcs := [], ea := some addr, outs := [(dst, .un (.trunc w) (.slot .ea))] }
  | .cmov c w dst src =>
    some
      { srcs := dst :: rmRegs src, ea := rmMem src
        rd := if (rmMem src).isSome then (rmMem src).map (·, wbytes w) else none
        guard := .cond c
        outs := [(dst, .fop (.cmov c w) .old (A 0) (rmV src 1))] }
  | .setcc c dst =>
    some
      (match dst with
       | .reg r =>
         { srcs := [r], guard := .cond c, outs := [(r, .fop (.setcc c) .old (A 0) (.lit 0))] }
       | .mem m =>
         { srcs := [], ea := some m, wr := some (m, 1), guard := .cond c
           store := .fop (.condByte c) .old (.lit 0) (.lit 0) })
  | .push r =>
    some
      { srcs := [r, .rsp], ea := some pushMem, wr := some (pushMem, 8)
        outs := [(.rsp, .bin .add (A 1) (.lit (-8)))], store := A 0 }
  | .pop r =>
    some
      { srcs := [.rsp], ea := some topMem, rd := some (topMem, 8)
        outs := [(.rsp, .bin .add (A 0) (.lit 8)), (r, .slot .cell)] }
  | .nop => some { srcs := [] }
  | .jmp (.rel d) =>
    some { srcs := [], goes := some (.bin .add (.slot .next) (.lit (d.signExtend 64))) }
  | .jmp (.ind (.reg r)) => some { srcs := [r], goes := some (A 0) }
  | .jmp (.ind (.mem m)) => some { srcs := [], rd := some (m, 8), goes := some (.slot .cell) }
  | .jcc c d =>
    some
      { srcs := [], guard := .cond c
        goes := some (.fop (.cmov c .w64) .old (.slot .next)
          (.bin .add (.slot .next) (.lit (d.signExtend 64)))) }
  | .call (.rel d) =>
    some
      { srcs := [.rsp], wr := some (pushMem, 8)
        outs := [(.rsp, .bin .add (A 0) (.lit (-8)))], store := .slot .next
        goes := some (.bin .add (.slot .next) (.lit (d.signExtend 64))) }
  | .call (.ind (.reg r)) =>
    some
      { srcs := [.rsp, r], wr := some (pushMem, 8)
        outs := [(.rsp, .bin .add (A 0) (.lit (-8)))], store := .slot .next, goes := some (A 1) }
  | .call (.ind (.mem m)) =>
    some
      { srcs := [.rsp], rd := some (m, 8), wr := some (pushMem, 8)
        outs := [(.rsp, .bin .add (A 0) (.lit (-8)))], store := .slot .next
        goes := some (.slot .cell) }
  | .ret =>
    some
      { srcs := [.rsp], rd := some (topMem, 8)
        outs := [(.rsp, .bin .add (A 0) (.lit 8))], goes := some (.slot .cell) }
  | .ud2 => none
  | .syscall => none

/-- What the data comes to, on given inputs: the description the machine's
own step is proved to follow. -/
def Sem.toDesc (s : Sem) : Desc where
  srcs := s.srcs
  ea := s.ea
  rd := s.rd
  wr := s.wr
  guard := fun vals fl next ea cell =>
    s.guard.eval fl (s.ga.den (slotEnv vals fl next ea cell))
      (s.gb.den (slotEnv vals fl next ea cell)) (s.gc.den (slotEnv vals fl next ea cell))
  run := fun vals fl next ea cell =>
    ⟨s.outs.map fun p => (p.1, p.2.den (slotEnv vals fl next ea cell)),
      s.flags.den (slotEnv vals fl next ea cell), s.store.den (slotEnv vals fl next ea cell)⟩
  goes := fun vals fl next ea cell => s.goes.map fun t => t.den (slotEnv vals fl next ea cell)

/-- **Each instruction, described**: what its data comes to. -/
def _root_.TypedAsm.Instr.desc (i : Instr) : Option Desc := i.sem.map Sem.toDesc

theorem sem_desc (i : Instr) : i.sem.map Sem.toDesc = i.desc := rfl

end TypedAsm.U
