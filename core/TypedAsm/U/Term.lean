import TypedAsm.U.Outs
import TypedAsm.U.Types
import TypedAsm.U.Ops

/-!
# Values and flags, as terms

A checker works on what a context says written as data. A value is a
number written out, a name, a sum, or what an instruction made of other
values: the value it gave the `k`th register it writes, the value it stored
to memory, or the address it sent control to. The flags are likewise as
written out, a name, or what an instruction left. There is one form for
every instruction: its inputs, and which of its results is meant. What the
result is, is what the instruction's description computes.

No instruction uses more than three registers, so the inputs are three
values; a description takes no notice of those it does not use.
-/

namespace TypedAsm.U

/-- What the names of terms stand for. -/
structure Env where
  val : Nat → BitVec 64 := fun _ => 0
  flags : Nat → Flags := fun _ => ⟨none, none, none, none⟩
  /-- What is known of a value, where it is not written out as data: that
  it is code wanting some contexts, say. -/
  ty : Nat → Ty := fun _ => .any
  /-- Regions held that are not written out: whatever else a caller holds. -/
  frame : Nat → List Region := fun _ => []
  /-- What each enclosing family of contexts ranges over, inside a value
  known to be code wanting the family: the innermost family first. -/
  bound : List Fam := []
  /-- What an instruction computes with, where a term is of an instruction's
  own description and not yet of any context. -/
  slot : Slot → BitVec 64 := fun _ => 0
  /-- The flags before an instruction, likewise. -/
  old : Flags := ⟨none, none, none, none⟩

mutual

/-- A value, as a term. -/
inductive Val
  | lit (v : BitVec 64)
  | var (i : Nat)
  /-- One of the values a family of contexts ranges over: of the family
  `d` out from here, the `i`th. -/
  | bvar (d i : Nat)
  | add (a b : Val)
  /-- A value shifted left by so many bits: an index scaled. -/
  | shl (a : Val) (k : Nat)
  /-- A thing an instruction computes with: in an instruction's description
  only, where the terms of a context are to be put. -/
  | slot (s : Slot)
  /-- An operator on one value, on two, on three; and on two with the flags. -/
  | un (o : Un) (a : Val)
  | bin (o : Bin) (a b : Val)
  | tri (o : Tri) (a b c : Val)
  | fop (o : FOp) (fl : FlagsT) (a b : Val)
  /-- The value the instruction gives the `k`th register it writes. -/
  | out (i : Instr) (k : Nat) (a b c : Val) (fl : FlagsT) (next : BitVec 64) (ea cell : Val)
  /-- The value the instruction stores to memory. -/
  | stored (i : Instr) (a b c : Val) (fl : FlagsT) (next : BitVec 64) (ea cell : Val)
  /-- The address the instruction sends control to. -/
  | goes (i : Instr) (a b c : Val) (fl : FlagsT) (next : BitVec 64) (ea cell : Val)

/-- The flags, as a term. -/
inductive FlagsT
  | lit (f : Flags)
  | var (i : Nat)
  /-- The flags the family `d` out from here ranges over. -/
  | bvar (d : Nat)
  /-- The flags before an instruction: in an instruction's description only. -/
  | old
  /-- The flags an operation leaves, on up to three values and the flags
  before. -/
  | src (o : FSrc) (fl : FlagsT) (a b c : Val)
  /-- The flags the instruction leaves. -/
  | out (i : Instr) (a b c : Val) (fl : FlagsT) (next : BitVec 64) (ea cell : Val)

end

deriving instance DecidableEq for Val, FlagsT

/-- What an instruction leaves, on given inputs: its description's, run on
as many of the inputs as it uses registers; and nothing where it has none. -/
def effectOf (i : Instr) (vals : List (BitVec 64)) (fl : Flags) (next ea cell : BitVec 64) :
    Effect :=
  match i.desc with
  | some d => d.run (vals.take d.srcs.length) fl next ea cell
  | none => ⟨[], fl, 0⟩

/-- Where an instruction sends control, on given inputs. -/
def targetOf (i : Instr) (vals : List (BitVec 64)) (fl : Flags) (next ea cell : BitVec 64) :
    BitVec 64 :=
  match i.desc with
  | some d => (d.goes (vals.take d.srcs.length) fl next ea cell).getD next
  | none => next

mutual

/-- The value a term stands for. -/
def Val.den (ρ : Env) : Val → BitVec 64
  | .lit v => v
  | .var i => ρ.val i
  | .bvar d i => (ρ.bound.getD d {}).vals i
  | .add a b => a.den ρ + b.den ρ
  | .shl a k => a.den ρ <<< k
  | .slot s => ρ.slot s
  | .un o a => o.eval (a.den ρ)
  | .bin o a b => o.eval (a.den ρ) (b.den ρ)
  | .tri o a b c => o.eval (a.den ρ) (b.den ρ) (c.den ρ)
  | .fop o fl a b => o.eval (fl.den ρ) (a.den ρ) (b.den ρ)
  | .out i k a b c fl next ea cell =>
    (((effectOf i [a.den ρ, b.den ρ, c.den ρ] (fl.den ρ) next (ea.den ρ) (cell.den ρ)).regs.getD k
      (.rax, 0)).2)
  | .stored i a b c fl next ea cell =>
    (effectOf i [a.den ρ, b.den ρ, c.den ρ] (fl.den ρ) next (ea.den ρ) (cell.den ρ)).store
  | .goes i a b c fl next ea cell =>
    targetOf i [a.den ρ, b.den ρ, c.den ρ] (fl.den ρ) next (ea.den ρ) (cell.den ρ)

/-- The flags a term stands for. -/
def FlagsT.den (ρ : Env) : FlagsT → Flags
  | .lit f => f
  | .var i => ρ.flags i
  | .bvar d => (ρ.bound.getD d {}).flags
  | .old => ρ.old
  | .src o fl a b c => o.eval (fl.den ρ) (a.den ρ) (b.den ρ) (c.den ρ)
  | .out i a b c fl next ea cell =>
    (effectOf i [a.den ρ, b.den ρ, c.den ρ] (fl.den ρ) next (ea.den ρ) (cell.den ρ)).flags

end

/-- The number a term is, if it is one written out. -/
def Val.lit? : Val → Option (BitVec 64)
  | .lit v => some v
  | _ => none

def FlagsT.lit? : FlagsT → Option Flags
  | .lit f => some f
  | _ => none

theorem Val.lit?_den {ρ : Env} {a : Val} {v : BitVec 64} (h : a.lit? = some v) : a.den ρ = v := by
  cases a <;> first | (cases h; rfl) | cases h

theorem FlagsT.lit?_den {ρ : Env} {a : FlagsT} {f : Flags} (h : a.lit? = some f) : a.den ρ = f := by
  cases a <;> first | (cases h; rfl) | cases h

end TypedAsm.U
