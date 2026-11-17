import TypedAsm.U.Instr

/-!
# What each instruction does to each flag

Of each flag, an instruction leaves it as it was, or leaves it defined, or
neither can be said. Here is which, as a table, and that the descriptions
say so. Whether a condition can be decided at some point of a program is
then a matter of looking back through the instructions that led there.
-/

namespace TypedAsm.U

open TypedAsm

/-- The four flags. -/
inductive Flag
  | cf | zf | sf | of
  deriving DecidableEq

def _root_.TypedAsm.Flags.get (f : Flags) : Flag → Option Bool
  | .cf => f.cf
  | .zf => f.zf
  | .sf => f.sf
  | .of => f.of

/-- What an instruction does to a flag. -/
inductive Fate
  /-- It is as it was. -/
  | keeps
  /-- It is defined. -/
  | defines
  /-- It is defined, if another flag was: the one the instruction reads. -/
  | definesIf (y : Flag)
  /-- Neither can be said. -/
  | lost
  deriving DecidableEq

/-- What a fate says of a flag before and after, given all the flags
before. -/
def Fate.Holds : Fate → Flags → Option Bool → Option Bool → Prop
  | .keeps, _, old, new => new = old
  | .defines, _, _, new => new.isSome = true
  | .definesIf y, all, _, new => (all.get y).isSome = true → new.isSome = true
  | .lost, _, _, _ => True

/-- A shift or a rotation by a count written out. -/
def shiftFate (op : ShiftOp) (n : Nat) (x : Flag) : Fate :=
  if n = 0 then .keeps else
  match op, x with
  | _, .of => if n = 1 then .defines else .lost
  | .rol, .cf | .ror, .cf => .defines
  | .rol, _ | .ror, _ => .keeps
  | _, _ => .defines

/-- A multiplication: carry and overflow say whether the product fit. -/
def mulFate : Flag → Fate
  | .cf | .of => .defines
  | _ => .lost

/-- **What each instruction does to each flag.** -/
def _root_.TypedAsm.Instr.fate : Instr → Flag → Fate
  | .alu .adc _ _, _ | .alu .sbb _ _, _ => .definesIf .cf
  | .alu _ _ _, _ => .defines
  | .test _ _ _, _ => .defines
  | .unary .neg _ _, _ => .defines
  | .shift op w _ (.imm k), x => shiftFate op (k.toNat % w.bits) x
  | .shift _ _ _ .cl, _ => .lost
  | .mulDiv .mul _ _, x | .mulDiv .imul _ _, x => mulFate x
  | .mulDiv _ _ _, _ => .lost
  | .imul2 _ _ _, x | .imul3 _ _ _ _, x => mulFate x
  | .popcnt _ _ _, _ => .defines
  | .ud2, _ | .syscall, _ => .lost
  | _, _ => .keeps

theorem rmSet_flags (x : RM) (v : BitVec 64) (f : Flags) (more : List (Reg × BitVec 64)) :
    (rmSet x v f more).flags = f := by
  cases x <;> rfl

theorem desc1_fate {i : Instr} {d : Desc1} (hd : i.desc1 = some d) (vals : List (BitVec 64))
    (fl : Flags) (a c : BitVec 64) (x : Flag) :
    (i.fate x).Holds fl (fl.get x) ((d.run vals fl a c).flags.get x) := by
  cases i with
  | alu op w ops =>
    cases hd
    cases op <;> first
      | (rcases ops with ⟨dst | m, src⟩ | ⟨dst, m⟩ | ⟨dst | m, imm⟩ <;> cases x <;> rfl)
      | (intro hcf
         obtain ⟨cf, zf, sf, of⟩ := fl
         cases cf with
         | none => cases hcf
         | some c =>
           rcases ops with ⟨dst | m, src⟩ | ⟨dst, m⟩ | ⟨dst | m, imm⟩ <;> cases x <;> rfl)
  | test w dst src => cases hd; cases x <;> rfl
  | unary op w dst =>
    cases op <;> cases hd
    · show Option.isSome (Flags.get (rmSet _ _ _ _).flags x) = true
      rw [rmSet_flags]; cases x <;> rfl
    · show Flags.get (rmSet _ _ _ _).flags x = _
      rw [rmSet_flags]
  | shift op w dst cnt =>
    cases hd
    cases cnt with
    | cl => exact trivial
    | imm k =>
      show (shiftFate op (k.toNat % w.bits) x).Holds fl (fl.get x)
        (Flags.get (rmSet _ _ (op.eval fl _ (k.toNat % w.bits)).2 _).flags x)
      rw [rmSet_flags]
      generalize k.toNat % w.bits = n
      unfold shiftFate ShiftOp.eval
      by_cases h0 : n = 0
      · simp only [h0, ↓reduceIte]; rfl
      · by_cases h1 : n = 1
        · subst h1; cases op <;> cases x <;> rfl
        · simp only [h0, h1, ↓reduceIte]
          cases op <;> cases x <;> first | exact trivial | rfl
  | mulDiv op w src =>
    cases hd
    cases op
    · cases x <;> first | exact trivial | rfl
    · cases x <;> first | exact trivial | rfl
    · exact trivial
    · exact trivial
  | imul2 w dst src => cases hd; cases x <;> first | exact trivial | rfl
  | imul3 w dst src imm => cases hd; cases x <;> first | exact trivial | rfl
  | popcnt w dst src => cases hd; cases x <;> rfl
  | mov w ops =>
    cases hd
    show Flags.get (rmSet _ _ _ _).flags x = _
    rw [rmSet_flags]
  | setcc cnd dst => cases hd; cases dst <;> rfl
  | jmp t => cases hd
  | jcc cnd rel => cases hd
  | call t => cases hd
  | ret => cases hd
  | ud2 => cases hd
  | syscall => cases hd
  | _ => cases hd; rfl

/-- **Each instruction does to each flag what the table says**, whatever it
is run on. -/
theorem desc_fate {i : Instr} {d : Desc} (hd : i.desc = some d) (vals : List (BitVec 64))
    (fl : Flags) (next a c : BitVec 64) (x : Flag) :
    (i.fate x).Holds fl (fl.get x) ((d.run vals fl next a c).flags.get x) := by
  cases hi : i.desc1 with
  | some d₁ =>
    have e : d = d₁.toDesc := Option.some.inj ((desc_of_desc1 hi).symm.trans hd).symm
    subst e
    exact desc1_fate hi vals fl a c x
  | none =>
    cases i with
    | jmp t => rcases t with rel | (r | m) <;> cases hd <;> rfl
    | jcc cnd rel => cases hd; rfl
    | call t => rcases t with rel | (r | m) <;> cases hd <;> rfl
    | ret => cases hd; rfl
    | unary op w dst => cases op <;> cases hi
    | _ => first | (cases hi; done) | (cases hd; done)

end TypedAsm.U
