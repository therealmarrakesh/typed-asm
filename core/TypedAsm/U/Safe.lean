import TypedAsm.U.Labels
import TypedAsm.Machine

/-!
# A checked program is safe

What the checker decides, as a statement of the machine. A program that
checks, started at one of its labels in a state that matches a member of
the label's family, runs safely for ever: on the machine that looks its
instructions up, and so on the machine that decodes them from memory,
wherever the program's bytes are loaded where it executes.
-/

namespace TypedAsm.U

open TypedAsm

variable {fetch : Fetch} {sys : Syscall} {Ψ : MemTy}

/-- **A checked program started at a label, in a state matching a member of
the label's family, is safe**: on any machine that fetches its instructions
at their addresses, under any system that does what Linux is described to
do. -/
theorem safe_of_checked {D : SysDesc} (hD : Describes sys D) (hkind : D.kind = linuxKind)
    {pg : Prog} (hpre : PreSound fetch sys Ψ D pg.pre) {labels : List Label} {fuel k : Nat}
    (hcode : ∀ e ∈ pg.code, fetch e.1 = some (e.2.1, e.2.2)) (hk : KindsOk Ψ pg.kinds)
    (hst : StaticsOk fetch sys Ψ pg.statics) (hwf : Ψ.WF)
    (h : checkProgram pg labels fuel k = true)
    {l : Label} (hl : l ∈ labels) {s : State} (hrip : s.rip = l.addr) (ρ : Env) (fam : Fam)
    (hw : ∀ n, (∀ l' ∈ labels, ∀ (ρ' : Env) (fam' : Fam),
        Ok fetch sys Ψ n l'.addr (l'.pat.den { ρ' with bound := fam' :: ρ'.bound })) →
      WellTyped fetch sys Ψ n (l.pat.den { ρ with bound := fam :: ρ.bound }) s) :
    Safe fetch sys s :=
  safe_of_safeN fun n =>
    program_ok hD hkind hpre hcode hk hst h n l hl ρ fam n (Nat.le_refl n) Ψ (MemTy.Ext.refl Ψ)
      hwf s hrip (hw n fun l' hl' ρ' fam' => program_ok hD hkind hpre hcode hk hst h n l' hl' ρ' fam')

/-- **And safe on the machine that decodes its instructions from memory**,
where the program is loaded and the system changes nothing a program's
instructions are read from. -/
theorem safeMem_of_checked {D : SysDesc} (hD : Describes sys D) (hkind : D.kind = linuxKind)
    {pg : Prog} (hpre : PreSound fetch sys Ψ D pg.pre) {labels : List Label} {fuel k : Nat}
    (hcode : ∀ e ∈ pg.code, fetch e.1 = some (e.2.1, e.2.2)) (hk : KindsOk Ψ pg.kinds)
    (hst : StaticsOk fetch sys Ψ pg.statics) (hwf : Ψ.WF)
    (h : checkProgram pg labels fuel k = true)
    {l : Label} (hl : l ∈ labels) {s : State} (hrip : s.rip = l.addr) (ρ : Env) (fam : Fam)
    (hw : ∀ n, (∀ l' ∈ labels, ∀ (ρ' : Env) (fam' : Fam),
        Ok fetch sys Ψ n l'.addr (l'.pat.den { ρ' with bound := fam' :: ρ'.bound })) →
      WellTyped fetch sys Ψ n (l.pat.den { ρ with bound := fam :: ρ.bound }) s)
    (hsys : ∀ s, (sys s).All (Frame s)) (hload : Loaded fetch s) : SafeMem sys s :=
  SafeMem.of_safe hsys hload (safe_of_checked hD hkind hpre hcode hk hst hwf h hl hrip ρ fam hw)

end TypedAsm.U
