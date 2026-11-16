import Lean
import TypedAsm.Sym

/-!
# Between contexts as written and contexts as data

A user writes a context as a `Ctx`. The checker works on a `Sym.CtxS`. Here
is the way from one to the other and back, for the tactics: `reifyCtx` reads
a context as it is written and gives the term for it, with a table of what
each variable of the term stands for; `denCtx` writes a term back out as a
context, in the form the tactics keep contexts in. The kernel checks that
the term means the context it was read from, by working out `Sym.CtxS.den`.
-/

namespace TypedAsm

open Lean Meta

deriving instance ToExpr for Reg
deriving instance ToExpr for Width
deriving instance ToExpr for NarrowW
deriving instance ToExpr for Cond
deriving instance ToExpr for Scale
deriving instance ToExpr for IndexReg
deriving instance ToExpr for Mem
deriving instance ToExpr for RM
deriving instance ToExpr for Operands
deriving instance ToExpr for RI
deriving instance ToExpr for AluOp
deriving instance ToExpr for UnOp
deriving instance ToExpr for ShiftOp
deriving instance ToExpr for MulDivOp
deriving instance ToExpr for Count
deriving instance ToExpr for Target
deriving instance ToExpr for Instr
deriving instance ToExpr for Flags
deriving instance ToExpr for RegMap
deriving instance ToExpr for Sym.Op1
deriving instance ToExpr for Sym.Op2
deriving instance ToExpr for Sym.Val
deriving instance ToExpr for Sym.Num
deriving instance ToExpr for Sym.TyS, Sym.ShapeS, Sym.ValsS
deriving instance ToExpr for Sym.FlagsS
deriving instance ToExpr for Sym.CtxS
deriving instance ToExpr for Sym.CondS

namespace Sym

instance : Inhabited TyS := ⟨.int⟩
instance : Inhabited ShapeS := ⟨.atom 0⟩

/-- What each variable of a context's terms stands for, as it is written. -/
structure Atoms where
  val : Array Expr := #[]
  num : Array Expr := #[]
  ty : Array Expr := #[]
  shape : Array Expr := #[]
  flags : Array Expr := #[]
  stack : Array Expr := #[]
  owned : Array Expr := #[]

abbrev ReifyM := StateT Atoms MetaM

private def intern (as : Array Expr) (e : Expr) : Nat × Array Expr :=
  match as.findIdx? (· == e) with
  | some i => (i, as)
  | none => (as.size, as.push e)

private def bv64 : Expr := mkApp (mkConst ``BitVec) (mkNatLit 64)

/-- A 64-bit value written as a number. -/
def bvLit? (e : Expr) : Option (BitVec 64) :=
  if e.isAppOfArity ``BitVec.ofNat 2 then
    (e.appArg!.nat? <|> e.appArg!.rawNatLit?).map (BitVec.ofNat 64)
  else if e.isAppOfArity ``OfNat.ofNat 3 then e.nat?.map (BitVec.ofNat 64)
  else none

def natLit? (e : Expr) : Option Nat := e.nat? <|> e.rawNatLit?

/-- An arithmetic or logic operation named outright. -/
def aluOp? (e : Expr) : Option AluOp :=
  match e.constName? with
  | some ``AluOp.add => some .add | some ``AluOp.or => some .or | some ``AluOp.adc => some .adc
  | some ``AluOp.sbb => some .sbb | some ``AluOp.and => some .and | some ``AluOp.sub => some .sub
  | some ``AluOp.xor => some .xor | some ``AluOp.cmp => some .cmp
  | _ => none

/-- `op.apply a b` at a width, taken apart. -/
private def aluApply? (e : Expr) : Option (Nat × AluOp × Expr × Expr) := do
  guard (e.isAppOfArity ``AluOp.apply 4)
  let a := e.getAppArgs
  let n ← natLit? a[0]!
  let op ← aluOp? a[1]!
  return (n, op, a[2]!, a[3]!)

/-- A 64-bit value cut to its low 32 bits, taken apart. -/
private def low? (e : Expr) : Option Expr := do
  guard (e.isAppOfArity ``BitVec.setWidth 3)
  guard (natLit? e.getAppArgs[1]! == some 32)
  return e.appArg!

/-- The term for a 64-bit value as it is written. -/
partial def reifyVal (e : Expr) : ReifyM Val := do
  let e := e.consumeMData
  if let some n := bvLit? e then return .lit n
  -- the result of an operation, as the rules write it
  if e.isAppOfArity ``Prod.fst 3 then
    if let some (64, op, a, b) := aluApply? e.appArg! then
      return .app2 (.alu op .w64) (← reifyVal a) (← reifyVal b)
  if e.isAppOfArity ``BitVec.setWidth 3 && natLit? e.getAppArgs[1]! == some 64 then
    let inner := e.appArg!
    if let some a := low? inner then
      if natLit? inner.getAppArgs[0]! == some 64 then return .app1 .low32 (← reifyVal a)
    if inner.isAppOfArity ``Prod.fst 3 then
      if let some (32, op, a, b) := aluApply? inner.appArg! then
        if let (some a, some b) := (low? a, low? b) then
          return .app2 (.alu op .w32) (← reifyVal a) (← reifyVal b)
  if e.isAppOfArity ``HAdd.hAdd 6 then
    return .add (← reifyVal e.appFn!.appArg!) (← reifyVal e.appArg!)
  if e.isAppOfArity ``HShiftLeft.hShiftLeft 6 then
    if let some k := natLit? e.appArg! then return .shl (← reifyVal e.appFn!.appArg!) k
  let s ← get
  let (i, as) := intern s.val e
  set { s with val := as }
  return .var i

/-- The term for a number as it is written. -/
partial def reifyNum (e : Expr) : ReifyM Num := do
  let e := e.consumeMData
  if let some n := natLit? e then return .lit n
  if e.isAppOfArity ``HAdd.hAdd 6 then
    return .add (← reifyNum e.appFn!.appArg!) (← reifyNum e.appArg!)
  if e.isAppOfArity ``HMul.hMul 6 then
    return .mul (← reifyNum e.appFn!.appArg!) (← reifyNum e.appArg!)
  if e.isAppOfArity ``HSub.hSub 6 then
    return .sub (← reifyNum e.appFn!.appArg!) (← reifyNum e.appArg!)
  if e.isAppOfArity ``BitVec.toNat 2 then
    if e.appFn!.appArg!.nat? == some 64 then return .toNat (← reifyVal e.appArg!)
  if e.isAppOfArity ``ShapeOf.size 2 then
    let s ← get
    let (i, as) := intern s.shape e.appArg!
    set { s with shape := as }
    return .size i
  let s ← get
  let (i, as) := intern s.num e
  set { s with num := as }
  return .var i

private def boolLit? (e : Expr) : Option Bool :=
  if e.isConstOf ``Bool.true then some true
  else if e.isConstOf ``Bool.false then some false else none

mutual

/-- The term for a type as it is written. A type with no form among the
terms is a variable. -/
partial def reifyTy (e : Expr) : ReifyM TyS := do
  let e := e.consumeMData
  let asAtom : ReifyM TyS := do
    let s ← get
    let (i, as) := intern s.ty e
    set { s with ty := as }
    return .atom i
  if e.isConstOf ``Ty.int then return .int
  if e.isAppOfArity ``Ty.eq 1 then return .eq (← reifyVal e.appArg!)
  if e.isAppOfArity ``Ty.ptr 3 then
    let some w := boolLit? e.getAppArgs[1]! | return ← asAtom
    return .ptr (← reifyShape e.getAppArgs[0]!) w (← reifyNum e.getAppArgs[2]!)
  if e.isAppOfArity ``Ty.ref 3 then
    let some tag := natLit? e.getAppArgs[0]! | return ← asAtom
    let some w := boolLit? e.getAppArgs[1]! | return ← asAtom
    return .ref tag w (← reifyNum e.getAppArgs[2]!)
  if e.isAppOfArity ``Ty.nullable 1 then return .nullable (← reifyTy e.appArg!)
  if e.isAppOfArity ``Ty.orErr 1 then return .orErr (← reifyTy e.appArg!)
  if e.isAppOfArity ``Ty.str 1 then
    let some m := boolLit? e.appArg! | return ← asAtom
    return .str m
  asAtom

/-- The term for a shape as it is written. -/
partial def reifyShape (e : Expr) : ReifyM ShapeS := do
  let e := e.consumeMData
  let asAtom : ReifyM ShapeS := do
    let s ← get
    let (i, as) := intern s.shape e
    set { s with shape := as }
    return .atom i
  if e.isAppOfArity ``ShapeOf.raw 2 then return .mk (← reifyNum e.appArg!) .nil
  if e.isAppOfArity ``ShapeOf.slot 2 then
    return .mk (.lit 8) (.cons 0 (← reifyTy e.appArg!) .nil)
  if e.isAppOfArity ``ShapeOf.rep 3 then
    return .rep (← reifyNum e.getAppArgs[1]!) (← reifyShape e.getAppArgs[2]!)
  if e.isAppOfArity ``ShapeOf.mk 3 then
    -- the typed values must be a list written out, each at a place that is a number
    let rec vals (l : Expr) : ReifyM (Option ValsS) := do
      if l.isAppOfArity ``List.nil 1 then return some .nil
      if l.isAppOfArity ``List.cons 3 then
        let p := l.getAppArgs[1]!
        unless p.isAppOfArity ``Prod.mk 4 do return none
        let some o := natLit? p.getAppArgs[2]! | return none
        let τ ← reifyTy p.getAppArgs[3]!
        let some rest ← vals l.appArg! | return none
        return some (.cons o τ rest)
      return none
    let saved ← get
    match ← vals e.getAppArgs[2]! with
    | some vs => return .mk (← reifyNum e.getAppArgs[1]!) vs
    | none => set saved
  asAtom

end

/-- The term for what a context says of the flags. -/
def reifyFlags (e : Expr) : ReifyM FlagsS := do
  let e := e.consumeMData
  if e.isConstOf ``Flags.Any then return .any
  if e.isConstOf ``Flags.Known then return .known
  -- exactly what an operation left
  if let .lam _ _ body _ := e then
    if let some (_, lhs, rhs) := body.eq? then
      if lhs == .bvar 0 && !rhs.hasLooseBVars then
        if rhs.isAppOfArity ``Prod.snd 3 then
          match aluApply? rhs.appArg! with
          | some (64, op, a, b) => return .alu op .w64 (← reifyVal a) (← reifyVal b)
          | some (32, op, a, b) =>
            if let (some a, some b) := (low? a, low? b) then
              return .alu op .w32 (← reifyVal a) (← reifyVal b)
          | _ => pure ()
        if rhs.isAppOfArity ``Flags.ofResult 4 then
          let r := rhs.getAppArgs
          if natLit? r[0]! == some 64 && r[2]!.isConstOf ``Bool.false && r[3]!.isConstOf ``Bool.false
              && r[1]!.isAppOfArity ``HAnd.hAnd 6 then
            return .test (← reifyVal r[1]!.appFn!.appArg!) (← reifyVal r[1]!.appArg!)
  let s ← get
  let (i, as) := intern s.flags e
  set { s with flags := as }
  return .atom i

/-- The cells of a list as far as it is written out, and what it goes on as. -/
private partial def cells (e : Expr) (acc : Array Expr := #[]) : Array Expr × Option Expr :=
  if e.isAppOfArity ``List.cons 3 then cells e.appArg! (acc.push e.getAppArgs[1]!)
  else if e.isAppOfArity ``List.nil 1 then (acc, none)
  else (acc, some e)

/-- The term for a context written out with its registers as a table. -/
def reifyCtx (Γ : Expr) : ReifyM (Option CtxS) := do
  unless Γ.isAppOfArity ``CtxOf.mk 7 do return none
  let c := Γ.getAppArgs
  unless c[1]!.isAppOfArity ``RegMap.get 2 && c[1]!.appArg!.isAppOfArity ``RegMap.mk 17 do
    return none
  let t := c[1]!.appArg!.getAppArgs
  let mut rs : Array TyS := #[]
  for j in [1:17] do rs := rs.push (← reifyTy t[j]!)
  let regs : RegMap TyS := ⟨rs[0]!, rs[1]!, rs[2]!, rs[3]!, rs[4]!, rs[5]!, rs[6]!, rs[7]!,
    rs[8]!, rs[9]!, rs[10]!, rs[11]!, rs[12]!, rs[13]!, rs[14]!, rs[15]!⟩
  let (pieces, stackRest) := cells c[2]!
  let mut stack : List ShapeS := []
  for p in pieces.reverse do stack := (← reifyShape p) :: stack
  let stackRest ← match stackRest with
    | none => pure none
    | some e =>
      let s ← get
      let (i, as) := intern s.stack e
      set { s with stack := as }
      pure (some i)
  let (blocks, ownedRest) := cells c[5]!
  let mut owned : List (Val × ShapeS) := []
  for b in blocks.reverse do
    unless b.isAppOfArity ``Prod.mk 4 do return none
    owned := (← reifyVal b.getAppArgs[2]!, ← reifyShape b.getAppArgs[3]!) :: owned
  let ownedRest ← match ownedRest with
    | none => pure none
    | some e =>
      let s ← get
      let (i, as) := intern s.owned e
      set { s with owned := as }
      pure (some i)
  return some { regs, stack, stackRest, room := ← reifyNum c[3]!, flags := ← reifyFlags c[4]!,
                owned, ownedRest, above := ← reifyNum c[6]! }

/-! ## Back to a context as written -/

private def listE (ty : Expr) (xs : Array Expr) (tail : Option Expr := none) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Level.zero]) ty x acc)
    (tail.getD (mkApp (mkConst ``List.nil [Level.zero]) ty))

/-- The environment the atoms make: what `den` is given. -/
def Atoms.env (a : Atoms) : Expr :=
  let ty := mkConst ``Ty
  let shape := mkApp (mkConst ``ShapeOf) ty
  let flagsTy := mkForall `f .default (mkConst ``Flags) (mkSort .zero)
  let block := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) bv64 shape
  let listOf (t : Expr) := mkApp (mkConst ``List [Level.zero]) t
  mkAppN (mkConst ``Sym.Env.mk)
    #[listE bv64 a.val, listE (mkConst ``Nat) a.num, listE ty a.ty, listE shape a.shape,
      listE flagsTy a.flags, listE (listOf shape) a.stack, listE (listOf block) a.owned]

private def bvBin (inst op : Name) (cls : Name) (a b : Expr) : Expr :=
  mkApp6 (mkConst op [Level.zero, Level.zero, Level.zero]) bv64 bv64 bv64
    (mkApp2 (mkConst inst [Level.zero]) bv64 (mkApp (mkConst cls) (mkNatLit 64))) a b

private def natBin (inst op cls : Name) (a b : Expr) : Expr :=
  let nat := mkConst ``Nat
  mkApp6 (mkConst op [Level.zero, Level.zero, Level.zero]) nat nat nat
    (mkApp2 (mkConst inst [Level.zero]) nat (mkConst cls)) a b

private def setWidthE (from' to : Nat) (a : Expr) : Expr :=
  mkApp3 (mkConst ``BitVec.setWidth) (mkNatLit from') (mkNatLit to) a

/-- A value term written out. -/
partial def denVal (as : Atoms) : Val → MetaM Expr
  | .lit n => return toExpr n
  | .var i => return as.val[i]!
  | .add a b => return bvBin ``instHAdd ``HAdd.hAdd ``BitVec.instAdd (← denVal as a) (← denVal as b)
  | .shl a k => do mkAppM ``HShiftLeft.hShiftLeft #[← denVal as a, mkNatLit k]
  | .app1 .low32 a => return setWidthE 32 64 (setWidthE 64 32 (← denVal as a))
  | .app2 (.alu op .w64) a b => do
    mkAppM ``Prod.fst #[← mkAppOptM ``AluOp.apply #[mkNatLit 64, toExpr op, ← denVal as a, ← denVal as b]]
  | .app2 (.alu op .w32) a b => do
    let r ← mkAppOptM ``AluOp.apply #[mkNatLit 32, toExpr op, setWidthE 64 32 (← denVal as a),
      setWidthE 64 32 (← denVal as b)]
    return setWidthE 32 64 (← mkAppM ``Prod.fst #[r])

/-- A number term written out. -/
partial def denNum (as : Atoms) : Num → MetaM Expr
  | .lit n => return mkNatLit n
  | .var i => return as.num[i]!
  | .add a b => return natBin ``instHAdd ``HAdd.hAdd ``instAddNat (← denNum as a) (← denNum as b)
  | .mul a b => return natBin ``instHMul ``HMul.hMul ``instMulNat (← denNum as a) (← denNum as b)
  | .sub a b => return natBin ``instHSub ``HSub.hSub ``instSubNat (← denNum as a) (← denNum as b)
  | .toNat v => return mkApp2 (mkConst ``BitVec.toNat) (mkNatLit 64) (← denVal as v)
  | .size i => return mkApp2 (mkConst ``ShapeOf.size) (mkConst ``Ty) as.shape[i]!

mutual

/-- A type term written out. -/
partial def denTy (as : Atoms) : TyS → MetaM Expr
  | .int => return mkConst ``Ty.int
  | .eq v => return mkApp (mkConst ``Ty.eq) (← denVal as v)
  | .ptr S w off => return mkApp3 (mkConst ``Ty.ptr) (← denShape as S) (toExpr w) (← denNum as off)
  | .ref tag w off => return mkApp3 (mkConst ``Ty.ref) (mkNatLit tag) (toExpr w) (← denNum as off)
  | .nullable τ => return mkApp (mkConst ``Ty.nullable) (← denTy as τ)
  | .orErr τ => return mkApp (mkConst ``Ty.orErr) (← denTy as τ)
  | .str m => return mkApp (mkConst ``Ty.str) (toExpr m)
  | .atom i => return as.ty[i]!

/-- A shape term written out. -/
partial def denShape (as : Atoms) : ShapeS → MetaM Expr
  | .mk size .nil => return mkApp2 (mkConst ``ShapeOf.raw) (mkConst ``Ty) (← denNum as size)
  | .mk (.lit 8) (.cons 0 τ .nil) =>
    return mkApp2 (mkConst ``ShapeOf.slot) (mkConst ``Ty) (← denTy as τ)
  | .mk size vals => do
    let ty := mkConst ``Ty
    let pairTy := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``Nat) ty
    let rec go : ValsS → MetaM (Array Expr)
      | .nil => return #[]
      | .cons o τ rest => do
        let p := mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) (mkConst ``Nat) ty
          (mkNatLit o) (← denTy as τ)
        return #[p] ++ (← go rest)
    return mkApp3 (mkConst ``ShapeOf.mk) ty (← denNum as size) (listE pairTy (← go vals))
  | .rep n E => return mkApp3 (mkConst ``ShapeOf.rep) (mkConst ``Ty) (← denNum as n) (← denShape as E)
  | .atom i => return as.shape[i]!

end

/-- What a flags term says, written out. -/
def denFlags (as : Atoms) : FlagsS → MetaM Expr
  | .any => return mkConst ``Flags.Any
  | .known => return mkConst ``Flags.Known
  | .atom i => return as.flags[i]!
  | .lit f => do
    withLocalDeclD `f (mkConst ``Flags) fun x => do mkLambdaFVars #[x] (← mkEq x (toExpr f))
  | .test a b => do
    let v ← mkAppM ``Flags.ofResult #[← mkAppM ``HAnd.hAnd #[← denVal as a, ← denVal as b],
      mkConst ``Bool.false, mkConst ``Bool.false]
    withLocalDeclD `f (mkConst ``Flags) fun x => do mkLambdaFVars #[x] (← mkEq x v)
  | .alu op .w64 a b => do
    let r ← mkAppOptM ``AluOp.apply #[mkNatLit 64, toExpr op, ← denVal as a, ← denVal as b]
    let v ← mkAppM ``Prod.snd #[r]
    withLocalDeclD `f (mkConst ``Flags) fun x => do mkLambdaFVars #[x] (← mkEq x v)
  | .alu op .w32 a b => do
    let r ← mkAppOptM ``AluOp.apply #[mkNatLit 32, toExpr op, setWidthE 64 32 (← denVal as a),
      setWidthE 64 32 (← denVal as b)]
    let v ← mkAppM ``Prod.snd #[r]
    withLocalDeclD `f (mkConst ``Flags) fun x => do mkLambdaFVars #[x] (← mkEq x v)

/-- A context term written out, with its registers as a table: the form the
tactics keep contexts in. -/
def denCtx (as : Atoms) (Γ : CtxS) : MetaM Expr := do
  let ty := mkConst ``Ty
  let shape := mkApp (mkConst ``ShapeOf) ty
  let block := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) bv64 shape
  let r := Γ.regs
  let mut tbl : Array Expr := #[ty]
  for τ in [r.rax, r.rcx, r.rdx, r.rbx, r.rsp, r.rbp, r.rsi, r.rdi, r.r8, r.r9, r.r10, r.r11,
      r.r12, r.r13, r.r14, r.r15] do
    tbl := tbl.push (← denTy as τ)
  let regs := mkApp2 (mkConst ``RegMap.get) ty (mkAppN (mkConst ``RegMap.mk) tbl)
  let stack := listE shape (← Γ.stack.toArray.mapM (denShape as)) (Γ.stackRest.map (as.stack[·]!))
  let owned := listE block
    (← Γ.owned.toArray.mapM fun (a, S) => do
      return mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) bv64 shape (← denVal as a)
        (← denShape as S))
    (Γ.ownedRest.map (as.owned[·]!))
  return mkAppN (mkConst ``CtxOf.mk)
    #[ty, regs, stack, ← denNum as Γ.room, ← denFlags as Γ.flags, owned, ← denNum as Γ.above]

/-- Something left to be shown, written out as the proposition it is. -/
def denCond (as : Atoms) : CondS → MetaM Expr
  | .le a b => do mkLe (← denNum as a) (← denNum as b)
  | .cf fl => do
    let P ← denFlags as fl
    withLocalDeclD `f (mkConst ``Flags) fun f => do
      let hyp := (mkApp P f).headBeta
      let concl ← mkEq (← mkAppM ``Option.isSome #[← mkAppM ``Flags.cf #[f]]) (mkConst ``Bool.true)
      mkForallFVars #[f] (← mkArrow hyp concl)

end Sym

end TypedAsm
