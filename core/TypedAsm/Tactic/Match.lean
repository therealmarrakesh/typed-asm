import TypedAsm.Sym

/-!
# Finding the parameters of a label's context

A label's context is written with parameters: how many elements a loop has
consumed, the address of a block. Where a block is handed over to the label,
the parameters are to be found for which the context reached may stand for
the label's. That is done here on the terms the two contexts are read as,
and by arithmetic: a number the pattern has as `8 * k` and the context
reached as `8 * i + 8` settles `k` as `i + 1`, however either is written.

Nothing here is trusted. What is found is a choice of parameters; that the
context reached stands for the label's context at them is the checker's to
compare and the kernel's to confirm.
-/

namespace TypedAsm.Sym.Match

/-- What the unknowns of a pattern have been found to be: numbers and
values, each by the variable that stands for it. -/
structure Sol where
  num : List (Nat × Num) := []
  val : List (Nat × Val) := []

/-- The unknowns: the variables of each kind that stand for one. -/
structure Unknowns where
  num : List Nat := []
  val : List Nat := []

mutual

/-- Whether a value mentions an unknown not yet found. -/
def openVal (u : Unknowns) (s : Sol) : Val → Bool
  | .lit _ => false
  | .var i => u.val.contains i && !(s.val.any (·.1 == i))
  | .add a b => openVal u s a || openVal u s b
  | .shl a _ => openVal u s a
  | .app1 _ a => openVal u s a
  | .app2 _ a b => openVal u s a || openVal u s b

end

/-- Whether a number mentions an unknown not yet found. -/
def openNum (u : Unknowns) (s : Sol) : Num → Bool
  | .lit _ => false
  | .var i => u.num.contains i && !(s.num.any (·.1 == i))
  | .add a b => openNum u s a || openNum u s b
  | .mul a b => openNum u s a || openNum u s b
  | .sub a b => openNum u s a || openNum u s b
  | .toNat v => openVal u s v
  | .size _ => false

/-- A value with the unknowns found so far written out. -/
def substVal (s : Sol) : Val → Val
  | .lit n => .lit n
  | .var i => ((s.val.find? (·.1 == i)).map (·.2)).getD (.var i)
  | .add a b => .add (substVal s a) (substVal s b)
  | .shl a k => .shl (substVal s a) k
  | .app1 f a => .app1 f (substVal s a)
  | .app2 f a b => .app2 f (substVal s a) (substVal s b)

/-- A number with the unknowns found so far written out. -/
def substNum (s : Sol) : Num → Num
  | .lit n => .lit n
  | .var i => ((s.num.find? (·.1 == i)).map (·.2)).getD (.var i)
  | .add a b => .add (substNum s a) (substNum s b)
  | .mul a b => .mul (substNum s a) (substNum s b)
  | .sub a b => .sub (substNum s a) (substNum s b)
  | .toNat v => .toNat (substVal s v)
  | .size i => .size i

/-- So many more of a term, in a sum written as a list. -/
def addTerm (t : Num) (k : Nat) : List (Num × Nat) → List (Num × Nat)
  | [] => [(t, k)]
  | (u, j) :: rest => if u = t then (u, j + k) :: rest else (u, j) :: addTerm t k rest

/-- A number as a constant and so many of each of the terms it is a sum of.
A product by a number written out is so many of the other side; anything
else is a term by itself. -/
def linear : Num → Nat × List (Num × Nat)
  | .lit n => (n, [])
  | .add a b =>
    let (ca, ta) := linear a
    let (cb, tb) := linear b
    (ca + cb, tb.foldl (fun acc (t, k) => addTerm t k acc) ta)
  | .mul (.lit k) a =>
    let (c, ts) := linear a
    (k * c, ts.map fun (t, j) => (t, k * j))
  | .mul a (.lit k) =>
    let (c, ts) := linear a
    (c * k, ts.map fun (t, j) => (t, j * k))
  | t => (0, [(t, 1)])

/-- The number a constant and a list of terms come to, written as a sum. -/
def build (c : Nat) (ts : List (Num × Nat)) : Num :=
  let terms := ts.filterMap fun (t, k) =>
    if k = 0 then none else if k = 1 then some t else some (.mul (.lit k) t)
  match terms with
  | [] => .lit c
  | t :: rest =>
    let sum := rest.foldl Num.add t
    if c = 0 then sum else .add sum (.lit c)

/-- A pattern number brought together with a number: where the pattern is a
sum in which one unknown not yet found occurs, so many times, and nowhere
else, the unknown is what is left of the number, divided: if that comes out
even and takes nothing away that is not there. -/
def num (u : Unknowns) (s : Sol) (p c : Num) : Sol :=
  let p := substNum s p
  if !openNum u s p then s
  else
    let (cp, tp) := linear p
    -- the terms that are an unknown, and the others
    let isUnknown : Num → Bool
      | .var i => u.num.contains i && !(s.num.any (·.1 == i))
      | _ => false
    match tp.filter (isUnknown ·.1), tp.filter (!isUnknown ·.1) with
    | [(.var i, a)], others =>
      if a = 0 || others.any (openNum u s ·.1) then s
      else
        let (cc, tc) := linear c
        -- what is left of the number once the pattern's other terms are taken
        let left? : Option (List (Num × Nat)) :=
          others.foldl (fun acc (t, k) =>
            match acc with
            | none => none
            | some l =>
              match l.find? (·.1 = t) with
              | some (_, j) => if k ≤ j then some (l.map fun (x, y) => if x = t then (x, y - k) else (x, y)) else none
              | none => if k = 0 then some l else none) (some tc)
        match left? with
        | some l =>
          if cp ≤ cc && (cc - cp) % a = 0 && l.all (·.2 % a = 0) then
            { s with num := (i, build ((cc - cp) / a) (l.map fun (t, k) => (t, k / a))) :: s.num }
          else s
        | none => s
    | _, _ => s

/-- One of each term of a list taken from another, if they are all there. -/
def removeEach : List Val → List Val → Option (List Val)
  | [], l => some l
  | t :: ts, l => if l.contains t then removeEach ts (l.erase t) else none

/-- The value a list of terms and a number come to, written as a sum. -/
def buildVal (ts : List Val) (c : BitVec 64) : Val :=
  match ts with
  | [] => .lit c
  | t :: rest =>
    let sum := rest.foldl Val.add t
    if c = 0 then sum else .add sum (.lit c)

/-- A pattern value brought together with a value: an unknown is the value;
an unknown among the terms of a sum is what is left of the value once the
other terms are taken from it; and the parts of the same operation are
brought together part by part. -/
partial def val (u : Unknowns) (s : Sol) (p c : Val) : Sol :=
  let p := substVal s p
  if !openVal u s p then s
  else
    match p with
    | .var i => { s with val := (i, c) :: s.val }
    | _ =>
      let (tp, cp) := p.summands
      let isUnknown : Val → Bool
        | .var i => u.val.contains i && !(s.val.any (·.1 == i))
        | _ => false
      match tp.filter isUnknown, tp.filter (!isUnknown ·) with
      | [.var i], others =>
        if others.any (openVal u s) then s
        else
          let (tc, cc) := c.summands
          match removeEach others tc with
          | some l => { s with val := (i, buildVal l (cc - cp)) :: s.val }
          | none => s
      | _, _ =>
        match p, c with
        | .shl a k, .shl b j => if k = j then val u s a b else s
        | .app1 f a, .app1 g b => if f = g then val u s a b else s
        | .app2 f a₁ a₂, .app2 g b₁ b₂ => if f = g then val u (val u s a₁ b₁) a₂ b₂ else s
        | _, _ => s

mutual

/-- A pattern type brought together with a type, where they are of one form. -/
partial def ty (u : Unknowns) (s : Sol) : TyS → TyS → Sol
  | .eq p, .eq c => val u s p c
  | .ptr Sp _ op, .ptr Sc _ oc => num u (shape u s Sp Sc) op oc
  | .ref tp _ op, .ref tc _ oc => if tp = tc then num u s op oc else s
  | .nullable p, .nullable c => ty u s p c
  | .orErr p, .orErr c => ty u s p c
  | _, _ => s

/-- A pattern shape brought together with a shape. -/
partial def shape (u : Unknowns) (s : Sol) : ShapeS → ShapeS → Sol
  | .mk zp vp, .mk zc vc => vals u (num u s zp zc) vp vc
  | .rep np Ep, .rep nc Ec => shape u (num u s np nc) Ep Ec
  | _, _ => s

/-- The typed values of a pattern shape, each brought together with the one
at the same place. -/
partial def vals (u : Unknowns) (s : Sol) : ValsS → ValsS → Sol
  | .cons o τ rest, vc =>
    let s := match vc.find o with
      | some υ => ty u s τ υ
      | none => s
    vals u s rest vc
  | .nil, _ => s

end

/-- The parameters of a pattern context, found from the context reached:
register by register, the stack and the blocks owned piece by piece, and the
room. A parameter nothing settles is left out. -/
def ctx (u : Unknowns) (pat cur : CtxS) : Sol := Id.run do
  let mut s : Sol := {}
  -- twice over: what one part settles may be what another needs
  for _ in [0:2] do
    for r in regList do
      s := ty u s (pat.regs.get r) (cur.regs.get r)
    for (p, c) in pat.stack.zip cur.stack do
      s := shape u s p c
    s := num u s pat.room cur.room
    for ((ap, Sp), (ac, Sc)) in pat.owned.zip cur.owned do
      s := shape u (val u s ap ac) Sp Sc
    s := num u s pat.above cur.above
  return s

end TypedAsm.Sym.Match
