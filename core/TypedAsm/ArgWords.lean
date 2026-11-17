import TypedAsm.Data

/-!
# The words and texts of a program's arguments

Where each argument's text lies among the texts, that each ends in a byte
of nought, and that the word the kernel puts on the stack for an argument
is the address of its text. Facts of lists of bytes.
-/

namespace TypedAsm

/-! ## The contract -/

/-! ## How the model lays out the arguments -/

theorem textsAt_length : ∀ (ts : List (List Byte)) (a : Nat), (textsAt ts a).length = ts.length
  | [], _ => rfl
  | _ :: ts, a => by simp only [textsAt, List.length_cons, textsAt_length ts]

theorem textBytes_length_cons (t : List Byte) (ts : List (List Byte)) :
    (textBytes (t :: ts)).length = t.length + 1 + (textBytes ts).length := by
  simp only [textBytes, List.length_append, List.length_cons]
  omega

/-- Each text lies within the run of texts, and is not empty. -/
theorem textsAt_bounds : ∀ (ts : List (List Byte)) (a : Nat), ∀ t ∈ textsAt ts a,
    a ≤ t.1 ∧ t.1 + t.2 ≤ a + (textBytes ts).length ∧ 0 < t.2
  | [], _, t, h => by simp [textsAt] at h
  | u :: ts, a, t, h => by
    rw [textBytes_length_cons]
    simp only [textsAt, List.mem_cons] at h
    rcases h with rfl | h
    · dsimp only
      omega
    · have := textsAt_bounds ts _ t h
      omega

/-- The last byte of each text is the zero that ends it. -/
theorem textsAt_zero : ∀ (ts : List (List Byte)) (a : Nat), ∀ t ∈ textsAt ts a,
    (textBytes ts)[t.1 - a + t.2 - 1]? = some 0
  | [], _, t, h => by simp [textsAt] at h
  | u :: ts, a, t, h => by
    simp only [textsAt, List.mem_cons] at h
    rcases h with rfl | h
    · show (u ++ 0 :: textBytes ts)[a - a + (u.length + 1) - 1]? = some 0
      rw [show a - a + (u.length + 1) - 1 = u.length by omega,
        List.getElem?_append_right (Nat.le_refl _)]
      simp
    · have hb := textsAt_bounds ts _ t h
      have ih := textsAt_zero ts _ t h
      show (u ++ 0 :: textBytes ts)[t.1 - a + t.2 - 1]? = some 0
      rw [List.getElem?_append_right (by omega),
        show t.1 - a + t.2 - 1 - u.length = (t.1 - (a + (u.length + 1)) + t.2 - 1) + 1 by omega,
        List.getElem?_cons_succ]
      exact ih

/-- Two texts are the same one, or one ends before the other starts. -/
theorem textsAt_apart : ∀ (ts : List (List Byte)) (a : Nat), ∀ t ∈ textsAt ts a,
    ∀ u ∈ textsAt ts a, t = u ∨ t.1 + t.2 ≤ u.1 ∨ u.1 + u.2 ≤ t.1
  | [], _, t, h, _, _ => by simp [textsAt] at h
  | v :: ts, a, t, ht, u, hu => by
    simp only [textsAt, List.mem_cons] at ht hu
    rcases ht with rfl | ht <;> rcases hu with rfl | hu
    · exact .inl rfl
    · have := textsAt_bounds ts _ u hu
      dsimp only
      omega
    · have := textsAt_bounds ts _ t ht
      dsimp only
      omega
    · exact textsAt_apart ts _ t ht u hu

theorem flatMap_le64_length {α : Type} (l : List α) (f : α → BitVec 64) :
    (l.flatMap fun x => le64 (f x)).length = 8 * l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, le64_length, ih, List.length_cons]
    omega

/-- Past eight bytes, a 64-bit value is read from what follows them. -/
theorem word64_shift (v : BitVec 64) (rest : List Byte) (k : Nat) :
    word64 (le64 v ++ rest) (8 + k) = word64 rest k := by
  have h : ∀ j, (le64 v ++ rest).getD (8 + k + j) 0 = rest.getD (k + j) 0 := by
    intro j
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [le64_length]; omega), le64_length,
      show 8 + k + j - 8 = k + j by omega]
  have h0 := h 0
  simp only [Nat.add_zero] at h0
  simp only [word64, h, h0]

theorem word64_flatMap {α : Type} (l : List α) (f : α → BitVec 64) (rest : List Byte) (i : Nat)
    (hi : i < l.length) :
    word64 (l.flatMap (fun x => le64 (f x)) ++ rest) (8 * i) = f l[i] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [List.flatMap_cons, List.append_assoc, List.getElem_cons_zero]
      exact word64_le64 _ _
    | succ j =>
      simp only [List.flatMap_cons, List.append_assoc, List.getElem_cons_succ]
      rw [show 8 * (j + 1) = 8 + 8 * j by omega, word64_shift]
      exact ih j (by simpa using hi)

theorem argBlock_length (args : List (List Byte)) :
    (argBlock args).length = 8 * (args.length + 5) + (textBytes args).length := by
  simp only [argBlock, List.length_append, le64_length, flatMap_le64_length, textsAt_length]
  omega

/-- After the words come the texts. -/
theorem argBlock_text (args : List (List Byte)) (j : Nat) :
    (argBlock args)[8 * (args.length + 5) + j]? = (textBytes args)[j]? := by
  have e : argBlock args =
      (le64 (BitVec.ofNat 64 args.length) ++
        (textsAt args (textBase args)).flatMap (fun t => le64 (BitVec.ofNat 64 t.1)) ++
        le64 0 ++ le64 0 ++ le64 0 ++ le64 0) ++ textBytes args := by
    simp only [argBlock, List.append_assoc]
  have hl : (le64 (BitVec.ofNat 64 args.length) ++
      (textsAt args (textBase args)).flatMap (fun t => le64 (BitVec.ofNat 64 t.1)) ++
      le64 0 ++ le64 0 ++ le64 0 ++ le64 0).length = 8 * (args.length + 5) := by
    simp only [List.length_append, le64_length, flatMap_le64_length, textsAt_length]
    omega
  rw [e, List.getElem?_append_right (by rw [hl]; omega), hl, Nat.add_sub_cancel_left]

/-- The word for an argument is the address of its text. -/
theorem argBlock_slot (args : List (List Byte)) (i : Nat) (hi : i < args.length) :
    word64 (argBlock args) (8 * (i + 1)) =
      BitVec.ofNat 64 ((textsAt args (textBase args))[i]'(by rw [textsAt_length]; exact hi)).1 := by
  have hT : i < (textsAt args (textBase args)).length := by rw [textsAt_length]; exact hi
  have h := word64_flatMap (textsAt args (textBase args)) (fun t => BitVec.ofNat 64 t.1)
    (le64 0 ++ (le64 0 ++ (le64 0 ++ (le64 0 ++ textBytes args)))) i hT
  have e : word64 (argBlock args) (8 * (i + 1)) =
      word64 ((textsAt args (textBase args)).flatMap (fun t => le64 (BitVec.ofNat 64 t.1)) ++
        (le64 0 ++ (le64 0 ++ (le64 0 ++ (le64 0 ++ textBytes args))))) (8 * i) := by
    rw [show 8 * (i + 1) = 8 + 8 * i by omega]
    exact word64_shift _ _ _
  rw [e, h]

/-! ## The model's starting states meet the contract -/

end TypedAsm

