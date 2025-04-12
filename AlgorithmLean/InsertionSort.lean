def sorted (xs : List Nat) : Prop :=
match xs with
| [] => True
| x0 :: xs0 =>
  match xs0 with
  | [] => True
  | x1 :: xs1 => x0 ≤ x1 ∧ sorted (x1 :: xs1)

def insert' (xs : List Nat) (x : Nat) : List Nat :=
match xs with
| [] => [x]
| x0 :: xs0 => if x ≤ x0 then x :: xs else x0 :: insert' xs0 x

theorem insert_preserve_sorted (xs : List Nat) (x : Nat) (h : sorted xs) : sorted (insert' xs x) := by
cases xs
case nil =>
  unfold insert'
  trivial
case cons x0 xs0 =>
  cases xs0
  case nil =>
    simp [insert']
    split
    case isTrue hc => trivial
    case isFalse hc =>
      simp [sorted]
      exact Nat.le_of_not_ge hc
  case cons x1 xs1 =>
    unfold insert'
    split
    case isTrue hc' =>
      simp [sorted]
      exact ⟨hc', h⟩
    case isFalse hc' =>
      simp [sorted] at h
      have ⟨ha, hb⟩ := h
      simp [insert']
      split
      case isTrue hc'' =>
        exact And.symm ⟨⟨hc'', hb⟩, Nat.le_of_lt (Nat.lt_of_not_ge hc')⟩
      case isFalse hc'' =>
        have ih := insert_preserve_sorted (x1 :: xs1) x hb
        unfold insert' at ih
        rw [if_neg hc''] at ih
        exact ⟨ha, ih⟩

def insertionSort : List Nat → List Nat
| [] => []
| x :: xs => insert' (insertionSort xs) x

theorem insertionSort_can_sort (xs : List Nat) : sorted (insertionSort xs) := by
cases xs
case nil =>
  simp [insertionSort]
  simp [sorted]
case cons x0 xs0 =>
  simp [insertionSort]
  exact insert_preserve_sorted (insertionSort xs0) x0 (insertionSort_can_sort xs0)
