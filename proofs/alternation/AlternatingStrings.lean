module

public import Mathlib.Tactic

@[expose] public section

/-! The literal alternating-string decomposition behind the weighted argument.
Values at least two are removed.  Adjacent equal binary values are cuts.
The prefix rank is the length of the first alternating binary string. -/

namespace SuperpermutationLowerBound.Refinement.ChainReturns

def binaryPrefixLength : List ℕ → ℕ
  | [] => 0
  | x :: xs =>
      if x ≤ 1 then
        match xs with
        | [] => 1
        | y :: _ => if y ≤ 1 ∧ x ≠ y then 1 + binaryPrefixLength xs else 1
      else 0

def removedCount : List ℕ → ℕ
  | [] => 0
  | x :: xs => (if x ≤ 1 then 0 else 1) + removedCount xs

def equalBinaryCuts : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | x :: y :: xs => (if x ≤ 1 ∧ y ≤ 1 ∧ x = y then 1 else 0) +
      equalBinaryCuts (y :: xs)

/-- Every suffix has a bounded initial alternating binary string.  This
is a concrete property of the list, rather than an aggregate cut count. -/
def BoundedAlternation (L : ℕ) : List ℕ → Prop
  | [] => True
  | x :: xs => binaryPrefixLength (x :: xs) ≤ L ∧ BoundedAlternation L xs

theorem BoundedAlternation.prefix {L : ℕ} {xs : List ℕ}
    (h : BoundedAlternation L xs) : binaryPrefixLength xs ≤ L := by
  cases xs with
  | nil => simp [binaryPrefixLength]
  | cons x xs => exact h.1

theorem BoundedAlternation.tail {L x : ℕ} {xs : List ℕ}
    (h : BoundedAlternation L (x :: xs)) : BoundedAlternation L xs := h.2

/-- Telescoping the prefix lengths counts all removed indices and all cuts.
The proof implements the decomposition, without supplying its cardinality
as a hypothesis. -/
theorem binary_string_count {L : ℕ} (xs : List ℕ)
    (h : BoundedAlternation L xs) :
    xs.length ≤ binaryPrefixLength xs + (L + 1) * removedCount xs +
      L * equalBinaryCuts xs := by
  induction xs with
  | nil => simp [binaryPrefixLength, removedCount, equalBinaryCuts]
  | cons x xs ih =>
      have ht := ih h.tail
      have hp := h.tail.prefix
      cases xs with
      | nil =>
          simp only [List.length_cons, List.length_nil, binaryPrefixLength,
            removedCount, equalBinaryCuts, Nat.mul_zero, Nat.add_zero]
          split_ifs <;> omega
      | cons y ys =>
          by_cases hx : x ≤ 1
          · by_cases hy : y ≤ 1
            · by_cases heq : x = y
              · simp [binaryPrefixLength, hx, hy, heq, removedCount,
                  equalBinaryCuts, Nat.mul_add] at *
                omega
              · simp [binaryPrefixLength, hx, hy, heq, removedCount,
                  equalBinaryCuts] at *
                omega
            · simp only [List.length_cons, binaryPrefixLength, hx, hy,
                false_and, and_false, ↓reduceIte, removedCount, equalBinaryCuts,
                Nat.zero_add] at *
              omega
          · simp only [List.length_cons, binaryPrefixLength, hx, false_and,
              ↓reduceIte, removedCount, equalBinaryCuts, Nat.zero_add,
              Nat.mul_add, Nat.mul_one] at *
            omega

theorem binary_string_count_uniform {L : ℕ} (xs : List ℕ)
    (h : BoundedAlternation L xs) :
    xs.length ≤ removedCount xs + L * (removedCount xs + equalBinaryCuts xs + 1) := by
  have hc := binary_string_count xs h
  have hp := h.prefix
  nlinarith

end SuperpermutationLowerBound.Refinement.ChainReturns
