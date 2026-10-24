module

public import pairs.SquareMap

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

set_option maxHeartbeats 5000000

def squareMiddleValue (n i : ℕ) : ℕ :=
  if i = 0 then 0 else if i = 1 then 7 else if i = 2 then 6
  else if i + 5 ≤ n then i + 5
  else if i + 4 = n then 3 else if i + 3 = n then 2
  else if i + 2 = n then 1 else if i + 1 = n then 5 else 4

theorem squareMiddle_value (n : ℕ) (hn : 8 ≤ n) (i : ℕ) (hi : i ≤ n) :
    cellRhoValue n (cellGInverseValue n (cellRhoValue n
      (cellGValue n (cellGValue n i)))) = squareMiddleValue n i := by
  conv_lhs => arg 2; arg 2; arg 2; arg 2; unfold cellGValue
  split_ifs <;> try (first | contradiction | omega)
  all_goals conv_lhs => arg 2; arg 2; arg 2; unfold cellGValue
  all_goals split_ifs <;> try (first | contradiction | omega)
  all_goals conv_lhs => arg 2; arg 2; unfold cellRhoValue
  all_goals split_ifs <;> try (first | contradiction | omega)
  all_goals conv_lhs => arg 2; unfold cellGInverseValue
  all_goals split_ifs <;> try (first | contradiction | omega)
  all_goals simp only [cellRhoValue, squareMiddleValue]
  all_goals split_ifs <;> (first | contradiction | omega)

def squareComparisonValue (n i : ℕ) : ℕ :=
  if i = 0 then 0 else if i = 1 then 3 else if i = 2 then 1
  else if i + 3 ≤ n then i + 1
  else if i + 2 = n then 2 else if i + 1 = n then n else n - 1

theorem squareComparison_value (m : ℕ) (hm : 2 ≤ m) (i : ℕ) (hi : i ≤ 3 * m + 2) :
    squareHalfValue (3 * m + 2)
      (squareMiddleValue (3 * m + 2) (squareHalfValue (3 * m + 2) i)) =
      squareComparisonValue (3 * m + 2) i := by
  conv_lhs => arg 2; arg 2; unfold squareHalfValue
  split_ifs <;> try (first | contradiction | omega)
  all_goals simp only [squareMiddleValue]
  all_goals split_ifs <;> try (first | contradiction | omega)
  all_goals simp only [squareHalfValue, squareComparisonValue]
  all_goals split_ifs <;> (first | contradiction | omega)

/-- The universal comparison permutation appearing in the full-run proof. -/
theorem squareComparison_apply (m : ℕ) (hm : 2 ≤ m) (hn : 7 ≤ 3 * m + 2)
    (i : Fin (3 * m + 2 + 1)) :
    ((cellG (3 * m + 2) hn ^ m * cellRho (3 * m + 2) hn *
      (cellG (3 * m + 2) hn)⁻¹ * cellRho (3 * m + 2) hn *
      cellG (3 * m + 2) hn ^ (m + 2)) i).val =
      squareComparisonValue (3 * m + 2) i.val := by
  have hhalf := cellG_pow_m_residueTwo m hm hn i
  have hbound : squareHalfValue (3 * m + 2) i.val ≤ 3 * m + 2 := by
    rw [← hhalf]
    exact Nat.le_of_lt_succ (((cellG (3 * m + 2) hn)^m) i).isLt
  have hinv (j : Fin (3 * m + 2 + 1)) :
      ((cellG (3 * m + 2) hn)⁻¹ j).val = cellGInverseValue (3 * m + 2) j.val := rfl
  rw [show m + 2 = 2 + m by omega, pow_add, pow_two]
  simp only [Equiv.Perm.mul_apply, cellG_pow_m_residueTwo m hm hn,
    cellRho_apply_val, hinv, cellG_apply_val]
  rw [squareMiddle_value (3 * m + 2) (by omega) _ hbound]
  exact squareComparison_value m hm i.val (by omega)

end SuperpermutationLowerBound.Refinement
