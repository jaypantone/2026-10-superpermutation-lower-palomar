module

public import SuperpermutationLowerBound.Refinement.ReturnNormalization
public import SuperpermutationLowerBound.Refinement.Parameters
public import SuperpermutationLowerBound.Refinement.ReturnPeriod
public import SuperpermutationLowerBound.Refinement.ReturnResidueOne
public import SuperpermutationLowerBound.Refinement.ReturnResidueTwo
public import SuperpermutationLowerBound.Refinement.ReturnUniversal

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

theorem cellG_pow_period_sub_one (n : ℕ) (hn : 7 ≤ n) :
    (cellG n hn)^(period n-1) = (cellG n hn)⁻¹ := by
  have hp : period n-1+1 = period n := by have := period_ge_two hn; omega
  apply mul_right_cancel (b := cellG n hn)
  rw [← pow_succ, hp, cellG_pow_period, inv_mul_cancel]

theorem cellNormalization_pure_period (n : ℕ) (hn : 7 ≤ n) :
    cellNormalization n hn (List.replicate (period n) false) = 1 := by
  rw [cellNormalization_replicate_false, cellG_pow_period]

theorem cellNormalization_basic_right (n : ℕ) (hn : 7 ≤ n) :
    cellNormalization n hn (chainWindow 0 (period n-1) []) =
      (cellG n hn)⁻¹ * cellRho n hn * cellG n hn := by
  rw [cellNormalization_chainWindow_empty, cellG_pow_period_sub_one]
  simp

theorem cellNormalization_basic_left (n : ℕ) (hn : 7 ≤ n) :
    cellNormalization n hn (chainWindow (period n-1) 0 []) = cellRho n hn := by
  have hp : period n-1+1 = period n := by have := period_ge_two hn; omega
  rw [cellNormalization_chainWindow_empty, hp, cellG_pow_period]
  simp

/-- This pair has one shortened cell; its product differs from the
two-shortened-cell return `shortened_return_residueOne_val`. -/
theorem cellNormalization_residueOne_pair (m : ℕ) (hn : 7 ≤ 3*m+1) :
    cellNormalization (3*m+1) hn (chainWindow m m []) =
      (cellG (3*m+1) hn)^m * cellRho (3*m+1) hn *
        (cellG (3*m+1) hn)^(m+1) :=
  cellNormalization_chainWindow_empty _ _ _ _

theorem cellNormalization_residueOne_triple_val (m : ℕ) (hm : 2 ≤ m)
    (hn : 7 ≤ 3*m+1) (i : Fin (3*m+1+1)) :
    (cellNormalization (3*m+1) hn (chainWindow m 0 [m]) i).val =
      cellQOneValue (3*m+1) i.val := by
  rw [cellNormalization_chainWindow_one _ _ _ _ _ (by omega)]
  simp only [pow_zero, one_mul]
  exact shortened_return_residueOne_val m hm hn i

theorem cellNormalization_residueTwo_pair (m : ℕ) (hm : 2 ≤ m)
    (hn : 7 ≤ 3*m+2) :
    cellNormalization (3*m+2) hn
      (chainWindow (2*m*(m+1)) (2*m*(m+1)-1) []) =
      (cellG (3*m+2) hn)⁻¹ * (cellRho (3*m+2) hn)⁻¹ * cellG (3*m+2) hn := by
  rw [cellNormalization_chainWindow_empty]
  exact involution_return_residueTwo m hm hn

theorem cellNormalization_residueTwo_triple (m : ℕ) (hm : 2 ≤ m)
    (hn : 7 ≤ 3*m+2) :
    cellNormalization (3*m+2) hn
      (chainWindow (2*m*(m+1)+1) 0 [2*m*(m+1)-1]) =
      cellK (3*m+2) hn * cellG (3*m+2) hn := by
  have hv' : 2 ≤ 2*m*(m+1) := by nlinarith
  have hv : 1 ≤ 2*m*(m+1)-1 := by omega
  rw [cellNormalization_chainWindow_one _ _ _ _ _ hv]
  simp only [pow_zero, one_mul, Nat.add_assoc]
  exact shortened_return_residueTwo m hm hn

theorem cellNormalization_universal (n : ℕ) (hn : 8 ≤ n) :
    cellNormalization n (by omega)
      (chainWindow 1 1 [period n-1,period n-1]) = cellUniversal n hn := by
  have hp : 1 ≤ period n-1 := by have := period_ge_two (show 7 ≤ n by omega); omega
  rw [cellNormalization_chainWindow_two _ _ _ _ _ _ hp hp]
  simp only [pow_one, cellG_pow_period_sub_one]
  unfold cellUniversal
  simp only [pow_succ, pow_zero, one_mul]
  group

end SuperpermutationLowerBound.Refinement
