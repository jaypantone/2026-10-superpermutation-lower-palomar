module

public import ReturnOneMap

@[expose] public section

/-! Descent times to the five anchors in the residue-one return map. -/
namespace SuperpermutationLowerBound.Refinement.ChainReturns

set_option maxHeartbeats 2000000

theorem efficientOne_six_step (m j : ℕ) :
    efficientOneValue m (6 * j + 12) = 6 * j + 6 := by
  simp (disch := omega) [efficientOneValue]
  omega

theorem efficientOne_nine_step (m j : ℕ) :
    efficientOneValue m (6 * j + 15) = 6 * j + 9 := by
  simp (disch := omega) [efficientOneValue]
  omega

theorem efficientOne_six_descent (m j : ℕ) :
    ((efficientOneValue m)^[j + 1]) (6 * j + 6) = 2 := by
  induction j with
  | zero => simp [efficientOneValue]
  | succ j ih =>
      rw [Function.iterate_succ_apply]
      rw [show 6 * (j + 1) + 6 = 6 * j + 12 by omega, efficientOne_six_step]
      exact ih

theorem efficientOne_nine_descent (m j : ℕ) :
    ((efficientOneValue m)^[j + 1]) (6 * j + 9) = 1 := by
  induction j with
  | zero => simp [efficientOneValue]
  | succ j ih =>
      rw [Function.iterate_succ_apply]
      rw [show 6 * (j + 1) + 9 = 6 * j + 15 by omega, efficientOne_nine_step]
      exact ih

theorem efficientOne_two_step (m x : ℕ) (hx : 4 ≤ x) (hmod : x % 3 ≠ 0) :
    efficientOneValue m (efficientOneValue m (x + 9)) = x := by
  by_cases h : x % 3 = 1
  · have h1 : efficientOneValue m (x + 9) = x + 4 := by
      simp (disch := omega) [efficientOneValue] <;> (try split_ifs) <;> omega
    rw [h1]
    simp (disch := omega) [efficientOneValue] <;> (try split_ifs) <;> omega
  · have h1 : efficientOneValue m (x + 9) = x + 5 := by
      simp (disch := omega) [efficientOneValue] <;> (try split_ifs) <;> omega
    rw [h1]
    simp (disch := omega) [efficientOneValue] <;> (try split_ifs) <;> omega

theorem efficientOne_double_descent (m x : ℕ) (hx : 4 ≤ x)
    (hmod : x % 3 ≠ 0) (j : ℕ) :
    ((efficientOneValue m)^[2 * j]) (x + 9 * j) = x := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [show 2 * (j + 1) = 2 * j + 2 by omega,
        Function.iterate_add_apply]
      have hstep : ((efficientOneValue m)^[2]) (x + 9 * (j + 1)) = x + 9 * j := by
        change efficientOneValue m (efficientOneValue m (x + 9 * (j + 1))) = _
        rw [show x + 9 * (j + 1) = (x + 9 * j) + 9 by omega]
        exact efficientOne_two_step m (x + 9 * j) (by omega) (by omega)
      rw [hstep]
      exact ih

theorem efficientOne_four_descent (m j : ℕ) :
    ((efficientOneValue m)^[2 * j]) (9 * j + 4) = 4 := by
  simpa [Nat.add_comm, Nat.mul_comm] using
    efficientOne_double_descent m 4 (by omega) (by decide) j

theorem efficientOne_five_descent (m j : ℕ) :
    ((efficientOneValue m)^[2 * j]) (9 * j + 5) = 5 := by
  simpa [Nat.add_comm, Nat.mul_comm] using
    efficientOne_double_descent m 5 (by omega) (by decide) j

theorem efficientOne_seven_descent (m j : ℕ) :
    ((efficientOneValue m)^[2 * j + 1]) (9 * j + 7) = 3 := by
  rw [Function.iterate_succ_apply']
  have h := efficientOne_double_descent m 7 (by omega) (by decide) j
  rw [show 9 * j + 7 = 7 + 9 * j by omega, h]
  simp [efficientOneValue]

theorem efficientOne_eight_descent (m j : ℕ) :
    ((efficientOneValue m)^[2 * j + 1]) (9 * j + 8) = 4 := by
  rw [Function.iterate_succ_apply']
  have h := efficientOne_double_descent m 8 (by omega) (by decide) j
  rw [show 9 * j + 8 = 8 + 9 * j by omega, h]
  simp [efficientOneValue]

theorem efficientOne_ten_descent (m j : ℕ) :
    ((efficientOneValue m)^[2 * j + 1]) (9 * j + 10) = 5 := by
  rw [Function.iterate_succ_apply']
  have h := efficientOne_double_descent m 10 (by omega) (by decide) j
  rw [show 9 * j + 10 = 10 + 9 * j by omega, h]
  simp [efficientOneValue]

theorem efficientOne_eleven_descent (m j : ℕ) :
    ((efficientOneValue m)^[2 * j + 2]) (9 * j + 11) = 3 := by
  rw [Function.iterate_add_apply, show 9 * j + 11 = 11 + 9 * j by omega]
  rw [← Function.iterate_add_apply, Nat.add_comm (2*j) 2,
    Function.iterate_add_apply]
  rw [efficientOne_double_descent m 11 (by omega) (by decide) j]
  simp [Function.iterate_succ_apply, efficientOneValue]

end SuperpermutationLowerBound.Refinement.ChainReturns
