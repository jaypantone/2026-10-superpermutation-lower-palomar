module

public import bridge.GenericTransfer

@[expose] public section

/-! Numerical admissibility of the frozen return parameters. These lemmas do
not assert geometric packing. Return orders enter only through `R ≥ 1`.
-/
namespace SuperpermutationLowerBound.ChainReturns

private theorem inverse_bounds {R : ℚ} (hR : 1 ≤ R) :
    0 ≤ 1 / R ∧ 1 / R ≤ 1 := by
  have hpos : 0 < R := by linarith
  exact ⟨le_of_lt (div_pos (by norm_num) hpos), (div_le_one hpos).2 hR⟩

/-- Alternating-chain parameters, with any positive return bound `R ≥ 1`. -/
theorem admissible_modZero (m : ℕ) (hm : 3 ≤ m) (R : ℚ) (hR : 1 ≤ R) :
    Admissible (3 * m) (2 * m + 1 / 2 + 1 / (4 * R))
      (4 * m - 3 - 1 / (2 * R)) := by
  have hmQ : (3 : ℚ) ≤ m := by exact_mod_cast hm
  obtain ⟨hi0, hi1⟩ := inverse_bounds hR
  have hR0 : R ≠ 0 := ne_of_gt (by linarith : 0 < R)
  have h4 : (1 : ℚ) / (4 * R) = (1 / R) / 4 := by field_simp
  have h2 : (1 : ℚ) / (2 * R) = (1 / R) / 2 := by field_simp
  have hprod : 0 ≤ ((m : ℚ) - 3)^2 := sq_nonneg _
  have hmix : 0 ≤ (1 - 1 / R) * (3 * (m : ℚ) / 2 - 1) :=
    mul_nonneg (by linarith) (by linarith)
  constructor
  · omega
  · rw [h4]; nlinarith
  · rw [h4, h2]; nlinarith
  · rw [h2]; nlinarith
  · rw [h4, h2]
    push_cast
    nlinarith

/-- Efficient-pair parameters in the residue class `n = 3m+1`. -/
theorem admissible_modOne (m : ℕ) (hm : 3 ≤ m) (R : ℚ) (hR : 1 ≤ R) :
    Admissible (3 * m + 1) ((m : ℚ) * (2 * m + 1))
      (2 * (m : ℚ)^2 + 2 * m - 2 - 1 / R) := by
  have hmQ : (3 : ℚ) ≤ m := by exact_mod_cast hm
  obtain ⟨hi0, hi1⟩ := inverse_bounds hR
  have hs : 0 ≤ ((m : ℚ) - 3)^2 := sq_nonneg _
  have hc : 0 ≤ ((m : ℚ) - 3)^3 := pow_nonneg (by linarith) _
  have hmix : 0 ≤ (1 - 1 / R) * (3 * (m : ℚ) - 3) :=
    mul_nonneg (by linarith) (by linarith)
  constructor
  · omega
  · positivity
  · nlinarith
  · nlinarith
  · push_cast
    nlinarith

/-- Full-run-collision parameters in the residue class `n = 3m+2`. -/
theorem admissible_modTwo (m : ℕ) (hm : 2 ≤ m) :
    Admissible (3 * m + 2) (((m : ℚ) + 1) * (2 * m + 1))
      (4 * (m : ℚ)^2 + 5 * m - 5 / 2) := by
  have hmQ : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have hs : 0 ≤ ((m : ℚ) - 2)^2 := sq_nonneg _
  have hc : 0 ≤ ((m : ℚ) - 2)^3 := pow_nonneg (by linarith) _
  constructor
  · omega
  · positivity
  · nlinarith
  · nlinarith
  · push_cast
    nlinarith

theorem admissible_eight : Admissible 7 10 (46 / 3) := by
  constructor <;> norm_num

theorem admissible_nine : Admissible 8 15 (287 / 12) := by
  constructor <;> norm_num

theorem admissible_ten : Admissible 9 (521 / 80) (359 / 40) := by
  constructor <;> norm_num

theorem admissible_eleven : Admissible 10 21 (263 / 12) := by
  constructor <;> norm_num

theorem admissible_twelve : Admissible 11 28 (195 / 4) := by
  constructor <;> norm_num

end SuperpermutationLowerBound.ChainReturns
