module

public import asymptotics.reference.ParameterTable
public import asymptotics.reference.IntegerComparison

@[expose] public section

/-! The exact and quadratic integer bounds compared with the all-size reference.
Every difference is formed in the reals, after casting the integer bounds. -/
noncomputable section
open Filter Topology
open SuperpermutationBounds.ChainReturns
open SuperpermutationLowerBound.ChainReturns
namespace SuperpermutationBounds.ChainReturns.Asymptotic

theorem table_reference_limit_zero {P : ℕ → ℚ × ℚ} {R S : ℕ → ℚ}
    (hEq : ∀ᶠ m in atTop, P m = generalParameters (3*m) (R m) (S m))
    (hR : ∀ᶠ m in atTop, 1 ≤ R m) (hS : ∀ᶠ m in atTop, 1 ≤ S m)
    (hA : ∀ᶠ m in atTop, Admissible (3*m) (P m).1 (P m).2) :
    Tendsto (fun m => ((paperBound (3*m+1) (P m).1 (P m).2 : ℝ) -
      (referenceNat (3*m+1) : ℝ)) / ((3*m-5).factorial : ℝ))
      atTop (𝓝 3) := by
  have hp : Tendsto (fun m => ((P m).1 : ℝ) / ((3*m : ℕ) : ℝ)^2)
      atTop (𝓝 (0:ℝ)) := by
    apply (general_p_zero_limit (R := R) (S := S) hR).congr'
    filter_upwards [hEq] with m hm
    simp only [hm, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  have ht : Tendsto (fun m => ((P m).2 : ℝ) / ((3*m : ℕ) : ℝ)^1)
      atTop (𝓝 (4/3:ℝ)) := by
    apply (general_t_zero_limit (R := R) (S := S) hR).congr'
    filter_upwards [hEq] with m hm
    simp only [hm, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, pow_one]
  have hN : Tendsto (fun m : ℕ => 3*m) atTop atTop := by
    simpa using residue_tendsto 0
  have h := reference_bound_difference_limit hN 1 (by norm_num : (4/3:ℝ) ≠ 0) hp ht hA
  norm_num at h
  exact h

theorem table_reference_limit_one {P : ℕ → ℚ × ℚ} {R S : ℕ → ℚ}
    (hEq : ∀ᶠ m in atTop, P m = generalParameters (3*m+1) (R m) (S m))
    (hR : ∀ᶠ m in atTop, 1 ≤ R m) (hS : ∀ᶠ m in atTop, 1 ≤ S m)
    (hA : ∀ᶠ m in atTop, Admissible (3*m+1) (P m).1 (P m).2) :
    Tendsto (fun m => ((paperBound (3*m+1+1) (P m).1 (P m).2 : ℝ) -
      (referenceNat (3*m+1+1) : ℝ)) / ((3*m+1-6).factorial : ℝ))
      atTop (𝓝 18) := by
  have hp : Tendsto (fun m => ((P m).1 : ℝ) / ((3*m+1 : ℕ) : ℝ)^2)
      atTop (𝓝 (2/9:ℝ)) := by
    apply (general_p_one_limit R S).congr'
    filter_upwards [hEq] with m hm
    simp only [hm, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  have ht : Tendsto (fun m => ((P m).2 : ℝ) / ((3*m+1 : ℕ) : ℝ)^2)
      atTop (𝓝 (2/9:ℝ)) := by
    apply (general_t_one_limit (R := R) (S := S) hS).congr'
    filter_upwards [hEq] with m hm
    simp only [hm, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, pow_one]
  have hN : Tendsto (fun m : ℕ => 3*m+1) atTop atTop := by
    simpa using residue_tendsto 1
  have h := reference_bound_difference_limit hN 2 (by norm_num : (2/9:ℝ) ≠ 0) hp ht hA
  norm_num at h
  exact h

theorem table_reference_limit_two {P : ℕ → ℚ × ℚ} {R S : ℕ → ℚ}
    (hEq : ∀ᶠ m in atTop, P m = generalParameters (3*m+2) (R m) (S m))
    (hR : ∀ᶠ m in atTop, 1 ≤ R m) (hS : ∀ᶠ m in atTop, 1 ≤ S m)
    (hA : ∀ᶠ m in atTop, Admissible (3*m+2) (P m).1 (P m).2) :
    Tendsto (fun m => ((paperBound (3*m+2+1) (P m).1 (P m).2 : ℝ) -
      (referenceNat (3*m+2+1) : ℝ)) / ((3*m+2-6).factorial : ℝ))
      atTop (𝓝 9) := by
  have hp : Tendsto (fun m => ((P m).1 : ℝ) / ((3*m+2 : ℕ) : ℝ)^2)
      atTop (𝓝 (2/9:ℝ)) := by
    apply (general_p_two_limit R S).congr'
    filter_upwards [hEq] with m hm
    simp only [hm, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  have ht : Tendsto (fun m => ((P m).2 : ℝ) / ((3*m+2 : ℕ) : ℝ)^2)
      atTop (𝓝 (4/9:ℝ)) := by
    apply (general_t_two_limit R S).congr'
    filter_upwards [hEq] with m hm
    simp only [hm, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, pow_one]
  have hN : Tendsto (fun m : ℕ => 3*m+2) atTop atTop := by
    simpa using residue_tendsto 2
  have h := reference_bound_difference_limit hN 2 (by norm_num : (4/9:ℝ) ≠ 0) hp ht hA
  norm_num at h
  exact h

/-- The exact frozen bound has reference gain 3 in this residue class. -/
theorem exact_reference_limit_zero :
    Tendsto (fun m : ℕ => ((exactNat (3*m+1) : ℝ) - (referenceNat (3*m+1) : ℝ)) /
      ((3*m+1-6).factorial : ℝ)) atTop (𝓝 3) := by
  have hEq := exact_table_eventually 0 (by omega)
  have hA : ∀ᶠ m in atTop, Admissible (3*m)
      (exactParameters (3*m+1)).1 (exactParameters (3*m+1)).2 := by
    filter_upwards [eventually_ge_atTop 4] with m hm
    simpa only [Nat.add_sub_cancel] using
      exactParameters_admissible (K := 3*m+1) (by omega)
  have h := table_reference_limit_zero (R := (fun m => (returnZero (3*m) : ℚ))) (S := (fun m => (returnOne m : ℚ)))
    hEq (exact_zero_return_ge_one 0) (exact_one_return_ge_one) hA
  convert h using 1
  ext m
  simp only [exactNat]
  congr 2 <;> congr 1 <;> omega

/-- The exact frozen bound has reference gain 18 in this residue class. -/
theorem exact_reference_limit_one :
    Tendsto (fun m : ℕ => ((exactNat (3*m+2) : ℝ) - (referenceNat (3*m+2) : ℝ)) /
      ((3*m+2-7).factorial : ℝ)) atTop (𝓝 18) := by
  have hEq := exact_table_eventually 1 (by omega)
  have hA : ∀ᶠ m in atTop, Admissible (3*m+1)
      (exactParameters (3*m+1+1)).1 (exactParameters (3*m+1+1)).2 := by
    filter_upwards [eventually_ge_atTop 4] with m hm
    simpa only [Nat.add_sub_cancel] using
      exactParameters_admissible (K := 3*m+1+1) (by omega)
  have h := table_reference_limit_one (R := (fun m => (returnZero (3*m+1) : ℚ))) (S := (fun m => (returnOne m : ℚ)))
    hEq (exact_zero_return_ge_one 1) (exact_one_return_ge_one) hA
  convert h using 1
  ext m
  simp only [exactNat]
  congr 2 <;> congr 1 <;> omega

/-- The exact frozen bound has reference gain 9 in this residue class. -/
theorem exact_reference_limit_two :
    Tendsto (fun m : ℕ => ((exactNat (3*m+3) : ℝ) - (referenceNat (3*m+3) : ℝ)) /
      ((3*m+3-7).factorial : ℝ)) atTop (𝓝 9) := by
  have hEq := exact_table_eventually 2 (by omega)
  have hA : ∀ᶠ m in atTop, Admissible (3*m+2)
      (exactParameters (3*m+2+1)).1 (exactParameters (3*m+2+1)).2 := by
    filter_upwards [eventually_ge_atTop 4] with m hm
    simpa only [Nat.add_sub_cancel] using
      exactParameters_admissible (K := 3*m+2+1) (by omega)
  have h := table_reference_limit_two (R := (fun m => (returnZero (3*m+2) : ℚ))) (S := (fun m => (returnOne m : ℚ)))
    hEq (exact_zero_return_ge_one 2) (exact_one_return_ge_one) hA
  convert h using 1
  ext m
  simp only [exactNat]
  congr 2 <;> congr 1 <;> omega

/-- The quadratic frozen bound has reference gain 3 in this residue class. -/
theorem quadratic_reference_limit_zero :
    Tendsto (fun m : ℕ => ((quadraticNat (3*m+1) : ℝ) - (referenceNat (3*m+1) : ℝ)) /
      ((3*m+1-6).factorial : ℝ)) atTop (𝓝 3) := by
  have hEq := quadratic_table_eventually 0
  have hA : ∀ᶠ m in atTop, Admissible (3*m)
      (quadraticParameters (3*m+1)).1 (quadraticParameters (3*m+1)).2 := by
    filter_upwards [eventually_ge_atTop 4] with m hm
    simpa only [Nat.add_sub_cancel] using
      quadraticParameters_admissible (K := 3*m+1) (by omega)
  have h := table_reference_limit_zero (R := (fun m => (3*(m:ℚ)+0)^2/4)) (S := (fun m => (3*(m:ℚ)+0)^2/4))
    hEq (quadratic_return_ge_one 0) (quadratic_return_ge_one 0) hA
  convert h using 1
  ext m
  simp only [quadraticNat]
  congr 2 <;> congr 1 <;> omega

/-- The quadratic frozen bound has reference gain 18 in this residue class. -/
theorem quadratic_reference_limit_one :
    Tendsto (fun m : ℕ => ((quadraticNat (3*m+2) : ℝ) - (referenceNat (3*m+2) : ℝ)) /
      ((3*m+2-7).factorial : ℝ)) atTop (𝓝 18) := by
  have hEq := quadratic_table_eventually 1
  have hA : ∀ᶠ m in atTop, Admissible (3*m+1)
      (quadraticParameters (3*m+1+1)).1 (quadraticParameters (3*m+1+1)).2 := by
    filter_upwards [eventually_ge_atTop 4] with m hm
    simpa only [Nat.add_sub_cancel] using
      quadraticParameters_admissible (K := 3*m+1+1) (by omega)
  have h := table_reference_limit_one (R := (fun m => (3*(m:ℚ)+1)^2/4)) (S := (fun m => (3*(m:ℚ)+1)^2/4))
    hEq (quadratic_return_ge_one 1) (quadratic_return_ge_one 1) hA
  convert h using 1
  ext m
  simp only [quadraticNat]
  congr 2 <;> congr 1 <;> omega

/-- The quadratic frozen bound has reference gain 9 in this residue class. -/
theorem quadratic_reference_limit_two :
    Tendsto (fun m : ℕ => ((quadraticNat (3*m+3) : ℝ) - (referenceNat (3*m+3) : ℝ)) /
      ((3*m+3-7).factorial : ℝ)) atTop (𝓝 9) := by
  have hEq := quadratic_table_eventually 2
  have hA : ∀ᶠ m in atTop, Admissible (3*m+2)
      (quadraticParameters (3*m+2+1)).1 (quadraticParameters (3*m+2+1)).2 := by
    filter_upwards [eventually_ge_atTop 4] with m hm
    simpa only [Nat.add_sub_cancel] using
      quadraticParameters_admissible (K := 3*m+2+1) (by omega)
  have h := table_reference_limit_two (R := (fun m => (3*(m:ℚ)+2)^2/4)) (S := (fun m => (3*(m:ℚ)+2)^2/4))
    hEq (quadratic_return_ge_one 2) (quadratic_return_ge_one 2) hA
  convert h using 1
  ext m
  simp only [quadraticNat]
  congr 2 <;> congr 1 <;> omega

end SuperpermutationBounds.ChainReturns.Asymptotic
