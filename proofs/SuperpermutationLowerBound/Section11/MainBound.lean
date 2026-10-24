module

public import SuperpermutationLowerBound.Section10.Assembly
public import Mathlib.Data.Rat.Floor

@[expose] public section

namespace SuperpermutationLowerBound

/-! Frozen Section 11 through the six numerical consequences immediately
following Theorem `thm:main`.  The rational expression in
`mainBoundThreshold` uses Mathlib's exact natural ceiling `Nat.ceil`; it is not
a rounded natural-number division. -/

variable {k : ℕ}

/-- The exact threshold
`W_k = ceil (((k-3)(k-1)!-2(k-1))/(k^2-4k+1))` from Theorem `thm:main`.

The displayed subtraction and division take place in `ℚ`, and `⌈·⌉₊` is
Mathlib's least-natural ceiling.  The remaining index subtractions `k-3` and
`k-1` are proved nontruncated on the theorem's domain `k ≥ 7`. -/
noncomputable def mainBoundThreshold (k : ℕ) : ℕ :=
  ⌈(((((k - 3 : ℕ) : ℚ) * ((k - 1).factorial : ℚ) -
        2 * ((k - 1 : ℕ) : ℚ)) /
      ((k : ℚ) ^ 2 - 4 * (k : ℚ) + 1)))⌉₊

private theorem pathForestResidualW_ge_mainBoundThreshold
    (hk : 7 ≤ k) (P : HamiltonianPath k) (hP : IsReducedMinimumPath P) :
    mainBoundThreshold k ≤ pathForestResidualW hk P := by
  let n := k - 1
  let W := pathForestResidualW hk P
  have hn : 6 ≤ n := by
    dsimp [n]
    omega
  have hk_eq : k = n + 1 := by
    dsimp [n]
    omega
  have hfactorial : n ≤ n.factorial := Nat.self_le_factorial n
  have hnumerator_nonnegative :
      2 * n ≤ (n - 2) * n.factorial := by
    calc
      2 * n ≤ (n - 2) * n := Nat.mul_le_mul_right n (by omega)
      _ ≤ (n - 2) * n.factorial := Nat.mul_le_mul_left (n - 2) hfactorial
  have hkappa_base : 2 * n + 2 < n ^ 2 := by
    nlinarith
  have hkappa_pos : 0 < n ^ 2 - 2 * n - 2 := by
    rw [Nat.sub_sub]
    exact Nat.sub_pos_of_lt hkappa_base
  have htwo_n_le_square : 2 * n ≤ n ^ 2 := by omega
  have htwo_le_square_sub : 2 ≤ n ^ 2 - 2 * n := by omega
  have hassembly := pathForest_assembly hk P hP
  have hisolated :
      (n - 2) * n.factorial - 2 * n ≤
        (n ^ 2 - 2 * n - 2) * W := by
    dsimp [n, W] at hassembly ⊢
    omega
  have hsquare : k ^ 2 = n ^ 2 + 2 * n + 1 := by
    rw [hk_eq]
    ring
  have hkm3 : k - 3 = n - 2 := by
    dsimp [n]
    omega
  have hnum_eq :
      (k - 3) * (k - 1).factorial - 2 * (k - 1) =
        (n - 2) * n.factorial - 2 * n := by
    rw [hkm3]
  have hkappa_eq :
      k ^ 2 - 4 * k + 1 = n ^ 2 - 2 * n - 2 := by
    omega
  have hnumerator_cast :
      ((((n - 2) * n.factorial - 2 * n : ℕ) : ℚ)) =
        ((n - 2 : ℕ) : ℚ) * (n.factorial : ℚ) - 2 * (n : ℚ) := by
    rw [Nat.cast_sub hnumerator_nonnegative]
    push_cast
    ring
  have hkappa_cast :
      (((n ^ 2 - 2 * n - 2 : ℕ) : ℚ)) =
        (n : ℚ) ^ 2 - 2 * (n : ℚ) - 2 := by
    rw [Nat.cast_sub htwo_le_square_sub, Nat.cast_sub htwo_n_le_square]
    push_cast
    ring
  have hquotient_nat :
      ((((n - 2) * n.factorial - 2 * n : ℕ) : ℚ) /
          ((n ^ 2 - 2 * n - 2 : ℕ) : ℚ)) ≤ (W : ℚ) := by
    apply (div_le_iff₀ (by exact_mod_cast hkappa_pos)).2
    exact_mod_cast (by simpa [mul_comm] using hisolated)
  rw [hnumerator_cast, hkappa_cast] at hquotient_nat
  have hkm1 : k - 1 = n := by rfl
  have hdenominator_cast :
      (k : ℚ) ^ 2 - 4 * (k : ℚ) + 1 =
        (n : ℚ) ^ 2 - 2 * (n : ℚ) - 2 := by
    rw [hk_eq]
    push_cast
    ring
  rw [mainBoundThreshold, hkm3, hkm1, hdenominator_cast]
  exact Nat.ceil_le.mpr hquotient_nat

/-- **Theorem `thm:main`.**  For every natural number `k ≥ 7`,

`S(k) ≥ k + (k+1)(k-1)! - 3
       + ceil (((k-3)(k-1)!-2(k-1))/(k^2-4k+1))`.

The ceiling is the exact rational ceiling exposed by `mainBoundThreshold`. -/
theorem shortestSuperpermutationLength_main_bound (k : ℕ) (hk : 7 ≤ k) :
    shortestSuperpermutationLength k ≥
      k + (k + 1) * (k - 1).factorial - 3 +
        ⌈(((((k - 3 : ℕ) : ℚ) * ((k - 1).factorial : ℚ) -
              2 * ((k - 1 : ℕ) : ℚ)) /
            ((k : ℚ) ^ 2 - 4 * (k : ℚ) + 1)))⌉₊ := by
  change shortestSuperpermutationLength k ≥
    k + (k + 1) * (k - 1).factorial - 3 + mainBoundThreshold k
  obtain ⟨P, hP⟩ := exists_reducedMinimumPath (by omega : 3 ≤ k)
  have hthreshold := pathForestResidualW_ge_mainBoundThreshold hk P hP
  have hresidual := pathForest_residual hk P hP
  rw [shortestSuperpermutationLength_eq_add_minimumHamiltonianPathWeight k
    (by omega : 3 ≤ k)]
  omega

/-- The exact threshold `W₇ = 131`. -/
theorem mainBoundThreshold_seven : mainBoundThreshold 7 = 131 := by
  norm_num [mainBoundThreshold, Nat.factorial]
  apply (Nat.ceil_eq_iff (by norm_num)).2
  norm_num

/-- The exact threshold `W₈ = 764`. -/
theorem mainBoundThreshold_eight : mainBoundThreshold 8 = 764 := by
  norm_num [mainBoundThreshold, Nat.factorial]
  apply (Nat.ceil_eq_iff (by norm_num)).2
  norm_num

/-- The exact threshold `W₉ = 5259`. -/
theorem mainBoundThreshold_nine : mainBoundThreshold 9 = 5259 := by
  norm_num [mainBoundThreshold, Nat.factorial]
  apply (Nat.ceil_eq_iff (by norm_num)).2
  norm_num

/-- The exact threshold `W₁₀ = 41642`. -/
theorem mainBoundThreshold_ten : mainBoundThreshold 10 = 41642 := by
  norm_num [mainBoundThreshold, Nat.factorial]
  apply (Nat.ceil_eq_iff (by norm_num)).2
  norm_num

/-- The exact threshold `W₁₁ = 372185`. -/
theorem mainBoundThreshold_eleven : mainBoundThreshold 11 = 372185 := by
  norm_num [mainBoundThreshold, Nat.factorial]
  apply (Nat.ceil_eq_iff (by norm_num)).2
  norm_num

/-- The exact threshold `W₁₂ = 3703621`. -/
theorem mainBoundThreshold_twelve : mainBoundThreshold 12 = 3703621 := by
  norm_num [mainBoundThreshold, Nat.factorial]
  apply (Nat.ceil_eq_iff (by norm_num)).2
  norm_num

/-- The ordinary-mathematics consequence `S(7) ≥ 5895`. -/
theorem shortestSuperpermutationLength_seven_lower_bound :
    shortestSuperpermutationLength 7 ≥ 5895 := by
  have h := shortestSuperpermutationLength_main_bound 7 (by norm_num)
  change shortestSuperpermutationLength 7 ≥
    7 + (7 + 1) * (7 - 1).factorial - 3 + mainBoundThreshold 7 at h
  norm_num [mainBoundThreshold_seven, Nat.factorial] at h
  exact h

/-- The ordinary-mathematics consequence `S(8) ≥ 46129`. -/
theorem shortestSuperpermutationLength_eight_lower_bound :
    shortestSuperpermutationLength 8 ≥ 46129 := by
  have h := shortestSuperpermutationLength_main_bound 8 (by norm_num)
  change shortestSuperpermutationLength 8 ≥
    8 + (8 + 1) * (8 - 1).factorial - 3 + mainBoundThreshold 8 at h
  norm_num [mainBoundThreshold_eight, Nat.factorial] at h
  exact h

/-- The ordinary-mathematics consequence `S(9) ≥ 408465`. -/
theorem shortestSuperpermutationLength_nine_lower_bound :
    shortestSuperpermutationLength 9 ≥ 408465 := by
  have h := shortestSuperpermutationLength_main_bound 9 (by norm_num)
  change shortestSuperpermutationLength 9 ≥
    9 + (9 + 1) * (9 - 1).factorial - 3 + mainBoundThreshold 9 at h
  norm_num [mainBoundThreshold_nine, Nat.factorial] at h
  exact h

/-- The ordinary-mathematics consequence `S(10) ≥ 4033329`. -/
theorem shortestSuperpermutationLength_ten_lower_bound :
    shortestSuperpermutationLength 10 ≥ 4033329 := by
  have h := shortestSuperpermutationLength_main_bound 10 (by norm_num)
  change shortestSuperpermutationLength 10 ≥
    10 + (10 + 1) * (10 - 1).factorial - 3 + mainBoundThreshold 10 at h
  norm_num [mainBoundThreshold_ten, Nat.factorial] at h
  exact h

/-- The ordinary-mathematics consequence `S(11) ≥ 43917793`. -/
theorem shortestSuperpermutationLength_eleven_lower_bound :
    shortestSuperpermutationLength 11 ≥ 43917793 := by
  have h := shortestSuperpermutationLength_main_bound 11 (by norm_num)
  change shortestSuperpermutationLength 11 ≥
    11 + (11 + 1) * (11 - 1).factorial - 3 + mainBoundThreshold 11 at h
  norm_num [mainBoundThreshold_eleven, Nat.factorial] at h
  exact h

/-- The ordinary-mathematics consequence `S(12) ≥ 522622030`. -/
theorem shortestSuperpermutationLength_twelve_lower_bound :
    shortestSuperpermutationLength 12 ≥ 522622030 := by
  have h := shortestSuperpermutationLength_main_bound 12 (by norm_num)
  change shortestSuperpermutationLength 12 ≥
    12 + (12 + 1) * (12 - 1).factorial - 3 + mainBoundThreshold 12 at h
  norm_num [mainBoundThreshold_twelve, Nat.factorial] at h
  exact h

end SuperpermutationLowerBound
