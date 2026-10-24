module

public import bridge.GenericTransfer
public import FrozenStatement

@[expose] public section

/-! Equality of the forest normalization and the literal displayed formula.
The nonnegativity check matters because the formulas use natural ceilings. -/
namespace SuperpermutationLowerBound.ChainReturns

private theorem ceil_nat_add {x : ℚ} (hx : 0 ≤ x) (a : ℕ) :
    ⌈((a : ℚ) + x)⌉₊ = a + ⌈x⌉₊ := by
  apply le_antisymm
  · apply Nat.ceil_le.mpr
    have hc : x ≤ (⌈x⌉₊ : ℚ) := Nat.le_ceil x
    push_cast
    linarith
  · have hc : (a : ℚ) + x ≤ (⌈((a : ℚ) + x)⌉₊ : ℚ) :=
      Nat.le_ceil ((a : ℚ) + x)
    have haQ : (a : ℚ) ≤ (⌈((a : ℚ) + x)⌉₊ : ℚ) := by linarith
    have ha : a ≤ ⌈((a : ℚ) + x)⌉₊ := by exact_mod_cast haQ
    have hxceil : ⌈x⌉₊ ≤ ⌈((a : ℚ) + x)⌉₊ - a := by
      apply Nat.ceil_le.mpr
      rw [Nat.cast_sub ha]
      linarith
    omega

private theorem factorial_pred_ge {K : ℕ} (hK : 8 ≤ K) :
    K ≤ (K - 2).factorial := by
  have hbase := Nat.self_le_factorial (K - 3)
  have htwo : 2 ≤ (K - 3).factorial := by omega
  have hmul := Nat.mul_le_mul_left (K - 2) htwo
  have hfac := Nat.factorial_succ (K - 3)
  rw [show K - 3 + 1 = K - 2 by omega] at hfac
  rw [← hfac] at hmul
  omega

/-- The denominator in the literal paper formula is positive on its domain. -/
theorem paper_denominator_pos {K : ℕ} (hK : 8 ≤ K) {p t : ℚ}
    (h : Admissible (K - 1) p t) :
    0 < (K : ℚ)^2 - 4 * K + 1 - 2 * ((K : ℚ) - 1) / t := by
  have hc : ((K - 1 : ℕ) : ℚ) = (K : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ K), Nat.cast_one]
  have ht := ne_of_gt h.t_pos
  have heq : (K : ℚ)^2 - 4 * K + 1 - 2 * ((K : ℚ) - 1) / t =
      (((K - 1 : ℕ) : ℚ) * lam (K - 1) t - 2 * t) / t := by
    dsimp [lam]
    rw [hc]
    field_simp
    ring
  rw [heq]
  exact div_pos (denominator_pos h) h.t_pos

/-- The final factorial-scale correction is nonnegative. -/
theorem paper_correction_nonneg {K : ℕ} (hK : 8 ≤ K) {p t : ℚ}
    (h : Admissible (K - 1) p t) :
    0 ≤ (2 * ((K - 2).factorial : ℚ) - 2 * ((K : ℚ) - 2) - 4 * p / t) /
      ((K : ℚ)^2 - 4 * K + 1 - 2 * ((K : ℚ) - 1) / t) := by
  have hf : (K : ℚ) ≤ (K - 2).factorial := by
    exact_mod_cast factorial_pred_ge hK
  have hpt : p / t ≤ 1 := (div_le_one h.t_pos).2 h.p_le_t
  have hnum : 0 ≤ 2 * ((K - 2).factorial : ℚ) -
      2 * ((K : ℚ) - 2) - 4 * p / t := by
    rw [mul_div_assoc]
    linarith
  exact div_nonneg hnum (le_of_lt (paper_denominator_pos hK h))

/-- Removal of the integer factorial from the rational forest quotient. -/
theorem forest_quotient_eq_factorial_add {K : ℕ} (hK : 8 ≤ K) {p t : ℚ}
    (h : Admissible (K - 1) p t) :
    (lam (K - 1) t * ((K - 1).factorial : ℚ) - intercept (K - 1) p t) /
      (((K - 1 : ℕ) : ℚ) * lam (K - 1) t - 2 * t) =
    ((K - 2).factorial : ℚ) +
      (2 * ((K - 2).factorial : ℚ) - 2 * ((K : ℚ) - 2) - 4 * p / t) /
        ((K : ℚ)^2 - 4 * K + 1 - 2 * ((K : ℚ) - 1) / t) := by
  have hc : ((K - 1 : ℕ) : ℚ) = (K : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ K), Nat.cast_one]
  have hfac := Nat.factorial_succ (K - 2)
  rw [show K - 2 + 1 = K - 1 by omega] at hfac
  have hfacQ : ((K - 1).factorial : ℚ) =
      ((K : ℚ) - 1) * ((K - 2).factorial : ℚ) := by
    rw [hfac, Nat.cast_mul, hc]
  have ht := ne_of_gt h.t_pos
  have hd := ne_of_gt (denominator_pos h)
  have hnum : 2 * ((K - 2).factorial : ℚ) - 2 * ((K : ℚ) - 2) - 4*p/t =
      (2*t*((K - 2).factorial : ℚ) - 2*t*((K : ℚ)-2) - 4*p)/t := by
    field_simp
  have hden : (K : ℚ)^2 - 4*K + 1 - 2*((K : ℚ)-1)/t =
      (((K-1 : ℕ) : ℚ)*lam (K-1) t-2*t)/t := by
    dsimp [lam]
    rw [hc]
    field_simp
    ring
  rw [hfacQ, hnum, hden, div_div_div_cancel_right₀ ht]
  apply (div_eq_iff hd).2
  rw [add_mul, div_mul_cancel₀ _ hd]
  dsimp [lam, intercept]
  rw [hc]
  ring

/-- The bound assembled from the forest is exactly the manuscript's formula. -/
theorem bound_eq_paperBound {K : ℕ} (hK : 8 ≤ K) {p t : ℚ}
    (h : Admissible (K - 1) p t) :
    bound K p t = SuperpermutationBounds.ChainReturns.paperBound K p t := by
  unfold bound SuperpermutationBounds.ChainReturns.paperBound
  dsimp only
  rw [forest_quotient_eq_factorial_add hK h,
    ceil_nat_add (paper_correction_nonneg hK h)]
  have hfac := Nat.factorial_succ (K - 1)
  rw [show K - 1 + 1 = K by omega] at hfac
  rw [hfac, Nat.add_mul, Nat.one_mul]
  omega

/-- Transfer stated using the exact formula in the frozen manuscript. -/
theorem paper_word_bound_of_actualPacking {K : ℕ} (hK : 8 ≤ K) {p t : ℚ}
    (h : Admissible (K - 1) p t) (H : ActualPacking K hK p t)
    (w : List (Fin K)) (hw : SuperpermutationBounds.Covers w) :
    SuperpermutationBounds.ChainReturns.paperBound K p t ≤ w.length := by
  rw [← bound_eq_paperBound hK h]
  exact word_bound_of_actualPacking hK h H w hw

end SuperpermutationLowerBound.ChainReturns
