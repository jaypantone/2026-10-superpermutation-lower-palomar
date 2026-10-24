module

public import SuperpermutationLowerBound.Refinement.Definitions
public import Mathlib.Tactic

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

theorem period_ge_two {n : ℕ} (hn : 7 ≤ n) : 2 ≤ period n := by
  have hm : 2 ≤ n / 3 := by omega
  unfold period
  split_ifs <;> nlinarith

theorem period_le_chainAllowance {n : ℕ} (hn : 7 ≤ n) :
    (period n : ℚ) ≤ chainAllowance n := by
  have hm : 2 ≤ n / 3 := by omega
  have hmQ : (2 : ℚ) ≤ (n / 3 : ℕ) := by exact_mod_cast hm
  unfold chainAllowance period
  split_ifs <;> push_cast <;> nlinarith

theorem chainAllowance_le_effectiveAllowance (n : ℕ) :
    chainAllowance n ≤ effectiveAllowance n := le_max_left _ _

theorem period_le_effectiveAllowance {n : ℕ} (hn : 7 ≤ n) :
    (period n : ℚ) ≤ effectiveAllowance n :=
  (period_le_chainAllowance hn).trans (chainAllowance_le_effectiveAllowance n)

theorem effectiveAllowance_ge_two {n : ℕ} (hn : 7 ≤ n) :
    2 ≤ effectiveAllowance n := by
  have hp : (2 : ℚ) ≤ period n := by exact_mod_cast period_ge_two hn
  exact hp.trans (period_le_effectiveAllowance hn)

theorem effectiveAllowance_margin {n : ℕ} (hn : 7 ≤ n) :
    4 * (period n : ℚ) + 6 ≤ effectiveAllowance n * ((n : ℚ) - 4) := by
  have hnQ : (7 : ℚ) ≤ n := by exact_mod_cast hn
  exact (div_le_iff₀ (by linarith : (0 : ℚ) < n - 4)).mp (le_max_right _ _)

private theorem rational_parameter_domain {n p t : ℚ}
    (hn : 7 ≤ n) (hp : 2 ≤ p) (ht : p ≤ t) :
    0 < (n - 2) * t - 2 ∧
    0 < 2*t / ((n-2)*t-2) ∧
    2*t / ((n-2)*t-2) < 1 ∧
    1 ≤ (2*t*(n-1)+4*p) / ((n-2)*t-2) ∧
    (2*t*(n-1)+4*p) / ((n-2)*t-2) ≤
      n - 2*t / ((n-2)*t-2) := by
  have ht2 : 2 ≤ t := hp.trans ht
  have hprod : 0 ≤ (n - 7) * t := mul_nonneg (by linarith) (by linarith)
  have hden : 0 < (n - 2) * t - 2 := by nlinarith
  have hsmall : 2*t < (n-2)*t-2 := by nlinarith
  have hbeta : (n-2)*t-2 ≤ 2*t*(n-1)+4*p := by nlinarith
  have hmid : 2*t ≤ (n-4)*t-2 := by nlinarith
  have hlarge := mul_le_mul_of_nonneg_left hmid (by linarith : 0 ≤ n)
  have hnt : 0 ≤ (n-2)*t := mul_nonneg (by linarith) (by linarith)
  have hupper : 2*t*(n-1)+4*p ≤ n*((n-2)*t-2)-2*t := by nlinarith
  refine ⟨hden, div_pos (by linarith) hden,
    (div_lt_one hden).2 hsmall, (le_div_iff₀ hden).2 ?_, ?_⟩
  · simpa using hbeta
  · apply (div_le_iff₀ hden).2
    rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hden)]
    exact hupper

theorem scalarLambda_pos {n : ℕ} (hn : 7 ≤ n) : 0 < scalarLambda n := by
  exact (rational_parameter_domain (by exact_mod_cast hn)
    (by exact_mod_cast period_ge_two hn) (period_le_effectiveAllowance hn)).1

/-- All parameter obligations required by the hereditary forest assembly. -/
theorem scalar_parameters {n : ℕ} (hn : 7 ≤ n) :
    0 < scalarDelta n ∧ scalarDelta n < 1 ∧
    1 ≤ scalarBeta n ∧ scalarBeta n ≤ (n : ℚ) - scalarDelta n := by
  exact (rational_parameter_domain (by exact_mod_cast hn)
    (by exact_mod_cast period_ge_two hn) (period_le_effectiveAllowance hn)).2

end SuperpermutationLowerBound.Refinement
