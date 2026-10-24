module

public import asymptotics.gains.ExactComparison

@[expose] public section

noncomputable section
open Filter Topology
namespace SuperpermutationBounds.ChainReturns.Asymptotic

/-- The exact return orders give an asymptotic lower bound of `9/2` on the
`(K-9)!` scale when `K=3m+1`. No convergence claim is made for these exact orders. -/
theorem exact_gain_zero_asymptotic_lower (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, (9/2:ℝ)-ε ≤
      ((exactNat (3*m+1):ℝ)-(oldNat (3*m+1):ℝ))/((3*m+1-9).factorial:ℝ) := by
  have hquad := quadratic_gain_zero_limit.eventually
    (eventually_gt_nhds (show (9/2:ℝ)-ε < 9/2 by linarith))
  filter_upwards [hquad, exact_ge_quadratic_zero_eventually] with m hlow hmono
  have hm : (quadraticNat (3*m+1):ℝ) ≤ (exactNat (3*m+1):ℝ) := by exact_mod_cast hmono
  exact hlow.le.trans (div_le_div_of_nonneg_right
    (sub_le_sub_right hm _) (by positivity))

/-- The exact return orders give an asymptotic lower bound of `324` on the
`(K-11)!` scale when `K=3m+2`. Exceptional linear return orders can give more. -/
theorem exact_gain_one_asymptotic_lower (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, (324:ℝ)-ε ≤
      ((exactNat (3*m+2):ℝ)-(oldNat (3*m+2):ℝ))/((3*m+2-11).factorial:ℝ) := by
  have hquad := quadratic_gain_one_limit.eventually
    (eventually_gt_nhds (show (324:ℝ)-ε < 324 by linarith))
  filter_upwards [hquad, exact_ge_quadratic_one_eventually] with m hlow hmono
  have hm : (quadraticNat (3*m+2):ℝ) ≤ (exactNat (3*m+2):ℝ) := by exact_mod_cast hmono
  exact hlow.le.trans (div_le_div_of_nonneg_right
    (sub_le_sub_right hm _) (by positivity))

end SuperpermutationBounds.ChainReturns.Asymptotic
