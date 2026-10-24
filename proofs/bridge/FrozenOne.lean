module

public import alternation.OneActualPacking
public import bridge.FrozenParameters

@[expose] public section

namespace SuperpermutationLowerBound.ChainReturns
open SuperpermutationBounds.ChainReturns
open SuperpermutationLowerBound.Refinement.ChainReturns

theorem frozen_actualPacking_eleven : ActualPacking 11 (by omega)
    (exactParameters 11).1 (exactParameters 11).2 := by
  have hR : returnOne 3 = 12 := by decide
  have hh := one_actualPacking 3 (by omega)
  norm_num [exactParameters, _root_.ChainReturns.onePeriod,
    _root_.ChainReturns.oneMean, hR] at hh ⊢
  exact hh

theorem generalParameters_one_actualPacking (m : ℕ) (hm : 3 ≤ m)
    (R₀ R₁ : ℚ) (hR₁ : (returnOne m : ℚ) ≤ R₁) :
    ActualPacking (3 * m + 2) (by omega)
      (generalParameters (3 * m + 1) R₀ R₁).1
      (generalParameters (3 * m + 1) R₀ R₁).2 := by
  have hh := one_actualPacking_upper m hm R₁ hR₁
  have hmod : (3 * m + 1) % 3 = 1 := by omega
  have hdiv : (3 * m + 1) / 3 = m := by omega
  convert hh using 1 <;>
    simp [generalParameters, hmod, hdiv,
      _root_.ChainReturns.onePeriod, _root_.ChainReturns.oneMean]
  ring

end SuperpermutationLowerBound.ChainReturns
