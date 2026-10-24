module

public import alternation.ActualPacking
public import bridge.FrozenParameters

@[expose] public section

namespace SuperpermutationLowerBound.ChainReturns
open SuperpermutationBounds.ChainReturns
open SuperpermutationLowerBound.Refinement.ChainReturns

theorem frozen_actualPacking_ten : ActualPacking 10 (by omega)
    (exactParameters 10).1 (exactParameters 10).2 := by
  have hR : returnZero 9 = 20 := by decide
  have hp : alternatingP 3 = 521 / 80 := by norm_num [alternatingP, hR]
  have ht : alternatingT 3 = 359 / 40 := by norm_num [alternatingT, hR]
  simpa only [hp, ht, exactParameters] using alternating_actualPacking 3 (by omega)

theorem generalParameters_zero_actualPacking (m : ℕ) (hm : 3 ≤ m)
    (R₀ R₁ : ℚ) (hR₀ : (returnZero (3 * m) : ℚ) ≤ R₀) :
    ActualPacking (3 * m + 1) (by omega)
      (generalParameters (3 * m) R₀ R₁).1
      (generalParameters (3 * m) R₀ R₁).2 := by
  have hh := alternating_actualPacking_upper m hm R₀ hR₀
  simpa [generalParameters, alternatingPAt, alternatingTAt] using hh

end SuperpermutationLowerBound.ChainReturns
