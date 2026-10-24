module

public import bridge.InheritedCheck
public import bridge.FrozenNine
public import bridge.FrozenZero
public import bridge.FrozenOne
public import bridge.FrozenTwo

@[expose] public section

/-! The complete parameter table on every actual light segment. -/
namespace SuperpermutationLowerBound.ChainReturns
open SuperpermutationBounds.ChainReturns

theorem generalParameters_actualPacking {K : ℕ} (hK : 13 ≤ K)
    (R₀ R₁ : ℚ) (hR₀ : (returnZero (K - 1) : ℚ) ≤ R₀)
    (hR₁ : (K - 1) % 3 = 1 → (returnOne ((K - 1) / 3) : ℚ) ≤ R₁) :
    ActualPacking K (by omega)
      (generalParameters (K - 1) R₀ R₁).1
      (generalParameters (K - 1) R₀ R₁).2 := by
  have hmod : (K - 1) % 3 = 0 ∨ (K - 1) % 3 = 1 ∨ (K - 1) % 3 = 2 := by omega
  rcases hmod with hmod | hmod | hmod
  · generalize hm : (K - 1) / 3 = m at *
    have hform : K = 3 * m + 1 := by omega
    subst K
    exact generalParameters_zero_actualPacking m (by omega) R₀ R₁
      (by simpa only [Nat.add_sub_cancel] using hR₀)
  · have hR := hR₁ hmod
    generalize hm : (K - 1) / 3 = m at *
    have hform : K = 3 * m + 2 := by omega
    subst K
    simpa only [show 3 * m + 2 - 1 = 3 * m + 1 by omega] using
      generalParameters_one_actualPacking m (by omega) R₀ R₁ hR
  · generalize hm : (K - 1) / 3 = m at *
    have hform : K = 3 * m + 3 := by omega
    subst K
    simpa only [show 3 * m + 3 - 1 = 3 * m + 2 by omega] using
      generalParameters_two_actualPacking m (by omega) R₀ R₁

theorem frozen_exact_actualPacking {K : ℕ} (hK : 8 ≤ K) :
    ActualPacking K hK (exactParameters K).1 (exactParameters K).2 := by
  by_cases hsmall : K < 13
  · interval_cases K
    · exact inherited_actualPacking_eight
    · exact frozen_actualPacking_nine
    · exact frozen_actualPacking_ten
    · exact frozen_actualPacking_eleven
    · exact frozen_actualPacking_twelve
  · rw [exactParameters_large (by omega)]
    exact generalParameters_actualPacking (by omega) _ _ le_rfl (fun _ => le_rfl)

theorem frozen_quadratic_actualPacking {K : ℕ} (hK : 8 ≤ K) :
    ActualPacking K hK (quadraticParameters K).1 (quadraticParameters K).2 := by
  unfold quadraticParameters
  split_ifs with hsmall
  · exact frozen_exact_actualPacking hK
  · apply generalParameters_actualPacking (by omega)
    · have hh := returnZero_quadratic (by omega : 2 ≤ K - 1)
      have hq : 4 * (returnZero (K - 1) : ℚ) ≤ ((K - 1 : ℕ) : ℚ)^2 := by
        exact_mod_cast hh
      linarith
    · intro hmod
      have hh := returnOne_quadratic (by omega : 3 ≤ (K - 1) / 3)
      have hform : 3 * ((K - 1) / 3) + 1 = K - 1 := by omega
      rw [hform] at hh
      have hq : 4 * (returnOne ((K - 1) / 3) : ℚ) ≤ ((K - 1 : ℕ) : ℚ)^2 := by
        exact_mod_cast hh
      linarith

end SuperpermutationLowerBound.ChainReturns
