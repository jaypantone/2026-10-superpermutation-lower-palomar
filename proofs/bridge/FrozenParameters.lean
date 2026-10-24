module

public import bridge.ParameterGates
public import bridge.ReturnPositivity

@[expose] public section

/-! Scalar admissibility of both complete frozen parameter tables. No geometric
packing assumption enters these arithmetic checks. -/
namespace SuperpermutationLowerBound.ChainReturns
open SuperpermutationBounds.ChainReturns

theorem generalParameters_admissible (n : ℕ) (hn : 12 ≤ n)
    (R₀ R₁ : ℚ) (hR₀ : 1 ≤ R₀) (hR₁ : 1 ≤ R₁) :
    Admissible n (generalParameters n R₀ R₁).1 (generalParameters n R₀ R₁).2 := by
  have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hmod with hmod | hmod | hmod
  · have hh := admissible_modZero (n / 3) (by omega) R₀ hR₀
    convert hh using 1 <;> first | omega | simp [generalParameters, hmod]
  · have hh := admissible_modOne (n / 3) (by omega) R₁ hR₁
    convert hh using 1 <;> first | omega | simp [generalParameters, hmod]
  · have hh := admissible_modTwo (n / 3) (by omega)
    convert hh using 1 <;> first | omega | simp [generalParameters, hmod]

theorem exactParameters_large {K : ℕ} (hK : 13 ≤ K) :
    exactParameters K = generalParameters (K - 1) (returnZero (K - 1))
      (returnOne ((K - 1) / 3)) := by
  unfold exactParameters
  split <;> try omega
  rfl

theorem exactParameters_admissible {K : ℕ} (hK : 8 ≤ K) :
    Admissible (K - 1) (exactParameters K).1 (exactParameters K).2 := by
  by_cases hsmall : K < 13
  · interval_cases K <;> simp only [exactParameters]
    · exact admissible_eight
    · exact admissible_nine
    · exact admissible_ten
    · exact admissible_eleven
    · exact admissible_twelve
  · rw [exactParameters_large (by omega)]
    apply generalParameters_admissible (K - 1) (by omega)
    · exact_mod_cast returnZero_pos (by omega : 2 ≤ K - 1)
    · exact_mod_cast returnOne_pos (by omega : 3 ≤ (K - 1) / 3)

theorem quadraticParameters_admissible {K : ℕ} (hK : 8 ≤ K) :
    Admissible (K - 1) (quadraticParameters K).1 (quadraticParameters K).2 := by
  unfold quadraticParameters
  split_ifs with hsmall
  · exact exactParameters_admissible hK
  · have hnQ : (12 : ℚ) ≤ (K - 1 : ℕ) := by exact_mod_cast (show 12 ≤ K - 1 by omega)
    apply generalParameters_admissible (K - 1) (by omega)
    all_goals nlinarith

end SuperpermutationLowerBound.ChainReturns
