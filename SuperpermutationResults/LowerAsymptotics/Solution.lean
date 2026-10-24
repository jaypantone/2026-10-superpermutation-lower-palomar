module

public import SuperpermutationResults.LowerAsymptotics.Challenge
public import asymptotics.foundation.Leading
public import asymptotics.reference.Results
public import asymptotics.gains.ExactGains

@[expose] public section

/-! All thirteen final asymptotic claims are exposed in the independent
challenge. The sequence definitions and arithmetic are unchanged. -/
namespace SuperpermutationResults.LowerAsymptotics
noncomputable section

theorem exactNat_eq (K : ℕ) :
    exactNat K = SuperpermutationBounds.ChainReturns.Asymptotic.exactNat K := rfl

theorem quadraticNat_eq (K : ℕ) :
    quadraticNat K = SuperpermutationBounds.ChainReturns.Asymptotic.quadraticNat K := rfl

theorem oldNat_eq (K : ℕ) :
    oldNat K = SuperpermutationBounds.ChainReturns.Asymptotic.oldNat K := rfl

theorem referenceNat_eq (K : ℕ) :
    referenceNat K = SuperpermutationBounds.ChainReturns.Asymptotic.referenceNat K := rfl

theorem exact_leading_limit : ExactLeadingLimit :=
  SuperpermutationBounds.ChainReturns.Asymptotic.exact_leading_limit

theorem quadratic_leading_limit : QuadraticLeadingLimit :=
  SuperpermutationBounds.ChainReturns.Asymptotic.quadratic_leading_limit

theorem word_lower_bound_two_sub_epsilon : WordLowerBound :=
  SuperpermutationBounds.ChainReturns.Asymptotic.word_lower_bound_two_sub_epsilon

theorem exact_reference_limit_zero : ExactReferenceZero :=
  SuperpermutationBounds.ChainReturns.Asymptotic.exact_reference_limit_zero

theorem exact_reference_limit_one : ExactReferenceOne :=
  SuperpermutationBounds.ChainReturns.Asymptotic.exact_reference_limit_one

theorem exact_reference_limit_two : ExactReferenceTwo :=
  SuperpermutationBounds.ChainReturns.Asymptotic.exact_reference_limit_two

theorem quadratic_reference_limit_zero : QuadraticReferenceZero :=
  SuperpermutationBounds.ChainReturns.Asymptotic.quadratic_reference_limit_zero

theorem quadratic_reference_limit_one : QuadraticReferenceOne :=
  SuperpermutationBounds.ChainReturns.Asymptotic.quadratic_reference_limit_one

theorem quadratic_reference_limit_two : QuadraticReferenceTwo :=
  SuperpermutationBounds.ChainReturns.Asymptotic.quadratic_reference_limit_two

theorem quadratic_gain_zero_limit : QuadraticGainZero :=
  SuperpermutationBounds.ChainReturns.Asymptotic.quadratic_gain_zero_limit

theorem quadratic_gain_one_limit : QuadraticGainOne :=
  SuperpermutationBounds.ChainReturns.Asymptotic.quadratic_gain_one_limit

theorem exact_gain_zero_asymptotic_lower : ExactGainZero :=
  SuperpermutationBounds.ChainReturns.Asymptotic.exact_gain_zero_asymptotic_lower

theorem exact_gain_one_asymptotic_lower : ExactGainOne :=
  SuperpermutationBounds.ChainReturns.Asymptotic.exact_gain_one_asymptotic_lower

end
end SuperpermutationResults.LowerAsymptotics
