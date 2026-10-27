import AlmanacDefs
import Submissions.Solution

/-! The complete lower submission, using the Almanac's word predicate for
the word bounds and preserving all thirteen original asymptotic statements.
The correction of order (n-4)! is not a positive coefficient of (n-3)!. -/

namespace AlmanacAdapter
open SuperpermutationPalomar

theorem covers_iff {n : Nat} (w : Almanac.Word n) :
    Covers w ↔ Almanac.IsSuperpermutation n w := by
  constructor
  · intro h p hnd hlen
    obtain ⟨u, v, huv⟩ := h p hlen hnd
    exact ⟨u, v, huv.symm⟩
  · intro h p hlen hnd
    obtain ⟨u, v, huv⟩ := h p hnd hlen
    exact ⟨u, v, huv.symm⟩

def ExactWordBound : Prop :=
  ∀ n : Nat, 8 ≤ n → ∀ w : Almanac.Word n,
    Almanac.IsSuperpermutation n w →
      GeneralLower.paperBound n (GeneralLower.exactParameters n).1
        (GeneralLower.exactParameters n).2 ≤ w.length

def QuadraticWordBound : Prop :=
  ∀ n : Nat, 8 ≤ n → ∀ w : Almanac.Word n,
    Almanac.IsSuperpermutation n w →
      GeneralLower.paperBound n (GeneralLower.quadraticParameters n).1
        (GeneralLower.quadraticParameters n).2 ≤ w.length

theorem exact_word_bound : ExactWordBound := by
  intro n hn w hw
  exact GeneralLower.exact_word_bound n hn w ((covers_iff w).mpr hw)

theorem quadratic_word_bound : QuadraticWordBound := by
  intro n hn w hw
  exact GeneralLower.quadratic_word_bound n hn w ((covers_iff w).mpr hw)

theorem lower10 : Almanac.LowerBoundAt 10 4033379 := by
  intro w hw
  exact Lower10.word_lower_bound w ((covers_iff w).mpr hw)

theorem lower12 : Almanac.LowerBoundAt 12 522622380 := by
  intro w hw
  have h := exact_word_bound 12 (by decide) w hw
  have hceil : ⌈((1415227652 : ℚ) / 18827)⌉₊ = 75171 := by
    apply (Nat.ceil_eq_iff (by norm_num)).2
    norm_num
  norm_num [GeneralLower.paperBound, GeneralLower.exactParameters, Nat.factorial, hceil] at h
  exact h

theorem lower14 : Almanac.LowerBoundAt 14 93891141150 := by
  intro w hw
  exact Lower14.word_lower_bound w ((covers_iff w).mpr hw)

/-- All seventeen original claims, plus the twelve-symbol consequence of
the general bound. All three improving finite values use the site's fixed
vocabulary. There is no assumed conclusion or extra premise. -/
def CompleteClaim : Prop :=
  ExactWordBound ∧ QuadraticWordBound ∧
  LowerAsymptotics.ExactLeadingLimit ∧
  LowerAsymptotics.QuadraticLeadingLimit ∧
  LowerAsymptotics.WordLowerBound ∧
  LowerAsymptotics.ExactReferenceZero ∧
  LowerAsymptotics.ExactReferenceOne ∧
  LowerAsymptotics.ExactReferenceTwo ∧
  LowerAsymptotics.QuadraticReferenceZero ∧
  LowerAsymptotics.QuadraticReferenceOne ∧
  LowerAsymptotics.QuadraticReferenceTwo ∧
  LowerAsymptotics.QuadraticGainZero ∧
  LowerAsymptotics.QuadraticGainOne ∧
  LowerAsymptotics.ExactGainZero ∧
  LowerAsymptotics.ExactGainOne ∧
  Almanac.LowerBoundAt 10 4033379 ∧ Almanac.LowerBoundAt 12 522622380 ∧
  Almanac.LowerBoundAt 14 93891141150

theorem complete_claim : CompleteClaim := by
  exact ⟨exact_word_bound, quadratic_word_bound,
    LowerAsymptotics.exact_leading_limit,
    LowerAsymptotics.quadratic_leading_limit,
    LowerAsymptotics.word_lower_bound_two_sub_epsilon,
    LowerAsymptotics.exact_reference_limit_zero,
    LowerAsymptotics.exact_reference_limit_one,
    LowerAsymptotics.exact_reference_limit_two,
    LowerAsymptotics.quadratic_reference_limit_zero,
    LowerAsymptotics.quadratic_reference_limit_one,
    LowerAsymptotics.quadratic_reference_limit_two,
    LowerAsymptotics.quadratic_gain_zero_limit,
    LowerAsymptotics.quadratic_gain_one_limit,
    LowerAsymptotics.exact_gain_zero_asymptotic_lower,
    LowerAsymptotics.exact_gain_one_asymptotic_lower,
    lower10, lower12, lower14⟩

end AlmanacAdapter
