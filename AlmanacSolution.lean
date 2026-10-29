import AlmanacDefs
import AlmanacAdapter

/-! Headline lower results: the full exact general formula, its twelve-symbol
consequence, two finite refinements, and the fourth-factorial asymptotic consequence. -/
namespace AlmanacSubmission

/-- The exact-order general lower formula for every n ≥ 8, on arbitrary
covering words. Its twelve-symbol consequence is S(12) ≥ 522,622,380. -/
theorem general_lower : AlmanacAdapter.ExactWordBound := AlmanacAdapter.exact_word_bound

/-- Every ten-symbol superpermutation has at least 4,033,379 letters. -/
theorem lower10 : Almanac.LowerBoundAt 10 4033379 := AlmanacAdapter.lower10

/-- Every twelve-symbol superpermutation has at least 522,622,380 letters. -/
theorem lower12 : Almanac.LowerBoundAt 12 522622380 := AlmanacAdapter.lower12

/-- Every fourteen-symbol superpermutation has at least 93,891,141,150 letters. -/
theorem lower14 : Almanac.LowerBoundAt 14 93891141150 := AlmanacAdapter.lower14

/-- S(n) ≥ F₃(n) + (2 - o(1))(n-4)! in the epsilon sense. -/
theorem asymptotic_lower_four : Almanac.AsymptoticLowerAt 4 2 :=
  AlmanacAdapter.asymptotic_lower_four

end AlmanacSubmission
