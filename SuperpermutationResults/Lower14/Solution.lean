module

public import SuperpermutationResults.Lower14.Challenge
public import new_results.Bounds

@[expose] public section

namespace SuperpermutationResults.Lower14

/-- The independent public coverage definition agrees by reflexivity. -/
theorem coverage_eq (w : List (Fin 14)) :
    Covers w = SuperpermutationBounds.Covers w := rfl

theorem word_lower_bound : WordBound := by
  intro w hw
  exact SuperpermutationLowerBound.NewResults.word_fourteen w hw

end SuperpermutationResults.Lower14
