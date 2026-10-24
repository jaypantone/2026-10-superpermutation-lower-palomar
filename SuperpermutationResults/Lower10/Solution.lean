module

public import SuperpermutationResults.Lower10.Challenge
public import H20.K10

@[expose] public section

namespace SuperpermutationResults.Lower10

/-- The independent public coverage definition agrees by reflexivity. -/
theorem coverage_eq (w : List (Fin 10)) :
    Covers w = SuperpermutationBounds.Covers w := rfl

theorem word_lower_bound : WordBound := by
  intro w hw
  exact H20.K10.word_lower_bound w hw

end SuperpermutationResults.Lower10
