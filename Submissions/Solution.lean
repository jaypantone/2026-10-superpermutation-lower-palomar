module

public import Submissions.General.Solution
public import Submissions.Asymptotics.Solution
public import Submissions.Ten.Solution
public import Submissions.Fourteen.Solution

@[expose] public section

/-! One set of formulas and word definitions for all submitted claims.
The four additional statements follow from the original theorems by
definitional equality; no mathematical assumption is added. -/

namespace SuperpermutationPalomar.GeneralLower

theorem exact_word_bound : ExactWordBound := by
  exact SuperpermutationResults.GeneralLower.exact_word_bound

theorem quadratic_word_bound : QuadraticWordBound := by
  exact SuperpermutationResults.GeneralLower.quadratic_word_bound

end SuperpermutationPalomar.GeneralLower

namespace SuperpermutationPalomar.Lower10

def WordBound : Prop :=
  ∀ w : List (Fin 10), Covers w → 4033379 ≤ w.length

theorem word_lower_bound : WordBound := by
  exact SuperpermutationResults.Lower10.word_lower_bound

end SuperpermutationPalomar.Lower10

namespace SuperpermutationPalomar.Lower14

def WordBound : Prop :=
  ∀ w : List (Fin 14), Covers w → 93891141150 ≤ w.length

theorem word_lower_bound : WordBound := by
  exact SuperpermutationResults.Lower14.word_lower_bound

end SuperpermutationPalomar.Lower14
