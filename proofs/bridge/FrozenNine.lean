module

public import pairs.PaidNine
public import bridge.FrozenEvaluations

@[expose] public section

namespace SuperpermutationLowerBound.ChainReturns
open SuperpermutationBounds.ChainReturns

theorem frozen_actualPacking_nine : ActualPacking 9 (by omega)
    (exactParameters 9).1 (exactParameters 9).2 := by
  intro P hP segment
  exact Refinement.actual_chainPacking_nine segment

theorem word_nine (w : List (Fin 9)) (hw : SuperpermutationBounds.Covers w) :
    408469 ≤ w.length := by
  have h := paper_word_bound_of_actualPacking (by omega : 8 ≤ 9)
    (exactParameters_admissible (by omega)) frozen_actualPacking_nine w hw
  simpa only [frozen_bound_9] using h

#print axioms word_nine
end SuperpermutationLowerBound.ChainReturns
