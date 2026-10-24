module

public import bridge.FrozenPacking
public import bridge.FrozenEvaluations

@[expose] public section

/-!
The frozen manuscript's two complete word bounds. The only premise on the word
is the original contiguous-subword covering predicate. All geometric, return,
loss-counting, endpoint, and scalar hypotheses are discharged in the imports.
-/
namespace SuperpermutationLowerBound.ChainReturns
open SuperpermutationBounds.ChainReturns

/-- The frozen exact-return theorem for every alphabet size K>=8. -/
theorem exact_word_bound : ExactWordBound := by
  intro K hK w hw
  exact paper_word_bound_of_actualPacking hK (exactParameters_admissible hK)
    (frozen_exact_actualPacking hK) w hw

/-- The polynomial-return alternative for every alphabet size K>=8. -/
theorem quadratic_word_bound : QuadraticWordBound := by
  intro K hK w hw
  exact paper_word_bound_of_actualPacking hK (quadraticParameters_admissible hK)
    (frozen_quadratic_actualPacking hK) w hw

theorem frozen_word_eight (w : List (Fin 8)) (hw : SuperpermutationBounds.Covers w) :
    46130 ≤ w.length := by
  simpa only [frozen_bound_8] using exact_word_bound 8 (by omega) w hw

theorem frozen_word_nine (w : List (Fin 9)) (hw : SuperpermutationBounds.Covers w) :
    408469 ≤ w.length := by
  simpa only [frozen_bound_9] using exact_word_bound 9 (by omega) w hw

theorem frozen_word_ten (w : List (Fin 10)) (hw : SuperpermutationBounds.Covers w) :
    4033374 ≤ w.length := by
  simpa only [frozen_bound_10] using exact_word_bound 10 (by omega) w hw

theorem frozen_word_eleven (w : List (Fin 11)) (hw : SuperpermutationBounds.Covers w) :
    43917903 ≤ w.length := by
  simpa only [frozen_bound_11] using exact_word_bound 11 (by omega) w hw

theorem frozen_word_twelve (w : List (Fin 12)) (hw : SuperpermutationBounds.Covers w) :
    522622380 ≤ w.length := by
  simpa only [frozen_bound_12] using exact_word_bound 12 (by omega) w hw

theorem frozen_word_thirteen (w : List (Fin 13)) (hw : SuperpermutationBounds.Covers w) :
    6746626531 ≤ w.length := by
  simpa only [frozen_bound_13] using exact_word_bound 13 (by omega) w hw

theorem frozen_word_fourteen (w : List (Fin 14)) (hw : SuperpermutationBounds.Covers w) :
    93891141149 ≤ w.length := by
  simpa only [frozen_bound_14] using exact_word_bound 14 (by omega) w hw

end SuperpermutationLowerBound.ChainReturns
