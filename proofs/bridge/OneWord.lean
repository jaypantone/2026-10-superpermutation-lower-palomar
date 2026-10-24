module

public import bridge.FrozenOne
public import bridge.FrozenEvaluations

@[expose] public section

namespace SuperpermutationLowerBound.ChainReturns
open SuperpermutationBounds.ChainReturns
open SuperpermutationLowerBound.Refinement.ChainReturns

theorem frozen_actualPacking_fourteen : ActualPacking 14 (by omega)
    (exactParameters 14).1 (exactParameters 14).2 := by
  have hR : returnOne 4 = 15 := by decide
  have hh := one_actualPacking 4 (by omega)
  rw [exactParameters_fourteen]
  norm_num [_root_.ChainReturns.onePeriod, _root_.ChainReturns.oneMean, hR] at hh ⊢
  exact hh

theorem word_eleven (w : List (Fin 11)) (hw : SuperpermutationBounds.Covers w) :
    43917903 ≤ w.length := by
  have h := paper_word_bound_of_actualPacking (by omega : 8 ≤ 11)
    (exactParameters_admissible (by omega)) frozen_actualPacking_eleven w hw
  simpa only [frozen_bound_11] using h

theorem word_fourteen (w : List (Fin 14)) (hw : SuperpermutationBounds.Covers w) :
    93891141149 ≤ w.length := by
  have h := paper_word_bound_of_actualPacking (by omega : 8 ≤ 14)
    (exactParameters_admissible (by omega)) frozen_actualPacking_fourteen w hw
  simpa only [frozen_bound_14] using h

#print axioms word_eleven
#print axioms word_fourteen
end SuperpermutationLowerBound.ChainReturns
