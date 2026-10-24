module

public import bridge.FrozenParameters
public import bridge.Normalization
public import bridge.NumericalEvaluations

@[expose] public section

namespace SuperpermutationLowerBound.ChainReturns
open SuperpermutationBounds.ChainReturns

theorem frozen_bound_8 : paperBound 8 (exactParameters 8).1 (exactParameters 8).2 = 46130 := by
  rw [← bound_eq_paperBound (by omega : 8 ≤ 8) (exactParameters_admissible (by omega))]
  exact bound_8

theorem frozen_bound_9 : paperBound 9 (exactParameters 9).1 (exactParameters 9).2 = 408469 := by
  rw [← bound_eq_paperBound (by omega : 8 ≤ 9) (exactParameters_admissible (by omega))]
  exact bound_9

theorem frozen_bound_10 : paperBound 10 (exactParameters 10).1 (exactParameters 10).2 = 4033374 := by
  rw [← bound_eq_paperBound (by omega : 8 ≤ 10) (exactParameters_admissible (by omega))]
  exact bound_10

theorem frozen_bound_11 : paperBound 11 (exactParameters 11).1 (exactParameters 11).2 = 43917903 := by
  rw [← bound_eq_paperBound (by omega : 8 ≤ 11) (exactParameters_admissible (by omega))]
  exact bound_11

theorem frozen_bound_12 : paperBound 12 (exactParameters 12).1 (exactParameters 12).2 = 522622380 := by
  rw [← bound_eq_paperBound (by omega : 8 ≤ 12) (exactParameters_admissible (by omega))]
  exact bound_12

theorem exactParameters_thirteen : exactParameters 13 = (1191/140, 909/70) := by
  have hR : returnZero 12 = 35 := by decide
  norm_num [exactParameters, generalParameters, hR]

theorem exactParameters_fourteen : exactParameters 14 = (36, 569/15) := by
  have hR : returnOne 4 = 15 := by decide
  norm_num [exactParameters, generalParameters, hR]

theorem frozen_bound_13 : paperBound 13 (exactParameters 13).1 (exactParameters 13).2 = 6746626531 := by
  rw [← bound_eq_paperBound (by omega : 8 ≤ 13) (exactParameters_admissible (by omega))]
  rw [exactParameters_thirteen]
  exact bound_13

theorem frozen_bound_14 : paperBound 14 (exactParameters 14).1 (exactParameters 14).2 = 93891141149 := by
  rw [← bound_eq_paperBound (by omega : 8 ≤ 14) (exactParameters_admissible (by omega))]
  rw [exactParameters_fourteen]
  exact bound_14

end SuperpermutationLowerBound.ChainReturns
