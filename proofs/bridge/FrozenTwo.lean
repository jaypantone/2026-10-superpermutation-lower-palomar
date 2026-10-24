module

public import PaidTwo
public import pairs.ActualSquare
public import SuperpermutationLowerBound.Refinement.GeometryPacking
public import bridge.FrozenParameters

@[expose] public section

namespace SuperpermutationLowerBound.ChainReturns
open SuperpermutationBounds.ChainReturns
open SuperpermutationLowerBound.Refinement
open _root_.ChainReturns

theorem frozen_two_actualPacking (m : ℕ) (hm : 3 ≤ m) :
    ActualPacking (3 * m + 3) (by omega) (twoMax m + 1)
      (2 * twoMean m - twoEpsilon m / 2) := by
  intro P hP segment
  have hn : 7 ≤ 3 * m + 2 := by omega
  have hold := actual_segment_returnAvoidance hn segment
  have hmod : (3 * m + 2) % 3 = 2 := by omega
  have hdiv : (3 * m + 2) / 3 = m := by omega
  have hperiod : period (3 * m + 2) = twoMax m + 1 := by
    simp [period, hmod, hdiv, twoMax]
    ring
  have hbasic : BasicCellAvoidance (3 * m + 2 - 2) (twoMax m + 1)
      segment.deficitString := by simpa only [hperiod] using hold.basic
  have hlocal : ResidueTwoAvoidance (3 * m + 2 - 2) (twoThreshold m)
      segment.deficitString := by
    simpa [hdiv, twoThreshold] using hold.residueTwo hmod
  have havoid := actual_square_pair_avoidance m (by omega) hn segment
  have hrepeat : ¬ CellFactor (3 * m + 2 - 2)
      (repeatedCells (completedPair (twoMax m) (twoThreshold m - 2)) 2)
      segment.deficitString := by
    simpa only [squareCells, repeatedCells, List.append_nil] using havoid
  simpa only [show 3 * m + 3 - 1 = 3 * m + 2 by omega] using
    chainPacking_paid_two (by omega) hm hbasic hlocal hrepeat

theorem frozen_actualPacking_twelve : ActualPacking 12 (by omega)
    (exactParameters 12).1 (exactParameters 12).2 := by
  have hh := frozen_two_actualPacking 3 (by omega)
  norm_num [exactParameters, twoMax, twoMean, twoThreshold, twoEpsilon] at hh ⊢
  exact hh

theorem generalParameters_two_actualPacking (m : ℕ) (hm : 4 ≤ m)
    (R₀ R₁ : ℚ) :
    ActualPacking (3 * m + 3) (by omega)
      (generalParameters (3 * m + 2) R₀ R₁).1
      (generalParameters (3 * m + 2) R₀ R₁).2 := by
  have hh := frozen_two_actualPacking m (by omega)
  have hmod : (3 * m + 2) % 3 = 2 := by omega
  have hdiv : (3 * m + 2) / 3 = m := by omega
  have hmQ : (4 : ℚ) ≤ m := by exact_mod_cast hm
  have heps : twoEpsilon m = 1 := by
    dsimp [twoEpsilon]
    apply min_eq_left
    linarith
  have hv : 2 ≤ twoThreshold m := by dsimp [twoThreshold]; nlinarith
  have hp : (twoMax m : ℚ) + 1 = ((m : ℚ) + 1) * (2 * m + 1) := by
    simp [twoMax]
    ring
  have ht : 2 * twoMean m - twoEpsilon m / 2 = 4 * (m : ℚ)^2 + 5 * m - 5 / 2 := by
    rw [twoMean, Nat.cast_sub hv, heps]
    simp only [twoMax, twoThreshold, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring
  simpa only [generalParameters, hmod, hdiv, hp, ht] using hh

end SuperpermutationLowerBound.ChainReturns
