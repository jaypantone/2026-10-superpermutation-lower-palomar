module

public import pairs.VerifiedOne
public import bridge.GenericTransfer

@[expose] public section

namespace SuperpermutationLowerBound.Refinement.ChainReturns

open SuperpermutationLowerBound.Refinement

/-- The proved residue-one return gives the frozen hereditary chain estimate
on every actual light segment. -/
theorem one_actualPacking (m : ℕ) (hm : 3 ≤ m) :
    SuperpermutationLowerBound.ChainReturns.ActualPacking (3 * m + 2) (by omega)
      (_root_.ChainReturns.onePeriod m)
      (2 * _root_.ChainReturns.oneMean m -
        1 / (SuperpermutationBounds.ChainReturns.returnOne m : ℚ)) := by
  intro P hP segment
  simpa only [show 3 * m + 2 - 1 = 3 * m + 1 by omega] using
    actual_chainPacking_residueOne m hm (by omega) segment

/-- Any upper bound on the proved return exponent weakens only the slope;
the endpoint allowance remains the original pure-chain period. -/
theorem one_actualPacking_upper (m : ℕ) (hm : 3 ≤ m) (U : ℚ)
    (hU : (SuperpermutationBounds.ChainReturns.returnOne m : ℚ) ≤ U) :
    SuperpermutationLowerBound.ChainReturns.ActualPacking (3 * m + 2) (by omega)
      (_root_.ChainReturns.onePeriod m)
      (2 * _root_.ChainReturns.oneMean m - 1 / U) := by
  intro P hP segment
  have hR : (0 : ℚ) < SuperpermutationBounds.ChainReturns.returnOne m := by
    exact_mod_cast SuperpermutationBounds.ChainReturns.returnOne_pos hm
  exact (one_actualPacking m hm P hP segment).mono (by
    have hinv : 1 / U ≤ 1 / (SuperpermutationBounds.ChainReturns.returnOne m : ℚ) :=
      one_div_le_one_div_of_le hR hU
    linarith)

/-- The polynomial specialization used by the frozen all-size theorem. -/
theorem one_actualPacking_quadratic (m : ℕ) (hm : 3 ≤ m) :
    SuperpermutationLowerBound.ChainReturns.ActualPacking (3 * m + 2) (by omega)
      (_root_.ChainReturns.onePeriod m)
      (2 * _root_.ChainReturns.oneMean m - 1 / ((3 * (m : ℚ) + 1) ^ 2 / 4)) := by
  apply one_actualPacking_upper m hm
  have hn := SuperpermutationBounds.ChainReturns.returnOne_quadratic hm
  have hq : 4 * (SuperpermutationBounds.ChainReturns.returnOne m : ℚ) ≤
      (3 * (m : ℚ) + 1) ^ 2 := by exact_mod_cast hn
  linarith

end SuperpermutationLowerBound.Refinement.ChainReturns
