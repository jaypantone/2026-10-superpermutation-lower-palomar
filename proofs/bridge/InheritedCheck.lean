module

public import bridge.NumericalEvaluations
public import SuperpermutationLowerBound.Refinement.GeometryPacking

@[expose] public section

/-! A complete integration test using inherited geometry. This recovers the
frozen general eight-letter bound, which was already established; it is not a
new bound. Stronger parameters require the new geometric packing proofs. -/
namespace SuperpermutationLowerBound.ChainReturns
open Refinement

theorem inherited_actualPacking_eight : ActualPacking 8 (by omega) 10 (46 / 3) := by
  intro P hP s
  have hold := actual_lightSegment_chainPacking (by omega : 8 ≤ 8) s
  have hten : ChainPacking (8 - 1 - 2) 10 10 s.deficitString := by
    simpa [period, chainAllowance] using hold
  exact hten.mono (by norm_num)

theorem inherited_word_eight (w : List (Fin 8)) (hw : SuperpermutationBounds.Covers w) :
    46130 ≤ w.length := by
  have h := word_bound_of_actualPacking (by omega : 8 ≤ 8) admissible_eight
    inherited_actualPacking_eight w hw
  simpa only [bound_8] using h

#print axioms inherited_word_eight
#print axioms word_bound_of_actualPacking

end SuperpermutationLowerBound.ChainReturns
