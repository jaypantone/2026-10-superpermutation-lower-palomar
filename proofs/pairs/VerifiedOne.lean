module

public import pairs.ActualOne
public import alternation.OneActualReturn
public import bridge.ReturnPositivity

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

/-- The frozen improved residue-one chain-packing theorem, with the explicit
return order proved and no geometric or order premise remaining. -/
theorem actual_chainPacking_residueOne (m : ℕ) (hm : 3 ≤ m)
    (hn : 7 ≤ 3 * m + 1) {hk : 7 ≤ 3 * m + 1 + 1}
    {p : OverlapPath (3 * m + 1 + 1)} {hp : IsBlockAligned p}
    (segment : BlockAlignedLightSegment hk p hp) :
    ChainPacking (3 * m + 1 - 2) (_root_.ChainReturns.onePeriod m)
      (2 * _root_.ChainReturns.oneMean m -
        1 / (SuperpermutationBounds.ChainReturns.returnOne m : ℚ)) segment.deficitString := by
  exact actual_chainPacking_paid_one m (SuperpermutationBounds.ChainReturns.returnOne m)
    hm (SuperpermutationBounds.ChainReturns.returnOne_pos hm) hn segment
    (ChainReturns.efficientOne_return m hm hn)

end SuperpermutationLowerBound.Refinement
