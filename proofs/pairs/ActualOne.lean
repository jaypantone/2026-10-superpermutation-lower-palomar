module

public import pairs.PaidOne
public import SuperpermutationLowerBound.Refinement.GeometryPacking

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

open ChainReturns

theorem period_onePeriod (m : ℕ) : period (3 * m + 1) = onePeriod m := by
  have hmod : (3 * m + 1) % 3 = 1 := by omega
  have hdiv : (3 * m + 1) / 3 = m := by omega
  simp [period, hmod, hdiv, onePeriod]

theorem cellG_onePeriod_pred (m : ℕ) (hm : 3 ≤ m) (hn : 7 ≤ 3 * m + 1) :
    (cellG (3 * m + 1) hn) ^ (onePeriod m - 1) = (cellG (3 * m + 1) hn)⁻¹ := by
  have hp : 1 ≤ onePeriod m := by dsimp [onePeriod]; nlinarith
  have hpow := cellG_pow_period (3 * m + 1) hn
  rw [period_onePeriod] at hpow
  calc
    _ = (cellG (3 * m + 1) hn) ^ (onePeriod m - 1) *
        (cellG (3 * m + 1) hn * (cellG (3 * m + 1) hn)⁻¹) := by group
    _ = (cellG (3 * m + 1) hn) ^ (onePeriod m) *
        (cellG (3 * m + 1) hn)⁻¹ := by
      rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hp]
    _ = _ := by rw [hpow]; simp

/-- Actual hereditary packing in residue one, parameterized only by a proved
return exponent of the explicit efficient-pair permutation. All loss,
partition, factor, endpoint, and word-geometry obligations are discharged. -/
theorem actual_chainPacking_paid_one (m R : ℕ) (hm : 3 ≤ m) (hR : 0 < R)
    (hn : 7 ≤ 3 * m + 1) {hk : 7 ≤ 3 * m + 1 + 1}
    {p : OverlapPath (3 * m + 1 + 1)} {hp : IsBlockAligned p}
    (segment : BlockAlignedLightSegment hk p hp)
    (horder : (cellRho (3 * m + 1) hn * (cellG (3 * m + 1) hn) ^ (m - 1) *
      cellRho (3 * m + 1) hn * (cellG (3 * m + 1) hn)⁻¹) ^ R = 1) :
    ChainPacking (3 * m + 1 - 2) (onePeriod m)
      (2 * oneMean m - 1 / (R : ℚ)) segment.deficitString := by
  have hold := actual_segment_returnAvoidance hn segment
  have hmod : (3 * m + 1) % 3 = 1 := by omega
  have hdiv : (3 * m + 1) / 3 = m := by omega
  apply chainPacking_paid_one (by omega) hm hR
  · simpa only [period_onePeriod] using hold.basic
  · simpa only [hdiv] using hold.residueOne hmod
  · apply actual_periodic_pair_avoidance (3 * m + 1) hn p hp segment
      (onePeriod m - 1) (m - 1) R
    · dsimp [onePeriod]
      have : 2 ≤ m * (2 * m + 1) := by nlinarith
      omega
    · omega
    · exact hR
    · simpa only [cellG_onePeriod_pred m hm hn] using horder

end SuperpermutationLowerBound.Refinement
