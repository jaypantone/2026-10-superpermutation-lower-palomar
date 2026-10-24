module

public import alternation.OneAnchorCycles

@[expose] public section

namespace SuperpermutationLowerBound.Refinement.ChainReturns

open SuperpermutationLowerBound.Refinement
open SuperpermutationBounds.ChainReturns

def efficientOnePermutation (m : ℕ) (hn : 7 ≤ 3 * m + 1) :
    Equiv.Perm (Fin (3 * m + 1 + 1)) :=
  cellRho (3 * m + 1) hn * (cellG (3 * m + 1) hn) ^ (m - 1) *
    cellRho (3 * m + 1) hn * (cellG (3 * m + 1) hn)⁻¹

theorem efficientOne_power_val (m : ℕ) (hm : 3 ≤ m) (hn : 7 ≤ 3 * m + 1)
    (r : ℕ) (i : Fin (3 * m + 1 + 1)) :
    ((efficientOnePermutation m hn ^ r) i).val = ((efficientOneValue m)^[r]) i.val := by
  induction r generalizing i with
  | zero => rfl
  | succ r ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, ih, Function.iterate_succ_apply]
      exact congrArg ((efficientOneValue m)^[r]) (efficientOne_apply_val m hm hn i)

theorem efficientOne_small_return (m : ℕ) (hm : 3 ≤ m) (a : ℕ) (ha : a ≤ 5) :
    ((efficientOneValue m)^[returnOne m]) a = a := by
  by_cases hz : a = 0
  · subst a
    apply Function.iterate_fixed
    simp [efficientOneValue]
  · exact efficientOne_anchors_return m hm a (by omega) ha

/-- Every point descends to an anchor. Injectivity of the actual permutation
then transports the common return exponent back to its starting point. -/
theorem efficientOne_return (m : ℕ) (hm : 3 ≤ m) (hn : 7 ≤ 3 * m + 1) :
    (cellRho (3 * m + 1) hn * (cellG (3 * m + 1) hn) ^ (m - 1) *
      cellRho (3 * m + 1) hn * (cellG (3 * m + 1) hn)⁻¹) ^ returnOne m = 1 := by
  change efficientOnePermutation m hn ^ returnOne m = 1
  apply Equiv.ext
  intro i
  let f := efficientOnePermutation m hn
  obtain ⟨r, hr⟩ := efficientOneValue_reaches_anchor m i.val
  have hj : ((f ^ r) i).val ≤ 5 := by
    dsimp [f]
    rw [efficientOne_power_val m hm hn]
    exact hr
  have hfix : (f ^ returnOne m) ((f ^ r) i) = (f ^ r) i := by
    apply Fin.ext
    dsimp [f]
    rw [efficientOne_power_val m hm hn]
    exact efficientOne_small_return m hm _ hj
  apply (f ^ r).injective
  change (f ^ r) ((f ^ returnOne m) i) = (f ^ r) i
  calc
    _ = (f ^ returnOne m) ((f ^ r) i) := by
      rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← pow_add, ← pow_add,
        Nat.add_comm r (returnOne m)]
    _ = _ := hfix

theorem efficientOne_completed_pair_return (m : ℕ) (hm : 3 ≤ m) (hn : 7 ≤ 3 * m + 1) :
    (cellRho (3 * m + 1) hn * (cellG (3 * m + 1) hn) ^ (m - 1) *
      cellRho (3 * m + 1) hn * (cellG (3 * m + 1) hn) ^ (m * (2 * m + 1) - 1)) ^
        returnOne m = 1 := by
  have hp : (cellG (3 * m + 1) hn) ^ (m * (2 * m + 1)) = 1 :=
    cellG_return_residue1 m hn
  have hg : (cellG (3 * m + 1) hn) ^ (m * (2 * m + 1) - 1) =
      (cellG (3 * m + 1) hn)⁻¹ := by
    have hpPos : 1 ≤ m * (2 * m + 1) := by nlinarith
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← pow_succ, Nat.sub_add_cancel hpPos]
    exact hp
  rw [hg]
  exact efficientOne_return m hm hn

end SuperpermutationLowerBound.Refinement.ChainReturns
