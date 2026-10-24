module

public import alternation.CircleCoordinates
public import pairs.PeriodicReturns
public import SuperpermutationLowerBound.Refinement.ReturnPeriod
public import bridge.ReturnZeroOrder

@[expose] public section

namespace SuperpermutationLowerBound.Refinement.ChainReturns

open SuperpermutationLowerBound.Refinement

theorem permutation_intertwines_inverse {α β : Type*} (f : Equiv.Perm α)
    (g : Equiv.Perm β) (e : β → α) (h : ∀ i, f (e i) = e (g i)) (i : β) :
    f⁻¹ (e i) = e (g⁻¹ i) := by
  apply f.injective
  simpa using (h (g⁻¹ i)).symm

theorem permutation_intertwines_power {α β : Type*} (f : Equiv.Perm α)
    (g : Equiv.Perm β) (e : β → α) (h : ∀ i, f (e i) = e (g i)) (r : ℕ) (i : β) :
    (f ^ r) (e i) = e ((g ^ r) i) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih, h]

theorem permutation_power_fixes {α : Type*} (f : Equiv.Perm α)
    (i : α) (h : f i = i) (r : ℕ) : (f ^ r) i = i := by
  induction r with
  | zero => rfl
  | succ r ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, h]

theorem circleLetter_zeroMap (n : ℕ) (hn : 7 ≤ n) (j : Fin n) :
    (circleTau n hn * (circleS n hn)⁻¹ ^ 7) (circleLetter n hn j) =
      circleLetter n hn (SuperpermutationBounds.ChainReturns.zeroMap n (by omega) j) := by
  have hi := permutation_intertwines_inverse (circleS n hn) (finRotate n)
    (circleLetter n hn) (circleLetter_rotate n hn)
  have hp := permutation_intertwines_power (circleS n hn)⁻¹ (finRotate n)⁻¹
    (circleLetter n hn) hi 7 j
  rw [Equiv.Perm.mul_apply, hp, circleLetter_swap]
  rfl

theorem circle_zeroMap_return_of_canonical (n : ℕ) (hn : 7 ≤ n) (R : ℕ)
    (hreturn : (SuperpermutationBounds.ChainReturns.zeroMap n (by omega)) ^ R = 1) :
    (circleTau n hn * (circleS n hn)⁻¹ ^ 7) ^ R = 1 := by
  have hs : circleS n hn (0 : Fin (n + 1)) = 0 := by
    apply Fin.ext
    simp [circleValue]
  have hsi : (circleS n hn)⁻¹ (0 : Fin (n + 1)) = 0 := by
    apply (circleS n hn).injective
    simpa using hs.symm
  have ht : circleTau n hn (0 : Fin (n + 1)) = 0 := by
    apply Fin.ext
    simp [circleTauValue]
  have hz : (circleTau n hn * (circleS n hn)⁻¹ ^ 7) (0 : Fin (n + 1)) = 0 := by
    rw [Equiv.Perm.mul_apply, permutation_power_fixes _ _ hsi, ht]
  apply Equiv.ext
  intro i
  by_cases hi : i.val = 0
  · have he : i = 0 := Fin.ext hi
    subst i
    exact permutation_power_fixes _ _ hz R
  · obtain ⟨j, rfl⟩ := circleLetter_covers_nonzero n hn i hi
    rw [permutation_intertwines_power _ _ _ (circleLetter_zeroMap n hn), hreturn]
    rfl

theorem alternating_pair_power_of_canonical_return (m : ℕ) (hm : 3 ≤ m)
    (hn : 7 ≤ 3 * m) (R : ℕ)
    (hreturn : (SuperpermutationBounds.ChainReturns.zeroMap (3 * m) (by omega)) ^ R = 1) :
    (cellRho (3 * m) hn * (cellG (3 * m) hn) ^ (2 * m - 2) *
      cellRho (3 * m) hn * (cellG (3 * m) hn) ^ (2 * m - 1)) ^ R = 1 := by
  have hp : (cellG (3 * m) hn) ^ (2 * m) = 1 := by
    simpa using cellG_return_residue0 m hn
  have hp1 : (cellG (3 * m) hn) ^ (2 * m - 1) = (cellG (3 * m) hn)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← pow_succ, show 2 * m - 1 + 1 = 2 * m by omega]
    exact hp
  have hp2 : (cellG (3 * m) hn) ^ (2 * m - 2) = ((cellG (3 * m) hn)⁻¹) ^ 2 := by
    rw [inv_pow]
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← pow_add, show 2 * m - 2 + 2 = 2 * m by omega]
    exact hp
  rw [hp1, hp2, circleRho, circleG]
  exact alternating_pair_return_of_rotation_return _ _
    (circleTau_involution (3 * m) hn) R
    (circle_zeroMap_return_of_canonical (3 * m) hn R hreturn)

theorem alternating_pair_power (m : ℕ) (hm : 3 ≤ m) (hn : 7 ≤ 3 * m) :
    (cellRho (3 * m) hn * (cellG (3 * m) hn) ^ (2 * m - 2) *
      cellRho (3 * m) hn * (cellG (3 * m) hn) ^ (2 * m - 1)) ^
        SuperpermutationBounds.ChainReturns.returnZero (3 * m) = 1 :=
  alternating_pair_power_of_canonical_return m hm hn _
    (SuperpermutationBounds.ChainReturns.zeroMap_return (by omega))

end SuperpermutationLowerBound.Refinement.ChainReturns
