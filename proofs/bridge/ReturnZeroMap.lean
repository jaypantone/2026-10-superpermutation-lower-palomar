module

public import bridge.ReturnPositivity
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.GroupTheory.Perm.Support

@[expose] public section

/-! Concrete seven-step return map on the cyclic coordinate alphabet. -/
namespace SuperpermutationBounds.ChainReturns
open Equiv
open scoped Fin.NatCast

variable {n : ℕ}

def zeroSwap (n : ℕ) (hn : 2 ≤ n) : Perm (Fin n) :=
  Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩

def zeroMap (n : ℕ) (hn : 2 ≤ n) : Perm (Fin n) :=
  zeroSwap n hn * (finRotate n)⁻¹ ^ 7

theorem rotation_inv_pow [NeZero n] (k : ℕ) (x : Fin n) :
    ((finRotate n)⁻¹ ^ k) x = x - (k : Fin n) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Perm.mul_apply, ih]
      change (finRotate n).symm (x - (k : Fin n)) = x - ((k + 1 : ℕ) : Fin n)
      simp [finRotate_symm_apply, Nat.cast_add, sub_sub]

/-- Subtracting seven descends until the bottom seven coordinates. -/
theorem rotation_seven_val (hn : 9 ≤ n) (x : Fin n) :
    (((finRotate n)⁻¹ ^ 7) x).val =
      if 7 ≤ x.val then x.val - 7 else x.val + n - 7 := by
  letI : NeZero n := ⟨by omega⟩
  rw [rotation_inv_pow, Fin.val_sub]
  have hseven : ((7 : ℕ) : Fin n).val = 7 := by
    simp [Nat.mod_eq_of_lt (by omega : 7 < n)]
  rw [hseven]
  split_ifs with hx
  · rw [show n - 7 + x.val = n + (x.val - 7) by omega]
    simp [Nat.mod_eq_of_lt (by omega : x.val - 7 < n)]
  · rw [Nat.mod_eq_of_lt (by omega : n - 7 + x.val < n)]
    omega

theorem zeroSwap_val (hn : 2 ≤ n) (x : Fin n) :
    (zeroSwap n hn x).val = if x.val = 0 then 1 else if x.val = 1 then 0 else x.val := by
  unfold zeroSwap
  by_cases h0 : x.val = 0
  · have hx : x = ⟨0, by omega⟩ := Fin.ext h0
    simp [hx]
  · by_cases h1 : x.val = 1
    · have hx : x = ⟨1, by omega⟩ := Fin.ext h1
      simp [hx]
    · have hx0 : x ≠ ⟨0, by omega⟩ := by intro he; exact h0 (congrArg Fin.val he)
      have hx1 : x ≠ ⟨1, by omega⟩ := by intro he; exact h1 (congrArg Fin.val he)
      simp [Equiv.swap_apply_of_ne_of_ne hx0 hx1, h0, h1]

/-- Away from the two cut points, the return map is literal subtraction. -/
theorem zeroMap_descent (hn : 9 ≤ n) (x : Fin n) (hx : 9 ≤ x.val) :
    (zeroMap n (by omega) x).val = x.val - 7 := by
  simp only [zeroMap, Perm.mul_apply, zeroSwap_val, rotation_seven_val hn]
  simp only [if_pos (by omega : 7 ≤ x.val)]
  split_ifs <;> omega

/-- A positive number of seven-step descents ends at the swapped residue. -/
theorem zeroMap_descent_pow (hn : 9 ≤ n) (q : ℕ) (hq : 0 < q)
    (r : ℕ) (hr : r < 7) (x : Fin n) (hx : x.val = 7 * q + r) :
    (zeroMap n (by omega) ^ q) x = zeroSwap n (by omega) ⟨r, by omega⟩ := by
  induction q generalizing x with
  | zero => omega
  | succ q ih =>
      by_cases hq0 : q = 0
      · subst q
        change zeroMap n (by omega) x = zeroSwap n (by omega) ⟨r, by omega⟩
        unfold zeroMap
        rw [Perm.mul_apply]
        congr 1
        apply Fin.ext
        rw [rotation_seven_val hn, if_pos (by omega : 7 ≤ x.val)]
        change x.val - 7 = r
        omega
      · rw [pow_succ, Perm.mul_apply]
        apply ih (by omega)
        rw [zeroMap_descent hn x (by omega)]
        omega

/-- The first step from a bottom coordinate wraps to the top; n>=9 keeps
that landing point away from the transposition. -/
theorem zeroMap_anchor_val (hn : 9 ≤ n) (x : Fin n) (hx : x.val < 7) :
    (zeroMap n (by omega) x).val = x.val + n - 7 := by
  simp only [zeroMap, Perm.mul_apply, zeroSwap_val, rotation_seven_val hn]
  simp only [if_neg (by omega : ¬ 7 ≤ x.val)]
  split_ifs <;> omega

/-- The induced map on the bottom seven coordinates, with its exact return
clock. This is the common geometric input for all seven residue cases. -/
theorem zeroMap_anchor_return (hn : 9 ≤ n) (a : ℕ) (ha : a < 7) :
    (zeroMap n (by omega) ^ ((n + a) / 7)) ⟨a, by omega⟩ =
      zeroSwap n (by omega) ⟨(n + a) % 7, by have := Nat.mod_lt (n+a) (by omega : 0 < 7); omega⟩ := by
  let q := (n + a) / 7
  let r := (n + a) % 7
  have hr : r < 7 := Nat.mod_lt _ (by omega)
  have hdiv : 7 * q + r = n + a := by
    dsimp [q, r]
    omega
  have hq : 1 ≤ q := by dsimp [q]; omega
  let x : Fin n := ⟨a, by omega⟩
  have hx : (zeroMap n (by omega) x).val = a + n - 7 :=
    zeroMap_anchor_val hn x ha
  change (zeroMap n (by omega) ^ q) x = zeroSwap n (by omega) ⟨r, by omega⟩
  by_cases hq1 : q = 1
  · rw [hq1, pow_one]
    apply Fin.ext
    rw [zeroSwap_val]
    change (zeroMap n (by omega) x).val = if r = 0 then 1 else if r = 1 then 0 else r
    have hre : r = a + n - 7 := by omega
    rw [hre]
    split_ifs <;> omega
  · have hqpred : 0 < q - 1 := by omega
    have hhop := zeroMap_descent_pow hn (q - 1) hqpred r hr
      (zeroMap n (by omega) x) (by omega)
    rw [show q = q - 1 + 1 by omega, pow_succ, Perm.mul_apply]
    exact hhop

end SuperpermutationBounds.ChainReturns
