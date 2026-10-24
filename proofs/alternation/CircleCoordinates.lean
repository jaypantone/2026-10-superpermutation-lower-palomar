module

public import SuperpermutationLowerBound.Refinement.ReturnMaps
public import Mathlib.Logic.Equiv.Fin.Rotate
public import alternation.AlternatingReturnAlgebra

@[expose] public section

namespace SuperpermutationLowerBound.Refinement.ChainReturns

open SuperpermutationLowerBound.Refinement

def circleValue (n i : ℕ) : ℕ :=
  if i = 0 then 0 else if i = 1 then 3 else if i = 2 then 1
  else if i < n then i + 1 else 2

def circleInverseValue (n i : ℕ) : ℕ :=
  if i = 0 then 0 else if i = 1 then 2 else if i = 2 then n
  else if i = 3 then 1 else i - 1

theorem circleValue_lt {n i : ℕ} (hn : 7 ≤ n) (hi : i < n + 1) :
    circleValue n i < n + 1 := by
  unfold circleValue
  split_ifs <;> omega

theorem circleInverseValue_lt {n i : ℕ} (hn : 7 ≤ n) (hi : i < n + 1) :
    circleInverseValue n i < n + 1 := by
  unfold circleInverseValue
  split_ifs <;> omega

def circleS (n : ℕ) (hn : 7 ≤ n) : Equiv.Perm (Fin (n + 1)) where
  toFun i := ⟨circleValue n i.val, circleValue_lt hn i.isLt⟩
  invFun i := ⟨circleInverseValue n i.val, circleInverseValue_lt hn i.isLt⟩
  left_inv i := by
    apply Fin.ext
    change circleInverseValue n (circleValue n i.val) = i.val
    have := i.isLt
    unfold circleValue
    split_ifs <;> simp_all [circleInverseValue] <;> first | omega | (split_ifs <;> omega)
  right_inv i := by
    apply Fin.ext
    change circleValue n (circleInverseValue n i.val) = i.val
    have := i.isLt
    unfold circleInverseValue
    split_ifs <;> simp_all [circleValue] <;> first | omega | (split_ifs <;> omega)

@[simp] theorem circleS_apply_val (n : ℕ) (hn : 7 ≤ n) (i : Fin (n + 1)) :
    (circleS n hn i).val = circleValue n i.val := rfl

def circleTau (n : ℕ) (hn : 7 ≤ n) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap ⟨1, by omega⟩ ⟨3, by omega⟩

def circleTauValue (i : ℕ) : ℕ := if i = 1 then 3 else if i = 3 then 1 else i

@[simp] theorem circleTau_apply_val (n : ℕ) (hn : 7 ≤ n) (i : Fin (n + 1)) :
    (circleTau n hn i).val = circleTauValue i.val := by
  simp only [circleTau, Equiv.swap_apply_def, Fin.ext_iff]
  split_ifs <;> simp_all [circleTauValue]

theorem circleTau_involution (n : ℕ) (hn : 7 ≤ n) :
    circleTau n hn * circleTau n hn = 1 := by
  ext i
  simp [circleTau, Equiv.Perm.mul_apply]

theorem circleRho (n : ℕ) (hn : 7 ≤ n) :
    cellRho n hn = circleTau n hn * circleS n hn := by
  ext i
  simp only [Equiv.Perm.mul_apply, cellRho_apply_val, circleTau_apply_val,
    circleS_apply_val]
  have := i.isLt
  unfold circleValue
  split_ifs <;> simp only [circleTauValue, cellRhoValue] <;> split_ifs <;> first | contradiction | omega

set_option maxHeartbeats 2000000 in
theorem circleGValue_eq (n x : ℕ) (hn : 7 ≤ n) (hx : x < n + 1) :
    cellGValue n x = circleTauValue (circleValue n (circleValue n (circleValue n x))) := by
  conv_rhs => arg 1; arg 2; arg 2; unfold circleValue
  all_goals split_ifs <;> try omega
  all_goals conv_rhs => arg 1; arg 2; unfold circleValue
  all_goals split_ifs <;> try omega
  all_goals simp only [circleValue]
  all_goals split_ifs <;> try omega
  all_goals simp only [circleTauValue, cellGValue]
  all_goals split_ifs <;> (first | contradiction | omega)

set_option maxHeartbeats 2000000 in
theorem circleG (n : ℕ) (hn : 7 ≤ n) :
    cellG n hn = circleTau n hn * (circleS n hn) ^ 3 := by
  ext i
  simp only [pow_succ, pow_zero, mul_one, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    cellG_apply_val, circleTau_apply_val, circleS_apply_val]
  exact circleGValue_eq n i.val hn i.isLt

def circleLetterValue (n j : ℕ) : ℕ :=
  if j = 0 then 1 else if j + 1 = n then 2 else j + 2

def circleLetter (n : ℕ) (hn : 7 ≤ n) (j : Fin n) : Fin (n + 1) :=
  ⟨circleLetterValue n j.val, by
    have := j.isLt
    unfold circleLetterValue
    split_ifs <;> omega⟩

@[simp] theorem circleLetter_val (n : ℕ) (hn : 7 ≤ n) (j : Fin n) :
    (circleLetter n hn j).val = circleLetterValue n j.val := rfl

theorem circleLetter_ne_zero (n : ℕ) (hn : 7 ≤ n) (j : Fin n) :
    (circleLetter n hn j).val ≠ 0 := by
  simp only [circleLetter_val, circleLetterValue]
  split_ifs <;> omega

theorem circleLetter_covers_nonzero (n : ℕ) (hn : 7 ≤ n) (i : Fin (n + 1))
    (hi : i.val ≠ 0) : ∃ j : Fin n, circleLetter n hn j = i := by
  have hib := i.isLt
  by_cases h1 : i.val = 1
  · refine ⟨⟨0, by omega⟩, ?_⟩
    apply Fin.ext
    simp [circleLetter_val, circleLetterValue, h1]
  by_cases h2 : i.val = 2
  · refine ⟨⟨n - 1, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [circleLetter_val, circleLetterValue]
    split_ifs <;> omega
  · refine ⟨⟨i.val - 2, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [circleLetter_val, circleLetterValue]
    split_ifs <;> omega

theorem circleLetter_rotate_value {n j : ℕ} (hn : 7 ≤ n) (hj : j < n) :
    circleValue n (circleLetterValue n j) = circleLetterValue n ((j + 1) % n) := by
  by_cases hend : j + 1 = n
  · rw [hend, Nat.mod_self]
    unfold circleLetterValue
    split_ifs <;> simp only [circleValue] <;> split_ifs <;> omega
  · rw [Nat.mod_eq_of_lt (by omega : j + 1 < n)]
    unfold circleLetterValue
    split_ifs <;> simp only [circleValue] <;> split_ifs <;> omega

theorem circleLetter_rotate (n : ℕ) (hn : 7 ≤ n) (j : Fin n) :
    circleS n hn (circleLetter n hn j) = circleLetter n hn (finRotate n j) := by
  haveI : NeZero n := ⟨by omega⟩
  apply Fin.ext
  simp only [circleS_apply_val, circleLetter_val, finRotate_apply, Fin.val_add,
    Fin.val_one, Nat.mod_eq_of_lt (by omega : 1 < n)]
  have h1 : ((1 : Fin n) : ℕ) = 1 := by
    change 1 % n = 1
    exact Nat.mod_eq_of_lt (by omega)
  rw [h1]
  exact circleLetter_rotate_value hn j.isLt

theorem circleLetter_swap (n : ℕ) (hn : 7 ≤ n) (j : Fin n) :
    circleTau n hn (circleLetter n hn j) =
      circleLetter n hn (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ j) := by
  apply Fin.ext
  simp only [circleTau_apply_val, circleLetter_val, Equiv.swap_apply_def, Fin.ext_iff]
  split_ifs <;> simp_all [circleLetter, circleLetterValue, circleTauValue]
  all_goals have := j.isLt
  all_goals first | omega | (split_ifs <;> omega)

end SuperpermutationLowerBound.Refinement.ChainReturns
