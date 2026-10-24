module

public import SuperpermutationLowerBound.Refinement.Definitions
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Literal return permutations on the zero-based labels `0, …, n`.
Products of permutations apply the rightmost factor first. -/

namespace SuperpermutationLowerBound.Refinement

def cellGValue (n i : ℕ) : ℕ :=
  if i = 0 then 0 else if i = 1 then 5 else if i = 2 then 4
  else if i + 3 ≤ n then i + 3
  else if i + 2 = n then 2 else if i + 1 = n then 3 else 1

def cellGInverseValue (n i : ℕ) : ℕ :=
  if i = 0 then 0 else if i = 1 then n else if i = 2 then n - 2
  else if i = 3 then n - 1 else if i = 4 then 2 else if i = 5 then 1
  else i - 3

theorem cellGValue_lt {n i : ℕ} (hn : 7 ≤ n) (hi : i < n + 1) :
    cellGValue n i < n + 1 := by
  unfold cellGValue
  split_ifs <;> omega

theorem cellGInverseValue_lt {n i : ℕ} (hn : 7 ≤ n) (hi : i < n + 1) :
    cellGInverseValue n i < n + 1 := by
  unfold cellGInverseValue
  split_ifs <;> omega

theorem cellGInverseValue_cellGValue {n i : ℕ} (hn : 7 ≤ n) (hi : i < n + 1) :
    cellGInverseValue n (cellGValue n i) = i := by
  unfold cellGValue
  split_ifs <;> simp only [cellGInverseValue] <;> split_ifs <;> (first | contradiction | omega)

theorem cellGValue_cellGInverseValue {n i : ℕ} (hn : 7 ≤ n) (hi : i < n + 1) :
    cellGValue n (cellGInverseValue n i) = i := by
  unfold cellGInverseValue
  split_ifs <;> simp only [cellGValue] <;> split_ifs <;> (first | contradiction | omega)

/-- Normalization after one complete regular cell. -/
def cellG (n : ℕ) (hn : 7 ≤ n) : Equiv.Perm (Fin (n + 1)) where
  toFun i := ⟨cellGValue n i.val, cellGValue_lt hn i.isLt⟩
  invFun i := ⟨cellGInverseValue n i.val, cellGInverseValue_lt hn i.isLt⟩
  left_inv i := Fin.ext (cellGInverseValue_cellGValue hn i.isLt)
  right_inv i := Fin.ext (cellGValue_cellGInverseValue hn i.isLt)

@[simp] theorem cellG_apply_val (n : ℕ) (hn : 7 ≤ n) (i : Fin (n+1)) :
    (cellG n hn i).val = cellGValue n i.val := rfl

@[simp] theorem cellG_symm_apply_val (n : ℕ) (hn : 7 ≤ n) (i : Fin (n+1)) :
    ((cellG n hn).symm i).val = cellGInverseValue n i.val := rfl

def cellRhoValue (n i : ℕ) : ℕ :=
  if i ≤ 1 then i else if i < n then i + 1 else 2

def cellRhoInverseValue (n i : ℕ) : ℕ :=
  if i ≤ 1 then i else if i = 2 then n else i - 1

theorem cellRhoValue_lt {n i : ℕ} (hn : 7 ≤ n) (hi : i < n + 1) :
    cellRhoValue n i < n + 1 := by
  unfold cellRhoValue
  split_ifs <;> omega

theorem cellRhoInverseValue_lt {n i : ℕ} (hn : 7 ≤ n) (hi : i < n + 1) :
    cellRhoInverseValue n i < n + 1 := by
  unfold cellRhoInverseValue
  split_ifs <;> omega

theorem cellRhoInverseValue_cellRhoValue {n i : ℕ} (hn : 7 ≤ n)
    (hi : i < n + 1) : cellRhoInverseValue n (cellRhoValue n i) = i := by
  unfold cellRhoInverseValue cellRhoValue
  split_ifs <;> omega

theorem cellRhoValue_cellRhoInverseValue {n i : ℕ} (hn : 7 ≤ n)
    (hi : i < n + 1) : cellRhoValue n (cellRhoInverseValue n i) = i := by
  unfold cellRhoValue cellRhoInverseValue
  split_ifs <;> omega

/-- The extra cyclic relabeling after a shortened cell. -/
def cellRho (n : ℕ) (hn : 7 ≤ n) : Equiv.Perm (Fin (n + 1)) where
  toFun i := ⟨cellRhoValue n i.val, cellRhoValue_lt hn i.isLt⟩
  invFun i := ⟨cellRhoInverseValue n i.val, cellRhoInverseValue_lt hn i.isLt⟩
  left_inv i := Fin.ext (cellRhoInverseValue_cellRhoValue hn i.isLt)
  right_inv i := Fin.ext (cellRhoValue_cellRhoInverseValue hn i.isLt)

@[simp] theorem cellRho_apply_val (n : ℕ) (hn : 7 ≤ n) (i : Fin (n+1)) :
    (cellRho n hn i).val = cellRhoValue n i.val := rfl

@[simp] theorem cellRho_symm_apply_val (n : ℕ) (hn : 7 ≤ n) (i : Fin (n+1)) :
    ((cellRho n hn).symm i).val = cellRhoInverseValue n i.val := rfl

end SuperpermutationLowerBound.Refinement
