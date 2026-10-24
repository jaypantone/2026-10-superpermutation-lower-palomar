module

public import SuperpermutationLowerBound.Refinement.ReturnMaps

@[expose] public section

/-! Canonical short-run and full-run entries as position-to-letter permutations. -/
namespace SuperpermutationLowerBound.Refinement

def cellYValue (n i : ℕ) : ℕ :=
  if i < n - 2 then i + 3 else if i = n - 2 then 2 else if i = n - 1 then 1 else 0

def cellYInverseValue (n i : ℕ) : ℕ :=
  if i = 0 then n else if i = 1 then n - 1 else if i = 2 then n - 2 else i - 3

theorem cellYValue_lt {n i : ℕ} (hn : 7 ≤ n) (hi : i < n + 1) :
    cellYValue n i < n + 1 := by
  unfold cellYValue
  split_ifs <;> omega

theorem cellYInverseValue_lt {n i : ℕ} (hn : 7 ≤ n) (hi : i < n + 1) :
    cellYInverseValue n i < n + 1 := by
  unfold cellYInverseValue
  split_ifs <;> omega

theorem cellYInverseValue_cellYValue {n i : ℕ} (hn : 7 ≤ n)
    (hi : i < n + 1) : cellYInverseValue n (cellYValue n i) = i := by
  unfold cellYValue
  split_ifs <;> simp only [cellYInverseValue] <;> split_ifs <;>
    (first | contradiction | omega)

theorem cellYValue_cellYInverseValue {n i : ℕ} (hn : 7 ≤ n)
    (hi : i < n + 1) : cellYValue n (cellYInverseValue n i) = i := by
  unfold cellYInverseValue
  split_ifs <;> simp only [cellYValue] <;> split_ifs <;>
    (first | contradiction | omega)

/-- Canonical deficit-two entry `(3, …, n, 2, 1, 0)`. -/
def cellY (n : ℕ) (hn : 7 ≤ n) : Equiv.Perm (Fin (n + 1)) where
  toFun i := ⟨cellYValue n i.val, cellYValue_lt hn i.isLt⟩
  invFun i := ⟨cellYInverseValue n i.val, cellYInverseValue_lt hn i.isLt⟩
  left_inv i := Fin.ext (cellYInverseValue_cellYValue hn i.isLt)
  right_inv i := Fin.ext (cellYValue_cellYInverseValue hn i.isLt)

@[simp] theorem cellY_apply_val (n : ℕ) (hn : 7 ≤ n) (i : Fin (n+1)) :
    (cellY n hn i).val = cellYValue n i.val := rfl

@[simp] theorem cellY_symm_apply_val (n : ℕ) (hn : 7 ≤ n) (i : Fin (n+1)) :
    ((cellY n hn).symm i).val = cellYInverseValue n i.val := rfl

def cellUValue (n i : ℕ) : ℕ :=
  if i = 0 then 1 else if i < n - 2 then i + 2 else if i = n - 2 then 2 else if i = n - 1 then n else 0

def cellUInverseValue (n i : ℕ) : ℕ :=
  if i = 0 then n else if i = 1 then 0 else if i = 2 then n - 2 else if i = n then n - 1 else i - 2

theorem cellUValue_lt {n i : ℕ} (hn : 7 ≤ n) (hi : i < n + 1) :
    cellUValue n i < n + 1 := by
  unfold cellUValue
  split_ifs <;> omega

theorem cellUInverseValue_lt {n i : ℕ} (hn : 7 ≤ n) (hi : i < n + 1) :
    cellUInverseValue n i < n + 1 := by
  unfold cellUInverseValue
  split_ifs <;> omega

theorem cellUInverseValue_cellUValue {n i : ℕ} (hn : 7 ≤ n)
    (hi : i < n + 1) : cellUInverseValue n (cellUValue n i) = i := by
  unfold cellUValue
  split_ifs <;> simp only [cellUInverseValue] <;> split_ifs <;>
    (first | contradiction | omega)

theorem cellUValue_cellUInverseValue {n i : ℕ} (hn : 7 ≤ n)
    (hi : i < n + 1) : cellUValue n (cellUInverseValue n i) = i := by
  unfold cellUInverseValue
  split_ifs <;> simp only [cellUValue] <;> split_ifs <;>
    (first | contradiction | omega)

/-- Canonical first full-run entry `(1, 3, …, n-1, 2, n, 0)`. -/
def cellU (n : ℕ) (hn : 7 ≤ n) : Equiv.Perm (Fin (n + 1)) where
  toFun i := ⟨cellUValue n i.val, cellUValue_lt hn i.isLt⟩
  invFun i := ⟨cellUInverseValue n i.val, cellUInverseValue_lt hn i.isLt⟩
  left_inv i := Fin.ext (cellUInverseValue_cellUValue hn i.isLt)
  right_inv i := Fin.ext (cellUValue_cellUInverseValue hn i.isLt)

@[simp] theorem cellU_apply_val (n : ℕ) (hn : 7 ≤ n) (i : Fin (n+1)) :
    (cellU n hn i).val = cellUValue n i.val := rfl

@[simp] theorem cellU_symm_apply_val (n : ℕ) (hn : 7 ≤ n) (i : Fin (n+1)) :
    ((cellU n hn).symm i).val = cellUInverseValue n i.val := rfl

end SuperpermutationLowerBound.Refinement
