module

public import SuperpermutationLowerBound.Refinement.ReturnGeometry

@[expose] public section

/-! Symbolic three-shortened-cell return, on the zero-based labels `0,…,n`.
Every calculation below is uniform in `n`; no computed permutation table is
used as a premise. -/

namespace SuperpermutationLowerBound.Refinement

def cellRhoGInverseValue (n i : ℕ) : ℕ :=
  if i = 0 then 0 else if i = 1 then 2 else if i = 2 then n - 1
  else if i = 3 then n else if i = 4 then 3 else if i = 5 then 1 else i - 2

theorem cellRhoGInverseValue_eq {n i : ℕ} (hn : 7 ≤ n) (hi : i ≤ n) :
    cellRhoValue n (cellGInverseValue n i) = cellRhoGInverseValue n i := by
  unfold cellGInverseValue cellRhoGInverseValue
  split_ifs <;> simp only [cellRhoValue] <;> split_ifs <;> omega

def cellUniversalValue (n i : ℕ) : ℕ :=
  if i = 0 then 0 else if i = 1 then 8 else if i = 2 then 7
  else if i + 6 ≤ n then i + 6
  else if i + 5 = n then 2 else if i + 4 = n then 1
  else if i + 3 = n then 3 else if i + 2 = n then 4
  else if i + 1 = n then 5 else 6

def cellUniversal (n : ℕ) (hn : 8 ≤ n) : Equiv.Perm (Fin (n + 1)) :=
  cellG n (by omega) * (cellRho n (by omega) * (cellG n (by omega))⁻¹)^3 *
    (cellG n (by omega))^3

theorem cellUniversalValue_of_steps {n i x1 x2 x3 x4 x5 x6 x7 : ℕ}
    (hn : 8 ≤ n) (_hi : i ≤ n)
    (h1 : cellGValue n i = x1) (h2 : cellGValue n x1 = x2)
    (h3 : cellGValue n x2 = x3) (h4 : cellRhoGInverseValue n x3 = x4)
    (h5 : cellRhoGInverseValue n x4 = x5) (h6 : cellRhoGInverseValue n x5 = x6)
    (h7 : cellGValue n x6 = x7) : x7 = cellUniversalValue n i := by
  grind (splits := 64) [cellGValue, cellRhoGInverseValue, cellUniversalValue]

theorem universal_product_apply {α : Type*} (g r : Equiv.Perm α) (i : α) :
    (g * (r * g⁻¹)^3 * g^3) i =
      g ((r * g⁻¹) ((r * g⁻¹) ((r * g⁻¹) (g (g (g i)))))) := by
  simp only [pow_succ, pow_zero, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]

@[simp] theorem cellUniversal_apply_val (n : ℕ) (hn : 8 ≤ n) (i : Fin (n + 1)) :
    (cellUniversal n hn i).val = cellUniversalValue n i.val := by
  let g := cellG n (by omega)
  let h := cellRho n (by omega) * g⁻¹
  let j1 := g i
  let j2 := g j1
  let j3 := g j2
  let j4 := h j3
  let j5 := h j4
  let j6 := h j5
  let j7 := g j6
  have hstep (j : Fin (n + 1)) : (h j).val = cellRhoGInverseValue n j.val := by
    exact cellRhoGInverseValue_eq (by omega) (by omega)
  have heq : cellUniversal n hn i = j7 :=
    universal_product_apply g (cellRho n (by omega)) i
  rw [heq]
  apply cellUniversalValue_of_steps hn (by omega)
    (x1 := j1.val) (x2 := j2.val) (x3 := j3.val)
    (x4 := j4.val) (x5 := j5.val) (x6 := j6.val)
  · exact (cellG_apply_val n (by omega) i).symm
  · exact (cellG_apply_val n (by omega) j1).symm
  · exact (cellG_apply_val n (by omega) j2).symm
  · exact (hstep j3).symm
  · exact (hstep j4).symm
  · exact (hstep j5).symm
  · exact (cellG_apply_val n (by omega) j6).symm

theorem cellUniversalValue_zero (n : ℕ) : cellUniversalValue n 0 = 0 := by
  simp [cellUniversalValue]

theorem cellUniversalValue_one {n : ℕ} (_hn : 8 ≤ n) : cellUniversalValue n 1 = 8 := by
  simp [cellUniversalValue]

theorem cellUniversalValue_two {n : ℕ} (_hn : 8 ≤ n) : cellUniversalValue n 2 = 7 := by
  simp [cellUniversalValue]

theorem cellUniversalValue_middle {n i : ℕ} (hn : 8 ≤ n)
    (hi : 3 ≤ i) (hi' : i ≤ n - 6) : cellUniversalValue n i = i + 6 := by
  unfold cellUniversalValue
  split_ifs <;> omega

theorem cellUniversalValue_last_six {n : ℕ} (hn : 8 ≤ n) :
    cellUniversalValue n (n - 5) = 2 ∧ cellUniversalValue n (n - 4) = 1 ∧
      cellUniversalValue n (n - 3) = 3 ∧ cellUniversalValue n (n - 2) = 4 ∧
      cellUniversalValue n (n - 1) = 5 ∧ cellUniversalValue n n = 6 := by
  grind (splits := 64) [cellUniversalValue]

private theorem mod_six_before_end {n i : ℕ} (hn : 8 ≤ n) (hi : i < n) :
    (n - 6 + i) % n = if i < 6 then n - 6 + i else i - 6 := by
  by_cases hir : i < 6
  · rw [if_pos hir, Nat.mod_eq_of_lt (by omega)]
  · have heq : n - 6 + i = n + (i - 6) := by omega
    rw [if_neg hir, heq]
    simp [Nat.mod_eq_of_lt (show i - 6 < n by omega)]

/-- The occupied row returns as a literal word, stronger than class equality. -/
theorem cellUniversal_row_value {n i : ℕ} (hn : 8 ≤ n) (hi : i < n) :
    cellUniversalValue n (cellYValue n ((n - 6 + i) % n)) = cellYValue n i := by
  rw [mod_six_before_end hn hi]
  grind [cellYValue, cellUniversalValue]

theorem cellUniversal_shortEntry_return (n : ℕ) (hn : 8 ≤ n)
    (e : Fin (n + 1) ≃ Alphabet (n + 1)) :
    runMapPower (by omega) (n - 6)
      (shortEntry n (by omega) ((cellUniversal n hn).trans e)) =
        shortEntry n (by omega) e := by
  apply PermutationVertex.ext
  apply List.ext_getElem
  · simp [PermutationVertex.length]
  · intro i hi hj
    have hilim : i < n + 1 := by simpa [PermutationVertex.length] using hi
    by_cases hicore : i < n
    · have hget := runMapPower_get_core (by omega : 2 ≤ n + 1)
        (shortEntry n (by omega) ((cellUniversal n hn).trans e)) (n - 6) i (by omega)
      simp only [Nat.add_sub_cancel] at hget
      rw [hget]
      simp only [shortEntry_word, List.getElem_ofFn, Equiv.trans_apply]
      apply congrArg e
      apply Fin.ext
      simp only [cellUniversal_apply_val, cellY_apply_val]
      exact cellUniversal_row_value hn hicore
    · have hieq : i = n := by omega
      subst i
      have hget := runMapPower_get_last (by omega : 2 ≤ n + 1)
        (shortEntry n (by omega) ((cellUniversal n hn).trans e)) (n - 6)
      simp only [Nat.add_sub_cancel] at hget
      rw [hget]
      simp only [shortEntry_word, List.getElem_ofFn, Equiv.trans_apply]
      apply congrArg e
      apply Fin.ext
      simp only [cellUniversal_apply_val, cellY_apply_val]
      have hy : cellYValue n n = 0 := by unfold cellYValue; split_ifs <;> omega
      rw [hy, cellUniversalValue_zero]

theorem cellUniversal_relabel_occupied_row (n : ℕ) (hn : 8 ≤ n)
    (e : Fin (n + 1) ≃ Alphabet (n + 1)) :
    relabelVertex (e.symm.trans ((cellUniversal n hn).trans e))
      (runMapPower (by omega) (n - 6) (shortEntry n (by omega) e)) =
        shortEntry n (by omega) e := by
  rw [relabelVertex_runMapPower (by omega : 2 ≤ n + 1)]
  have hentry : relabelVertex (e.symm.trans ((cellUniversal n hn).trans e))
      (shortEntry n (by omega) e) =
        shortEntry n (by omega) ((cellUniversal n hn).trans e) := by
    unfold relabelVertex shortEntry
    rw [vertexCoordinates_coordinateVertex]
    apply congrArg coordinateVertex
    ext i
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [hentry]
  exact cellUniversal_shortEntry_return n hn e

end SuperpermutationLowerBound.Refinement
