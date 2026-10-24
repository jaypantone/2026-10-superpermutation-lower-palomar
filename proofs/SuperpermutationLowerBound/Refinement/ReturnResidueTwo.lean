module

public import SuperpermutationLowerBound.Refinement.ReturnCycleShift
public import SuperpermutationLowerBound.Refinement.ReturnEntries

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

set_option linter.unusedSimpArgs false


/-- The literal involution `(2 n) ∏ (3j+2 3j+3)` in the residue-two case. -/
def cellJValue (n i : ℕ) : ℕ :=
  if i = 2 then n else if i = n then 2
  else if 5 ≤ i ∧ i % 3 = 2 then i + 1
  else if 6 ≤ i ∧ i % 3 = 0 then i - 1 else i

theorem cellJValue_lt (m : ℕ) (hm : 2 ≤ m) {i : ℕ} (hi : i < 3 * m + 2 + 1) :
    cellJValue (3 * m + 2) i < 3 * m + 2 + 1 := by
  unfold cellJValue
  split_ifs <;> omega

theorem cellJValue_involutive (m : ℕ) (hm : 2 ≤ m) {i : ℕ}
    (hi : i < 3 * m + 2 + 1) :
    cellJValue (3 * m + 2) (cellJValue (3 * m + 2) i) = i := by
  unfold cellJValue
  split_ifs <;> omega

def cellJ (m : ℕ) (hm : 2 ≤ m) : Equiv.Perm (Fin (3 * m + 2 + 1)) where
  toFun i := ⟨cellJValue (3 * m + 2) i.val, cellJValue_lt m hm i.isLt⟩
  invFun i := ⟨cellJValue (3 * m + 2) i.val, cellJValue_lt m hm i.isLt⟩
  left_inv i := Fin.ext (cellJValue_involutive m hm i.isLt)
  right_inv i := Fin.ext (cellJValue_involutive m hm i.isLt)

@[simp] theorem cellJ_apply_val (m : ℕ) (hm : 2 ≤ m) (i : Fin (3 * m + 2 + 1)) :
    (cellJ m hm i).val = cellJValue (3 * m + 2) i.val := rfl

theorem cellJ_mul_self (m : ℕ) (hm : 2 ≤ m) : cellJ m hm * cellJ m hm = 1 := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  exact cellJValue_involutive m hm i.isLt

theorem cellRho_a2_eq_J (m j : ℕ) (hm : 2 ≤ m) (hj : j < m + 1) :
    cellRhoValue (3 * m + 2) (ReturnCycle.a2 m j) =
      cellJValue (3 * m + 2) (ReturnCycle.a2 m j) := by
  unfold ReturnCycle.a2
  split_ifs <;> simp only [cellRhoValue, cellJValue] <;> split_ifs <;> omega

theorem cellRho_b2_shift_eq_J (m j : ℕ) (hm : 2 ≤ m) (hj : j < 2 * m + 1) :
    cellRhoValue (3 * m + 2)
      (ReturnCycle.b2 m (if m + j ≤ 2 * m + 1 then m + j else m + j - (2 * m + 1))) =
      cellJValue (3 * m + 2) (ReturnCycle.b2 m j) := by
  split_ifs <;> simp only [ReturnCycle.b2] <;> split_ifs <;>
    simp only [cellRhoValue, cellJValue] <;> split_ifs <;> omega

/-- The residue-two power has the exact transposition formula; this is
stronger than just establishing its finite order. -/
theorem cellRho_pow_residueTwo (m : ℕ) (hm : 2 ≤ m) (hn : 7 ≤ 3 * m + 2) :
    cellRho (3 * m + 2) hn * (cellG (3 * m + 2) hn) ^ (2 * m * (m + 1)) =
      cellJ m hm := by
  let n := 3 * m + 2
  let g := cellG n hn
  apply Equiv.ext
  intro i
  rcases ReturnCycle.cover2 m i.val hm (by omega) with hz | hA | hB
  · have hi : i = 0 := Fin.ext hz
    subst i
    simp [Equiv.Perm.mul_apply, cellRho, cellJ, cellRhoValue, cellJValue]
  · obtain ⟨j, hj, hv⟩ := hA
    have hi : i = ⟨ReturnCycle.a2 m j, by have := ReturnCycle.a2_le m j hm; omega⟩ :=
      Fin.ext hv.symm
    rw [hi, Equiv.Perm.mul_apply]
    have hfix := cellG_pow_fix_walk n hn (ReturnCycle.a2 m) (m + 1)
      (2 * m * (m + 1)) (fun k => ReturnCycle.a2_le m k hm)
      (fun k hk => ReturnCycle.a2_step m k hm hk) (ReturnCycle.a2_closed m hm)
      (dvd_mul_left _ _) j (by omega)
    change (cellRho n hn) ((g ^ (2 * m * (m + 1))) _) = _
    rw [hfix]
    apply Fin.ext
    exact cellRho_a2_eq_J m j hm hj
  · obtain ⟨j, hj, hv⟩ := hB
    let w : ℕ → Fin (n + 1) := fun k =>
      ⟨ReturnCycle.b2 m k, by have := ReturnCycle.b2_le m k hm; dsimp [n]; omega⟩
    have hi : i = w j := Fin.ext hv.symm
    have hstep : ∀ k < 2 * m + 1, g (w k) = w (k + 1) := by
      intro k hk
      exact Fin.ext (ReturnCycle.b2_step m k hm hk)
    have hclosed : w (2 * m + 1) = w 0 := Fin.ext (ReturnCycle.b2_closed m hm)
    have hfix := ReturnCycle.pow_fix_of_closed_walk g w (2 * m + 1)
      ((2 * m + 1) * m) hstep hclosed (dvd_mul_right _ _) j (by omega)
    have hshift := ReturnCycle.pow_shift_walk g w (2 * m + 1) hstep hclosed j m
      (by omega) (by omega)
    have he : 2 * m * (m + 1) = m + (2 * m + 1) * m := by ring
    rw [hi, Equiv.Perm.mul_apply]
    change (cellRho n hn) ((g ^ (2 * m * (m + 1))) (w j)) = _
    rw [he, pow_add, Equiv.Perm.mul_apply, hfix, hshift]
    apply Fin.ext
    exact cellRho_b2_shift_eq_J m j hm hj

def cellKValue (n i : ℕ) : ℕ :=
  if i = 2 then n else if i = n then 2 else if i = 1 then 3 else if i = 3 then 1 else i

theorem cellKValue_lt (n : ℕ) (hn : 7 ≤ n) {i : ℕ} (hi : i < n + 1) :
    cellKValue n i < n + 1 := by
  unfold cellKValue
  split_ifs <;> omega

theorem cellKValue_involutive (n : ℕ) (hn : 7 ≤ n) {i : ℕ} (hi : i < n + 1) :
    cellKValue n (cellKValue n i) = i := by
  unfold cellKValue
  split_ifs <;> omega

/-- The two disjoint transpositions `(2 n)(1 3)`. -/
def cellK (n : ℕ) (hn : 7 ≤ n) : Equiv.Perm (Fin (n + 1)) where
  toFun i := ⟨cellKValue n i.val, cellKValue_lt n hn i.isLt⟩
  invFun i := ⟨cellKValue n i.val, cellKValue_lt n hn i.isLt⟩
  left_inv i := Fin.ext (cellKValue_involutive n hn i.isLt)
  right_inv i := Fin.ext (cellKValue_involutive n hn i.isLt)

@[simp] theorem cellK_apply_val (n : ℕ) (hn : 7 ≤ n) (i : Fin (n + 1)) :
    (cellK n hn i).val = cellKValue n i.val := rfl

set_option maxHeartbeats 1000000 in
theorem cellJ_commutator_value (m : ℕ) (hm : 2 ≤ m) {i : ℕ}
    (hi : i < 3 * m + 2 + 1) :
    cellJValue (3 * m + 2) (cellGInverseValue (3 * m + 2)
      (cellJValue (3 * m + 2) (cellGValue (3 * m + 2) i))) =
      cellKValue (3 * m + 2) i := by
  unfold cellGValue
  split_ifs <;> try (first | contradiction | omega)
  all_goals conv_lhs => arg 2; arg 2; unfold cellJValue
  all_goals split_ifs <;> try (first | contradiction | omega)
  all_goals simp only [cellGInverseValue]
  all_goals split_ifs <;> try (first | contradiction | omega)
  all_goals simp only [cellJValue, cellKValue]
  all_goals split_ifs <;> try (first | contradiction | omega)
  all_goals first | contradiction | omega

theorem cellJ_commutator (m : ℕ) (hm : 2 ≤ m) (hn : 7 ≤ 3 * m + 2) :
    cellJ m hm * (cellG (3 * m + 2) hn)⁻¹ * cellJ m hm * cellG (3 * m + 2) hn =
      cellK (3 * m + 2) hn := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  exact cellJ_commutator_value m hm i.isLt

/-- Normalization of the two-shortened-cell word in the declared order. -/
theorem involution_return_residueTwo (m : ℕ) (hm : 2 ≤ m) (hn : 7 ≤ 3 * m + 2) :
    (cellG (3 * m + 2) hn) ^ (2 * m * (m + 1) - 1) * cellRho (3 * m + 2) hn *
      (cellG (3 * m + 2) hn) ^ (2 * m * (m + 1) + 1) =
      (cellG (3 * m + 2) hn)⁻¹ * (cellRho (3 * m + 2) hn)⁻¹ * cellG (3 * m + 2) hn := by
  let g := cellG (3 * m + 2) hn
  let rho := cellRho (3 * m + 2) hn
  let v := 2 * m * (m + 1)
  have hv : 1 ≤ v := by dsimp [v]; nlinarith
  have hJ : rho * g ^ v = cellJ m hm := cellRho_pow_residueTwo m hm hn
  have hmid : g ^ v * rho * g ^ v = rho⁻¹ := by
    have h := congrArg (fun q => rho⁻¹ * q) (cellJ_mul_self m hm)
    rw [← hJ] at h
    simpa only [mul_assoc, inv_mul_cancel_left, mul_one] using h
  have hpred : g ^ (v - 1) = g⁻¹ * g ^ v := by
    calc
      g ^ (v - 1) = g⁻¹ * (g * g ^ (v - 1)) := by group
      _ = g⁻¹ * g ^ v := by rw [← pow_succ', Nat.sub_add_cancel hv]
  change g ^ (v - 1) * rho * g ^ (v + 1) = g⁻¹ * rho⁻¹ * g
  rw [hpred, pow_succ]
  calc
    g⁻¹ * g ^ v * rho * (g ^ v * g) = g⁻¹ * (g ^ v * rho * g ^ v) * g := by
      simp only [mul_assoc]
    _ = g⁻¹ * rho⁻¹ * g := by rw [hmid]

/-- Normalization of the two-shortened-cell word in the declared order. -/
theorem shortened_return_residueTwo (m : ℕ) (hm : 2 ≤ m) (hn : 7 ≤ 3 * m + 2) :
    cellRho (3 * m + 2) hn * (cellG (3 * m + 2) hn) ^ (2 * m * (m + 1) - 1) *
      cellRho (3 * m + 2) hn * (cellG (3 * m + 2) hn) ^ (2 * m * (m + 1) + 2) =
      cellK (3 * m + 2) hn * cellG (3 * m + 2) hn := by
  let g := cellG (3 * m + 2) hn
  let rho := cellRho (3 * m + 2) hn
  let v := 2 * m * (m + 1)
  have hv : 1 ≤ v := by dsimp [v]; nlinarith
  have hpred : g ^ (v - 1) = g ^ v * g⁻¹ := by
    apply (eq_mul_inv_iff_mul_eq).2
    rw [← pow_succ, Nat.sub_add_cancel hv]
  have hJ : rho * g ^ v = cellJ m hm := cellRho_pow_residueTwo m hm hn
  change rho * g ^ (v - 1) * rho * g ^ (v + 2) = cellK (3 * m + 2) hn * g
  rw [hpred, pow_add, pow_two]
  calc
    rho * (g ^ v * g⁻¹) * rho * (g ^ v * (g * g)) =
        (rho * g ^ v) * g⁻¹ * (rho * g ^ v) * g * g := by simp only [mul_assoc]
    _ = cellJ m hm * g⁻¹ * cellJ m hm * g * g := by rw [hJ]
    _ = cellK (3 * m + 2) hn * g := by rw [cellJ_commutator m hm hn]

theorem cellK_g_y_core_value (n : ℕ) (hn : 7 ≤ n) (i : ℕ) (hi : i < n) :
    cellKValue n (cellGValue n (cellYValue n i)) = cellUValue n ((4 + i) % n) := by
  have hmod : (4 + i) % n = if 4 + i < n then 4 + i else 4 + i - n := by
    by_cases h : 4 + i < n
    · simp [h, Nat.mod_eq_of_lt h]
    · rw [if_neg h, Nat.mod_eq_sub_mod (by omega : n ≤ 4 + i),
        Nat.mod_eq_of_lt (by omega : 4 + i - n < n)]
  rw [hmod]
  by_cases hrot : 4 + i < n
  all_goals simp only [hrot, ↓reduceIte]
  all_goals simp only [cellYValue]
  all_goals split_ifs <;> try (first | contradiction | omega)
  all_goals simp only [cellGValue]
  all_goals split_ifs <;> try (first | contradiction | omega)
  all_goals simp only [cellKValue, cellUValue]
  all_goals split_ifs <;> (first | contradiction | omega)

theorem cellK_g_y_last_value (n : ℕ) (hn : 7 ≤ n) :
    cellKValue n (cellGValue n (cellYValue n n)) = 0 := by
  have hy : cellYValue n n = 0 := by unfold cellYValue; split_ifs <;> omega
  simp [hy, cellGValue, cellKValue, show (0 : ℕ) ≠ n by omega]

/-- Literal occupied-slot identity used by the terminal collision table. -/
theorem shortened_return_y_core (m : ℕ) (hm : 2 ≤ m) (hn : 7 ≤ 3 * m + 2)
    (i : ℕ) (hi : i < 3 * m + 2) :
    ((cellRho (3 * m + 2) hn * (cellG (3 * m + 2) hn) ^ (2 * m * (m + 1) - 1) *
      cellRho (3 * m + 2) hn * (cellG (3 * m + 2) hn) ^ (2 * m * (m + 1) + 2))
      (cellY (3 * m + 2) hn ⟨i, by omega⟩)).val =
      cellUValue (3 * m + 2) ((4 + i) % (3 * m + 2)) := by
  rw [shortened_return_residueTwo m hm hn]
  exact cellK_g_y_core_value (3 * m + 2) hn i hi

theorem shortened_return_y_last (m : ℕ) (hm : 2 ≤ m) (hn : 7 ≤ 3 * m + 2) :
    ((cellRho (3 * m + 2) hn * (cellG (3 * m + 2) hn) ^ (2 * m * (m + 1) - 1) *
      cellRho (3 * m + 2) hn * (cellG (3 * m + 2) hn) ^ (2 * m * (m + 1) + 2))
      (cellY (3 * m + 2) hn ⟨3 * m + 2, by omega⟩)).val = 0 := by
  rw [shortened_return_residueTwo m hm hn]
  exact cellK_g_y_last_value (3 * m + 2) hn

end SuperpermutationLowerBound.Refinement
