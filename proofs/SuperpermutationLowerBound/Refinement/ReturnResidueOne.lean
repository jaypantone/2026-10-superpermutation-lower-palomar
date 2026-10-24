module

public import SuperpermutationLowerBound.Refinement.ReturnCycleShift
public import SuperpermutationLowerBound.Refinement.ReturnEntries

@[expose] public section

/-! The two-shortened-cell return when `n = 3m+1`, proved by following
the explicit cycles and then evaluating four symbolic maps. -/
namespace SuperpermutationLowerBound.Refinement

def cellHalfOneValue (n i : ℕ) : ℕ :=
  if i = 1 then 2 else if i = 2 then n else if i = 4 then 1
  else if 7 ≤ i ∧ i % 3 = 1 then i - 2
  else if 5 ≤ i ∧ i % 3 = 2 then i - 1 else i

theorem cellHalfOne_a1 (m j : ℕ) (hm : 2 ≤ m) (hj : j < 2*m+1) :
    ReturnCycle.a1 m (if m+j ≤ 2*m+1 then m+j else m+j-(2*m+1)) =
      cellHalfOneValue (3*m+1) (ReturnCycle.a1 m j) := by
  split_ifs <;> simp only [ReturnCycle.a1] <;> split_ifs <;>
    simp only [cellHalfOneValue] <;> split_ifs <;> omega

theorem cellHalfOne_b1 (m j : ℕ) (hm : 2 ≤ m) (hj : j < m) :
    cellHalfOneValue (3*m+1) (ReturnCycle.b1 m j) = ReturnCycle.b1 m j := by
  simp only [ReturnCycle.b1]
  split_ifs <;> simp only [cellHalfOneValue] <;> split_ifs <;> omega

theorem cellG_pow_residueOne_val (m : ℕ) (hm : 2 ≤ m) (hn : 7 ≤ 3*m+1)
    (i : Fin (3*m+1+1)) :
    (((cellG (3*m+1) hn)^m) i).val = cellHalfOneValue (3*m+1) i.val := by
  let n := 3*m+1
  let g := cellG n hn
  rcases ReturnCycle.cover1 m i.val hm (by omega) with hz | hA | hB
  · have hi : i = 0 := Fin.ext hz
    subst i
    simp [cellHalfOneValue]
  · obtain ⟨j, hj, hv⟩ := hA
    let w : ℕ → Fin (n+1) := fun k =>
      ⟨ReturnCycle.a1 m k, by have := ReturnCycle.a1_le m k hm; dsimp [n]; omega⟩
    have hi : i = w j := Fin.ext hv.symm
    have hstep : ∀ k < 2*m+1, g (w k) = w (k+1) := by
      intro k hk
      exact Fin.ext (ReturnCycle.a1_step m k hm hk)
    have hclosed : w (2*m+1) = w 0 := Fin.ext (ReturnCycle.a1_closed m hm)
    have hshift := ReturnCycle.pow_shift_walk g w (2*m+1) hstep hclosed
      j m (by omega) (by omega)
    rw [hi]
    change ((g^m) (w j)).val = _
    rw [hshift]
    exact cellHalfOne_a1 m j hm hj
  · obtain ⟨j, hj, hv⟩ := hB
    have hi : i = ⟨ReturnCycle.b1 m j,
      by have := ReturnCycle.b1_le m j hm; omega⟩ := Fin.ext hv.symm
    rw [hi]
    have hfix := cellG_pow_fix_walk n hn (ReturnCycle.b1 m) m m
      (fun k => ReturnCycle.b1_le m k hm)
      (fun k hk => ReturnCycle.b1_step m k hm hk) (ReturnCycle.b1_closed m hm)
      (dvd_refl m) j (by omega)
    change ((g^m) _).val = _
    rw [hfix]
    exact (cellHalfOne_b1 m j hm hj).symm

def cellQOneValue (n i : ℕ) : ℕ :=
  if i = 0 then 0 else if i = 1 then 5 else if i = 2 then 3
  else if i + 3 ≤ n then i + 3 else if i + 2 = n then 2
  else if i + 1 = n then 1 else 4

set_option maxHeartbeats 1000000 in
theorem cellQOne_composition (m : ℕ) (hm : 2 ≤ m) {i : ℕ} (hi : i < 3*m+1+1) :
    cellRhoValue (3*m+1) (cellHalfOneValue (3*m+1)
      (cellRhoValue (3*m+1) (cellGValue (3*m+1)
        (cellHalfOneValue (3*m+1) i)))) = cellQOneValue (3*m+1) i := by
  conv_lhs => arg 2; arg 2; arg 2; arg 2; unfold cellHalfOneValue
  all_goals split_ifs <;> try omega
  all_goals simp only [cellGValue]
  all_goals split_ifs <;> try omega
  all_goals conv_lhs => arg 2; arg 2; unfold cellRhoValue
  all_goals split_ifs <;> try omega
  all_goals simp only [cellHalfOneValue]
  all_goals split_ifs <;> try omega
  all_goals simp only [cellRhoValue, cellQOneValue]
  all_goals split_ifs <;> (first | contradiction | omega)

/-- Exact letterwise normalization of `C^m B C^(m-1) B`. -/
theorem shortened_return_residueOne_val (m : ℕ) (hm : 2 ≤ m) (hn : 7 ≤ 3*m+1)
    (i : Fin (3*m+1+1)) :
    ((cellRho (3*m+1) hn * (cellG (3*m+1) hn)^m * cellRho (3*m+1) hn *
      (cellG (3*m+1) hn)^(m+1)) i).val = cellQOneValue (3*m+1) i.val := by
  simp only [pow_succ', Equiv.Perm.mul_apply, cellRho_apply_val,
    cellG_pow_residueOne_val m hm hn, cellG_apply_val]
  exact cellQOne_composition m hm i.isLt

/-- The earlier occupied block in the first full row maps literally to `y`. -/
theorem cellQOne_u_core_value (n : ℕ) (hn : 7 ≤ n) (i : ℕ) (hi : i < n) :
    cellQOneValue n (cellUValue n ((n-2+i) % n)) = cellYValue n i := by
  have hmod : (n-2+i) % n = if i < 2 then n-2+i else i-2 := by
    by_cases h : i < 2
    · simp [h, Nat.mod_eq_of_lt (by omega : n-2+i < n)]
    · rw [if_neg h, Nat.mod_eq_sub_mod (by omega : n ≤ n-2+i),
        Nat.mod_eq_of_lt (by omega : n-2+i-n < n)]
      omega
  rw [hmod]
  split_ifs <;> simp only [cellUValue] <;> split_ifs <;>
    simp only [cellQOneValue, cellYValue] <;> split_ifs <;>
    (first | contradiction | omega)

theorem cellQOne_u_last_value (n : ℕ) (hn : 7 ≤ n) :
    cellQOneValue n (cellUValue n n) = cellYValue n n := by
  simp only [cellUValue, cellQOneValue, cellYValue]
  split_ifs <;> omega

end SuperpermutationLowerBound.Refinement
