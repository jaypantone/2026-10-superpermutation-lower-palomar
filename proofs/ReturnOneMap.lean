module

public import SuperpermutationLowerBound.Refinement.ReturnResidueOne

@[expose] public section

/-!
The literal map in Appendix A. This is source under development until its
compilation receipt exists. The pointwise formula is separate from the
cycle-order theorem; the latter must still be proved for the final bound.
-/

namespace SuperpermutationLowerBound.Refinement.ChainReturns

open SuperpermutationLowerBound.Refinement

set_option maxHeartbeats 2000000

def efficientOneValue (m x : ℕ) : ℕ :=
  if x = 0 then 0
  else if x = 1 then 3 * m - 1
  else if x = 2 then 3 * m - 2
  else if x = 3 then 3 * m - 3
  else if x = 4 then 3 * m + 1
  else if x = 5 then 3 * m
  else if x = 6 then 2
  else if x = 7 then 3
  else if x = 8 then 4
  else if x = 9 then 1
  else if x % 3 = 0 then x - 6
  else if x % 3 = 1 then x - 5
  else x - 4

theorem efficientOneValue_lt {m x : ℕ} (hm : 3 ≤ m) (hx : x < 3 * m + 2) :
    efficientOneValue m x < 3 * m + 2 := by
  unfold efficientOneValue
  split_ifs <;> omega

theorem efficientOneValue_descends {m x : ℕ} (hx : 5 < x) :
    efficientOneValue m x < x := by
  unfold efficientOneValue
  split_ifs <;> omega

theorem efficientOneValue_pos {m x : ℕ} (hm : 3 ≤ m) (hx : 0 < x) :
    0 < efficientOneValue m x := by
  unfold efficientOneValue
  split_ifs <;> omega

/-- Repeated application of the displayed map reaches one of the anchors.
This alone does not compute the first-return times or prove the cycle table. -/
theorem efficientOneValue_reaches_anchor (m x : ℕ) :
    ∃ r : ℕ, ((efficientOneValue m)^[r]) x ≤ 5 := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
      by_cases hx : x ≤ 5
      · exact ⟨0, by simpa using hx⟩
      · obtain ⟨r, hr⟩ := ih (efficientOneValue m x)
          (efficientOneValue_descends (by omega))
        refine ⟨r + 1, ?_⟩
        simpa only [Function.iterate_succ_apply] using hr

theorem cellG_pow_pred_residueOne_val (m : ℕ) (hm : 3 ≤ m)
    (hn : 7 ≤ 3 * m + 1) (i : Fin (3 * m + 1 + 1)) :
    (((cellG (3 * m + 1) hn) ^ (m - 1)) i).val =
      cellHalfOneValue (3 * m + 1) (cellGInverseValue (3 * m + 1) i.val) := by
  let g := cellG (3 * m + 1) hn
  have hpow : (g ^ (m - 1)) i = (g ^ m) (g.symm i) := by
    have hm' : m - 1 + 1 = m := by omega
    calc
      (g ^ (m - 1)) i = (g ^ (m - 1)) (g (g.symm i)) := by
        rw [Equiv.apply_symm_apply]
      _ = (g ^ (m - 1 + 1)) (g.symm i) := by
        rw [pow_succ, Equiv.Perm.mul_apply]
      _ = (g ^ m) (g.symm i) := by rw [hm']
  rw [show ((cellG (3 * m + 1) hn) ^ (m - 1)) i =
      ((cellG (3 * m + 1) hn) ^ m) ((cellG (3 * m + 1) hn).symm i) from hpow]
  rw [cellG_pow_residueOne_val m (by omega) hn, cellG_symm_apply_val]

set_option maxHeartbeats 2000000 in
theorem efficientOne_composition (m : ℕ) (hm : 3 ≤ m)
    {x : ℕ} (hx : x < 3 * m + 1 + 1) :
    cellRhoValue (3 * m + 1)
      (cellHalfOneValue (3 * m + 1)
        (cellGInverseValue (3 * m + 1)
          (cellRhoValue (3 * m + 1) (cellGInverseValue (3 * m + 1) x)))) =
      efficientOneValue m x := by
  by_cases hsmall : x < 10
  · interval_cases x
    · have h1 : cellGInverseValue (3*m+1) 0 = 0 := by
        norm_num [cellGInverseValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h2 : cellRhoValue (3*m+1) (0) = 0 := by
        norm_num [cellRhoValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h3 : cellGInverseValue (3*m+1) (0) = 0 := by
        norm_num [cellGInverseValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h4 : cellHalfOneValue (3*m+1) (0) = 0 := by
        norm_num [cellHalfOneValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h5 : cellRhoValue (3*m+1) (0) = 0 := by
        norm_num [cellRhoValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have ho : efficientOneValue m 0 = 0 := by
        norm_num [efficientOneValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      rw [h1, h2, h3, h4, h5, ho]
    · have h1 : cellGInverseValue (3*m+1) 1 = 3*m+1 := by
        norm_num [cellGInverseValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h2 : cellRhoValue (3*m+1) (3*m+1) = 2 := by
        norm_num [cellRhoValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h3 : cellGInverseValue (3*m+1) (2) = 3*m-1 := by
        norm_num [cellGInverseValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h4 : cellHalfOneValue (3*m+1) (3*m-1) = 3*m-2 := by
        norm_num [cellHalfOneValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h5 : cellRhoValue (3*m+1) (3*m-2) = 3*m-1 := by
        norm_num [cellRhoValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have ho : efficientOneValue m 1 = 3*m-1 := by
        norm_num [efficientOneValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      rw [h1, h2, h3, h4, h5, ho]
    · have h1 : cellGInverseValue (3*m+1) 2 = 3*m-1 := by
        norm_num [cellGInverseValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h2 : cellRhoValue (3*m+1) (3*m-1) = 3*m := by
        norm_num [cellRhoValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h3 : cellGInverseValue (3*m+1) (3*m) = 3*m-3 := by
        norm_num [cellGInverseValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h4 : cellHalfOneValue (3*m+1) (3*m-3) = 3*m-3 := by
        norm_num [cellHalfOneValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h5 : cellRhoValue (3*m+1) (3*m-3) = 3*m-2 := by
        norm_num [cellRhoValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have ho : efficientOneValue m 2 = 3*m-2 := by
        norm_num [efficientOneValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      rw [h1, h2, h3, h4, h5, ho]
    · have h1 : cellGInverseValue (3*m+1) 3 = 3*m := by
        norm_num [cellGInverseValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h2 : cellRhoValue (3*m+1) (3*m) = 3*m+1 := by
        norm_num [cellRhoValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h3 : cellGInverseValue (3*m+1) (3*m+1) = 3*m-2 := by
        norm_num [cellGInverseValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h4 : cellHalfOneValue (3*m+1) (3*m-2) = 3*m-4 := by
        norm_num [cellHalfOneValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h5 : cellRhoValue (3*m+1) (3*m-4) = 3*m-3 := by
        norm_num [cellRhoValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have ho : efficientOneValue m 3 = 3*m-3 := by
        norm_num [efficientOneValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      rw [h1, h2, h3, h4, h5, ho]
    · have h1 : cellGInverseValue (3*m+1) 4 = 2 := by
        norm_num [cellGInverseValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h2 : cellRhoValue (3*m+1) (2) = 3 := by
        norm_num [cellRhoValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h3 : cellGInverseValue (3*m+1) (3) = 3*m := by
        norm_num [cellGInverseValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h4 : cellHalfOneValue (3*m+1) (3*m) = 3*m := by
        norm_num [cellHalfOneValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h5 : cellRhoValue (3*m+1) (3*m) = 3*m+1 := by
        norm_num [cellRhoValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have ho : efficientOneValue m 4 = 3*m+1 := by
        norm_num [efficientOneValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      rw [h1, h2, h3, h4, h5, ho]
    · have h1 : cellGInverseValue (3*m+1) 5 = 1 := by
        norm_num [cellGInverseValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h2 : cellRhoValue (3*m+1) (1) = 1 := by
        norm_num [cellRhoValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h3 : cellGInverseValue (3*m+1) (1) = 3*m+1 := by
        norm_num [cellGInverseValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h4 : cellHalfOneValue (3*m+1) (3*m+1) = 3*m-1 := by
        norm_num [cellHalfOneValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h5 : cellRhoValue (3*m+1) (3*m-1) = 3*m := by
        norm_num [cellRhoValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have ho : efficientOneValue m 5 = 3*m := by
        norm_num [efficientOneValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      rw [h1, h2, h3, h4, h5, ho]
    · have h1 : cellGInverseValue (3*m+1) 6 = 3 := by
        norm_num [cellGInverseValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h2 : cellRhoValue (3*m+1) (3) = 4 := by
        norm_num [cellRhoValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h3 : cellGInverseValue (3*m+1) (4) = 2 := by
        norm_num [cellGInverseValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h4 : cellHalfOneValue (3*m+1) (2) = 3*m+1 := by
        norm_num [cellHalfOneValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h5 : cellRhoValue (3*m+1) (3*m+1) = 2 := by
        norm_num [cellRhoValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have ho : efficientOneValue m 6 = 2 := by
        norm_num [efficientOneValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      rw [h1, h2, h3, h4, h5, ho]
    · have h1 : cellGInverseValue (3*m+1) 7 = 4 := by
        norm_num [cellGInverseValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h2 : cellRhoValue (3*m+1) (4) = 5 := by
        norm_num [cellRhoValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h3 : cellGInverseValue (3*m+1) (5) = 1 := by
        norm_num [cellGInverseValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h4 : cellHalfOneValue (3*m+1) (1) = 2 := by
        norm_num [cellHalfOneValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h5 : cellRhoValue (3*m+1) (2) = 3 := by
        norm_num [cellRhoValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have ho : efficientOneValue m 7 = 3 := by
        norm_num [efficientOneValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      rw [h1, h2, h3, h4, h5, ho]
    · have h1 : cellGInverseValue (3*m+1) 8 = 5 := by
        norm_num [cellGInverseValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h2 : cellRhoValue (3*m+1) (5) = 6 := by
        norm_num [cellRhoValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h3 : cellGInverseValue (3*m+1) (6) = 3 := by
        norm_num [cellGInverseValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h4 : cellHalfOneValue (3*m+1) (3) = 3 := by
        norm_num [cellHalfOneValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h5 : cellRhoValue (3*m+1) (3) = 4 := by
        norm_num [cellRhoValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have ho : efficientOneValue m 8 = 4 := by
        norm_num [efficientOneValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      rw [h1, h2, h3, h4, h5, ho]
    · have h1 : cellGInverseValue (3*m+1) 9 = 6 := by
        norm_num [cellGInverseValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h2 : cellRhoValue (3*m+1) (6) = 7 := by
        norm_num [cellRhoValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h3 : cellGInverseValue (3*m+1) (7) = 4 := by
        norm_num [cellGInverseValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h4 : cellHalfOneValue (3*m+1) (4) = 1 := by
        norm_num [cellHalfOneValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have h5 : cellRhoValue (3*m+1) (1) = 1 := by
        norm_num [cellRhoValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      have ho : efficientOneValue m 9 = 1 := by
        norm_num [efficientOneValue] <;> (try split_ifs) <;> (first | omega | contradiction)
      rw [h1, h2, h3, h4, h5, ho]
  · have h1 : cellGInverseValue (3 * m + 1) x = x - 3 := by
      norm_num [cellGInverseValue] <;> (try split_ifs) <;> (first | omega | contradiction)
    have h2 : cellRhoValue (3 * m + 1) (x - 3) = x - 2 := by
      norm_num [cellRhoValue] <;> (try split_ifs) <;> (first | omega | contradiction)
    have h3 : cellGInverseValue (3 * m + 1) (x - 2) = x - 5 := by
      norm_num [cellGInverseValue] <;> (try split_ifs) <;> (first | omega | contradiction)
    rw [h1, h2, h3]
    by_cases hz : x % 3 = 0
    · have h4 : cellHalfOneValue (3*m+1) (x-5) = x-7 := by
        unfold cellHalfOneValue; split_ifs <;> omega
      have h5 : cellRhoValue (3*m+1) (x-7) = x-6 := by
        unfold cellRhoValue; split_ifs <;> omega
      have ho : efficientOneValue m x = x-6 := by
        unfold efficientOneValue; split_ifs <;> omega
      rw [h4, h5, ho]
    · by_cases hu : x % 3 = 1
      · have h4 : cellHalfOneValue (3*m+1) (x-5) = x-6 := by
          unfold cellHalfOneValue; split_ifs <;> omega
        have h5 : cellRhoValue (3*m+1) (x-6) = x-5 := by
          unfold cellRhoValue; split_ifs <;> omega
        have ho : efficientOneValue m x = x-5 := by
          unfold efficientOneValue; split_ifs <;> omega
        rw [h4, h5, ho]
      · have h4 : cellHalfOneValue (3*m+1) (x-5) = x-5 := by
          unfold cellHalfOneValue; split_ifs <;> omega
        have h5 : cellRhoValue (3*m+1) (x-5) = x-4 := by
          unfold cellRhoValue; split_ifs <;> omega
        have ho : efficientOneValue m x = x-4 := by
          unfold efficientOneValue; split_ifs <;> omega
        rw [h4, h5, ho]

/-- The efficient pair has exactly the letterwise action used in Appendix A. -/
theorem efficientOne_apply_val (m : ℕ) (hm : 3 ≤ m)
    (hn : 7 ≤ 3 * m + 1) (i : Fin (3 * m + 1 + 1)) :
    ((cellRho (3 * m + 1) hn * (cellG (3 * m + 1) hn) ^ (m - 1) *
      cellRho (3 * m + 1) hn * (cellG (3 * m + 1) hn)⁻¹) i).val =
      efficientOneValue m i.val := by
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, cellRho_apply_val,
    cellG_pow_pred_residueOne_val m hm hn, cellG_symm_apply_val]
  exact efficientOne_composition m hm i.isLt

end SuperpermutationLowerBound.Refinement.ChainReturns
