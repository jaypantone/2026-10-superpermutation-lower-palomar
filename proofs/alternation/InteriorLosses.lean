module

public import alternation.AlternationPayment
public import alternation.AlternatingStrings

@[expose] public section

namespace SuperpermutationLowerBound.Refinement.ChainReturns

open SuperpermutationLowerBound.Refinement

def equalBinaryIndicator (x y : ℕ) : ℕ :=
  if x ≤ 1 ∧ y ≤ 1 ∧ x = y then 1 else 0

theorem equalBinaryCuts_eq_sum (xs : List ℕ) :
    equalBinaryCuts xs = ∑ i ∈ Finset.range (xs.length - 1),
      equalBinaryIndicator (deficitAt xs i) (deficitAt xs (i + 1)) := by
  induction xs with
  | nil => simp [equalBinaryCuts]
  | cons x xs ih =>
      cases xs with
      | nil => simp [equalBinaryCuts]
      | cons y ys =>
          simp only [List.length_cons, Nat.add_sub_cancel, Finset.sum_range_succ',
            equalBinaryCuts] at *
          rw [ih]
          simp only [equalBinaryIndicator, deficitAt, List.getElem?_cons_zero,
            List.getElem?_cons_succ, Option.getD_some, Nat.add_assoc]
          exact Nat.add_comm _ _

theorem removedCount_eq_sum (xs : List ℕ) :
    removedCount xs = ∑ i ∈ Finset.range xs.length,
      (if deficitAt xs i ≤ 1 then 0 else 1) := by
  rw [show (∑ i ∈ Finset.range xs.length,
      (if deficitAt xs i ≤ 1 then 0 else 1)) =
      (xs.map (fun x => if x ≤ 1 then 0 else 1)).sum from
    sum_range_deficitAt (fun x => if x ≤ 1 then 0 else 1) xs]
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [removedCount, ih]

def interiorLosses (b : ℕ) (ls : List ℕ) : List ℕ :=
  ((ls.drop 1).take (ls.length - 2)).map (fun x => b - x)

theorem interiorLosses_length (b : ℕ) (ls : List ℕ) :
    (interiorLosses b ls).length = ls.length - 2 := by
  simp only [interiorLosses, List.length_map, List.length_take, List.length_drop]
  exact Nat.min_eq_left (by omega)

theorem interiorLosses_at (b : ℕ) (ls : List ℕ) (i : ℕ) (hi : i < ls.length - 2) :
    deficitAt (interiorLosses b ls) i = b - deficitAt ls (i + 1) := by
  unfold deficitAt interiorLosses
  rw [List.getElem?_map, List.getElem?_take_of_lt hi, List.getElem?_drop]
  rw [show 1 + i = i + 1 by omega]
  rw [List.getElem?_eq_getElem (by omega : i + 1 < ls.length)]
  rfl

theorem equalBinary_loss_identity {b x y : ℕ} (hb : 1 ≤ b)
    (hx : x ≤ b) (hy : y ≤ b) :
    equalBinaryIndicator (b - x) (b - y) =
      doubleMaxIndicator b x y + doubleNearMaxIndicator b x y := by
  unfold equalBinaryIndicator doubleMaxIndicator doubleNearMaxIndicator
  split_ifs <;> omega

theorem interiorLosses_cuts {b : ℕ} (hb : 1 ≤ b) (ls : List ℕ)
    (hbound : ∀ x ∈ ls, x ≤ b) :
    equalBinaryCuts (interiorLosses b ls) =
      doubleMaxCount b ls + doubleNearMaxCount b ls := by
  rw [equalBinaryCuts_eq_sum, interiorLosses_length]
  have hlen : ls.length - 2 - 1 = ls.length - 3 := by omega
  rw [hlen]
  unfold doubleMaxCount doubleNearMaxCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hir := Finset.mem_range.mp hi
  rw [interiorLosses_at b ls i (by omega),
    interiorLosses_at b ls (i + 1) (by omega)]
  have hx := hbound _ (deficitAt_mem ls (i + 1) (by omega))
  have hy := hbound _ (deficitAt_mem ls (i + 2) (by omega))
  simpa only [Nat.add_assoc] using equalBinary_loss_identity hb hx hy

theorem removedLoss_paid (b x : ℕ) :
    (if b - x ≤ 1 then 0 else 1) ≤ ordinaryBadIndicator b x + singletonIndicator x := by
  unfold ordinaryBadIndicator singletonIndicator
  split_ifs <;> omega

theorem interiorLosses_removed (b : ℕ) (ls : List ℕ) :
    removedCount (interiorLosses b ls) ≤ ordinaryBadCount b ls + oneCount ls := by
  by_cases hlen : 2 ≤ ls.length
  swap
  · have hi : interiorLosses b ls = [] := by
      apply List.length_eq_zero_iff.mp
      rw [interiorLosses_length]
      omega
    simp [hi, removedCount]
  rw [removedCount_eq_sum, interiorLosses_length]
  have hlocal : ∀ i ∈ Finset.range (ls.length - 2),
      (if deficitAt (interiorLosses b ls) i ≤ 1 then 0 else 1) ≤
        ordinaryBadIndicator b (deficitAt ls (i + 1)) +
          singletonIndicator (deficitAt ls (i + 1)) := by
    intro i hi
    rw [interiorLosses_at b ls i (Finset.mem_range.mp hi)]
    exact removedLoss_paid b _
  have hs := Finset.sum_le_sum hlocal
  have h0 := nat_sum_range_shift_le
    (fun i => ordinaryBadIndicator b (deficitAt ls i)) ls.length 1 (ls.length - 2) (by omega)
  have h1 := nat_sum_range_shift_le
    (fun i => singletonIndicator (deficitAt ls i)) ls.length 1 (ls.length - 2) (by omega)
  have hB := sum_range_deficitAt (ordinaryBadIndicator b) ls
  have hW := sum_range_deficitAt singletonIndicator ls
  simp only [Finset.sum_add_distrib, Nat.add_comm 1] at *
  unfold ordinaryBadCount oneCount
  omega

/-- The paper's cut count follows from literal loss strings and the original
four-chain restriction.  No aggregate cut-count hypothesis remains. -/
theorem interior_alternation_cut_count {b R : ℕ} (hb : 1 ≤ b) (ls : List ℕ)
    (hbound : ∀ x ∈ ls, 1 ≤ x ∧ x ≤ b) (htrap : FourChainTrap b ls)
    (halt : BoundedAlternation (2 * R) (interiorLosses b ls)) :
    ls.length - 2 ≤ ordinaryBadCount b ls + oneCount ls +
      2 * R * (ordinaryBadCount b ls + 3 * oneCount ls + excessWitness b ls + 1) := by
  have hc := binary_string_count_uniform (interiorLosses b ls) halt
  rw [interiorLosses_length,
    interiorLosses_cuts hb ls (fun x hx => (hbound x hx).2)] at hc
  have hbnd := interiorLosses_removed b ls
  have hcuts := equal_cuts_paid hb ls hbound htrap
  have hremoved := Nat.mul_le_mul_left (2 * R) hbnd
  have hpaid := Nat.mul_le_mul_left (2 * R) hcuts
  nlinarith

theorem alternation_allowance_of_bounded_factors {b R : ℕ} (hb : 5 ≤ b)
    (hR : 1 ≤ R) (ls : List ℕ) (hq : 3 ≤ ls.length)
    (hbound : ∀ x ∈ ls, 1 ≤ x ∧ x ≤ b) (htrap : FourChainTrap b ls)
    (halt : BoundedAlternation (2 * R) (interiorLosses b ls)) :
    (ls.sum : ℚ) ≤ ((b : ℚ) + 3 / 2 + 1 / (4 * (R : ℚ))) +
      (((2 * (b : ℚ) - 1) - 1 / (2 * (R : ℚ))) / 2) *
        ((ls.length : ℚ) - 1) :=
  alternation_allowance_of_cut_count hb hR ls hq hbound htrap
    (interior_alternation_cut_count (by omega) ls hbound htrap halt)

theorem alternation_allowance_two {b R : ℕ} (hR : 1 ≤ R) (ls : List ℕ)
    (hq : ls.length = 2) (hbound : ∀ x ∈ ls, x ≤ b) :
    (ls.sum : ℚ) ≤ ((b : ℚ) + 3 / 2 + 1 / (4 * (R : ℚ))) +
      (((2 * (b : ℚ) - 1) - 1 / (2 * (R : ℚ))) / 2) *
        ((ls.length : ℚ) - 1) := by
  have hmass := sum_add_chain_deficits b ls hbound
  rw [hq] at hmass
  have hs : ls.sum ≤ 2 * b := by omega
  have hsQ : (ls.sum : ℚ) ≤ 2 * (b : ℚ) := by exact_mod_cast hs
  have hRQ : (0 : ℚ) < R := by exact_mod_cast (show 0 < R by omega)
  have hhalf : 1 / (2 * (R : ℚ)) = 2 * (1 / (4 * (R : ℚ))) := by
    field_simp [ne_of_gt hRQ] <;> ring
  rw [hq, hhalf]
  norm_num at hsQ ⊢
  linarith

theorem alternation_allowance_nontrivial {b R : ℕ} (hb : 5 ≤ b)
    (hR : 1 ≤ R) (ls : List ℕ) (hq : 2 ≤ ls.length)
    (hbound : ∀ x ∈ ls, 1 ≤ x ∧ x ≤ b) (htrap : FourChainTrap b ls)
    (halt : BoundedAlternation (2 * R) (interiorLosses b ls)) :
    (ls.sum : ℚ) ≤ ((b : ℚ) + 3 / 2 + 1 / (4 * (R : ℚ))) +
      (((2 * (b : ℚ) - 1) - 1 / (2 * (R : ℚ))) / 2) *
        ((ls.length : ℚ) - 1) := by
  by_cases hthree : 3 ≤ ls.length
  · exact alternation_allowance_of_bounded_factors hb hR ls hthree hbound htrap halt
  · exact alternation_allowance_two hR ls (by omega) (fun x hx => (hbound x hx).2)

end SuperpermutationLowerBound.Refinement.ChainReturns
