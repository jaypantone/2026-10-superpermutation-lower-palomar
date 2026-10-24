module

public import pairs.SquareComparison
public import SuperpermutationLowerBound.Refinement.ReturnGeometry

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

open PermutationVertex

set_option maxHeartbeats 1000000

private theorem near_end_mod {n q i : ℕ} (hq : q ≤ n) (hi : i < n) :
    (n-q+i) % n = if i < q then n-q+i else i-q := by
  by_cases h : i < q
  · rw [if_pos h, Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg h, show n-q+i = n + (i-q) by omega]
    simp [Nat.mod_eq_of_lt (show i-q < n by omega)]

theorem square_full_core_value {n i : ℕ} (hn : 8 ≤ n) (hi : i < n-1) :
    squareComparisonValue n (cellUValue n ((n-4+i) % (n-1))) =
      cellUValue n ((n-2+i) % n) := by
  have hleft : (n-4+i) % (n-1) = if i < 3 then n-4+i else i-3 := by
    simpa only [show n-1-3 = n-4 by omega] using
      near_end_mod (n := n-1) (q := 3) (by omega) hi
  have hright := near_end_mod (n := n) (q := 2) (by omega) (show i<n by omega)
  rw [hleft, hright]
  split_ifs <;> try omega
  all_goals conv_lhs => arg 2; unfold cellUValue
  all_goals split_ifs <;> try (first | contradiction | omega)
  all_goals simp only [squareComparisonValue, cellUValue]
  all_goals split_ifs <;> (first | contradiction | omega)

theorem square_full_coordinates_value {n i : ℕ} (hn : 8 ≤ n) (hi : i < n+1) :
    squareComparisonValue n
      (cellUValue n (prefixRotateIndex (n+1) (n+1-2) (n-4) i)) =
      cellUValue n (prefixRotateIndex (n+1) (n+1-1) (n-2) i) := by
  have hcut : n+1-2 = n-1 := by omega
  simp only [prefixRotateIndex, hcut, Nat.add_sub_cancel]
  by_cases h : i < n-1
  · rw [if_pos h, if_pos (show i<n by omega)]
    exact square_full_core_value hn h
  · rw [if_neg h]
    by_cases he : i = n-1
    · subst i
      rw [if_pos (show n-1<n by omega)]
      have hmod : (n-2+(n-1)) % n = n-3 := by
        have hh := near_end_mod (n := n) (q := 2) (i := n-1) (by omega) (by omega)
        rw [if_neg (by omega)] at hh
        simpa only [show n-1-2 = n-3 by omega] using hh
      rw [hmod]
      have hu : cellUValue n (n-1) = n := by
        unfold cellUValue; split_ifs <;> omega
      rw [hu]
      unfold squareComparisonValue cellUValue
      split_ifs <;> omega
    · have he : i = n := by omega
      subst i
      rw [if_neg (by omega)]
      have hu : cellUValue n n = 0 := by
        unfold cellUValue; split_ifs <;> omega
      rw [hu]
      simp [squareComparisonValue]

/-- The two full-run entries coincide after a permitted shift in the first
full run. This is literal equality of words, stronger than equality of cores. -/
theorem square_full_entry (m : ℕ) (hm : 2 ≤ m) (hn : 7 ≤ 3*m+2)
    (e : Fin (3*m+2+1) ≃ Alphabet (3*m+2+1)) :
    fullRunMapPower (by omega) (3*m+2-4)
      (fullEntry (3*m+2) hn
        ((cellG (3*m+2) hn ^ m * cellRho (3*m+2) hn *
          (cellG (3*m+2) hn)⁻¹ * cellRho (3*m+2) hn *
          cellG (3*m+2) hn ^ (m+2)).trans e)) =
      runMapPower (by omega) (3*m+2-2) (fullEntry (3*m+2) hn e) := by
  have hc : vertexCoordinates
      (fullRunMapPower (by omega) (3*m+2-4)
        (fullEntry (3*m+2) hn
          ((cellG (3*m+2) hn ^ m * cellRho (3*m+2) hn *
            (cellG (3*m+2) hn)⁻¹ * cellRho (3*m+2) hn *
            cellG (3*m+2) hn ^ (m+2)).trans e))) =
      vertexCoordinates (runMapPower (by omega) (3*m+2-2)
        (fullEntry (3*m+2) hn e)) := by
    apply Equiv.ext
    intro i
    rw [fullRunMapPower_coordinates (by omega), runMapPower_coordinates (by omega)]
    simp only [fullEntry, vertexCoordinates_coordinateVertex, Equiv.trans_apply]
    apply congrArg e
    apply Fin.ext
    rw [squareComparison_apply m hm hn, cellU_apply_val, cellU_apply_val]
    exact square_full_coordinates_value (by omega) i.isLt
  have he := congrArg coordinateVertex hc
  simpa only [coordinateVertex_vertexCoordinates] using he

end SuperpermutationLowerBound.Refinement
