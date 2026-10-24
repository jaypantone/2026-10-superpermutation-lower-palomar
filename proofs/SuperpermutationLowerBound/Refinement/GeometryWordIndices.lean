module

public import SuperpermutationLowerBound.Refinement.GeometryIntervals

@[expose] public section

/-! Literal index formulas for the two run maps. -/

namespace SuperpermutationLowerBound.Refinement

open PermutationVertex

variable {k : ℕ}

def prefixRotateIndex (length cut shift i : ℕ) : ℕ :=
  if i < cut then (shift + i) % cut else i

theorem prefixRotateIndex_lt {length cut shift i : ℕ} (hc : cut ≤ length)
    (hi : i < length) : prefixRotateIndex length cut shift i < length := by
  unfold prefixRotateIndex
  split_ifs with h
  · exact (Nat.mod_lt _ (by omega)).trans_le hc
  · exact hi

theorem runMapPower_get_core (hk : 2 ≤ k) (u : PermutationVertex k)
    (t i : ℕ) (hi : i < k - 1) :
    (runMapPower (by omega) t u).1[i]'(by simpa [PermutationVertex.length] using
      (show i < k by omega)) =
      u.1[(t + i) % (k - 1)]'(by
        have := Nat.mod_lt (t + i) (show 0 < k - 1 by omega)
        simpa [u.length] using (show (t + i) % (k - 1) < k by omega)) := by
  simp only [runMapPower_word hk]
  rw [List.getElem_append_left (by simp [PermutationVertex.length]; omega)]
  simp only [List.getElem_rotate, List.length_dropLast, PermutationVertex.length,
    List.getElem_dropLast, Nat.add_comm]

theorem runMapPower_get_last (hk : 2 ≤ k) (u : PermutationVertex k) (t : ℕ) :
    (runMapPower (by omega) t u).1[k - 1]'(by simp [PermutationVertex.length]; omega) =
      u.1[k - 1]'(by simp [u.length]; omega) := by
  simp only [runMapPower_word hk]
  rw [List.getElem_append_right (by simp [PermutationVertex.length])]
  simp only [List.length_rotate, List.length_dropLast, PermutationVertex.length,
    Nat.sub_self, List.getElem_cons_zero]
  simp only [entrySatellite, List.getLast_eq_getElem, PermutationVertex.length]

theorem fullRunMapPower_get_core (hk : 3 ≤ k) (u : PermutationVertex k)
    (t i : ℕ) (hi : i < k - 2) :
    (fullRunMapPower hk t u).1[i]'(by simpa [PermutationVertex.length] using
      (show i < k by omega)) =
      u.1[(t + i) % (k - 2)]'(by
        have := Nat.mod_lt (t + i) (show 0 < k - 2 by omega)
        simpa [u.length] using (show (t + i) % (k - 2) < k by omega)) := by
  simp only [fullRunMapPower_word hk]
  rw [List.getElem_append_left (by simp [PermutationVertex.length]; omega)]
  simp only [List.getElem_rotate, List.length_take, PermutationVertex.length,
    Nat.min_eq_left (Nat.sub_le k 2), List.getElem_take, Nat.add_comm]

theorem fullRunMapPower_get_tail (hk : 3 ≤ k) (u : PermutationVertex k)
    (t i : ℕ) (hi : i < k) (htail : k - 2 ≤ i) :
    (fullRunMapPower hk t u).1[i]'(by simpa [PermutationVertex.length] using hi) =
      u.1[i]'(by simpa [u.length] using hi) := by
  simp only [fullRunMapPower_word hk]
  rw [List.getElem_append_right (by simp [PermutationVertex.length]; omega)]
  simp only [List.length_rotate, List.length_take, PermutationVertex.length,
    Nat.min_eq_left (Nat.sub_le k 2), List.getElem_drop,
    Nat.add_sub_of_le htail]

theorem runMapPower_coordinates (hk : 2 ≤ k) (u : PermutationVertex k)
    (t : ℕ) (i : Fin k) :
    vertexCoordinates (runMapPower (by omega) t u) i =
      vertexCoordinates u ⟨prefixRotateIndex k (k - 1) t i,
        prefixRotateIndex_lt (Nat.sub_le k 1) i.2⟩ := by
  by_cases hi : i.1 < k - 1
  · simpa only [vertexCoordinates_apply, prefixRotateIndex, if_pos hi] using
      runMapPower_get_core hk u t i.1 hi
  · have hieq : i.1 = k - 1 := by omega
    simp only [vertexCoordinates_apply, prefixRotateIndex, if_neg hi, hieq,
      lt_self_iff_false, if_false]
    exact runMapPower_get_last hk u t

theorem fullRunMapPower_coordinates (hk : 3 ≤ k) (u : PermutationVertex k)
    (t : ℕ) (i : Fin k) :
    vertexCoordinates (fullRunMapPower hk t u) i =
      vertexCoordinates u ⟨prefixRotateIndex k (k - 2) t i,
        prefixRotateIndex_lt (Nat.sub_le k 2) i.2⟩ := by
  by_cases hi : i.1 < k - 2
  · simpa only [vertexCoordinates_apply, prefixRotateIndex, if_pos hi] using
      fullRunMapPower_get_core hk u t i.1 hi
  · simpa only [vertexCoordinates_apply, prefixRotateIndex, if_neg hi] using
      fullRunMapPower_get_tail hk u t i.1 i.2 (by omega)

theorem rotationPower_coordinates (hk : 1 ≤ k) (u : PermutationVertex k)
    (t : ℕ) (i : Fin k) :
    vertexCoordinates (rotationPower t u) i =
      vertexCoordinates u ⟨(t + i) % k, Nat.mod_lt _ (by omega)⟩ := by
  simp only [vertexCoordinates_apply, rotationPower_word hk, List.getElem_rotate,
    PermutationVertex.length, Nat.add_comm]

end SuperpermutationLowerBound.Refinement
