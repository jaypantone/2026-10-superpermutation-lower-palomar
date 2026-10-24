module

public import SuperpermutationLowerBound.Refinement.ReturnGeometry
public import SuperpermutationLowerBound.Refinement.GeometryFullChart

@[expose] public section

/-! The delayed old-short-row collisions that force cell exits. -/

namespace SuperpermutationLowerBound.Refinement

open PermutationVertex

private theorem rem_lt_twice {x n : ℕ} (hn : 0 < n) (hx : x < 2 * n) :
    x % n = if x < n then x else x - n := by
  by_cases h : x < n
  · simp [h, Nat.mod_eq_of_lt h]
  · have heq : x = n + (x - n) := by omega
    rw [if_neg h, heq]
    simp [Nat.mod_eq_of_lt (show x - n < n by omega)]

private theorem rem_near_end {n r i : ℕ} (hr : r ≤ n) (hi : i < n) :
    (n - r + i) % n = if i < r then n - r + i else i - r := by
  by_cases hir : i < r
  · rw [if_pos hir, Nat.mod_eq_of_lt (by omega)]
  · have heq : n - r + i = n + (i - r) := by omega
    rw [if_neg hir, heq]
    simp [Nat.mod_eq_of_lt (show i - r < n by omega)]

private def lastFullValue (n d i : ℕ) : ℕ :=
  if i < d + 1 then n - d - 1 + i
  else if i = d + 1 then 2 else if i = d + 2 then 1
  else if i < n - 1 then i - d else if i = n - 1 then n else 0

private theorem lastFullValue_eq {n d i : ℕ} (hn : 7 ≤ n)
    (hd1 : 1 ≤ d) (hd2 : d ≤ 2) (hi : i < n + 1) :
    cellUValue n (prefixRotateIndex (n + 1) (n - 1) (n - 3 - d) i) =
      lastFullValue n d i := by
  unfold prefixRotateIndex
  split_ifs with hcore
  · rw [show n - 3 - d = (n - 1) - (d + 2) by omega,
      rem_near_end (by omega) hcore]
    split_ifs <;> unfold cellUValue lastFullValue <;> split_ifs <;> omega
  · unfold cellUValue lastFullValue
    split_ifs <;> omega

private def collisionValue (n r i : ℕ) : ℕ :=
  if i = 0 then 2 else if i = 1 then 1 else if i < n - r then i + 1
  else if i = n - r then 0 else i

private theorem rotatedShortValue_eq {n r i : ℕ} (hn : 7 ≤ n)
    (hr1 : 2 ≤ r) (hr2 : r ≤ 4) (hi : i < n + 1) :
    cellYValue n (prefixRotateIndex (n + 1) n (n - r - 2)
      ((r + i) % (n + 1))) = collisionValue n r i := by
  have hmod : (r + i) % (n + 1) =
      if r + i < n + 1 then r + i else r + i - (n + 1) :=
    rem_lt_twice (by omega) (by omega)
  rw [hmod]
  split_ifs with hwrap
  · unfold prefixRotateIndex
    split_ifs with hcore
    · have hsum : n - r - 2 + (r + i) = n - 2 + i := by omega
      rw [hsum, rem_near_end (by omega) (by omega)]
      split_ifs <;> unfold cellYValue collisionValue <;> split_ifs <;> omega
    · have hieq : i = n - r := by omega
      have heq : r + i = n := by omega
      rw [heq]
      have hy : cellYValue n n = 0 := by unfold cellYValue; split_ifs <;> omega
      rw [hy]
      unfold collisionValue
      split_ifs <;> omega
  · have hcore : r + i - (n + 1) < n := by omega
    simp only [prefixRotateIndex, if_pos hcore]
    have hsum : n - r - 2 + (r + i - (n + 1)) = i - 3 := by omega
    rw [hsum, Nat.mod_eq_of_lt (by omega)]
    unfold cellYValue collisionValue
    split_ifs <;> omega

private theorem chart2_collision_value {n d i : ℕ} (hn : 7 ≤ n)
    (hd1 : 1 ≤ d) (hd2 : d ≤ 2) (hi : i < n + 1) :
    lastFullValue n d
      (fullChart2Index (n + 1) (prefixRotateIndex (n + 1) n d i)) =
      collisionValue n (d + 1) i := by
  unfold prefixRotateIndex
  split_ifs with hcore
  · rw [rem_lt_twice (by omega) (by omega)]
    split_ifs <;> first | omega | skip
    all_goals unfold fullChart2Index
    all_goals split_ifs <;> first | omega | skip
    all_goals unfold lastFullValue
    all_goals split_ifs <;> first | omega | skip
    all_goals unfold collisionValue
    all_goals split_ifs <;> omega
  · have hieq : i = n := by omega
    subst i
    unfold fullChart2Index
    split_ifs <;> first | omega | skip
    all_goals unfold lastFullValue
    all_goals split_ifs <;> first | omega | skip
    all_goals unfold collisionValue
    all_goals split_ifs <;> omega

private theorem chart5_collision_value {n d i : ℕ} (hn : 7 ≤ n)
    (hd1 : 1 ≤ d) (hd2 : d ≤ 2) (hi : i < n + 1) :
    lastFullValue n d
      (fullChart5Index (n + 1) (prefixRotateIndex (n + 1) n d i)) =
      collisionValue n (d + 2) i := by
  unfold prefixRotateIndex
  split_ifs with hcore
  · rw [rem_lt_twice (by omega) (by omega)]
    split_ifs <;> first | omega | skip
    all_goals unfold fullChart5Index
    all_goals split_ifs <;> first | omega | skip
    all_goals unfold lastFullValue
    all_goals split_ifs <;> first | omega | skip
    all_goals unfold collisionValue
    all_goals split_ifs <;> omega
  · have hieq : i = n := by omega
    subst i
    unfold fullChart5Index
    split_ifs <;> first | omega | skip
    all_goals unfold lastFullValue
    all_goals split_ifs <;> first | omega | skip
    all_goals unfold collisionValue
    all_goals split_ifs <;> omega

theorem vertex_eq_of_coordinates_eq {k : ℕ} {u v : PermutationVertex k}
    (h : ∀ i, vertexCoordinates u i = vertexCoordinates v i) : u = v := by
  have heq : vertexCoordinates u = vertexCoordinates v := Equiv.ext h
  have := congrArg coordinateVertex heq
  simpa only [coordinateVertex_vertexCoordinates] using this

/-- Target 2 collides after one block for C and two blocks for B. -/
theorem cell_exit_target2_collision (n : ℕ) (hn : 7 ≤ n) (d : ℕ)
    (hd1 : 1 ≤ d) (hd2 : d ≤ 2)
    (e : Fin (n + 1) ≃ Alphabet (n + 1)) :
    runMapPower (by omega) d
      (fullRunChartTarget2 (by omega)
        (fullRunMapPower (by omega) (n - 3 - d) (fullEntry n hn e))) =
      rotationPower (d + 1)
        (runMapPower (by omega) (n - d - 3) (shortEntry n hn e)) := by
  apply vertex_eq_of_coordinates_eq
  intro i
  rw [runMapPower_coordinates, fullRunChartTarget2_coordinates,
    fullRunMapPower_coordinates, rotationPower_coordinates, runMapPower_coordinates]
  simp only [fullEntry, shortEntry, vertexCoordinates_coordinateVertex, Equiv.trans_apply]
  apply congrArg e
  apply Fin.ext
  change cellUValue n
      (prefixRotateIndex (n + 1) (n + 1 - 2) (n - 3 - d)
        (fullChart2Index (n + 1) (prefixRotateIndex (n + 1) (n + 1 - 1) d i.1))) =
    cellYValue n (prefixRotateIndex (n + 1) (n + 1 - 1) (n - d - 3)
      ((d + 1 + i.1) % (n + 1)))
  simp only [Nat.add_sub_cancel, show n + 1 - 2 = n - 1 by omega]
  rw [lastFullValue_eq hn hd1 hd2
    (fullChart2Index_lt (by omega)
      (prefixRotateIndex_lt (by omega) i.2))]
  rw [show n - d - 3 = n - (d + 1) - 2 by omega,
    rotatedShortValue_eq hn (by omega) (by omega) i.2]
  exact chart2_collision_value hn hd1 hd2 i.2
  all_goals omega

/-- Target 5 collides at the same short exit threshold. -/
theorem cell_exit_target5_collision (n : ℕ) (hn : 7 ≤ n) (d : ℕ)
    (hd1 : 1 ≤ d) (hd2 : d ≤ 2)
    (e : Fin (n + 1) ≃ Alphabet (n + 1)) :
    runMapPower (by omega) d
      (fullRunChartTarget5 (by omega)
        (fullRunMapPower (by omega) (n - 3 - d) (fullEntry n hn e))) =
      rotationPower (d + 2)
        (runMapPower (by omega) (n - d - 4) (shortEntry n hn e)) := by
  apply vertex_eq_of_coordinates_eq
  intro i
  rw [runMapPower_coordinates, fullRunChartTarget5_coordinates,
    fullRunMapPower_coordinates, rotationPower_coordinates, runMapPower_coordinates]
  simp only [fullEntry, shortEntry, vertexCoordinates_coordinateVertex, Equiv.trans_apply]
  apply congrArg e
  apply Fin.ext
  change cellUValue n
      (prefixRotateIndex (n + 1) (n + 1 - 2) (n - 3 - d)
        (fullChart5Index (n + 1) (prefixRotateIndex (n + 1) (n + 1 - 1) d i.1))) =
    cellYValue n (prefixRotateIndex (n + 1) (n + 1 - 1) (n - d - 4)
      ((d + 2 + i.1) % (n + 1)))
  simp only [Nat.add_sub_cancel, show n + 1 - 2 = n - 1 by omega]
  rw [lastFullValue_eq hn hd1 hd2
    (fullChart5Index_lt (by omega)
      (prefixRotateIndex_lt (by omega) i.2))]
  rw [show n - d - 4 = n - (d + 2) - 2 by omega,
    rotatedShortValue_eq hn (by omega) (by omega) i.2]
  exact chart5_collision_value hn hd1 hd2 i.2
  all_goals omega

end SuperpermutationLowerBound.Refinement
