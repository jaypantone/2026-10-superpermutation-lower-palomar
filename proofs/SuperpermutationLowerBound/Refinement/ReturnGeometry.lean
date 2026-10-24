module

public import SuperpermutationLowerBound.Refinement.GeometryWordIndices
public import SuperpermutationLowerBound.Refinement.ReturnEntries

@[expose] public section

/-! Literal entries of regular cells in arbitrary alphabet coordinates. -/

namespace SuperpermutationLowerBound.Refinement

open PermutationVertex

noncomputable def shortEntry (n : ℕ) (hn : 7 ≤ n)
    (e : Fin (n + 1) ≃ Alphabet (n + 1)) : PermutationVertex (n + 1) :=
  coordinateVertex ((cellY n hn).trans e)

noncomputable def fullEntry (n : ℕ) (hn : 7 ≤ n)
    (e : Fin (n + 1) ≃ Alphabet (n + 1)) : PermutationVertex (n + 1) :=
  coordinateVertex ((cellU n hn).trans e)

@[simp] theorem shortEntry_word (n : ℕ) (hn : 7 ≤ n)
    (e : Fin (n + 1) ≃ Alphabet (n + 1)) :
    (shortEntry n hn e).1 = List.ofFn (fun i => e (cellY n hn i)) := rfl

@[simp] theorem fullEntry_word (n : ℕ) (hn : 7 ≤ n)
    (e : Fin (n + 1) ≃ Alphabet (n + 1)) :
    (fullEntry n hn e).1 = List.ofFn (fun i => e (cellU n hn i)) := rfl

@[simp] theorem shortEntry_get (n : ℕ) (hn : 7 ≤ n)
    (e : Fin (n + 1) ≃ Alphabet (n + 1)) (i : ℕ) (hi : i < n + 1) :
    (shortEntry n hn e).1[i]'(by simp only [PermutationVertex.length]; exact hi) =
      e (cellY n hn ⟨i, hi⟩) := by
  simp only [shortEntry, coordinateVertex_word, List.getElem_ofFn, Equiv.trans_apply]

@[simp] theorem fullEntry_get (n : ℕ) (hn : 7 ≤ n)
    (e : Fin (n + 1) ≃ Alphabet (n + 1)) (i : ℕ) (hi : i < n + 1) :
    (fullEntry n hn e).1[i]'(by simp only [PermutationVertex.length]; exact hi) =
      e (cellU n hn ⟨i, hi⟩) := by
  simp only [fullEntry, coordinateVertex_word, List.getElem_ofFn, Equiv.trans_apply]

/-- Every actual word admits these literal coordinates, with no quotient choice. -/
theorem shortEntry_normalize (n : ℕ) (hn : 7 ≤ n)
    (u : PermutationVertex (n + 1)) :
    shortEntry n hn ((cellY n hn).symm.trans (vertexCoordinates u)) = u := by
  unfold shortEntry
  rw [← Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.refl_trans]
  exact coordinateVertex_vertexCoordinates u

private theorem mod_before_end {n i : ℕ} (hn : 1 ≤ n) (hi : i < n) :
    (n - 1 + i) % n = if i = 0 then n - 1 else i - 1 := by
  by_cases hzero : i = 0
  · subst i
    simp [Nat.mod_eq_of_lt (show n - 1 < n by omega)]
  · have heq : n - 1 + i = n + (i - 1) := by omega
    rw [heq, if_neg hzero]
    simp [Nat.mod_eq_of_lt (show i - 1 < n by omega)]

/-- The regular satellite branch after a deficit-two run is exactly `u`,
in the same coordinates in which its short entry is `y`. -/
theorem deficitTwo_target_rot_normalized
    {n : ℕ} (hn : 7 ≤ n) {hk : 7 ≤ n + 1}
    {p : OverlapPath (n + 1)} {hp : IsBlockAligned p}
    {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment)
    (e : Fin (n + 1) ≃ Alphabet (n + 1))
    (hdeficit : R.deficit = 2) (hentry : R.entry = shortEntry n hn e) :
    R.target .rot = fullEntry n hn e := by
  have hlength : R.length = n - 2 := by
    have := R.length_add_deficit
    omega
  have htail : R.tail.length = n - 2 := by
    simpa using R.tail_length
  have hc1 : R.c1 = e ⟨n, by omega⟩ := by
    simp only [SatelliteContext.c1, SatelliteContext.rotatedCore, List.get_eq_getElem,
      List.getElem_rotate, List.length_dropLast, PermutationVertex.length,
      List.getElem_dropLast, hlength, hentry, shortEntry_word, List.getElem_ofFn,
      List.length_ofFn, Nat.add_sub_cancel]
    apply congrArg e
    apply Fin.ext
    simp only [cellY_apply_val, Nat.mod_eq_of_lt (show 0 + (n - 2 - 1) < n by omega),
      cellYValue]
    split_ifs <;> omega
  have hc2 : R.c2 = e ⟨2, by omega⟩ := by
    simp only [SatelliteContext.c2, SatelliteContext.rotatedCore, List.get_eq_getElem,
      List.getElem_rotate, List.length_dropLast, PermutationVertex.length,
      List.getElem_dropLast, hlength, hentry, shortEntry_word, List.getElem_ofFn,
      List.length_ofFn, Nat.add_sub_cancel]
    apply congrArg e
    apply Fin.ext
    simp only [cellY_apply_val, Nat.mod_eq_of_lt (show 1 + (n - 2 - 1) < n by omega),
      cellYValue]
    split_ifs <;> omega
  have hsat : R.satellite = e ⟨0, by omega⟩ := by
    simp only [SatelliteContext.satellite, entrySatellite, List.getLast_eq_getElem,
      PermutationVertex.length, hentry, shortEntry_word, List.getElem_ofFn,
      List.length_ofFn, Nat.add_sub_cancel]
    apply congrArg e
    apply Fin.ext
    simp only [cellY_apply_val, cellYValue]
    split_ifs <;> omega
  apply PermutationVertex.ext
  apply List.ext_getElem
  · simp [PermutationVertex.length]
  · intro i hi hj
    have hilim : i < n + 1 := by simpa [PermutationVertex.length] using hi
    simp only [R.target_word, SatelliteContext.targetSuffix]
    by_cases hicore : i < n - 2
    · rw [List.getElem_append_left (by omega)]
      simp only [SatelliteContext.tail, List.getElem_drop,
        SatelliteContext.rotatedCore, List.getElem_rotate, List.length_dropLast,
        PermutationVertex.length, List.getElem_dropLast, hlength, hentry,
        shortEntry_word, fullEntry_word, List.getElem_ofFn,
        List.length_ofFn, Nat.add_sub_cancel]
      apply congrArg e
      apply Fin.ext
      change cellYValue n ((2 + i + (n - 2 - 1)) % n) = cellUValue n i
      have hidx : 2 + i + (n - 2 - 1) = n - 1 + i := by omega
      rw [hidx, mod_before_end (by omega) (by omega)]
      simp only [cellYValue, cellUValue]
      split_ifs <;> omega
    · rw [List.getElem_append_right (by omega)]
      simp only [htail, hc1, hc2, hsat, fullEntry_word, List.getElem_ofFn]
      have hiCases : i = n - 2 ∨ i = n - 1 ∨ i = n := by omega
      rcases hiCases with heq | heq | heq <;> simp only [heq] <;>
        simp only [show n - 2 - (n - 2) = 0 by omega,
          show n - 1 - (n - 2) = 1 by omega,
          show n - (n - 2) = 2 by omega,
          List.getElem_cons_zero, List.getElem_cons_succ] <;>
        apply congrArg e <;> apply Fin.ext <;>
        simp only [cellU_apply_val, cellUValue] <;> split_ifs <;> omega

private theorem mod_rotate_near_end {n r i : ℕ} (hr : r ≤ n) (hi : i < n) :
    (n - r + i) % n = if i < r then n - r + i else i - r := by
  by_cases hir : i < r
  · rw [if_pos hir, Nat.mod_eq_of_lt (by omega)]
  · have heq : n - r + i = n + (i - r) := by omega
    rw [if_neg hir, heq]
    simp [Nat.mod_eq_of_lt (show i - r < n by omega)]

private theorem regular_transfer_core_value {n i : ℕ} (hn : 7 ≤ n) (hi : i < n - 1) :
    cellUValue n ((n - 3 + i) % (n - 1)) = cellGInverseValue n (cellYValue n i) := by
  rw [show n - 3 = (n - 1) - 2 by omega, mod_rotate_near_end (by omega) hi]
  unfold cellYValue
  split_ifs <;> first | omega | skip
  all_goals simp only [cellGInverseValue, cellUValue]
  all_goals split_ifs <;> omega

private theorem regular_transfer_tail_value {n i : ℕ} (hn : 7 ≤ n)
    (hi : i < n + 1) (htail : n - 1 ≤ i) :
    cellUValue n i = cellGInverseValue n (cellYValue n i) := by
  have hc : i = n - 1 ∨ i = n := by omega
  rcases hc with h | h
  · subst i
    have hy : cellYValue n (n - 1) = 1 := by unfold cellYValue; split_ifs <;> omega
    have hu : cellUValue n (n - 1) = n := by unfold cellUValue; split_ifs <;> omega
    rw [hy, hu]
    norm_num [cellGInverseValue]
  · subst i
    have hy : cellYValue n n = 0 := by unfold cellYValue; split_ifs <;> omega
    have hu : cellUValue n n = 0 := by unfold cellUValue; split_ifs <;> omega
    rw [hy, hu]
    norm_num [cellGInverseValue]

set_option maxHeartbeats 1000000 in
private theorem shortened_transfer_core_value {n i : ℕ} (hn : 7 ≤ n) (hi : i < n - 1) :
    cellUValue n ((n - 4 + i) % (n - 1)) =
      cellGInverseValue n (cellRhoInverseValue n (cellYValue n i)) := by
  rw [show n - 4 = (n - 1) - 3 by omega, mod_rotate_near_end (by omega) hi]
  unfold cellYValue
  split_ifs <;> first | omega | skip
  all_goals simp only [cellRhoInverseValue]
  all_goals split_ifs <;> first | omega | skip
  all_goals simp only [cellGInverseValue, cellUValue]
  all_goals split_ifs <;> omega

private theorem shortened_transfer_tail_value {n i : ℕ} (hn : 7 ≤ n)
    (hi : i < n + 1) (htail : n - 1 ≤ i) :
    cellUValue n i = cellGInverseValue n (cellRhoInverseValue n (cellYValue n i)) := by
  have hc : i = n - 1 ∨ i = n := by omega
  have hsame : cellRhoInverseValue n (cellYValue n i) = cellYValue n i := by
    rcases hc with h | h
    · have hy : cellYValue n (n - 1) = 1 := by unfold cellYValue; split_ifs <;> omega
      rw [h, hy]
      norm_num [cellRhoInverseValue]
    · have hy : cellYValue n n = 0 := by unfold cellYValue; split_ifs <;> omega
      rw [h, hy]
      norm_num [cellRhoInverseValue]
  rw [hsame]
  exact regular_transfer_tail_value hn hi htail

/-- Completing the `n-3` full runs of a regular cell changes coordinates by
`g⁻¹`. This is an equality of literal entries. -/
theorem regularCell_entry_transfer (n : ℕ) (hn : 7 ≤ n)
    (e : Fin (n + 1) ≃ Alphabet (n + 1)) :
    fullRunMapPower (by omega) (n - 3) (fullEntry n hn e) =
      shortEntry n hn ((cellG n hn).symm.trans e) := by
  apply PermutationVertex.ext
  apply List.ext_getElem
  · simp [PermutationVertex.length]
  · intro i hi hj
    have hilim : i < n + 1 := by simpa [PermutationVertex.length] using hi
    by_cases hicore : i < n - 1
    · have hget := fullRunMapPower_get_core (by omega : 3 ≤ n + 1)
        (fullEntry n hn e) (n - 3) i (by omega)
      simp only [show n + 1 - 2 = n - 1 by omega] at hget
      rw [hget]
      simp only [fullEntry_word, shortEntry_word, List.getElem_ofFn, Equiv.trans_apply]
      apply congrArg e
      apply Fin.ext
      change cellUValue n ((n - 3 + i) % (n - 1)) =
        cellGInverseValue n (cellYValue n i)
      exact regular_transfer_core_value hn hicore
    · have hget := fullRunMapPower_get_tail (by omega : 3 ≤ n + 1)
        (fullEntry n hn e) (n - 3) i hilim (by omega)
      rw [hget]
      simp only [fullEntry_word, shortEntry_word, List.getElem_ofFn, Equiv.trans_apply]
      apply congrArg e
      apply Fin.ext
      change cellUValue n i = cellGInverseValue n (cellYValue n i)
      exact regular_transfer_tail_value hn hilim (by omega)

/-- Completing the `n-4` full runs of a shortened cell changes coordinates
by `(ρg)⁻¹ = g⁻¹ρ⁻¹`. -/
theorem shortenedCell_entry_transfer (n : ℕ) (hn : 7 ≤ n)
    (e : Fin (n + 1) ≃ Alphabet (n + 1)) :
    fullRunMapPower (by omega) (n - 4) (fullEntry n hn e) =
      shortEntry n hn (((cellRho n hn * cellG n hn).symm).trans e) := by
  apply PermutationVertex.ext
  apply List.ext_getElem
  · simp [PermutationVertex.length]
  · intro i hi hj
    have hilim : i < n + 1 := by simpa [PermutationVertex.length] using hi
    by_cases hicore : i < n - 1
    · have hget := fullRunMapPower_get_core (by omega : 3 ≤ n + 1)
        (fullEntry n hn e) (n - 4) i (by omega)
      simp only [show n + 1 - 2 = n - 1 by omega] at hget
      rw [hget]
      simp only [fullEntry_word, shortEntry_word, List.getElem_ofFn, Equiv.trans_apply]
      apply congrArg e
      apply Fin.ext
      change cellUValue n ((n - 4 + i) % (n - 1)) =
        cellGInverseValue n (cellRhoInverseValue n (cellYValue n i))
      exact shortened_transfer_core_value hn hicore
    · have hget := fullRunMapPower_get_tail (by omega : 3 ≤ n + 1)
        (fullEntry n hn e) (n - 4) i hilim (by omega)
      rw [hget]
      simp only [fullEntry_word, shortEntry_word, List.getElem_ofFn, Equiv.trans_apply]
      apply congrArg e
      apply Fin.ext
      change cellUValue n i =
        cellGInverseValue n (cellRhoInverseValue n (cellYValue n i))
      exact shortened_transfer_tail_value hn hilim (by omega)

end SuperpermutationLowerBound.Refinement
