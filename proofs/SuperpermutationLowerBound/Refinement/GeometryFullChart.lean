module

public import SuperpermutationLowerBound.Refinement.GeometryWordIndices

@[expose] public section

/-! The three surviving targets at an actual full-run boundary. -/

namespace SuperpermutationLowerBound.Refinement

open PermutationVertex

variable {k : ℕ}

theorem vertex_chart_split (hk : 7 ≤ k) (u : PermutationVertex k) :
    ∃ a rest b c, rest.length = k - 3 ∧ u.1 = a :: rest ++ [b, c] := by
  let pre := u.1.take (k - 2)
  let tail := u.1.drop (k - 2)
  have hpreLength : pre.length = k - 2 := by
    simp [pre, PermutationVertex.length]
  have htailLength : tail.length = 2 := by
    simp [tail, PermutationVertex.length]
    omega
  cases hpreEq : pre with
  | nil => simp [hpreEq] at hpreLength; omega
  | cons a rest =>
      obtain ⟨b, c, htail⟩ := List.length_eq_two.mp htailLength
      refine ⟨a, rest, b, c, ?_, ?_⟩
      · rw [hpreEq] at hpreLength
        simp at hpreLength
        omega
      · calc
          u.1 = u.1.take (k - 2) ++ u.1.drop (k - 2) :=
            (u.1.take_append_drop (k - 2)).symm
          _ = a :: rest ++ [b, c] := by
            change pre ++ tail = _
            rw [hpreEq, htail]

def fullChart2Index (k i : ℕ) : ℕ :=
  if i < k - 3 then i + 1 else if i = k - 3 then 0
  else if i = k - 2 then k - 1 else k - 2

def fullChart5Index (k i : ℕ) : ℕ :=
  if i < k - 3 then i + 1 else if i = k - 3 then k - 1
  else if i = k - 2 then 0 else k - 2

theorem fullChart2Index_lt (hk : 7 ≤ k) {i : ℕ} (hi : i < k) :
    fullChart2Index k i < k := by unfold fullChart2Index; split_ifs <;> omega

theorem fullChart5Index_lt (hk : 7 ≤ k) {i : ℕ} (hi : i < k) :
    fullChart5Index k i < k := by unfold fullChart5Index; split_ifs <;> omega

theorem fullRunChartTarget2_coordinates (hk : 7 ≤ k) (u : PermutationVertex k)
    (i : Fin k) :
    vertexCoordinates (fullRunChartTarget2 hk u) i =
      vertexCoordinates u ⟨fullChart2Index k i, fullChart2Index_lt hk i.2⟩ := by
  obtain ⟨a, rest, b, c, hrest, hu⟩ := vertex_chart_split hk u
  have hw := (fullRunChart_target_words_of_split hk u a b c rest hrest hu).2.1
  by_cases hcore : i.1 < k - 3
  · simp only [vertexCoordinates_apply, hw, fullChart2Index, if_pos hcore, hu,
      List.cons_append, List.getElem_cons_succ]
    rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega)]
  · have hi : i.1 = k - 3 ∨ i.1 = k - 2 ∨ i.1 = k - 1 := by omega
    rcases hi with hi | hi | hi <;>
      simp only [vertexCoordinates_apply, hw, hu, fullChart2Index, if_neg hcore,
        hi, List.cons_append] <;>
      simp only [show ¬k - 3 = k - 2 by omega, show ¬k - 1 = k - 3 by omega,
        show ¬k - 1 = k - 2 by omega, show ¬k - 2 = k - 3 by omega,
        if_true, if_false, List.getElem_cons_zero] <;>
      simp only [List.getElem_append, hrest] <;>
      split_ifs <;> try omega
    all_goals simp only [show k - 3 - (k - 3) = 0 by omega,
      show k - 2 - (k - 3) = 1 by omega, show k - 1 - (k - 3) = 2 by omega,
      List.getElem_cons_zero, List.getElem_cons_succ]
    all_goals simp only [show k - 1 = (k - 2) + 1 by omega,
      show k - 2 = (k - 3) + 1 by omega, List.getElem_cons_succ,
      List.getElem_append, hrest] <;> split_ifs <;> first | rfl | omega | simp_all

theorem fullRunChartTarget5_coordinates (hk : 7 ≤ k) (u : PermutationVertex k)
    (i : Fin k) :
    vertexCoordinates (fullRunChartTarget5 hk u) i =
      vertexCoordinates u ⟨fullChart5Index k i, fullChart5Index_lt hk i.2⟩ := by
  obtain ⟨a, rest, b, c, hrest, hu⟩ := vertex_chart_split hk u
  have hw := (fullRunChart_target_words_of_split hk u a b c rest hrest hu).2.2.2.2.1
  by_cases hcore : i.1 < k - 3
  · simp only [vertexCoordinates_apply, hw, fullChart5Index, if_pos hcore, hu,
      List.cons_append, List.getElem_cons_succ]
    rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega)]
  · have hi : i.1 = k - 3 ∨ i.1 = k - 2 ∨ i.1 = k - 1 := by omega
    rcases hi with hi | hi | hi <;>
      simp only [vertexCoordinates_apply, hw, hu, fullChart5Index, if_neg hcore,
        hi, List.cons_append] <;>
      simp only [show ¬k - 3 = k - 2 by omega, show ¬k - 1 = k - 3 by omega,
        show ¬k - 1 = k - 2 by omega, show ¬k - 2 = k - 3 by omega,
        if_true, if_false, List.getElem_cons_zero] <;>
      simp only [List.getElem_append, hrest] <;>
      split_ifs <;> try omega
    all_goals simp only [show k - 3 - (k - 3) = 0 by omega,
      show k - 2 - (k - 3) = 1 by omega, show k - 1 - (k - 3) = 2 by omega,
      List.getElem_cons_zero, List.getElem_cons_succ]
    all_goals simp only [show k - 1 = (k - 2) + 1 by omega,
      show k - 2 = (k - 3) + 1 by omega, List.getElem_cons_succ,
      List.getElem_append, hrest] <;> split_ifs <;> first | rfl | omega | simp_all

theorem actualFullBoundary_threeTargets (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (j : ℕ) (hj : j + 1 < (blockAlignedRuns hk p hp).length)
    (hfull : (blockAlignedRunAt hk p hp ⟨j, by omega⟩).IsFull)
    (hlight : IsLightRunBoundary
      (blockAlignedRunAt hk p hp ⟨j, by omega⟩).blocks
      (blockAlignedRunAt hk p hp ⟨j + 1, hj⟩).blocks) :
    let left := blockAlignedRunAt hk p hp ⟨j, by omega⟩
    let right := blockAlignedRunAt hk p hp ⟨j + 1, hj⟩
    right.entry = fullRunMap (by omega) left.entry ∨
      right.entry = fullRunChartTarget2 hk left.entry ∨
      right.entry = fullRunChartTarget5 hk left.entry := by
  dsimp only
  let left := blockAlignedRunAt hk p hp ⟨j, by omega⟩
  let right := blockAlignedRunAt hk p hp ⟨j + 1, hj⟩
  change right.entry = fullRunMap (by omega) left.entry ∨
    right.entry = fullRunChartTarget2 hk left.entry ∨
    right.entry = fullRunChartTarget5 hk left.entry
  have hfullLeft : left.IsFull := hfull
  have hleftLength : left.length = k - 1 := hfullLeft
  have hleftNonempty : left.blocks ≠ [] := List.ne_nil_of_mem_splitBy left.isRun
  have hrightNonempty : right.blocks ≠ [] := List.ne_nil_of_mem_splitBy right.isRun
  have hweight : overlapWeight (blockExit left.lastEntry) right.entry = 3 := by
    have hraw : runBoundaryWeight left.blocks right.blocks = 3 := hlight
    simpa only [runBoundaryWeight, List.getLast?_eq_some_getLast hleftNonempty,
      List.head?_eq_some_head hrightNonempty, BlockAlignedRun.lastEntry,
      BlockAlignedRun.entry] using hraw
  have hchartWeight :
      overlapWeight (fullRunChartExit hk left.entry) right.entry = 3 := by
    rw [fullRunChart_lastEntry hk p hp left hfullLeft] at hweight
    exact hweight
  have htargets :=
    (fullRunChart_weightThree_successors hk left.entry right.entry).mp hchartWeight
  rw [fullRunChartTargets_eq_named] at htargets
  simp only [List.mem_cons, List.not_mem_nil, or_false] at htargets
  have hne {x : PermutationVertex k} (hx : x ∈ left.blocks) :
      rotationClass x ≠ rotationClass right.entry :=
    actualRuns_rotationClasses_ne hk p hp j (j + 1) (by omega) hj (by omega)
      hx (List.head_mem hrightNonempty)
  rcases htargets with h1 | h2 | h3 | h4 | h5 | h6
  · exact Or.inl (h1.trans (fullRunChart_target1_eq_fullRunMap hk left.entry))
  · exact Or.inr (Or.inl h2)
  · have hi : 1 < left.length := by omega
    have heq : left.blocks.get ⟨1, hi⟩ = runMap (by omega) left.entry := by
      simpa [runMapPower] using blockAlignedRun_entrySequence hk p hp left 1 hi
    have hcollision : rotationClass (left.blocks.get ⟨1, hi⟩) =
        rotationClass right.entry := by
      rw [heq, h3, fullRunChart_target3_eq_runMap]
    exact (hne (List.get_mem _ _) hcollision).elim
  · have hcollision : rotationClass left.entry = rotationClass right.entry := by
      rw [h4, fullRunChart_target4_eq_rotation]
      simpa [rotationPower] using (rotationClass_rotationPower (by omega) 1 left.entry).symm
    exact (hne (List.head_mem hleftNonempty) hcollision).elim
  · exact Or.inr (Or.inr h5)
  · have hcollision : rotationClass left.lastEntry = rotationClass right.entry := by
      rw [h6, fullRunChart_target6_eq_rotationPower_lastEntry,
        rotationClass_rotationPower (by omega),
        fullRunChart_lastEntry hk p hp left hfullLeft]
    exact (hne (List.getLast_mem hleftNonempty) hcollision).elim

end SuperpermutationLowerBound.Refinement
