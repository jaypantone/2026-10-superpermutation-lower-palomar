module

public import SuperpermutationLowerBound.Refinement.ReflectionBasic
public import SuperpermutationLowerBound.Refinement.ReflectionLists

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

open PermutationVertex

variable {k : ℕ}

theorem blockSequencePath_aligned (hk : 7 ≤ k) (entries : List (PermutationVertex k))
    (hne : entries ≠ []) (hclasses : PairwiseDistinctRotationClasses entries) :
    IsBlockAligned (blockSequencePath (by omega) entries hne hclasses) := by
  refine ⟨(blockSequencePath_stronglyExitless (by omega) entries hne hclasses).1, ?_⟩
  rw [blockSequencePath_length]
  exact dvd_mul_right _ _

theorem blockSequencePath_entries (hk : 7 ≤ k) (entries : List (PermutationVertex k))
    (hne : entries ≠ []) (hclasses : PairwiseDistinctRotationClasses entries) :
    blockAlignedBlockEntries hk (blockSequencePath (by omega) entries hne hclasses)
      (blockSequencePath_aligned hk entries hne hclasses) = entries := by
  let Q := blockSequencePath (by omega : 1 ≤ k) entries hne hclasses
  have hcount : pathBlockCount Q = entries.length := by
    unfold pathBlockCount
    rw [show Q.length = k * entries.length by exact blockSequencePath_length _ _ _ _]
    exact Nat.mul_div_cancel_left entries.length (by omega)
  apply List.ext_get
  · rw [blockAlignedBlockEntries_length]
    exact hcount
  · intro i hiLeft hiRight
    have hi : i < entries.length := hiRight
    have hiQ : i < pathBlockCount Q := by omega
    rw [blockAlignedBlockEntry_eq_vertex hk Q
      (blockSequencePath_aligned hk entries hne hclasses) i hiQ]
    change (blockSequenceVertices (by omega) entries).get
      ⟨k * i, by simp; exact Nat.mul_lt_mul_of_pos_left hi (by omega)⟩ = _
    simp only [List.get_eq_getElem]
    rw [blockSequenceVertices_getElem (by omega) entries (k * i) (by
      exact Nat.mul_lt_mul_of_pos_left hi (by omega)), Nat.mul_mod_right]
    simp only [rotationPower_zero]
    change entries.get _ = entries.get _
    apply congrArg entries.get
    apply Fin.ext
    exact Nat.mul_div_cancel_left i (by omega)

theorem reflectEntries_distinct (hk : 1 ≤ k) (entries : List (PermutationVertex k))
    (hclasses : PairwiseDistinctRotationClasses entries) :
    PairwiseDistinctRotationClasses (reflectList reflectEntry entries) := by
  unfold PairwiseDistinctRotationClasses reflectList
  rw [List.pairwise_map, List.pairwise_reverse]
  apply hclasses.imp
  intro u v huv hsame
  exact huv ((reflectEntry_class_iff hk v u).mp hsame).symm

/-- Reverse traversal and reverse every permutation word. The entry formula
is `reverse(blockExit oldEntry)`, and complete-block expansion keeps the path
inside the accepted block-aligned universe. -/
noncomputable def reflectedPath (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p) :
    OverlapPath k :=
  blockSequencePath (by omega)
    (reflectList reflectEntry (blockAlignedBlockEntries hk p hp))
    (by simpa using blockAlignedBlockEntries_nonempty hk p hp)
    (reflectEntries_distinct (by omega) _ (blockAlignedBlockEntries_pairwiseDistinct hk p hp))

theorem reflectedPath_aligned (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p) :
    IsBlockAligned (reflectedPath hk p hp) := blockSequencePath_aligned hk _ _ _

theorem reflectedPath_entries (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p) :
    blockAlignedBlockEntries hk (reflectedPath hk p hp) (reflectedPath_aligned hk p hp) =
      reflectList reflectEntry (blockAlignedBlockEntries hk p hp) :=
  blockSequencePath_entries hk _ _ _

theorem isWeightTwoBoundary_reflect (hk : 1 ≤ k) (u v : PermutationVertex k) :
    isWeightTwoBoundary (reflectEntry v) (reflectEntry u) = isWeightTwoBoundary u v := by
  unfold isWeightTwoBoundary
  rw [reflectEntry_boundary_weight hk]

theorem reflectedPath_runs (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p) :
    blockAlignedRuns hk (reflectedPath hk p hp) (reflectedPath_aligned hk p hp) =
      reflectList (reflectList reflectEntry) (blockAlignedRuns hk p hp) := by
  unfold blockAlignedRuns weightTwoRuns
  rw [reflectedPath_entries]
  exact splitBy_reflectList reflectEntry isWeightTwoBoundary isWeightTwoBoundary
    (isWeightTwoBoundary_reflect (by omega)) _

theorem runBoundaryWeight_reflect (hk : 1 ≤ k) (xs ys : List (PermutationVertex k)) :
    runBoundaryWeight (reflectList reflectEntry ys) (reflectList reflectEntry xs) =
      runBoundaryWeight xs ys := by
  by_cases hx : xs = []
  · subst xs
    simp [runBoundaryWeight, reflectList]
  by_cases hy : ys = []
  · subst ys
    simp [runBoundaryWeight, reflectList]
  have hx' : reflectList reflectEntry xs ≠ [] := by simpa using hx
  have hy' : reflectList reflectEntry ys ≠ [] := by simpa using hy
  simp only [runBoundaryWeight, List.getLast?_eq_some_getLast hx,
    List.head?_eq_some_head hy, List.getLast?_eq_some_getLast hy',
    List.head?_eq_some_head hx', reflectList_getLast, reflectList_head,
    reflectEntry_boundary_weight hk]

theorem isLightRunBoundary_reflect (hk : 1 ≤ k) (xs ys : List (PermutationVertex k)) :
    isLightRunBoundary (reflectList reflectEntry ys) (reflectList reflectEntry xs) =
      isLightRunBoundary xs ys := by
  unfold isLightRunBoundary IsLightRunBoundary
  rw [runBoundaryWeight_reflect hk]

theorem reflectedPath_segments (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p) :
    blockAlignedLightSegments hk (reflectedPath hk p hp) (reflectedPath_aligned hk p hp) =
      reflectList (reflectList (reflectList reflectEntry)) (blockAlignedLightSegments hk p hp) := by
  unfold blockAlignedLightSegments
  rw [reflectedPath_runs]
  exact splitBy_reflectList (reflectList reflectEntry) isLightRunBoundary isLightRunBoundary
    (isLightRunBoundary_reflect (by omega)) _

/-- Every actual light segment has a reflected actual light segment. -/
noncomputable def reflectedSegment (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p)
    (s : BlockAlignedLightSegment hk p hp) :
    BlockAlignedLightSegment hk (reflectedPath hk p hp) (reflectedPath_aligned hk p hp) where
  runs := reflectList (reflectList reflectEntry) s.runs
  isSegment := by
    rw [reflectedPath_segments]
    apply List.mem_map.mpr
    exact ⟨s.runs, by simpa using s.isSegment, rfl⟩

@[simp] theorem reflectedSegment_deficitString (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) (s : BlockAlignedLightSegment hk p hp) :
    (reflectedSegment hk p hp s).deficitString = s.deficitString.reverse := by
  simp [BlockAlignedLightSegment.deficitString, reflectedSegment, reflectList, List.map_map]

end SuperpermutationLowerBound.Refinement
