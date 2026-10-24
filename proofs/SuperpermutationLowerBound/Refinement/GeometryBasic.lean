module

public import SuperpermutationLowerBound.Section05.LegalDeficits

@[expose] public section

/-!
Actual-run interfaces for the refined return geometry. No abstract word
realization is assumed here: every entry belongs to the given block-aligned
path, so a collision with any earlier run contradicts the accepted E1 theorem.
-/

namespace SuperpermutationLowerBound.Refinement

open PermutationVertex

variable {k : ℕ}

/-- The chart's two alternative branches cannot support `deficit` full runs.
This is the forcing statement used inside both regular and shortened cells. -/
theorem fullChain_first_eq_rot_of_deficit_le
    {hk : 7 ≤ k} {p : OverlapPath k} {hp : IsBlockAligned p}
    {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain)
    (hcount : R.deficit ≤ chain.runCount) :
    chain.firstRun.entry = R.target .rot := by
  rcases chain.first_entry_classification with hrot | hA | hC
  · exact hrot
  · have hbound := chain.threeChains.2.1 hA
    have hlength := R.length_add_deficit
    have hpositive := R.deficit_pos
    omega
  · have hbound := chain.threeChains.2.2 hC
    have hlength := R.length_add_deficit
    have hpositive := R.deficit_pos
    omega

/-- In particular, two following full runs force the branch after deficit two. -/
theorem deficitTwo_fullChain_first_eq_rot
    {hk : 7 ≤ k} {p : OverlapPath k} {hp : IsBlockAligned p}
    {segment : BlockAlignedLightSegment hk p hp}
    {R : SatelliteContext hk p hp segment} (chain : R.FullRunChain)
    (hdeficit : R.deficit = 2) (hcount : 2 ≤ chain.runCount) :
    chain.firstRun.entry = R.target .rot :=
  fullChain_first_eq_rot_of_deficit_le chain (by omega)

/-- Equality of rotation classes for actual block entries is equality of entries. -/
theorem actualEntries_eq_of_rotationClass_eq (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    {u v : PermutationVertex k}
    (hu : u ∈ blockAlignedBlockEntries hk p hp)
    (hv : v ∈ blockAlignedBlockEntries hk p hp)
    (hclasses : rotationClass u = rotationClass v) : u = v := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hu
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hv
  have hpair := blockAlignedBlockEntries_pairwiseDistinct hk p hp
  by_cases hij : i.1 < j.1
  · have hrel := List.pairwise_iff_getElem.mp hpair i.1 j.1 i.2 j.2 hij
    change rotationClass ((blockAlignedBlockEntries hk p hp).get i) ≠
      rotationClass ((blockAlignedBlockEntries hk p hp).get j) at hrel
    rw [hi, hj] at hrel
    exact (hrel hclasses).elim
  · by_cases hji : j.1 < i.1
    · have hrel := List.pairwise_iff_getElem.mp hpair j.1 i.1 j.2 i.2 hji
      change rotationClass ((blockAlignedBlockEntries hk p hp).get j) ≠
        rotationClass ((blockAlignedBlockEntries hk p hp).get i) at hrel
      rw [hj, hi] at hrel
      exact (hrel hclasses.symm).elim
    · have hindex : i = j := Fin.ext (by omega)
      subst j
      exact hi.symm.trans hj

/-- A class appearing in an earlier actual run cannot appear in a later run. -/
theorem actualRuns_rotationClasses_ne (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (i j : ℕ) (hi : i < (blockAlignedRuns hk p hp).length)
    (hj : j < (blockAlignedRuns hk p hp).length) (hij : i < j)
    {u v : PermutationVertex k}
    (hu : u ∈ (blockAlignedRunAt hk p hp ⟨i, hi⟩).blocks)
    (hv : v ∈ (blockAlignedRunAt hk p hp ⟨j, hj⟩).blocks) :
    rotationClass u ≠ rotationClass v := by
  let runs := blockAlignedRuns hk p hp
  have hflat : runs.flatten = blockAlignedBlockEntries hk p hp :=
    (blockAlignedRuns_spec hk p hp).1
  have hnodup : runs.flatten.Nodup := by
    rw [hflat, List.nodup_iff_pairwise_ne]
    exact (blockAlignedBlockEntries_pairwiseDistinct hk p hp).imp (by
      intro x y hclasses hxy
      exact hclasses (congrArg rotationClass hxy))
  have hpair : runs.Pairwise List.Disjoint := (List.nodup_flatten.mp hnodup).2
  have hdisjoint := hpair.rel_get_of_lt
    (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) (Fin.mk_lt_mk.mpr hij)
  have huEntries : u ∈ blockAlignedBlockEntries hk p hp := by
    rw [← hflat]
    exact List.mem_flatten.mpr ⟨runs.get ⟨i, hi⟩, List.get_mem _ _, hu⟩
  have hvEntries : v ∈ blockAlignedBlockEntries hk p hp := by
    rw [← hflat]
    exact List.mem_flatten.mpr ⟨runs.get ⟨j, hj⟩, List.get_mem _ _, hv⟩
  intro hclasses
  have heq := actualEntries_eq_of_rotationClass_eq hk p hp huEntries hvEntries hclasses
  exact List.disjoint_left.mp hdisjoint hu (heq ▸ hv)

end SuperpermutationLowerBound.Refinement
