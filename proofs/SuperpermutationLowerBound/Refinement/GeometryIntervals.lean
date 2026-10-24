module

public import SuperpermutationLowerBound.Refinement.GeometryCoordinates

@[expose] public section

/-!
Full-run prefixes inside actual light segments. A prefix need not be maximal:
this distinction is essential at the final zero of a hereditary factor.
-/

namespace SuperpermutationLowerBound.Refinement

open PermutationVertex

variable {k : ℕ}

structure FullPrefix {hk : 7 ≤ k} {p : OverlapPath k}
    {hp : IsBlockAligned p} {segment : BlockAlignedLightSegment hk p hp}
    (R : SatelliteContext hk p hp segment) where
  count : ℕ
  positive : 0 < count
  inBounds : R.localIndex.1 + 1 + count ≤ segment.length
  full : ∀ j, ∀ hj : j < count,
    (segment.runAt ⟨R.localIndex.1 + 1 + j, by omega⟩).length = k - 1

namespace FullPrefix

variable {hk : 7 ≤ k} {p : OverlapPath k} {hp : IsBlockAligned p}
  {segment : BlockAlignedLightSegment hk p hp}
  {R : SatelliteContext hk p hp segment}

noncomputable def run (C : FullPrefix R) (j : Fin C.count) :
    BlockAlignedRun hk p hp :=
  blockAlignedRunAt hk p hp
    ⟨segment.globalStart + (R.localIndex.1 + 1 + j.1), by
      have := blockAlignedLightSegment_globalStart_bounds hk p hp segment
      have := C.inBounds
      omega⟩

theorem run_blocks (C : FullPrefix R) (j : Fin C.count) :
    (C.run j).blocks = segment.runAt
      ⟨R.localIndex.1 + 1 + j.1, by have := C.inBounds; omega⟩ := by
  simpa [run] using
    (blockAlignedLightSegment_runAt_eq_globalRun hk p hp segment
      ⟨R.localIndex.1 + 1 + j.1, by have := C.inBounds; omega⟩).symm

noncomputable def first (C : FullPrefix R) : BlockAlignedRun hk p hp :=
  C.run ⟨0, C.positive⟩

theorem run_isFull (C : FullPrefix R) (j : Fin C.count) :
    (C.run j).IsFull := by
  change (C.run j).blocks.length = k - 1
  rw [C.run_blocks]
  exact C.full j.1 j.2

theorem entry_formula (C : FullPrefix R) (j : Fin C.count) :
    (C.run j).entry = fullRunMapPower (by omega) j.1 C.first.entry := by
  let interval := segment.fullIntervalChain hk p hp
    (R.localIndex.1 + 1) C.count C.inBounds C.full
  have h := blockAlignedFullLightChain_entry_formula hk p hp interval j.1 j.2
  simpa [interval, run, first, Nat.add_assoc] using h

theorem first_classification (C : FullPrefix R) :
    C.first.entry = R.target .rot ∨ C.first.entry = R.target .A ∨
      C.first.entry = R.target .C := by
  have hnext : R.localIndex.1 + 1 < segment.length := by
    have := C.positive
    have := C.inBounds
    omega
  have heq : C.first = R.nextRun hnext := rfl
  have hfull : (R.nextRun hnext).IsFull := by
    rw [← heq]
    exact C.run_isFull ⟨0, C.positive⟩
  simpa [heq] using (R.immediateFates hnext).2.2.2.2 hfull

theorem no_entry_class_collision (C : FullPrefix R) (j : Fin C.count)
    (i : ℕ) (hi : i < (C.run j).length) :
    rotationClass (runMapPower (by omega) i (C.run j).entry) ≠
      rotationClass R.entry := by
  have hR : R.run.blocks ≠ [] := by
    have := blockAlignedRun_length_pos hk p hp R.run
    simpa [BlockAlignedRun.length] using (Nat.ne_of_gt this)
  have hentry : (C.run j).blocks.get ⟨i, hi⟩ =
      runMapPower (by omega) i (C.run j).entry :=
    blockAlignedRun_entrySequence hk p hp (C.run j) i hi
  have hne := actualRuns_rotationClasses_ne hk p hp
    (segment.globalStart + R.localIndex.1)
    (segment.globalStart + (R.localIndex.1 + 1 + j.1))
    (by have := blockAlignedLightSegment_globalStart_bounds hk p hp segment; omega)
    (by have := blockAlignedLightSegment_globalStart_bounds hk p hp segment
        have := C.inBounds; omega)
    (by omega) (List.head_mem hR) (List.get_mem (C.run j).blocks ⟨i, hi⟩)
  change rotationClass R.entry ≠
    rotationClass ((C.run j).blocks.get ⟨i, hi⟩) at hne
  rw [hentry] at hne
  exact Ne.symm hne

/-- The branch is forced already by a sufficiently long actual prefix. -/
theorem first_eq_rot (C : FullPrefix R) (hcount : R.deficit ≤ C.count) :
    C.first.entry = R.target .rot := by
  have hlength := R.length_add_deficit
  have hbounds := R.length_bounds
  let q := k - 2 - R.length
  have hq : q < C.count := by dsimp [q]; omega
  have hfull : (C.run ⟨q, hq⟩).length = k - 1 := C.run_isFull ⟨q, hq⟩
  rcases C.first_classification with hrot | hA | hC
  · exact hrot
  · have hi : R.length < (C.run ⟨q, hq⟩).length := by omega
    have heq : runMapPower (by omega) R.length (C.run ⟨q, hq⟩).entry =
        rotationPower (R.length + 1) R.entry := by
      rw [C.entry_formula, hA]
      exact R.fullRunMapPower_A_collision
    have hne := C.no_entry_class_collision ⟨q, hq⟩ R.length hi
    rw [heq, rotationClass_rotationPower (by omega)] at hne
    exact (hne rfl).elim
  · have hi : R.length - 1 < (C.run ⟨q, hq⟩).length := by omega
    have heq : runMapPower (by omega) (R.length - 1) (C.run ⟨q, hq⟩).entry =
        rotationPower R.length R.entry := by
      rw [C.entry_formula, hC]
      exact R.fullRunMapPower_C_collision
    have hne := C.no_entry_class_collision ⟨q, hq⟩ (R.length - 1) hi
    rw [heq, rotationClass_rotationPower (by omega)] at hne
    exact (hne rfl).elim

end FullPrefix

end SuperpermutationLowerBound.Refinement
