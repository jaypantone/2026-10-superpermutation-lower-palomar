module

public import SuperpermutationLowerBound.Refinement.ReturnLocalCollisions

@[expose] public section

/-! Forced exits of actual regular and shortened cells. -/

namespace SuperpermutationLowerBound.Refinement

open PermutationVertex

namespace FullPrefix

variable {k : ℕ} {hk : 7 ≤ k} {p : OverlapPath k} {hp : IsBlockAligned p}
  {segment : BlockAlignedLightSegment hk p hp}
  {R : SatelliteContext hk p hp segment}

noncomputable def afterRun (C : FullPrefix R)
    (hnext : R.localIndex.1 + 1 + C.count < segment.length) : BlockAlignedRun hk p hp :=
  blockAlignedRunAt hk p hp
    ⟨segment.globalStart + (R.localIndex.1 + 1 + C.count), by
      have := blockAlignedLightSegment_globalStart_bounds hk p hp segment
      omega⟩

theorem afterRun_blocks (C : FullPrefix R)
    (hnext : R.localIndex.1 + 1 + C.count < segment.length) :
    (C.afterRun hnext).blocks = segment.runAt
      ⟨R.localIndex.1 + 1 + C.count, hnext⟩ := by
  simpa [afterRun] using
    (blockAlignedLightSegment_runAt_eq_globalRun hk p hp segment
      ⟨R.localIndex.1 + 1 + C.count, hnext⟩).symm

theorem after_threeTargets (C : FullPrefix R)
    (hnext : R.localIndex.1 + 1 + C.count < segment.length) :
    let last := C.run ⟨C.count - 1, by have := C.positive; omega⟩
    (C.afterRun hnext).entry = fullRunMap (by omega) last.entry ∨
      (C.afterRun hnext).entry = fullRunChartTarget2 hk last.entry ∨
      (C.afterRun hnext).entry = fullRunChartTarget5 hk last.entry := by
  dsimp only
  let last := C.run ⟨C.count - 1, by have := C.positive; omega⟩
  let j := segment.globalStart + (R.localIndex.1 + 1 + (C.count - 1))
  have hj : j + 1 < (blockAlignedRuns hk p hp).length := by
    have := blockAlignedLightSegment_globalStart_bounds hk p hp segment
    have := C.positive
    dsimp [j]
    omega
  have hleft : blockAlignedRunAt hk p hp ⟨j, by omega⟩ = last := rfl
  have hright : blockAlignedRunAt hk p hp ⟨j + 1, hj⟩ = C.afterRun hnext := by
    have hindex : j + 1 = segment.globalStart + (R.localIndex.1 + 1 + C.count) := by
      have := C.positive
      dsimp [j]
      omega
    simp only [hindex]
    rfl
  have hlastLocal : R.localIndex.1 + 1 + (C.count - 1) + 1 < segment.length := by
    have := C.positive
    omega
  have hlight := blockAlignedLightSegment_runAt_light hk p hp segment
    (R.localIndex.1 + 1 + (C.count - 1)) hlastLocal
  have hlastBlocks := C.run_blocks ⟨C.count - 1, by have := C.positive; omega⟩
  have hafterBlocks : (C.afterRun hnext).blocks = segment.runAt
      ⟨R.localIndex.1 + 1 + (C.count - 1) + 1, hlastLocal⟩ := by
    have hindex : R.localIndex.1 + 1 + (C.count - 1) + 1 =
        R.localIndex.1 + 1 + C.count := by have := C.positive; omega
    simpa only [hindex] using C.afterRun_blocks hnext
  rw [← hlastBlocks, ← hafterBlocks] at hlight
  have h := actualFullBoundary_threeTargets hk p hp j hj
    (by rw [hleft]; exact C.run_isFull ⟨C.count - 1, by have := C.positive; omega⟩)
    (by rw [hleft, hright]; exact hlight)
  simpa only [hleft, hright] using h

theorem after_no_old_collision (C : FullPrefix R)
    (hnext : R.localIndex.1 + 1 + C.count < segment.length)
    (i j : ℕ) (hi : i < (C.afterRun hnext).length) (hj : j < R.length) :
    rotationClass (runMapPower (by omega) i (C.afterRun hnext).entry) ≠
      rotationClass (runMapPower (by omega) j R.entry) := by
  have hnew := blockAlignedRun_entrySequence hk p hp (C.afterRun hnext) i hi
  have hold := blockAlignedRun_entrySequence hk p hp R.run j hj
  have hne := actualRuns_rotationClasses_ne hk p hp
    (segment.globalStart + R.localIndex.1)
    (segment.globalStart + (R.localIndex.1 + 1 + C.count))
    (by have := blockAlignedLightSegment_globalStart_bounds hk p hp segment; omega)
    (by have := blockAlignedLightSegment_globalStart_bounds hk p hp segment; omega)
    (by omega) (List.get_mem R.run.blocks ⟨j, hj⟩)
    (List.get_mem (C.afterRun hnext).blocks ⟨i, hi⟩)
  change rotationClass (R.run.blocks.get ⟨j, hj⟩) ≠
    rotationClass ((C.afterRun hnext).blocks.get ⟨i, hi⟩) at hne
  rw [hnew, hold] at hne
  exact Ne.symm hne

end FullPrefix

namespace FullPrefix

variable {n : ℕ} (hn : 7 ≤ n) {hk : 7 ≤ n + 1}
  {p : OverlapPath (n + 1)} {hp : IsBlockAligned p}
  {segment : BlockAlignedLightSegment hk p hp}
  {R : SatelliteContext hk p hp segment}

/-- The two- and three-block exit thresholds, including nonmaximal terminal prefixes. -/
theorem cell_exit_forced (C : FullPrefix R) (d : ℕ) (hd1 : 1 ≤ d) (hd2 : d ≤ 2)
    (hdeficit : R.deficit = 2) (hcount : C.count = n - 2 - d)
    (hnext : R.localIndex.1 + 1 + C.count < segment.length)
    (hlong : d < (C.afterRun hnext).length) :
    (C.afterRun hnext).entry = fullRunMapPower (by omega) C.count C.first.entry := by
  have hlength : R.length = n - 2 := by have := R.length_add_deficit; omega
  let e := (cellY n hn).symm.trans (vertexCoordinates R.entry)
  have hentry : R.entry = shortEntry n hn e := (shortEntry_normalize n hn R.entry).symm
  have hfirst : C.first.entry = fullEntry n hn e :=
    (C.first_eq_rot (by omega)).trans
      (deficitTwo_target_rot_normalized hn R e hdeficit hentry)
  have hlast : (C.run ⟨C.count - 1, by have := C.positive; omega⟩).entry =
      fullRunMapPower (by omega) (n - 3 - d) (fullEntry n hn e) := by
    rw [C.entry_formula, hfirst]
    change fullRunMapPower (by omega) (C.count - 1) (fullEntry n hn e) = _
    congr 1
    omega
  rcases C.after_threeTargets hnext with hrot | h2 | h5
  · rw [hrot, C.entry_formula]
    have heq : C.count = (C.count - 1) + 1 := by have := C.positive; omega
    conv_rhs => rw [heq]
    simp only [fullRunMapPower, Function.iterate_succ_apply']
  · have hne := C.after_no_old_collision hnext d (n - d - 3) hlong (by omega)
    rw [h2, hlast, cell_exit_target2_collision n hn d hd1 hd2 e,
      rotationClass_rotationPower (by omega), ← hentry] at hne
    exact (hne rfl).elim
  · have hne := C.after_no_old_collision hnext d (n - d - 4) hlong (by omega)
    rw [h5, hlast, cell_exit_target5_collision n hn d hd1 hd2 e,
      rotationClass_rotationPower (by omega), ← hentry] at hne
    exact (hne rfl).elim

theorem regular_cell_exit (C : FullPrefix R) (hdeficit : R.deficit = 2)
    (hcount : C.count = n - 3)
    (hnext : R.localIndex.1 + 1 + C.count < segment.length)
    (hlong : 1 < (C.afterRun hnext).length)
    (e : Fin (n + 1) ≃ Alphabet (n + 1))
    (hentry : R.entry = shortEntry n hn e) :
    (C.afterRun hnext).entry = shortEntry n hn ((cellG n hn).symm.trans e) := by
  have hfirst : C.first.entry = fullEntry n hn e :=
    (C.first_eq_rot (by omega)).trans
      (deficitTwo_target_rot_normalized hn R e hdeficit hentry)
  rw [C.cell_exit_forced hn 1 (by omega) (by omega) hdeficit (by omega) hnext hlong,
    hcount, hfirst, regularCell_entry_transfer]

theorem shortened_cell_exit (C : FullPrefix R) (hdeficit : R.deficit = 2)
    (hcount : C.count = n - 4)
    (hnext : R.localIndex.1 + 1 + C.count < segment.length)
    (hlong : 2 < (C.afterRun hnext).length)
    (e : Fin (n + 1) ≃ Alphabet (n + 1))
    (hentry : R.entry = shortEntry n hn e) :
    (C.afterRun hnext).entry =
      shortEntry n hn ((cellRho n hn * cellG n hn).symm.trans e) := by
  have hfirst : C.first.entry = fullEntry n hn e :=
    (C.first_eq_rot (by omega)).trans
      (deficitTwo_target_rot_normalized hn R e hdeficit hentry)
  rw [C.cell_exit_forced hn 2 (by omega) (by omega) hdeficit (by omega) hnext hlong,
    hcount, hfirst, shortenedCell_entry_transfer]

end FullPrefix

end SuperpermutationLowerBound.Refinement
