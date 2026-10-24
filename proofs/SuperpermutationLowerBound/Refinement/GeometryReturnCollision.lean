module

public import SuperpermutationLowerBound.Refinement.GeometryCellWord

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

open PermutationVertex

/-- Slots in two distinct actual runs have distinct rotation classes. -/
theorem segment_actualRun_slots_ne {k : ℕ} {hk : 7 ≤ k}
    {p : OverlapPath k} {hp : IsBlockAligned p}
    (segment : BlockAlignedLightSegment hk p hp)
    (old new : Fin segment.length) (horder : old.val < new.val)
    (i j : ℕ) (hi : i < (segment.actualRun old).length)
    (hj : j < (segment.actualRun new).length) :
    rotationClass (runMapPower (by omega) i (segment.actualRun old).entry) ≠
      rotationClass (runMapPower (by omega) j (segment.actualRun new).entry) := by
  have hne := actualRuns_rotationClasses_ne hk p hp
    (segment.globalStart + old.val) (segment.globalStart + new.val)
    (by have := blockAlignedLightSegment_globalStart_bounds hk p hp segment; omega)
    (by have := blockAlignedLightSegment_globalStart_bounds hk p hp segment; omega)
    (by omega)
    (List.get_mem (segment.actualRun old).blocks ⟨i, hi⟩)
    (List.get_mem (segment.actualRun new).blocks ⟨j, hj⟩)
  change rotationClass ((segment.actualRun old).blocks.get ⟨i, hi⟩) ≠
    rotationClass ((segment.actualRun new).blocks.get ⟨j, hj⟩) at hne
  rw [blockAlignedRun_entrySequence, blockAlignedRun_entrySequence] at hne
  exact hne

theorem cellWord_length_pos {a : ℕ} {cells : List Bool} (h : cells ≠ []) :
    0 < (cellWord a cells).length := by
  cases cells with
  | nil => contradiction
  | cons b bs => simp [cellWord_cons, cellDigits]

namespace PatternAt

variable {n : ℕ} (hn : 7 ≤ n) {hk : 7 ≤ n+1}
  {p : OverlapPath (n+1)} {hp : IsBlockAligned p}
  {segment : BlockAlignedLightSegment hk p hp} {start : ℕ}

/-- A return into an occupied slot of the first short run is impossible. -/
theorem cellWord_short_collision {cells : List Bool} {d : ℕ} {tail : List ℕ}
    (h : PatternAt segment start (cellWord (n-2) cells ++ d :: tail))
    (hcells : cells ≠ []) (hd : d ≤ 2)
    (e : Fin (n+1) ≃ Alphabet (n+1))
    (he : (segment.actualRun ⟨start, by
      have := h.1; simp only [List.length_append, List.length_cons] at this; omega⟩).entry =
        shortEntry n hn e)
    (slot : ℕ) (hslot : slot < n-2)
    (hreturn : shortEntry n hn ((cellNormalization n hn cells).symm.trans e) =
      runMapPower (by omega) slot (shortEntry n hn e)) : False := by
  have hpos := cellWord_length_pos (a := n-2) hcells
  have hstart : start < segment.length := by
    have := h.1; simp only [List.length_append, List.length_cons] at this; omega
  have hstop : start + (cellWord (n-2) cells).length < segment.length := by
    have := h.1; simp only [List.length_append, List.length_cons] at this; omega
  let old : Fin segment.length := ⟨start, hstart⟩
  let new : Fin segment.length := ⟨start + (cellWord (n-2) cells).length, hstop⟩
  have holdLength : (segment.actualRun old).length = n-2 := by
    cases cells with
    | nil => contradiction
    | cons b bs =>
      have hl := h.actual_length 0 (by simp [cellWord_cons, cellDigits])
      simpa only [cellWord_cons, cellDigits, List.cons_append,
        List.getElem_cons_zero, Nat.add_zero, Nat.add_sub_cancel] using hl
  have hnewLength : 0 < (segment.actualRun new).length :=
    blockAlignedRun_length_pos hk p hp _
  have hne := segment_actualRun_slots_ne segment old new (by dsimp [old, new]; omega)
    slot 0 (by rw [holdLength]; exact hslot) hnewLength
  have hfinal := h.cellWord_entry hn hd e he
  change rotationClass (runMapPower (by omega) slot
    (segment.actualRun ⟨start, hstart⟩).entry) ≠
      rotationClass (runMapPower (by omega) 0
        (segment.actualRun ⟨start + (cellWord (n-2) cells).length, hstop⟩).entry) at hne
  rw [he, hfinal, hreturn] at hne
  exact hne (by rfl)

/-- A return into an occupied slot of the first following full run is impossible. -/
theorem cellWord_full_cons_collision {b : Bool} {bs : List Bool} {d : ℕ} {tail : List ℕ}
    (h : PatternAt segment start (cellWord (n-2) (b::bs) ++ d :: tail))
    (hd : d ≤ 2) (e : Fin (n+1) ≃ Alphabet (n+1))
    (he : (segment.actualRun ⟨start, by
      have := h.1; simp only [List.length_append, List.length_cons] at this; omega⟩).entry =
        shortEntry n hn e)
    (slot : ℕ) (hslot : slot < n)
    (hreturn : shortEntry n hn ((cellNormalization n hn (b::bs)).symm.trans e) =
      runMapPower (by omega) slot (fullEntry n hn e)) : False := by
  have hcell : 1 < (cellWord (n-2) (b::bs)).length := by
    simp only [cellWord_cons, cellDigits, List.length_append, List.length_cons,
      List.length_replicate]
    split_ifs <;> omega
  have hfirst : start+1 < segment.length := by
    have := h.1; simp only [List.length_append, List.length_cons] at this; omega
  have hstop : start + (cellWord (n-2) (b::bs)).length < segment.length := by
    have := h.1; simp only [List.length_append, List.length_cons] at this; omega
  have h' : PatternAt segment start
      (cellDigits (n-2) b ++ (cellWord (n-2) bs ++ d :: tail)) := by
    simpa only [cellWord_cons, List.append_assoc] using h
  have hfull := h'.cell_full_entry hn e he 0 (by split_ifs <;> omega)
  simp only [Nat.add_zero, fullRunMapPower, Function.iterate_zero_apply] at hfull
  let old : Fin segment.length := ⟨start+1, hfirst⟩
  let new : Fin segment.length := ⟨start + (cellWord (n-2) (b::bs)).length, hstop⟩
  have holdLength : (segment.actualRun old).length = n := by
    have hl := h'.actual_length 1 (by
      simp only [cellDigits, List.length_append, List.length_cons, List.length_replicate]
      split_ifs <;> omega)
    simp only [cellDigits, List.cons_append, List.getElem_cons_succ] at hl
    rw [List.getElem_append_left (by
      simp only [List.length_replicate]; split_ifs <;> omega)] at hl
    simpa only [List.getElem_replicate, Nat.add_sub_cancel, Nat.sub_zero] using hl
  have hnewLength : 0 < (segment.actualRun new).length :=
    blockAlignedRun_length_pos hk p hp _
  have hne := segment_actualRun_slots_ne segment old new (by
    change start+1 < start + (cellWord (n-2) (b::bs)).length
    omega) slot 0 (by rw [holdLength]; exact hslot) hnewLength
  have hfinal := h.cellWord_entry hn hd e he
  change rotationClass (runMapPower (by omega) slot
    (segment.actualRun ⟨start+1, hfirst⟩).entry) ≠
      rotationClass (runMapPower (by omega) 0
        (segment.actualRun ⟨start + (cellWord (n-2) (b::bs)).length, hstop⟩).entry) at hne
  rw [hfull, hfinal, hreturn] at hne
  exact hne (by rfl)

theorem cellWord_full_collision {cells : List Bool} {d : ℕ} {tail : List ℕ}
    (h : PatternAt segment start (cellWord (n-2) cells ++ d :: tail))
    (hcells : cells ≠ []) (hd : d ≤ 2) (e : Fin (n+1) ≃ Alphabet (n+1))
    (he : (segment.actualRun ⟨start, by
      have := h.1; simp only [List.length_append, List.length_cons] at this; omega⟩).entry =
        shortEntry n hn e)
    (slot : ℕ) (hslot : slot < n)
    (hreturn : shortEntry n hn ((cellNormalization n hn cells).symm.trans e) =
      runMapPower (by omega) slot (fullEntry n hn e)) : False := by
  cases cells with
  | nil => contradiction
  | cons b bs => exact h.cellWord_full_cons_collision hn hd e he slot hslot hreturn

end PatternAt
end SuperpermutationLowerBound.Refinement
