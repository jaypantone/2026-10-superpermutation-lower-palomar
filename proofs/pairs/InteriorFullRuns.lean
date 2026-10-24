module

public import pairs.PeriodicReturns

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

namespace PatternAt

theorem full_after_cells {n : ℕ} (hn : 7 ≤ n) {hk : 7 ≤ n + 1}
    {p : OverlapPath (n + 1)} {hp : IsBlockAligned p}
    {segment : BlockAlignedLightSegment hk p hp} {start : ℕ}
    {before : List Bool} {tail : List ℕ}
    (h : PatternAt segment start
      (cellWord (n - 2) before ++ (cellDigits (n - 2) false ++ tail)))
    (hstart : start < segment.length) (e : Fin (n + 1) ≃ Alphabet (n + 1))
    (he : (segment.actualRun ⟨start, hstart⟩).entry = shortEntry n hn e)
    (r : ℕ) (hr : r < n - 3) :
    ∃ row : Fin segment.length,
      row.val = start + (cellWord (n - 2) before).length + 1 + r ∧
      (segment.actualRun row).length = n ∧
      (segment.actualRun row).entry = fullRunMapPower (by omega) r
        (fullEntry n hn ((cellNormalization n hn before).symm.trans e)) := by
  have h' : PatternAt segment start
      (cellWord (n - 2) before ++ 2 :: (List.replicate ((n - 2) - 1) 0 ++ tail)) := by
    simpa only [cellDigits, Bool.false_eq_true, ↓reduceIte, List.cons_append] using h
  have hentry := h'.cellWord_entry hn (by decide) e he
  have htail := h.append_right
  have hformula := htail.cell_full_entry hn
    ((cellNormalization n hn before).symm.trans e) hentry r (by simpa using hr)
  have hrow : start + (cellWord (n - 2) before).length + 1 + r < segment.length := by
    have hh := htail.1
    simp only [cellDigits, Bool.false_eq_true, ↓reduceIte, List.length_append,
      List.length_cons, List.length_replicate] at hh
    omega
  refine ⟨⟨_, hrow⟩, rfl, ?_, hformula⟩
  have hi : r + 1 < (cellDigits (n - 2) false ++ tail).length := by
    simp only [cellDigits, Bool.false_eq_true, ↓reduceIte, List.length_append,
      List.length_cons, List.length_replicate]
    omega
  have hl := htail.actual_length (r + 1) hi
  simp only [cellDigits, Bool.false_eq_true, ↓reduceIte, List.cons_append] at hl
  rw [List.getElem_cons_succ] at hl
  rw [List.getElem_append_left (by simp only [List.length_replicate]; omega)] at hl
  simpa only [List.getElem_replicate, Nat.add_sub_cancel, Nat.sub_zero, Nat.add_assoc, Nat.add_comm r 1] using hl

end PatternAt

end SuperpermutationLowerBound.Refinement
