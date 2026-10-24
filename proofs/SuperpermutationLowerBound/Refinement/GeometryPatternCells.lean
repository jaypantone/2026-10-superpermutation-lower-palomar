module

public import SuperpermutationLowerBound.Refinement.GeometryPatterns

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

open PermutationVertex

namespace PatternAt

variable {n : ℕ} (hn : 7 ≤ n) {hk : 7 ≤ n + 1}
  {p : OverlapPath (n + 1)} {hp : IsBlockAligned p}
  {segment : BlockAlignedLightSegment hk p hp} {start : ℕ}

theorem cell_step_entry {b : Bool} {d : ℕ} {tail : List ℕ}
    (h : PatternAt segment start (cellDigits (n - 2) b ++ d :: tail)) (hd : d ≤ 2)
    (e : Fin (n + 1) ≃ Alphabet (n + 1))
    (he : (segment.actualRun ⟨start, by
      have := h.1
      simp only [cellDigits, List.length_append, List.length_cons,
        List.length_replicate] at this
      omega⟩).entry = shortEntry n hn e) :
    (segment.actualRun ⟨start + (cellDigits (n - 2) b).length, by
      have := h.1
      simp only [List.length_append, List.length_cons] at this
      omega⟩).entry =
      shortEntry n hn ((if b then cellRho n hn * cellG n hn else cellG n hn).symm.trans e) := by
  let g := if b then (n - 2) - 2 else (n - 2) - 1
  have hg : 0 < g := by dsimp [g]; split_ifs <;> omega
  have h' : PatternAt segment start (2 :: List.replicate g 0 ++ d :: tail) := h
  let R := h'.firstContext
  let C := h'.fullPrefix hg
  have hR : R.deficit = 2 := h'.firstContext_deficit
  have hRentry : R.entry = shortEntry n hn e := he
  have htail : PatternAt segment (start + 1 + g) (d :: tail) := by
    have hh := h'.cons_tail.append_right (xs := List.replicate g 0)
    simpa only [List.length_replicate] using hh
  have hnext : R.localIndex.1 + 1 + C.count < segment.length := by
    change start + 1 + g < segment.length
    have := htail.1
    simp only [List.length_cons] at this
    omega
  have hafterLength : (C.afterRun hnext).length = n - d := by
    have hl := htail.actual_length 0 (by simp)
    change (segment.actualRun ⟨start + 1 + g, by exact hnext⟩).length = n - d
    simpa only [Nat.add_zero, Nat.add_sub_cancel, List.getElem_cons_zero] using hl
  have hafterIndex : start + (cellDigits (n - 2) b).length = start + 1 + g := by
    simp only [cellDigits, List.length_cons, List.length_replicate]
    dsimp [g]
    omega
  have hafterEq : segment.actualRun
      ⟨start + (cellDigits (n - 2) b).length, by
        have := h.1
        simp only [List.length_append, List.length_cons] at this
        omega⟩ = C.afterRun hnext := by
    simp only [hafterIndex]
    rfl
  rw [hafterEq]
  cases b with
  | false =>
    simpa only [Bool.false_eq_true, ↓reduceIte] using
      C.regular_cell_exit hn hR (by dsimp [C, PatternAt.fullPrefix, g]; omega)
        hnext (by omega) e hRentry
  | true =>
    simpa only [↓reduceIte] using
      C.shortened_cell_exit hn hR (by dsimp [C, PatternAt.fullPrefix, g]; omega)
        hnext (by omega) e hRentry

/-- Every full row inside the first cell retains its literal entry formula. -/
theorem cell_full_entry {b : Bool} {tail : List ℕ}
    (h : PatternAt segment start (cellDigits (n - 2) b ++ tail))
    (e : Fin (n + 1) ≃ Alphabet (n + 1))
    (he : (segment.actualRun ⟨start, by
      have := h.1
      simp only [cellDigits, List.length_append, List.length_cons,
        List.length_replicate] at this
      omega⟩).entry = shortEntry n hn e)
    (j : ℕ) (hj : j < if b then n - 4 else n - 3) :
    (segment.actualRun ⟨start + 1 + j, by
      have := h.1
      simp only [cellDigits, List.length_append, List.length_cons,
        List.length_replicate] at this
      split_ifs at * <;> omega⟩).entry =
      fullRunMapPower (by omega) j (fullEntry n hn e) := by
  let g := if b then (n - 2) - 2 else (n - 2) - 1
  have hg : 0 < g := by dsimp [g]; split_ifs <;> omega
  have hjg : j < g := by dsimp [g]; split_ifs at * <;> omega
  have h' : PatternAt segment start (2 :: List.replicate g 0 ++ tail) := h
  let C := h'.fullPrefix hg
  have hfirst : C.first.entry = fullEntry n hn e :=
    (C.first_eq_rot (by
      change h'.firstContext.deficit ≤ g
      rw [h'.firstContext_deficit]
      dsimp [g]
      split_ifs <;> omega)).trans
        (deficitTwo_target_rot_normalized hn h'.firstContext e h'.firstContext_deficit he)
  have hformula := C.entry_formula ⟨j, hjg⟩
  rw [hfirst] at hformula
  simpa only [FullPrefix.run, PatternAt.firstContext_index, Nat.add_assoc,
    BlockAlignedLightSegment.actualRun] using hformula


end PatternAt

end SuperpermutationLowerBound.Refinement
