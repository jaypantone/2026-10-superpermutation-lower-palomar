module

public import SuperpermutationLowerBound.Refinement.ReturnTerminal
public import SuperpermutationLowerBound.Refinement.ReturnResidueTwoGeometry
public import SuperpermutationLowerBound.Refinement.GeometryCellWord
public import SuperpermutationLowerBound.Refinement.GeometryPatternIncoming
public import SuperpermutationLowerBound.Refinement.ReturnNormalizationPatterns
public import SuperpermutationLowerBound.Refinement.ChainPatterns

@[expose] public section

/-! Actual terminal collisions for normalized cell words. -/
namespace SuperpermutationLowerBound.Refinement

open PermutationVertex

set_option linter.unusedSimpArgs false

set_option maxHeartbeats 1000000 in
private theorem basicRight_core_value (n : ℕ) (hn : 7 ≤ n) (i : ℕ) (hi : i < n) :
    cellGInverseValue n (cellRhoValue n (cellGValue n (cellYValue n i))) =
      cellUValue n ((2 + i) % n) := by
  have hmod : (2 + i) % n = if 2 + i < n then 2 + i else 2 + i - n := by
    by_cases h : 2 + i < n
    · simp [h, Nat.mod_eq_of_lt h]
    · rw [if_neg h, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hmod]
  unfold cellYValue
  split_ifs <;> simp only [cellGValue] <;> split_ifs <;>
    try (first | contradiction | omega)
  all_goals simp only [cellRhoValue]
  all_goals split_ifs <;> try (first | contradiction | omega)
  all_goals simp only [cellGInverseValue, cellUValue]
  all_goals split_ifs <;> (first | contradiction | omega)

private theorem basicRight_last_value (n : ℕ) (hn : 7 ≤ n) :
    cellGInverseValue n (cellRhoValue n (cellGValue n (cellYValue n n))) = 0 := by
  simp only [cellYValue]
  split_ifs <;> try omega
  simp [cellGValue, cellRhoValue, cellGInverseValue]

/-- The universal conjugate return transports the first short row by two
slots in the final full-entry chart. -/
theorem basicRight_return_shortEntry (n : ℕ) (hn : 7 ≤ n)
    (e : Fin (n + 1) ≃ Alphabet (n + 1)) :
    shortEntry n hn (((cellG n hn)⁻¹ * cellRho n hn * cellG n hn).trans e) =
      runMapPower (by omega) 2 (fullEntry n hn e) := by
  apply shortEntry_eq_runMapPower_of_values n hn _ 2
  · intro i hi
    simpa only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, cellG_symm_apply_val,
      cellRho_apply_val, cellG_apply_val, cellY_apply_val] using basicRight_core_value n hn i hi
  · simpa only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, cellG_symm_apply_val,
      cellRho_apply_val, cellG_apply_val, cellY_apply_val] using basicRight_last_value n hn

namespace PatternAt

/-- A final literal `[2,0]` suffices for the terminal contradiction. The
transported row and incoming full run remain actual runs of this segment. -/
theorem terminal_collision {n : ℕ} (hn : 7 ≤ n) {hk : 7 ≤ n + 1}
    {p : OverlapPath (n + 1)} {hp : IsBlockAligned p}
    {segment : BlockAlignedLightSegment hk p hp} {stop : ℕ}
    (h : PatternAt segment stop [2,0])
    (e : Fin (n + 1) ≃ Alphabet (n + 1))
    (he : (segment.actualRun ⟨stop, by have := h.1; simp at this; omega⟩).entry =
      shortEntry n hn e)
    (shift : ℕ) (hshiftLow : 2 ≤ shift) (hshiftHigh : shift ≤ n - 2)
    (old : Fin segment.length) (hold : old.val < stop + 1)
    (holdLength : (segment.actualRun old).length = n - 2)
    (holdEntry : (segment.actualRun old).entry =
      runMapPower (by omega) shift (fullEntry n hn e))
    (incoming : Fin segment.length) (hincoming : incoming.val < stop + 1)
    (hfull : (segment.actualRun incoming).length = n)
    (hnext : fullRunMap (by omega) (segment.actualRun incoming).entry = shortEntry n hn e) :
    False := by
  have h' : PatternAt segment stop (2 :: List.replicate 1 0 ++ []) := h
  let C := h'.fullPrefix (by decide)
  apply terminal_full_run_collision_of_earlier_run hn h'.firstContext C e
    h'.firstContext_deficit he shift hshiftLow hshiftHigh old hold holdLength holdEntry
  exact incoming_full_identity_occupied hn segment incoming (stop + 1) hincoming hfull e hnext

/-- The last completed cell provides an actual incoming full row at the final
cell boundary. This applies to every nonempty C/B word. -/
theorem cellWord_incoming {n : ℕ} (hn : 7 ≤ n) {hk : 7 ≤ n + 1}
    {p : OverlapPath (n + 1)} {hp : IsBlockAligned p}
    {segment : BlockAlignedLightSegment hk p hp} {start : ℕ}
    {cells : List Bool} {d : ℕ} {tail : List ℕ}
    (h : PatternAt segment start (cellWord (n - 2) cells ++ d :: tail))
    (hc : cells ≠ []) (hd : d ≤ 2) :
    let stop := start + (cellWord (n - 2) cells).length
    let incoming := segment.actualRun ⟨stop - 1, by
      have := h.1
      simp only [List.length_append, List.length_cons] at this
      omega⟩
    let finalRun := segment.actualRun ⟨stop, by
      have := h.1
      simp only [List.length_append, List.length_cons] at this
      omega⟩
    incoming.length = n ∧ fullRunMap (by omega) incoming.entry = finalRun.entry := by
  obtain ⟨pre, b, hcells⟩ : ∃ pre b, cells = pre ++ [b] :=
    ⟨cells.dropLast, cells.getLast hc, (List.dropLast_concat_getLast hc).symm⟩
  subst cells
  have h' : PatternAt segment start
      (cellWord (n - 2) pre ++ (cellDigits (n - 2) b ++ d :: tail)) := by
    simpa only [cellWord_append, cellWord_cons, cellWord_nil, List.append_nil,
      List.append_assoc] using h
  have hlast := h'.append_right.cell_step_incoming hn hd
  simpa only [cellWord_append, cellWord_cons, cellWord_nil, List.append_nil,
    List.length_append, Nat.add_assoc] using hlast

/-- A literal return that shifts the original short row into the final full
chart creates a collision at the terminal zero. -/
theorem cellWord_terminal_collision {n : ℕ} (hn : 7 ≤ n) {hk : 7 ≤ n + 1}
    {p : OverlapPath (n + 1)} {hp : IsBlockAligned p}
    {segment : BlockAlignedLightSegment hk p hp} {start : ℕ}
    {cells : List Bool}
    (h : PatternAt segment start (cellWord (n - 2) cells ++ [2,0])) (hc : cells ≠ [])
    (shift : ℕ) (hshiftLow : 2 ≤ shift) (hshiftHigh : shift ≤ n - 2)
    (hreturn : ∀ e : Fin (n + 1) ≃ Alphabet (n + 1),
      shortEntry n hn ((cellNormalization n hn cells).trans e) =
        runMapPower (by omega) shift (fullEntry n hn e)) : False := by
  let stop := start + (cellWord (n - 2) cells).length
  have hstop : stop + 2 ≤ segment.length := by
    have := h.1
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    dsimp [stop]
    omega
  obtain ⟨e, he⟩ := h.cellWord_initial_coordinates hn
  let ef := (cellNormalization n hn cells).symm.trans e
  have hfinal := h.cellWord_entry hn (by decide : 2 ≤ 2) e he
  have hfinal' : (segment.actualRun ⟨stop, by omega⟩).entry = shortEntry n hn ef := hfinal
  have hterminal : PatternAt segment stop [2,0] := h.append_right
  let old : Fin segment.length := ⟨start, by dsimp [stop] at hstop; omega⟩
  have hfirstLength : (segment.actualRun old).length = n - 2 := by
    have hl := h.actual_length 0 (by simp)
    have hhead : (cellWord (n - 2) cells ++ [2,0])[0]'(by simp) = 2 := by
      cases cells with
      | nil => rfl
      | cons b bs => simp [cellWord_cons, cellDigits]
    simpa only [hhead, Nat.add_zero, Nat.add_sub_cancel] using hl
  have hcoords : (cellNormalization n hn cells).trans ef = e := by
    ext i
    simp [ef, Equiv.trans_apply]
  have htransport : (segment.actualRun old).entry =
      runMapPower (by omega) shift (fullEntry n hn ef) := by
    exact he.trans (by simpa only [hcoords] using hreturn ef)
  have hin := h.cellWord_incoming hn hc (by decide : 2 ≤ 2)
  apply hterminal.terminal_collision hn ef hfinal' shift hshiftLow hshiftHigh old
    (by dsimp [old, stop]; omega) hfirstLength htransport
    ⟨stop - 1, by omega⟩ (by change stop - 1 < stop + 1; omega) hin.1
  exact hin.2.trans hfinal'

end PatternAt

/-- Abstract return arithmetic is discharged against actual literal factors
before any chain-packing count is invoked. -/
theorem not_cellFactor_of_terminal_return {n : ℕ} (hn : 7 ≤ n) {hk : 7 ≤ n + 1}
    {p : OverlapPath (n + 1)} {hp : IsBlockAligned p}
    (segment : BlockAlignedLightSegment hk p hp)
    (cells : List Bool) (hc : cells ≠ [])
    (shift : ℕ) (hshiftLow : 2 ≤ shift) (hshiftHigh : shift ≤ n - 2)
    (hreturn : ∀ e : Fin (n + 1) ≃ Alphabet (n + 1),
      shortEntry n hn ((cellNormalization n hn cells).trans e) =
        runMapPower (by omega) shift (fullEntry n hn e)) :
    ¬ CellFactor (n - 2) cells segment.deficitString := by
  intro hf
  obtain ⟨start, h⟩ := hf.exists_patternAt
  exact h.cellWord_terminal_collision hn hc shift hshiftLow hshiftHigh hreturn

/-- `B C^(p-1) 2,0` is impossible in every actual light segment. -/
theorem basicRight_not_cellFactor {n : ℕ} (hn : 7 ≤ n) {hk : 7 ≤ n + 1}
    {p : OverlapPath (n + 1)} {hp : IsBlockAligned p}
    (segment : BlockAlignedLightSegment hk p hp) :
    ¬ CellFactor (n - 2) (chainWindow 0 (period n - 1) []) segment.deficitString := by
  apply not_cellFactor_of_terminal_return hn segment _ (by simp [chainWindow])
    2 (by decide) (by omega)
  intro e
  rw [cellNormalization_basic_right]
  exact basicRight_return_shortEntry n hn e

/-- The shortened residue-two return uses its exact terminal zero; no
third short run or maximal full prefix is assumed. -/
theorem residueTwoTriple_not_cellFactor (m : ℕ) (hm : 2 ≤ m) (hn : 7 ≤ 3 * m + 2)
    {hk : 7 ≤ 3 * m + 2 + 1} {p : OverlapPath (3 * m + 2 + 1)}
    {hp : IsBlockAligned p} (segment : BlockAlignedLightSegment hk p hp) :
    ¬ CellFactor (3 * m + 2 - 2)
      (chainWindow (2 * m * (m + 1) + 1) 0 [2 * m * (m + 1) - 1])
      segment.deficitString := by
  apply not_cellFactor_of_terminal_return hn segment _ (by simp [chainWindow])
    4 (by decide) (by omega)
  intro e
  rw [cellNormalization_residueTwo_triple m hm hn]
  apply shortEntry_eq_runMapPower_of_values (3 * m + 2) hn _ 4
  · exact cellK_g_y_core_value (3 * m + 2) hn
  · exact cellK_g_y_last_value (3 * m + 2) hn

end SuperpermutationLowerBound.Refinement
