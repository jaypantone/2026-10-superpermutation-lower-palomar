module

public import pairs.InteriorFullRuns
public import alternation.SquareLocations
public import SquareCharts

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

/-- Two consecutive efficient residue-two pairs repeat an occupied rotation
class. Both selected full rows are internal to the displayed cells; the
`CellFactor` interface retains the following short row needed by chain counting. -/
theorem actual_square_pair_avoidance (m : ℕ) (hm : 2 ≤ m) (hn : 7 ≤ 3*m+2)
    {hk : 7 ≤ 3*m+2+1} {p : OverlapPath (3*m+2+1)} {hp : IsBlockAligned p}
    (segment : BlockAlignedLightSegment hk p hp) :
    ¬ CellFactor (3*m+2-2) (squareCells m) segment.deficitString := by
  intro hf
  obtain ⟨start, h⟩ := hf.exists_patternAt
  obtain ⟨e, he⟩ := h.cellWord_initial_coordinates hn
  have hstart : start < segment.length := by
    have hh := h.1
    simp only [List.length_append, List.length_cons, List.length_nil] at hh
    omega
  obtain ⟨tailOne, hone⟩ := squareCells_prefixOne m hm
  obtain ⟨tailTwo, htwo⟩ := squareCells_prefixTwo m hm
  have hpatternOne : PatternAt segment start
      (cellWord (3*m+2-2) (squarePrefixOne m) ++
        (cellDigits (3*m+2-2) false ++
          (cellWord (3*m+2-2) tailOne ++ [2,0]))) := by
    rw [hone] at h
    simpa only [cellWord_append, cellWord_cons, List.append_assoc] using h
  have hpatternTwo : PatternAt segment start
      (cellWord (3*m+2-2) (squarePrefixTwo m) ++
        (cellDigits (3*m+2-2) false ++
          (cellWord (3*m+2-2) tailTwo ++ [2,0]))) := by
    rw [htwo] at h
    simpa only [cellWord_append, cellWord_cons, List.append_assoc] using h
  obtain ⟨old, hold, holdLength, holdEntry⟩ :=
    hpatternOne.full_after_cells hn hstart e he (3*m+2-4) (by omega)
  obtain ⟨new, hnew, hnewLength, hnewEntry⟩ :=
    hpatternTwo.full_after_cells hn hstart e he 0 (by omega)
  have horder : old.val < new.val := by
    have hh := square_full_row_order m hm
    omega
  have hquot :
      cellNormalization (3*m+2) hn (squarePrefixTwo m) *
        (cellNormalization (3*m+2) hn (squarePrefixOne m))⁻¹ =
      cellG (3*m+2) hn ^ m * cellRho (3*m+2) hn *
        (cellG (3*m+2) hn)⁻¹ * cellRho (3*m+2) hn *
        cellG (3*m+2) hn ^ (m+2) := by
    rw [squarePrefixOne_normalization m hm hn, squarePrefixTwo_normalization m hm hn]
    exact square_chart_quotient m hm hn
  have hcollision := square_entries_of_quotient m hm hn
    (cellNormalization (3*m+2) hn (squarePrefixOne m))
    (cellNormalization (3*m+2) hn (squarePrefixTwo m)) hquot e
  have hequal : (segment.actualRun old).entry =
      runMapPower (by omega) (3*m+2-2) (segment.actualRun new).entry := by
    rw [holdEntry, hnewEntry]
    simpa only [fullRunMapPower, Function.iterate_zero_apply] using hcollision
  have hne := segment_actualRun_slots_ne segment old new horder 0 (3*m+2-2)
    (by rw [holdLength]; omega) (by rw [hnewLength]; omega)
  apply hne
  simpa only [runMapPower, Function.iterate_zero_apply] using
    (congrArg rotationClass hequal)

end SuperpermutationLowerBound.Refinement
