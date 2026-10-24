module

public import SuperpermutationLowerBound.Refinement.GeometryReturnCollision
public import SuperpermutationLowerBound.Refinement.GeometryTerminalTraps
public import SuperpermutationLowerBound.Refinement.ReturnResidueOneGeometry
public import SuperpermutationLowerBound.Refinement.ReturnNormalizationPatterns

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

open PermutationVertex

/-- A full cell is a shortened cell followed by one additional full run. -/
theorem cellDigits_full_eq_short (a : ℕ) (ha : 2 ≤ a) :
    cellDigits a false = cellDigits a true ++ [0] := by
  have he : a-1 = (a-2)+1 := by omega
  simp only [cellDigits, Bool.false_eq_true, ↓reduceIte]
  rw [he, List.replicate_add]
  simp

/-- The residue-one pair contains the two-shortened-cell return followed
by a full run. This is the exact terminal-zero identity behind `Z0`. -/
theorem residueOne_pair_digits (a m : ℕ) (ha : 2 ≤ a) (hm : 1 ≤ m) :
    cellWord a (chainWindow m m []) =
      cellWord a (chainWindow m 0 [m]) ++ [0] := by
  have hmrep : List.replicate m false = List.replicate (m-1) false ++ [false] := by
    rw [← List.replicate_one (a := false), ← List.replicate_add, Nat.sub_add_cancel hm]
  have hmword : cellWord a (List.replicate m false) =
      cellWord a (List.replicate (m-1) false) ++ cellDigits a true ++ [0] := by
    rw [hmrep, cellWord_append]
    simp only [cellWord_cons, cellWord_nil, List.append_nil, cellDigits_full_eq_short a ha,
      List.append_assoc]
  simp only [chainWindow, chainCells, List.replicate_zero, List.cons_ne_nil, List.nil_append,
    ↓reduceIte, List.append_nil, cellWord_append, cellWord_cons, cellWord_nil]
  rw [hmword]
  simp only [List.append_nil, List.append_assoc]

theorem residueOne_inverse_return (m : ℕ) (hm : 2 ≤ m) (hn : 7 ≤ 3*m+1)
    (e : Fin (3*m+1+1) ≃ Alphabet (3*m+1+1)) :
    shortEntry (3*m+1) hn
      ((cellNormalization (3*m+1) hn (chainWindow m 0 [m])).symm.trans e) =
      runMapPower (by omega) (3*m+1-2) (fullEntry (3*m+1) hn e) := by
  let Q := cellRho (3*m+1) hn * (cellG (3*m+1) hn)^m * cellRho (3*m+1) hn *
    (cellG (3*m+1) hn)^(m+1)
  have hQ : cellNormalization (3*m+1) hn (chainWindow m 0 [m]) = Q := by
    rw [cellNormalization_chainWindow_one _ _ _ _ _ (by omega)]
    simp [Q]
  rw [hQ]
  have h := shortened_return_residueOne_entry m hm hn (Q.symm.trans e)
  simpa only [Q, ← Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.refl_trans] using h

theorem residueOneTriple_not_cellFactor (m : ℕ) (hm : 2 ≤ m) (hn : 7 ≤ 3*m+1)
    {hk : 7 ≤ 3*m+1+1} {p : OverlapPath (3*m+1+1)} {hp : IsBlockAligned p}
    (segment : BlockAlignedLightSegment hk p hp) :
    ¬CellFactor (3*m+1-2) (chainWindow m 0 [m]) segment.deficitString := by
  intro hf
  obtain ⟨start, h⟩ := hf.exists_patternAt
  obtain ⟨e, he⟩ := h.cellWord_initial_coordinates hn
  exact h.cellWord_full_collision hn (by simp [chainWindow]) (by omega) e he
    (3*m+1-2) (by omega) (residueOne_inverse_return m hm hn e)

theorem residueOnePair_not_cellFactor (m : ℕ) (hm : 2 ≤ m) (hn : 7 ≤ 3*m+1)
    {hk : 7 ≤ 3*m+1+1} {p : OverlapPath (3*m+1+1)} {hp : IsBlockAligned p}
    (segment : BlockAlignedLightSegment hk p hp) :
    ¬CellFactor (3*m+1-2) (chainWindow m m []) segment.deficitString := by
  intro hf
  obtain ⟨start, h⟩ := hf.exists_patternAt
  have h' : PatternAt segment start
      (cellWord (3*m+1-2) (chainWindow m 0 [m]) ++ 0 :: [2,0]) := by
    simpa only [residueOne_pair_digits (3*m+1-2) m (by omega) (by omega),
      List.append_assoc, List.cons_append, List.nil_append] using h
  obtain ⟨e, he⟩ := h'.cellWord_initial_coordinates hn
  exact h'.cellWord_full_collision hn (by simp [chainWindow]) (by omega) e he
    (3*m+1-2) (by omega) (residueOne_inverse_return m hm hn e)

theorem residueTwo_inverse_return (m : ℕ) (hm : 2 ≤ m) (hn : 7 ≤ 3*m+2)
    (e : Fin (3*m+2+1) ≃ Alphabet (3*m+2+1)) :
    shortEntry (3*m+2) hn
      ((cellNormalization (3*m+2) hn (chainWindow (2*m*(m+1)) (2*m*(m+1)-1) [])).symm.trans e) =
      runMapPower (by omega) 2 (fullEntry (3*m+2) hn e) := by
  rw [cellNormalization_residueTwo_pair m hm hn]
  have hsymm : ((cellG (3*m+2) hn)⁻¹ * (cellRho (3*m+2) hn)⁻¹ *
      cellG (3*m+2) hn).symm =
      (cellG (3*m+2) hn)⁻¹ * cellRho (3*m+2) hn * cellG (3*m+2) hn := by
    change ((cellG (3*m+2) hn)⁻¹ * (cellRho (3*m+2) hn)⁻¹ *
      cellG (3*m+2) hn)⁻¹ = _
    group
  rw [hsymm]
  exact basicRight_return_shortEntry (3*m+2) hn e

theorem residueTwoPair_not_cellFactor (m : ℕ) (hm : 2 ≤ m) (hn : 7 ≤ 3*m+2)
    {hk : 7 ≤ 3*m+2+1} {p : OverlapPath (3*m+2+1)} {hp : IsBlockAligned p}
    (segment : BlockAlignedLightSegment hk p hp) :
    ¬CellFactor (3*m+2-2) (chainWindow (2*m*(m+1)) (2*m*(m+1)-1) [])
      segment.deficitString := by
  intro hf
  obtain ⟨start, h⟩ := hf.exists_patternAt
  obtain ⟨e, he⟩ := h.cellWord_initial_coordinates hn
  exact h.cellWord_full_collision hn (by simp [chainWindow]) (by omega) e he
    2 (by omega) (residueTwo_inverse_return m hm hn e)

end SuperpermutationLowerBound.Refinement
