module

public import SuperpermutationLowerBound.Refinement.GeometryReturnCollision
public import SuperpermutationLowerBound.Refinement.ReturnNormalizationPatterns

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

theorem cellNormalization_universal_inverse_return (n : ℕ) (hn : 8 ≤ n)
    (e : Fin (n+1) ≃ Alphabet (n+1)) :
    shortEntry n (by omega)
      ((cellNormalization n (by omega)
        (chainWindow 1 1 [period n-1,period n-1])).symm.trans e) =
      runMapPower (by omega) (n-6) (shortEntry n (by omega) e) := by
  rw [cellNormalization_universal]
  have h := cellUniversal_shortEntry_return n hn ((cellUniversal n hn).symm.trans e)
  rw [← Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.refl_trans] at h
  exact h.symm

theorem actual_pure_cell_avoidance (n : ℕ) (hn : 7 ≤ n) {hk : 7 ≤ n+1}
    (p : OverlapPath (n+1)) (hp : IsBlockAligned p)
    (segment : BlockAlignedLightSegment hk p hp) :
    ¬CellFactor (n-2) (List.replicate (period n) false) segment.deficitString := by
  intro hf
  obtain ⟨start, h⟩ := hf.exists_patternAt
  obtain ⟨e, he⟩ := h.cellWord_initial_coordinates hn
  apply h.cellWord_short_collision hn
    (by intro heq
        have hh := congrArg List.length heq
        simp only [List.length_replicate, List.length_nil] at hh
        have := period_ge_two hn
        omega)
    (by decide) e he 0 (by omega)
  rw [cellNormalization_pure_period]
  rfl

theorem actual_universal_cell_avoidance (n : ℕ) (hn : 8 ≤ n) {hk : 7 ≤ n+1}
    (p : OverlapPath (n+1)) (hp : IsBlockAligned p)
    (segment : BlockAlignedLightSegment hk p hp) :
    ¬CellFactor (n-2) (chainWindow 1 1 [period n-1,period n-1])
      segment.deficitString := by
  intro hf
  obtain ⟨start, h⟩ := hf.exists_patternAt
  obtain ⟨e, he⟩ := h.cellWord_initial_coordinates (show 7 ≤ n by omega)
  apply h.cellWord_short_collision (show 7 ≤ n by omega)
    (by simp [chainWindow]) (by decide) e he (n-6) (by omega)
  exact cellNormalization_universal_inverse_return n hn e

end SuperpermutationLowerBound.Refinement
