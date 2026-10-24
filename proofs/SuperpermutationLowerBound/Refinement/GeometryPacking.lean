module

public import SuperpermutationLowerBound.Refinement.GeometryPureUniversal
public import SuperpermutationLowerBound.Refinement.GeometryAlgebraicTraps
public import SuperpermutationLowerBound.Refinement.GeometryTerminalTraps
public import SuperpermutationLowerBound.Refinement.ReflectionTraps
public import SuperpermutationLowerBound.Refinement.ReturnPacking

@[expose] public section

/-! Genuine segment chain packing. All return hypotheses are discharged on
actual contiguous factors before the abstract chain count is invoked. -/
namespace SuperpermutationLowerBound.Refinement

/-- The complete return exclusions hold for every actual light segment,
including segments obtained after prepending a door and all endpoint cases. -/
theorem actual_segment_returnAvoidance {n : ℕ} (hn : 7 ≤ n) {hk : 7 ≤ n + 1}
    {p : OverlapPath (n + 1)} {hp : IsBlockAligned p}
    (segment : BlockAlignedLightSegment hk p hp) :
    ReturnAvoidance n segment.deficitString := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact actual_pure_cell_avoidance n hn p hp segment
    · exact basicRight_not_cellFactor hn segment
    · exact actual_basicLeft_of_basicRight hk (n - 2) (period n)
        (fun p hp segment => basicRight_not_cellFactor hn segment) p hp segment
  · intro hmod
    exact actual_universal_cell_avoidance n (by omega) p hp segment
  · intro hmod
    obtain ⟨m, rfl⟩ : ∃ m, n = 3 * m + 1 := ⟨n / 3, by omega⟩
    have hm : 2 ≤ m := by omega
    have hdiv : (3 * m + 1) / 3 = m := by omega
    simpa only [hdiv] using
      (show ResidueOneAvoidance (3 * m + 1 - 2) m segment.deficitString from
        ⟨residueOnePair_not_cellFactor m hm hn segment,
          residueOneTriple_not_cellFactor m hm hn segment⟩)
  · intro hmod
    obtain ⟨m, rfl⟩ : ∃ m, n = 3 * m + 2 := ⟨n / 3, by omega⟩
    have hm : 2 ≤ m := by omega
    have hdiv : (3 * m + 2) / 3 = m := by omega
    simpa only [hdiv] using
      (show ResidueTwoAvoidance (3 * m + 2 - 2) (2 * m * (m + 1))
          segment.deficitString from
        ⟨residueTwoPair_not_cellFactor m hm hn segment,
          residueTwoTriple_not_cellFactor m hm hn segment⟩)

/-- The refined hereditary packing theorem on genuine deficit strings.
There is no geometric or realization premise remaining. -/
theorem actual_segment_chainPacking {n : ℕ} (hn : 7 ≤ n) {hk : 7 ≤ n + 1}
    {p : OverlapPath (n + 1)} {hp : IsBlockAligned p}
    (segment : BlockAlignedLightSegment hk p hp) :
    ChainPacking (n - 2) (period n) (chainAllowance n) segment.deficitString :=
  chainPacking_of_returnAvoidance hn (actual_segment_returnAvoidance hn segment)

/-- Alphabet-size formulation consumed by the accepted path and forest
reduction. The light segment and its whole block-aligned path are arbitrary. -/
theorem actual_lightSegment_chainPacking {k : ℕ} (hk : 8 ≤ k) {hk' : 7 ≤ k}
    {p : OverlapPath k} {hp : IsBlockAligned p}
    (segment : BlockAlignedLightSegment hk' p hp) :
    ChainPacking (k - 1 - 2) (period (k - 1)) (chainAllowance (k - 1))
      segment.deficitString := by
  cases k with
  | zero => omega
  | succ n => simpa only [Nat.add_sub_cancel] using
      actual_segment_chainPacking (by omega : 7 ≤ n) segment

/-- Empty and nonempty contiguous factors inherit the same packing bound. -/
theorem actual_segment_factor_chainPacking {n : ℕ} (hn : 7 ≤ n) {hk : 7 ≤ n + 1}
    {p : OverlapPath (n + 1)} {hp : IsBlockAligned p}
    (segment : BlockAlignedLightSegment hk p hp) (i j : ℕ) :
    ChainPacking (n - 2) (period n) (chainAllowance n)
      ((segment.deficitString.drop i).take j) :=
  (actual_segment_chainPacking hn segment).drop_take i j

end SuperpermutationLowerBound.Refinement
