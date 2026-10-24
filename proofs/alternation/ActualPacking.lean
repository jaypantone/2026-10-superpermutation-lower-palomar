module

public import alternation.AlternatingActualReturn
public import alternation.AlternatingFactors
public import SuperpermutationLowerBound.Refinement.GeometryPacking
public import bridge.GenericTransfer

@[expose] public section

namespace SuperpermutationLowerBound.Refinement.ChainReturns

open SuperpermutationLowerBound.Refinement

def alternatingP (m : ℕ) : ℚ := 2 * (m : ℚ) + 1 / 2 +
  1 / (4 * (SuperpermutationBounds.ChainReturns.returnZero (3 * m) : ℚ))

def alternatingT (m : ℕ) : ℚ := 4 * (m : ℚ) - 3 -
  1 / (2 * (SuperpermutationBounds.ChainReturns.returnZero (3 * m) : ℚ))

def alternatingPAt (m : ℕ) (U : ℚ) : ℚ := 2 * (m : ℚ) + 1 / 2 + 1 / (4 * U)
def alternatingTAt (m : ℕ) (U : ℚ) : ℚ := 4 * (m : ℚ) - 3 - 1 / (2 * U)

theorem alternating_allowance_monotone (m : ℕ) {R U q : ℚ}
    (hR : 0 < R) (hRU : R ≤ U) (hq : 2 ≤ q) :
    2 * alternatingPAt m R + alternatingTAt m R * (q - 1) ≤
      2 * alternatingPAt m U + alternatingTAt m U * (q - 1) := by
  have hU : 0 < U := lt_of_lt_of_le hR hRU
  have hinv : 1 / (2 * U) ≤ 1 / (2 * R) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hprod := mul_nonneg (sub_nonneg.mpr hinv) (show 0 ≤ q - 2 by linarith)
  have hRhalf : 1 / (4 * R) = (1 / (2 * R)) / 2 := by
    field_simp [ne_of_gt hR] <;> ring
  have hUhalf : 1 / (4 * U) = (1 / (2 * U)) / 2 := by
    field_simp [ne_of_gt hU] <;> ring
  unfold alternatingPAt alternatingTAt
  rw [hRhalf, hUhalf]
  nlinarith

theorem actual_no_alternatingFactor (m : ℕ) (hm : 3 ≤ m) (hn : 7 ≤ 3 * m)
    {hk : 7 ≤ 3 * m + 1} {P : OverlapPath (3 * m + 1)} {hP : IsBlockAligned P}
    (segment : BlockAlignedLightSegment hk P hP) {ls : List ℕ}
    (hreal : RealizesChains (3 * m - 2) ls segment.deficitString) :
    NoAlternatingFactor (2 * m - 1)
      (SuperpermutationBounds.ChainReturns.returnZero (3 * m)) ls := by
  let R := SuperpermutationBounds.ChainReturns.returnZero (3 * m)
  have hR : 0 < R := SuperpermutationBounds.ChainReturns.returnZero_pos (by omega)
  have hp := alternating_pair_power m hm hn
  have hp' : (cellRho (3 * m) hn * (cellG (3 * m) hn) ^ (2 * m - 1) *
      cellRho (3 * m) hn * (cellG (3 * m) hn) ^ (2 * m - 2)) ^ R = 1 := by
    have hh := reversed_pair_return
      (cellRho (3 * m) hn * (cellG (3 * m) hn) ^ (2 * m - 1))
      (cellRho (3 * m) hn * (cellG (3 * m) hn) ^ (2 * m - 2)) R
      (by simpa only [mul_assoc] using hp)
    simpa only [mul_assoc] using hh
  apply no_alternatingFactor_of_periodic_avoidance hreal
  · apply actual_periodic_pair_avoidance (3 * m) hn P hP segment
      (2 * m - 1) (2 * m - 1 - 1) R (by omega) (by omega) hR
    simpa only [show 2 * m - 1 - 1 = 2 * m - 2 by omega] using hp
  · apply actual_periodic_pair_avoidance (3 * m) hn P hP segment
      (2 * m - 1 - 1) (2 * m - 1) R (by omega) (by omega) hR
    simpa only [show 2 * m - 1 - 1 = 2 * m - 2 by omega] using hp'

theorem actual_alternating_chain_sum (m : ℕ) (hm : 3 ≤ m) (hn : 7 ≤ 3 * m)
    {hk : 7 ≤ 3 * m + 1} {P : OverlapPath (3 * m + 1)} {hP : IsBlockAligned P}
    (segment : BlockAlignedLightSegment hk P hP) {ls : List ℕ}
    (hreal : RealizesChains (3 * m - 2) ls segment.deficitString)
    (hne : ls ≠ []) (hpos : ∀ x ∈ ls, 1 ≤ x) :
    2 * (ls.sum : ℚ) ≤ 2 * alternatingP m + alternatingT m * ((ls.length : ℚ) - 1) := by
  have H := actual_segment_returnAvoidance hn segment
  have hp : period (3 * m) = 2 * m := by simp [period]
  have hpbound := chain_bound_of_pure hreal H.basic.pure
  rw [hp] at hpbound
  let R := SuperpermutationBounds.ChainReturns.returnZero (3 * m)
  have hR : 1 ≤ R := SuperpermutationBounds.ChainReturns.returnZero_pos (by omega)
  by_cases hq : 2 ≤ ls.length
  · have hb := chain_bound_of_basic (by rw [hp]; omega) hreal hpos H.basic hq
    rw [hp] at hb
    have ht := fourChainTrap_of_universal hreal (H.residueZero (by omega))
    rw [hp] at ht
    have ha := actual_no_alternatingFactor m hm hn segment hreal
    have halt := (boundedAlternation_of_no_factor (2 * m - 1) R ls hb ha).interior
    have hs := alternation_allowance_nontrivial (b := 2 * m - 1) (by omega) hR ls hq
      (fun x hx => ⟨hpos x hx, hb x hx⟩) ht halt
    have hbcast : ((2 * m - 1 : ℕ) : ℚ) = 2 * (m : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * m)]
      push_cast
      rfl
    rw [hbcast] at hs
    unfold alternatingP alternatingT
    dsimp [R] at hs
    linarith
  · have hlen : ls.length = 1 := by
      have := List.length_pos_iff.mpr hne
      omega
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hlen
    have hx : x ≤ 2 * m := hpbound x (by simp)
    have hxQ : (x : ℚ) ≤ 2 * (m : ℚ) := by exact_mod_cast hx
    have hfrac : (0 : ℚ) ≤ 1 / (4 * (R : ℚ)) := by positivity
    simp only [List.sum_singleton, List.length_singleton, Nat.cast_one, sub_self,
      mul_zero, add_zero, alternatingP]
    dsimp [R] at hfrac
    linarith

/-- The new alternating estimate on every genuine light segment. There is
no assumed return identity, abstract-chain realization, or bounded-factor
premise in this theorem's hypotheses. -/
theorem actual_segment_alternating_packing (m : ℕ) (hm : 3 ≤ m)
    {hk : 7 ≤ 3 * m + 1} {P : OverlapPath (3 * m + 1)} {hP : IsBlockAligned P}
    (segment : BlockAlignedLightSegment hk P hP) :
    ChainPacking (3 * m - 2) (alternatingP m) (alternatingT m) segment.deficitString := by
  intro gaps hg before after hd
  have hreal := realizes_chainLengths (by omega : 3 ≤ 3 * m - 2) hg hd
  have hs := actual_alternating_chain_sum m hm (by omega) segment hreal
    (chainLengthsFrom_nonempty (3 * m - 2) 1 gaps)
    (chainLengths_positive (3 * m - 2) gaps)
  rw [chainLengths_sum, chainLengths_length] at hs
  push_cast at hs
  linarith

theorem alternating_actualPacking (m : ℕ) (hm : 3 ≤ m) :
    SuperpermutationLowerBound.ChainReturns.ActualPacking (3 * m + 1) (by omega)
      (alternatingP m) (alternatingT m) := by
  intro P hP segment
  simpa only [Nat.add_sub_cancel] using actual_segment_alternating_packing m hm segment

theorem actual_alternating_chain_sum_upper (m : ℕ) (hm : 3 ≤ m) (hn : 7 ≤ 3 * m)
    (U : ℚ) (hU : (SuperpermutationBounds.ChainReturns.returnZero (3 * m) : ℚ) ≤ U)
    {hk : 7 ≤ 3 * m + 1} {P : OverlapPath (3 * m + 1)} {hP : IsBlockAligned P}
    (segment : BlockAlignedLightSegment hk P hP) {ls : List ℕ}
    (hreal : RealizesChains (3 * m - 2) ls segment.deficitString)
    (hne : ls ≠ []) (hpos : ∀ x ∈ ls, 1 ≤ x) :
    2 * (ls.sum : ℚ) ≤ 2 * alternatingPAt m U + alternatingTAt m U * ((ls.length : ℚ) - 1) := by
  have hR : (0 : ℚ) < SuperpermutationBounds.ChainReturns.returnZero (3 * m) := by
    exact_mod_cast SuperpermutationBounds.ChainReturns.returnZero_pos (by omega : 2 ≤ 3 * m)
  by_cases hq : 2 ≤ ls.length
  · have hs := actual_alternating_chain_sum m hm hn segment hreal hne hpos
    have hmono := alternating_allowance_monotone m hR hU
      (by exact_mod_cast hq : (2 : ℚ) ≤ ls.length)
    exact hs.trans hmono
  · have hlen : ls.length = 1 := by
      have := List.length_pos_iff.mpr hne
      omega
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hlen
    have hpbound := chain_bound_of_pure hreal (actual_segment_returnAvoidance hn segment).basic.pure
    have hp : period (3 * m) = 2 * m := by simp [period]
    rw [hp] at hpbound
    have hx : (x : ℚ) ≤ 2 * (m : ℚ) := by exact_mod_cast hpbound x (by simp)
    have hfrac : (0 : ℚ) ≤ 1 / (4 * U) := by have := lt_of_lt_of_le hR hU; positivity
    simp only [List.sum_singleton, List.length_singleton, Nat.cast_one, sub_self,
      mul_zero, add_zero, alternatingPAt]
    linarith

theorem alternating_actualPacking_upper (m : ℕ) (hm : 3 ≤ m) (U : ℚ)
    (hU : (SuperpermutationBounds.ChainReturns.returnZero (3 * m) : ℚ) ≤ U) :
    SuperpermutationLowerBound.ChainReturns.ActualPacking (3 * m + 1) (by omega)
      (alternatingPAt m U) (alternatingTAt m U) := by
  intro P hP segment
  change ChainPacking (3 * m - 2) (alternatingPAt m U) (alternatingTAt m U) segment.deficitString
  intro gaps hg before after hd
  have hreal := realizes_chainLengths (by omega : 3 ≤ 3 * m - 2) hg hd
  have hs := actual_alternating_chain_sum_upper m hm (by omega) U hU segment hreal
    (chainLengthsFrom_nonempty (3 * m - 2) 1 gaps)
    (chainLengths_positive (3 * m - 2) gaps)
  rw [chainLengths_sum, chainLengths_length] at hs
  push_cast at hs
  linarith

theorem alternating_actualPacking_quadratic (m : ℕ) (hm : 3 ≤ m) :
    SuperpermutationLowerBound.ChainReturns.ActualPacking (3 * m + 1) (by omega)
      (alternatingPAt m ((3 * (m : ℚ)) ^ 2 / 4))
      (alternatingTAt m ((3 * (m : ℚ)) ^ 2 / 4)) := by
  apply alternating_actualPacking_upper m hm
  have hn := SuperpermutationBounds.ChainReturns.returnZero_quadratic (by omega : 2 ≤ 3 * m)
  have hq : 4 * (SuperpermutationBounds.ChainReturns.returnZero (3 * m) : ℚ) ≤
      (3 * (m : ℚ)) ^ 2 := by exact_mod_cast hn
  linarith

end SuperpermutationLowerBound.Refinement.ChainReturns
