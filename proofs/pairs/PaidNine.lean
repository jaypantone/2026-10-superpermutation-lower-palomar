module

public import pairs.ChunkPayment
public import bridge.NineReturn
public import SuperpermutationLowerBound.Refinement.GeometryPacking

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

open _root_.ChainReturns

/-- The frozen nine-symbol packing constant, using the actual order-twelve
prefix collision for its three different efficient tile types. -/
theorem actual_chainPacking_nine {hk : 7 ≤ 9} {p : OverlapPath 9}
    {hp : IsBlockAligned p} (segment : BlockAlignedLightSegment hk p hp) :
    ChainPacking 6 15 (287 / 12) segment.deficitString := by
  have hold := actual_segment_returnAvoidance (n := 8) (by omega) segment
  have hbasic : BasicCellAvoidance 6 15 segment.deficitString := by
    simpa [period] using hold.basic
  have hlocal : ResidueTwoAvoidance 6 (twoThreshold 2) segment.deficitString := by
    simpa [twoThreshold] using hold.residueTwo (by norm_num)
  intro gaps hg before after hd
  let ls := chainLengths 6 gaps
  have hreal : RealizesChains 6 ls segment.deficitString := realizes_chainLengths (by omega) hg hd
  have hpos : ∀ x ∈ ls, 1 ≤ x := chainLengths_positive 6 gaps
  have hne : ls ≠ [] := chainLengthsFrom_nonempty 6 1 gaps
  have hsum : 2 * (ls.sum : ℚ) ≤ 30 + (287 / 12 : ℚ) * ((ls.length : ℚ) - 1) := by
    by_cases hlen : 2 ≤ ls.length
    · have hb : ∀ x ∈ ls, x ≤ twoMax 2 := by
        simpa [twoMax] using chain_bound_of_basic (by omega : 1 ≤ 15) hreal hpos hbasic hlen
      have hs := twoSuccessors_of_avoidance (by omega : 2 ≤ 2) hreal hpos hlocal
      have hv := greedy_two_valid 2 ls hb hs
      have hpay : ∀ chunk ∈ (greedyChunks 12 ls).dropLast,
          chunk.tile.loss 12 = 0 ∨ 1 ≤ chunk.tile.loss 12 := by
        intro chunk hc
        rcases smallTwoInterior_loss chunk (hv.interior chunk hc) with ⟨_, hz⟩ | hp
        · exact Or.inl hz
        · exact Or.inr hp
      have hclass : ∀ chunk ∈ (greedyChunks 12 ls).dropLast,
          chunk.tile.loss 12 = 0 → SmallTwoEfficient chunk := by
        intro chunk hc hz
        rcases smallTwoInterior_loss chunk (hv.interior chunk hc) with ⟨he, _⟩ | hp
        · exact he
        · rw [hz] at hp
          norm_num at hp
      have hf : ∀ middle : List Chunk, (∀ chunk ∈ middle, SmallTwoEfficient chunk) →
          CellFactor 6 (completedChains (middle.map Chunk.chains).flatten) segment.deficitString →
          middle.length < 12 := by
        intro middle he hh
        exact SuperpermutationLowerBound.ChainReturns.nine_efficient_factor_length
          segment middle he hh
      have hz := chunk_loss_zero_runs (threshold := 12) (by omega : 0 < 12)
        hreal hne 12 SmallTwoEfficient hclass hf
      have hlast : -(2 : ℚ) ≤ ((greedyChunks 12 ls).getLast
          (greedyChunks_ne_nil 12 hne)).tile.loss 12 := by
        have hh := twoFinal_loss 2 (by omega) _ (hv.last (greedyChunks_ne_nil _ hne))
        norm_num [twoMean, twoThreshold, twoMax] at hh
        exact hh
      have hp := greedy_chain_sum_paid 12 12 12 1 2 (by omega) (by norm_num)
        ls hne hpay hlast hz
      norm_num only [Nat.cast_ofNat] at hp
      linarith
    · have hlen1 : ls.length = 1 := by
        have := List.length_pos_iff.mpr hne
        omega
      obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen1
      have hb := chain_bound_of_pure hreal hbasic.pure x (by simp [hx])
      have hbQ : (x : ℚ) ≤ 15 := by exact_mod_cast hb
      simp only [hx, List.sum_singleton, List.length_singleton, Nat.cast_one,
        sub_self, mul_zero, add_zero]
      linarith
  dsimp [ls] at hsum
  rw [chainLengths_sum, chainLengths_length] at hsum
  push_cast at hsum
  linarith

end SuperpermutationLowerBound.Refinement
