module

public import pairs.ChunkPayment

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

open _root_.ChainReturns

theorem two_loss_zero_runs {a m : ℕ} (hm : 3 ≤ m)
    {ls d : List ℕ} (H : RealizesChains a ls d)
    (hbound : ∀ x ∈ ls, x ≤ twoMax m)
    (hsucc : TwoSuccessors m ls) (hne : ls ≠ [])
    (havoid : ¬ CellFactor a
      (repeatedCells (completedPair (twoMax m) (twoThreshold m - 2)) 2) d) :
    ShortZeroRuns 2 (((greedyChunks (twoThreshold m) ls).dropLast).map
      (fun chunk => chunk.tile.loss (twoMean m))) := by
  let chunks := greedyChunks (twoThreshold m) ls
  have hchunks : chunks ≠ [] := greedyChunks_ne_nil _ hne
  let last := chunks.getLast hchunks
  have hsplit : chunks = chunks.dropLast ++ [last] :=
    (List.dropLast_concat_getLast hchunks).symm
  have hvalid := greedy_two_valid m ls hbound hsucc
  have hε := twoEpsilon_pos m hm
  apply shortZeroRuns_of_map
  intro before middle after he hz
  have hmiddle : middle = List.replicate middle.length
      (Chunk.pair (twoMax m) (twoThreshold m - 2)) := by
    apply List.eq_replicate_of_mem
    intro chunk hc
    have hc' : chunk ∈ chunks.dropLast := by
      rw [he]
      simp [hc]
    rcases twoInterior_loss m hm chunk (hvalid.interior chunk hc') with h | h
    · exact h.1
    · have hh := hz chunk hc
      rw [hh] at h
      linarith
  by_contra hbad
  have hle : 2 ≤ middle.length := by omega
  let rest := List.replicate (middle.length - 2)
    (Chunk.pair (twoMax m) (twoThreshold m - 2)) ++ after ++ [last]
  have hrest : rest ≠ [] := by simp [rest]
  have hrep : List.replicate middle.length (Chunk.pair (twoMax m) (twoThreshold m - 2)) =
      List.replicate 2 (Chunk.pair (twoMax m) (twoThreshold m - 2)) ++
      List.replicate (middle.length - 2) (Chunk.pair (twoMax m) (twoThreshold m - 2)) := by
    rw [← List.replicate_add, Nat.add_sub_of_le hle]
  have he' : chunks = before ++
      List.replicate 2 (Chunk.pair (twoMax m) (twoThreshold m - 2)) ++ rest := by
    rw [hsplit, he, hmiddle, hrep]
    simp only [rest, List.append_assoc]
  have hf := repeated_pair_factor_of_chunks (greedyChunks_flatten _ ls)
    (twoMax m) (twoThreshold m - 2) 2 (by omega) hrest he'
  exact havoid (H _ hf)

theorem two_chain_sum_paid {a m : ℕ} (hm : 3 ≤ m)
    {ls d : List ℕ} (H : RealizesChains a ls d)
    (hbound : ∀ x ∈ ls, x ≤ twoMax m)
    (hsucc : TwoSuccessors m ls) (hne : ls ≠ [])
    (havoid : ¬ CellFactor a
      (repeatedCells (completedPair (twoMax m) (twoThreshold m - 2)) 2) d) :
    (ls.sum : ℚ) ≤ (twoMax m + 1 : ℕ) +
      (twoMean m - twoEpsilon m / 4) * ((ls.length : ℚ) - 1) := by
  have hvalid := greedy_two_valid m ls hbound hsucc
  have hpay : ∀ chunk ∈ (greedyChunks (twoThreshold m) ls).dropLast,
      chunk.tile.loss (twoMean m) = 0 ∨ twoEpsilon m ≤ chunk.tile.loss (twoMean m) := by
    intro chunk hc
    rcases twoInterior_loss m hm chunk (hvalid.interior chunk hc) with h | h
    · exact Or.inl h.2
    · exact Or.inr h
  have hlast := twoFinal_loss m (by omega) _
    (hvalid.last (greedyChunks_ne_nil _ hne))
  have hp := greedy_chain_sum_paid (twoThreshold m) 2 (twoMean m)
    (twoEpsilon m) (((m : ℚ) + 2) / 2) (by omega) (twoEpsilon_pos m hm)
    ls hne hpay hlast (two_loss_zero_runs hm H hbound hsucc hne havoid)
  have hmax := twoMean_max m (by omega)
  have heps : twoEpsilon m ≤ 1 := min_le_left _ _
  norm_num only [Nat.cast_ofNat] at hp
  rw [Nat.cast_add, Nat.cast_one]
  nlinarith

theorem chainPacking_paid_two {a m : ℕ} (ha : 3 ≤ a) (hm : 3 ≤ m)
    {d : List ℕ} (hbasic : BasicCellAvoidance a (twoMax m + 1) d)
    (hlocal : ResidueTwoAvoidance a (twoThreshold m) d)
    (hrepeat : ¬ CellFactor a
      (repeatedCells (completedPair (twoMax m) (twoThreshold m - 2)) 2) d) :
    ChainPacking a (twoMax m + 1) (2 * twoMean m - twoEpsilon m / 2) d := by
  intro gaps hg before after hd
  let ls := chainLengths a gaps
  have hreal : RealizesChains a ls d := realizes_chainLengths ha hg hd
  have hpos : ∀ x ∈ ls, 1 ≤ x := chainLengths_positive a gaps
  have hne : ls ≠ [] := chainLengthsFrom_nonempty a 1 gaps
  have hsum : 2 * (ls.sum : ℚ) ≤ 2 * (twoMax m + 1 : ℕ) +
      (2 * twoMean m - twoEpsilon m / 2) * ((ls.length : ℚ) - 1) := by
    by_cases hlen : 2 ≤ ls.length
    · have hb := chain_bound_of_basic (by omega : 1 ≤ twoMax m + 1)
        hreal hpos hbasic hlen
      simp only [Nat.add_sub_cancel] at hb
      have hp := two_chain_sum_paid hm hreal hb
        (twoSuccessors_of_avoidance (by omega) hreal hpos hlocal) hne hrepeat
      nlinarith
    · have hlen1 : ls.length = 1 := by
        have := List.length_pos_iff.mpr hne
        omega
      obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen1
      have hb := chain_bound_of_pure hreal hbasic.pure x (by simp [hx])
      have hbQ : (x : ℚ) ≤ (twoMax m + 1 : ℕ) := by exact_mod_cast hb
      simp only [hx, List.sum_singleton, List.length_singleton, Nat.cast_one,
        sub_self, mul_zero, add_zero]
      linarith
  dsimp [ls] at hsum
  rw [chainLengths_sum, chainLengths_length] at hsum
  push_cast at hsum
  linarith

end SuperpermutationLowerBound.Refinement
