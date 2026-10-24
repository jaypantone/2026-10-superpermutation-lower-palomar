module

public import pairs.GreedyLocal
public import pairs.CompletedFactors
public import SuperpermutationLowerBound.Refinement.ReturnPacking

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

open ChainReturns

theorem oneSuccessors_of_avoidance {a m : ℕ} {ls d : List ℕ}
    (H : RealizesChains a ls d) (hpos : ∀ x ∈ ls, 1 ≤ x)
    (havoid : ResidueOneAvoidance a m d) : OneSuccessors m ls := by
  intro pre after x y he hx
  have hym : y ≤ m := by
    by_contra hbad
    have he' : ls = pre ++ (x :: ([] ++ [y])) ++ after := by simpa using he
    exact havoid.pair (H _ (chainWindow_factor_of_list he' (by omega) (by omega)))
  refine ⟨hym, ?_⟩
  intro hafter
  by_contra hbad
  have hy : y = m := by omega
  cases after with
  | nil => contradiction
  | cons z zs =>
      have hz := hpos z (by simp [he])
      have he' : ls = pre ++ (x :: ([m] ++ [z])) ++ zs := by simpa [hy] using he
      exact havoid.triple (H _ (chainWindow_factor_of_list he' (by omega) hz))

theorem one_loss_zero_runs {a m R : ℕ} (hm : 3 ≤ m) (hR : 0 < R)
    {ls d : List ℕ} (H : RealizesChains a ls d)
    (hbound : ∀ x ∈ ls, x ≤ onePeriod m - 1)
    (hsucc : OneSuccessors m ls) (hne : ls ≠ [])
    (havoid : ¬ CellFactor a
      (repeatedCells (completedPair (onePeriod m - 1) (m - 1)) R) d) :
    ShortZeroRuns R (((greedyChunks m ls).dropLast).map
      (fun chunk => chunk.tile.loss (oneMean m))) := by
  let chunks := greedyChunks m ls
  have hchunks : chunks ≠ [] := greedyChunks_ne_nil m hne
  let last := chunks.getLast hchunks
  have hsplit : chunks = chunks.dropLast ++ [last] :=
    (List.dropLast_concat_getLast hchunks).symm
  have hvalid := greedy_one_valid m ls hbound hsucc
  apply shortZeroRuns_of_map
  intro before middle after he hz
  have hmiddle : middle = List.replicate middle.length
      (Chunk.pair (onePeriod m - 1) (m - 1)) := by
    apply List.eq_replicate_of_mem
    intro chunk hc
    have hc' : chunk ∈ chunks.dropLast := by
      change chunk ∈ (greedyChunks m ls).dropLast
      rw [he]
      simp [hc]
    exact (oneInterior_zero_iff m hm chunk (hvalid.interior chunk hc')).mp (hz chunk hc)
  by_contra hbad
  have hle : R ≤ middle.length := by omega
  let rest := List.replicate (middle.length - R)
    (Chunk.pair (onePeriod m - 1) (m - 1)) ++ after ++ [last]
  have hrest : rest ≠ [] := by simp [rest]
  have hrep : List.replicate middle.length (Chunk.pair (onePeriod m - 1) (m - 1)) =
      List.replicate R (Chunk.pair (onePeriod m - 1) (m - 1)) ++
      List.replicate (middle.length - R) (Chunk.pair (onePeriod m - 1) (m - 1)) := by
    rw [← List.replicate_add, Nat.add_sub_of_le hle]
  have he' : chunks = before ++
      List.replicate R (Chunk.pair (onePeriod m - 1) (m - 1)) ++ rest := by
    rw [hsplit, he, hmiddle, hrep]
    simp only [rest, List.append_assoc]
  have hf := repeated_pair_factor_of_chunks (greedyChunks_flatten m ls)
    (onePeriod m - 1) (m - 1) R hR hrest he'
  exact havoid (H _ hf)

/-- The paid bound for a nontrivial chain list, with all tile hypotheses
derived from actual literal chain restrictions. The only new geometric
input is the explicitly stated repeated-pair exclusion. -/
theorem one_chain_sum_paid {a m R : ℕ} (hm : 3 ≤ m) (hR : 0 < R)
    {ls d : List ℕ} (H : RealizesChains a ls d)
    (hbound : ∀ x ∈ ls, x ≤ onePeriod m - 1)
    (hsucc : OneSuccessors m ls) (hne : ls ≠ [])
    (havoid : ¬ CellFactor a
      (repeatedCells (completedPair (onePeriod m - 1) (m - 1)) R) d) :
    (ls.sum : ℚ) ≤ (onePeriod m : ℚ) +
      (oneMean m - 1 / (2 * (R : ℚ))) * ((ls.length : ℚ) - 1) := by
  let chunks := greedyChunks m ls
  have hchunks : chunks ≠ [] := greedyChunks_ne_nil m hne
  let last := chunks.getLast hchunks
  have hsplit : chunks = chunks.dropLast ++ [last] :=
    (List.dropLast_concat_getLast hchunks).symm
  have hvalid := greedy_one_valid m ls hbound hsucc
  have hz := one_loss_zero_runs hm hR H hbound hsucc hne havoid
  have hzero : ShortZeroRuns R ((chunks.dropLast.map Chunk.tile).map
      (Tile.loss (oneMean m))) := by simpa only [chunks, List.map_map, Function.comp_def] using hz
  have hpay : ∀ x ∈ (chunks.dropLast.map Chunk.tile).map (Tile.loss (oneMean m)),
      x = 0 ∨ 1 ≤ x := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨tile, ⟨chunk, hc, rfl⟩, rfl⟩ := hx
    exact oneInterior_pay m hm chunk (hvalid.interior chunk hc)
  have htiles : chunks.dropLast.map Chunk.tile ++ [last.tile] = greedyTiles m ls := by
    calc
      chunks.dropLast.map Chunk.tile ++ [last.tile] = chunks.map Chunk.tile := by
        simpa using (congrArg (List.map Chunk.tile) hsplit).symm
      _ = greedyTiles m ls := greedyChunks_tiles m ls
  have hsize : ∀ tile ∈ chunks.dropLast.map Chunk.tile ++ [last.tile], tile.chains ≤ 2 := by
    rw [htiles]
    intro tile ht
    rcases greedyTiles_sizes m ls tile ht with h | h <;> omega
  have hlast := oneFinal_loss m hm last (hvalid.last hchunks)
  have hpaid := paid_tile_bound (oneMean m) 1 ((m : ℚ)^2) R
    (chunks.dropLast.map Chunk.tile) last.tile (by norm_num) hR hsize hpay hzero hlast
  rw [htiles, greedyTiles_chainCount, greedyTiles_chainLength] at hpaid
  have hRpos : (0 : ℚ) < R := by exact_mod_cast hR
  have hreturn : 0 ≤ 1 / (2 * (R : ℚ)) := by positivity
  have hmean : (onePeriod m : ℚ) = oneMean m + (m : ℚ)^2 + 1 := by
    simp [onePeriod, oneMean]
    ring
  rw [hmean]
  nlinarith

theorem chainPacking_paid_one {a m R : ℕ} (ha : 3 ≤ a) (hm : 3 ≤ m) (hR : 0 < R)
    {d : List ℕ} (hbasic : BasicCellAvoidance a (onePeriod m) d)
    (hlocal : ResidueOneAvoidance a m d)
    (hrepeat : ¬ CellFactor a
      (repeatedCells (completedPair (onePeriod m - 1) (m - 1)) R) d) :
    ChainPacking a (onePeriod m) (2 * oneMean m - 1 / (R : ℚ)) d := by
  intro gaps hg before after hd
  let ls := chainLengths a gaps
  have hreal : RealizesChains a ls d := realizes_chainLengths ha hg hd
  have hpos : ∀ x ∈ ls, 1 ≤ x := chainLengths_positive a gaps
  have hne : ls ≠ [] := chainLengthsFrom_nonempty a 1 gaps
  have hp : 1 ≤ onePeriod m := by dsimp [onePeriod]; nlinarith
  have hsum : 2 * (ls.sum : ℚ) ≤ 2 * (onePeriod m : ℚ) +
      (2 * oneMean m - 1 / (R : ℚ)) * ((ls.length : ℚ) - 1) := by
    by_cases hlen : 2 ≤ ls.length
    · have hb := chain_bound_of_basic hp hreal hpos hbasic hlen
      have hpaid := one_chain_sum_paid hm hR hreal hb
        (oneSuccessors_of_avoidance hreal hpos hlocal) hne hrepeat
      have hRQ : (R : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hR
      have hcoef : 2 * (oneMean m - 1 / (2 * (R : ℚ))) =
          2 * oneMean m - 1 / (R : ℚ) := by field_simp
      rw [← hcoef]
      nlinarith
    · have hlen1 : ls.length = 1 := by
        have := List.length_pos_iff.mpr hne
        omega
      obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen1
      have hb := chain_bound_of_pure hreal hbasic.pure x (by simp [hx])
      have hbQ : (x : ℚ) ≤ onePeriod m := by exact_mod_cast hb
      simp only [hx, List.sum_singleton, List.length_singleton, Nat.cast_one,
        sub_self, mul_zero, add_zero]
      linarith
  dsimp [ls] at hsum
  rw [chainLengths_sum, chainLengths_length] at hsum
  push_cast at hsum
  linarith

end SuperpermutationLowerBound.Refinement
