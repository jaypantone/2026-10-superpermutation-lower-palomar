module

public import pairs.TwoLocal
public import pairs.CompletedFactors

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

open ChainReturns

/-- A bound on actual completed efficient factors gives the literal zero-run
bound for the interior greedy partition. Efficient tiles may have different
shapes or transfer maps. -/
theorem chunk_loss_zero_runs {a R threshold : ℕ} (hR : 0 < R)
    {ls d : List ℕ} (H : RealizesChains a ls d) (hne : ls ≠ [])
    (μ : ℚ) (Efficient : Chunk → Prop)
    (hclass : ∀ chunk ∈ (greedyChunks threshold ls).dropLast,
      chunk.tile.loss μ = 0 → Efficient chunk)
    (hfactor : ∀ middle : List Chunk, (∀ chunk ∈ middle, Efficient chunk) →
      CellFactor a (completedChains (middle.map Chunk.chains).flatten) d → middle.length < R) :
    ShortZeroRuns R (((greedyChunks threshold ls).dropLast).map
      (fun chunk => chunk.tile.loss μ)) := by
  let chunks := greedyChunks threshold ls
  have hchunks : chunks ≠ [] := greedyChunks_ne_nil threshold hne
  let last := chunks.getLast hchunks
  have hsplit : chunks = chunks.dropLast ++ [last] :=
    (List.dropLast_concat_getLast hchunks).symm
  apply shortZeroRuns_of_map
  intro before middle after he hz
  by_cases hmiddle : middle = []
  · simpa [hmiddle] using hR
  have he' : chunks = before ++ middle ++ (after ++ [last]) := by
    rw [hsplit, he]
    simp only [List.append_assoc]
  have hf := completed_chunk_factor (greedyChunks_flatten threshold ls)
    hmiddle (by simp : after ++ [last] ≠ []) he'
  apply hfactor middle _ (H _ hf)
  intro chunk hc
  apply hclass chunk _ (hz chunk hc)
  rw [he]
  simp [hc]

end SuperpermutationLowerBound.Refinement

namespace ChainReturns

theorem greedy_chain_sum_paid (threshold R : ℕ) (μ ε c : ℚ) (hR : 0 < R)
    (hε : 0 < ε) (ls : List ℕ) (hne : ls ≠ [])
    (hpay : ∀ chunk ∈ (greedyChunks threshold ls).dropLast,
      chunk.tile.loss μ = 0 ∨ ε ≤ chunk.tile.loss μ)
    (hlast : -c ≤ ((greedyChunks threshold ls).getLast
      (greedyChunks_ne_nil threshold hne)).tile.loss μ)
    (hzero : ShortZeroRuns R (((greedyChunks threshold ls).dropLast).map
      (fun chunk => chunk.tile.loss μ))) :
    (ls.sum : ℚ) ≤ (μ - ε / (2 * (R : ℚ))) * ls.length + c + ε := by
  let chunks := greedyChunks threshold ls
  have hchunks : chunks ≠ [] := greedyChunks_ne_nil threshold hne
  let last := chunks.getLast hchunks
  have hsplit : chunks = chunks.dropLast ++ [last] :=
    (List.dropLast_concat_getLast hchunks).symm
  have hz : ShortZeroRuns R ((chunks.dropLast.map Chunk.tile).map (Tile.loss μ)) := by
    simpa only [chunks, List.map_map, Function.comp_def] using hzero
  have hpay' : ∀ x ∈ (chunks.dropLast.map Chunk.tile).map (Tile.loss μ), x = 0 ∨ ε ≤ x := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨tile, ⟨chunk, hc, rfl⟩, rfl⟩ := hx
    exact hpay chunk hc
  have htiles : chunks.dropLast.map Chunk.tile ++ [last.tile] = greedyTiles threshold ls := by
    calc
      chunks.dropLast.map Chunk.tile ++ [last.tile] = chunks.map Chunk.tile := by
        simpa using (congrArg (List.map Chunk.tile) hsplit).symm
      _ = greedyTiles threshold ls := greedyChunks_tiles threshold ls
  have hsize : ∀ tile ∈ chunks.dropLast.map Chunk.tile ++ [last.tile], tile.chains ≤ 2 := by
    rw [htiles]
    intro tile ht
    rcases greedyTiles_sizes threshold ls tile ht with h | h <;> omega
  have hpaid := paid_tile_bound μ ε c R (chunks.dropLast.map Chunk.tile) last.tile
    hε hR hsize hpay' hz hlast
  rwa [htiles, greedyTiles_chainCount, greedyTiles_chainLength] at hpaid

end ChainReturns
