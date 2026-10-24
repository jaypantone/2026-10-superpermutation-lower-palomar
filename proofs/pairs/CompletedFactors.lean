module

public import pairs.PeriodicReturns
public import pairs.GreedyChunks

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

def completedChains : List ℕ → List Bool
  | [] => []
  | x :: xs => completedChain x ++ completedChains xs

theorem completedChains_append (xs ys : List ℕ) :
    completedChains (xs ++ ys) = completedChains xs ++ completedChains ys := by
  induction xs with
  | nil => simp [completedChains]
  | cons x xs ih => simp [completedChains, ih, List.append_assoc]

theorem completedChains_eq (xs : List ℕ) (hne : xs ≠ []) :
    completedChains xs = chainCells xs ++ [true] := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
      by_cases hx : xs = []
      · subst xs
        simp [completedChains, completedChain, chainCells]
      · simp [completedChains, completedChain, chainCells, hx, ih hx, List.append_assoc]

theorem completedChains_factor (before middle after : List ℕ)
    (hmiddle : middle ≠ []) (hafter : after ≠ []) :
    MarkFactor (completedChains middle) (chainCells (before ++ middle ++ after)) := by
  rw [completedChains_eq middle hmiddle]
  by_cases hbefore : before = []
  · subst before
    refine ⟨[], chainCells after, ?_⟩
    simp [chainCells_append hmiddle hafter, List.append_assoc]
  · refine ⟨chainCells before ++ [true], chainCells after, ?_⟩
    rw [chainCells_append (by simp [hbefore] : before ++ middle ≠ []) hafter,
      chainCells_append hbefore hmiddle]
    simp [List.append_assoc]

theorem completed_pair_chains (x y : ℕ) :
    completedChains [x, y] = completedPair x y := by
  simp [completedChains, completedPair]

theorem completed_replicate_pairs (x y R : ℕ) :
    completedChains ((List.replicate R [x, y]).flatten) =
      repeatedCells (completedPair x y) R := by
  induction R with
  | zero => rfl
  | succ R ih =>
      simp [List.replicate_succ, completedChains, ih, repeatedCells,
        completedPair, List.append_assoc]

open ChainReturns in
theorem completed_chunk_factor {ls : List ℕ} {chunks before middle after : List Chunk}
    (hflat : (chunks.map Chunk.chains).flatten = ls)
    (hmiddle : middle ≠ []) (hafter : after ≠ [])
    (he : chunks = before ++ middle ++ after) :
    MarkFactor (completedChains (middle.map Chunk.chains).flatten) (chainCells ls) := by
  have hmf : (middle.map Chunk.chains).flatten ≠ [] := by
    cases middle with
    | nil => contradiction
    | cons chunk rest => cases chunk <;> simp [Chunk.chains]
  have haf : (after.map Chunk.chains).flatten ≠ [] := by
    cases after with
    | nil => contradiction
    | cons chunk rest => cases chunk <;> simp [Chunk.chains]
  have hf := completedChains_factor (before.map Chunk.chains).flatten
    (middle.map Chunk.chains).flatten (after.map Chunk.chains).flatten hmf haf
  have hls : ls = (before.map Chunk.chains).flatten ++
      (middle.map Chunk.chains).flatten ++ (after.map Chunk.chains).flatten := by
    rw [← hflat, he]
    simp
  simpa [hls] using hf

open ChainReturns in
theorem repeated_pair_factor_of_chunks {ls : List ℕ} {chunks before after : List Chunk}
    (hflat : (chunks.map Chunk.chains).flatten = ls)
    (b c R : ℕ) (hR : 0 < R) (hafter : after ≠ [])
    (he : chunks = before ++ List.replicate R (.pair b c) ++ after) :
    MarkFactor (repeatedCells (completedPair b c) R) (chainCells ls) := by
  have haf : (after.map Chunk.chains).flatten ≠ [] := by
    cases after with
    | nil => contradiction
    | cons chunk rest => cases chunk <;> simp [Chunk.chains]
  have hmid : (List.replicate R [b, c]).flatten ≠ [] := by
    cases R with
    | zero => omega
    | succ R => simp [List.replicate_succ]
  have hf := completedChains_factor (before.map Chunk.chains).flatten
    (List.replicate R [b, c]).flatten (after.map Chunk.chains).flatten hmid haf
  rw [completed_replicate_pairs] at hf
  have hls : ls = (before.map Chunk.chains).flatten ++
      (List.replicate R [b, c]).flatten ++ (after.map Chunk.chains).flatten := by
    rw [← hflat, he]
    simp [Chunk.chains]
  simpa [hls] using hf

end SuperpermutationLowerBound.Refinement
