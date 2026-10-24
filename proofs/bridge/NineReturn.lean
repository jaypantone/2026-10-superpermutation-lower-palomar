module

public import bridge.NineGroup
public import pairs.TwoClassification
public import FinitePrefixReturns

@[expose] public section

namespace SuperpermutationLowerBound.ChainReturns
open SuperpermutationLowerBound.Refinement
open _root_.ChainReturns
open SuperpermutationLowerBound.Refinement.ChainReturns

/-- Completed cells of a list of greedy chunks, including the outgoing short cell. -/
def nineChunksCells (chunks : List Chunk) : List Bool :=
  completedChains (chunks.map Chunk.chains).flatten

def nineChunksNormalization (chunks : List Chunk) : Equiv.Perm (Fin 9) :=
  cellNormalization 8 (by omega) (nineChunksCells chunks)

theorem nineChunksCells_append (xs ys : List Chunk) :
    nineChunksCells (xs ++ ys) = nineChunksCells xs ++ nineChunksCells ys := by
  simp [nineChunksCells, completedChains_append]

theorem nineChunksCells_ne_nil {xs : List Chunk} (hne : xs ≠ []) :
    nineChunksCells xs ≠ [] := by
  cases xs with
  | nil => contradiction
  | cons c cs => cases c <;> simp [nineChunksCells, Chunk.chains, completedChains, completedChain]

theorem nineChunksNormalization_nil : nineChunksNormalization [] = 1 := by
  rfl

theorem nineChunksNormalization_append (xs ys : List Chunk) :
    nineChunksNormalization (xs ++ ys) =
      nineChunksNormalization ys * nineChunksNormalization xs := by
  simp [nineChunksNormalization, nineChunksCells_append, cellNormalization_append]

theorem nineChunksNormalization_mem (xs : List Chunk)
    (he : ∀ x ∈ xs, SmallTwoEfficient x) : nineChunksNormalization xs ∈ nineGroup := by
  induction xs with
  | nil => exact nineGroup_one
  | cons x xs ih =>
    have hi := ih (fun c hc => he c (by simp [hc]))
    have hx := he x (by simp)
    have hn : nineChunksNormalization (x :: xs) =
        nineChunksNormalization xs * nineChunkNormalization x := by
      simp [nineChunksNormalization, nineChunksCells, nineChunkNormalization,
        nineChunkCells, completedChains_append, cellNormalization_append]
    rw [hn]
    rcases hx with rfl | rfl | rfl
    · rw [nine_single_normalization]
      exact (nineGroup_mul_generators _ hi).1
    · rw [nine_pair_first_normalization]
      exact (nineGroup_mul_generators _ hi).2.1
    · rw [nine_pair_second_normalization]
      exact (nineGroup_mul_generators _ hi).2.2

/-- Twelve consecutive efficient interior chunks force a repeated occupied
rotation class. No abstract class assignment or restricted word predicate is assumed. -/
theorem nine_efficient_factor_length {hk : 7 ≤ 9}
    {P : OverlapPath 9} {hP : IsBlockAligned P}
    (segment : BlockAlignedLightSegment hk P hP) (chunks : List Chunk)
    (he : ∀ x ∈ chunks, SmallTwoEfficient x)
    (hf : CellFactor 6 (nineChunksCells chunks) segment.deficitString) :
    chunks.length < 12 := by
  rw [← nineGroup_card]
  apply finite_prefix_bound chunks nineChunksNormalization nineChunksNormalization_nil
    nineChunksNormalization_append nineGroup
  · intro i hi
    apply nineChunksNormalization_mem
    intro c hc
    exact he c (List.mem_of_mem_take hc)
  · intro before middle after hsplit hmiddle hreturn
    have hmark : MarkFactor (nineChunksCells middle) (nineChunksCells chunks) := by
      refine ⟨nineChunksCells before, nineChunksCells after, ?_⟩
      rw [hsplit, nineChunksCells_append, nineChunksCells_append]
    have hmid : CellFactor 6 (nineChunksCells middle) segment.deficitString := by
      obtain ⟨pre, post, hp⟩ := hf
      exact (hmark.to_cellFactor (by omega)).trans hp
    exact actual_identity_cell_avoidance 8 (by omega) P hP segment
      (nineChunksCells middle) (nineChunksCells_ne_nil hmiddle) hreturn hmid

end SuperpermutationLowerBound.ChainReturns
