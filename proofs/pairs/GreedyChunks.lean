module

public import pairs.PaidTiles

@[expose] public section

namespace ChainReturns

/-- A tile before forgetting the individual chain lengths. -/
inductive Chunk where
  | single (x : ℕ)
  | pair (x y : ℕ)
  deriving DecidableEq

def Chunk.chains : Chunk → List ℕ
  | .single x => [x]
  | .pair x y => [x, y]

def Chunk.tile : Chunk → Tile
  | .single x => ⟨1, x⟩
  | .pair x y => ⟨2, (x : ℚ) + y⟩

def greedyChunks (threshold : ℕ) : List ℕ → List Chunk
  | [] => []
  | [x] => [.single x]
  | x :: y :: xs =>
      if x ≤ threshold then .single x :: greedyChunks threshold (y :: xs)
      else .pair x y :: greedyChunks threshold xs

theorem greedyChunks_tiles (threshold : ℕ) (xs : List ℕ) :
    (greedyChunks threshold xs).map Chunk.tile = greedyTiles threshold xs := by
  induction xs using List.twoStepInduction with
  | nil => simp [greedyChunks, greedyTiles]
  | singleton x => simp [greedyChunks, greedyTiles, Chunk.tile]
  | cons_cons x y xs ihAfter ihCons =>
      by_cases h : x ≤ threshold
      · simp [greedyChunks, greedyTiles, h, Chunk.tile, ihCons]
      · simp [greedyChunks, greedyTiles, h, Chunk.tile, ihAfter]

theorem greedyChunks_flatten (threshold : ℕ) (xs : List ℕ) :
    ((greedyChunks threshold xs).map Chunk.chains).flatten = xs := by
  induction xs using List.twoStepInduction with
  | nil => simp [greedyChunks]
  | singleton x => simp [greedyChunks, Chunk.chains]
  | cons_cons x y xs ihAfter ihCons =>
      by_cases h : x ≤ threshold
      · simp [greedyChunks, h, Chunk.chains, ihCons]
      · simp [greedyChunks, h, Chunk.chains, ihAfter]

/-- Pulling back a zero-loss string retains its literal tile positions. -/
theorem shortZeroRuns_of_map {α : Type*} (loss : α → ℚ) (R : ℕ) (xs : List α)
    (h : ∀ before middle after : List α,
      xs = before ++ middle ++ after →
      (∀ x ∈ middle, loss x = 0) → middle.length < R) :
    ShortZeroRuns R (xs.map loss) := by
  intro pre post k he
  obtain ⟨left, after, hx, hl, ha⟩ := List.map_eq_append_iff.mp he
  obtain ⟨before, middle, hleft, hb, hm⟩ := List.map_eq_append_iff.mp hl
  have hlen : middle.length = k := by
    have hh := congrArg List.length hm
    simpa using hh
  have hz : ∀ x ∈ middle, loss x = 0 := by
    apply List.map_eq_replicate_iff.mp
    simpa [hlen] using hm
  have hs := h before middle after (by simpa [hleft] using hx) hz
  simpa [hlen] using hs

end ChainReturns
