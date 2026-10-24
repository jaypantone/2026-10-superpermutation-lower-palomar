module

public import SuperpermutationLowerBound.Refinement.GeometryReturnCollision

@[expose] public section

/-!
Completed chains include their outgoing shortened cell. This file proves the
composition convention and the return-to-an-occupied-class implication directly
for inherited block-aligned light segments. It does not identify the order of
the residue-one efficient pair: that is the separate cycle-calculation task.
-/

namespace SuperpermutationLowerBound.Refinement

def completedChain (length : ℕ) : List Bool :=
  List.replicate (length - 1) false ++ [true]

def completedPair (first second : ℕ) : List Bool :=
  completedChain first ++ completedChain second

def repeatedCells (cells : List Bool) : ℕ → List Bool
  | 0 => []
  | r + 1 => cells ++ repeatedCells cells r

@[simp] theorem repeatedCells_length (cells : List Bool) (r : ℕ) :
    (repeatedCells cells r).length = r * cells.length := by
  induction r with
  | zero => simp [repeatedCells]
  | succ r ih => simp [repeatedCells, ih, Nat.succ_mul, Nat.add_comm]

theorem repeatedCells_ne_nil {cells : List Bool} {r : ℕ}
    (hcells : cells ≠ []) (hr : 0 < r) : repeatedCells cells r ≠ [] := by
  intro he
  have hz := congrArg List.length he
  have hp := List.length_pos_iff.mpr hcells
  simp only [repeatedCells_length, List.length_nil] at hz
  have := Nat.mul_pos hr hp
  omega

theorem completedChain_normalization (n : ℕ) (hn : 7 ≤ n)
    (length : ℕ) (hlength : 1 ≤ length) :
    cellNormalization n hn (completedChain length) =
      cellRho n hn * (cellG n hn) ^ length := by
  have hlength' : length - 1 + 1 = length := by omega
  simp only [completedChain, cellNormalization_append,
    cellNormalization_singleton_true, cellNormalization_replicate_false]
  rw [mul_assoc, ← pow_succ', hlength']

theorem completedPair_normalization (n : ℕ) (hn : 7 ≤ n)
    (first second : ℕ) (hfirst : 1 ≤ first) (hsecond : 1 ≤ second) :
    cellNormalization n hn (completedPair first second) =
      cellRho n hn * (cellG n hn) ^ second *
        cellRho n hn * (cellG n hn) ^ first := by
  simp only [completedPair, cellNormalization_append,
    completedChain_normalization n hn first hfirst,
    completedChain_normalization n hn second hsecond]
  exact (mul_assoc _ _ _).symm

theorem repeatedCells_normalization (n : ℕ) (hn : 7 ≤ n)
    (cells : List Bool) (r : ℕ) :
    cellNormalization n hn (repeatedCells cells r) =
      (cellNormalization n hn cells) ^ r := by
  induction r with
  | zero => simp [repeatedCells]
  | succ r ih => simp [repeatedCells, ih, pow_succ]

/-- Identity normalization at a later actual short run repeats its rotation
class. `CellFactor` includes that later short run and its bounding zero, so the
terminal-chain exception is not suppressed in this statement. -/
theorem actual_identity_cell_avoidance (n : ℕ) (hn : 7 ≤ n) {hk : 7 ≤ n + 1}
    (p : OverlapPath (n + 1)) (hp : IsBlockAligned p)
    (segment : BlockAlignedLightSegment hk p hp)
    (cells : List Bool) (hcells : cells ≠ [])
    (hreturn : cellNormalization n hn cells = 1) :
    ¬ CellFactor (n - 2) cells segment.deficitString := by
  intro hf
  obtain ⟨start, h⟩ := hf.exists_patternAt
  obtain ⟨e, he⟩ := h.cellWord_initial_coordinates hn
  apply h.cellWord_short_collision hn hcells (by decide) e he 0 (by omega)
  rw [hreturn]
  rfl

/-- The complete efficient-pair return implication, after its order has been
established. It applies to actual light segments, not abstract label strings. -/
theorem actual_periodic_pair_avoidance (n : ℕ) (hn : 7 ≤ n) {hk : 7 ≤ n + 1}
    (p : OverlapPath (n + 1)) (hp : IsBlockAligned p)
    (segment : BlockAlignedLightSegment hk p hp)
    (first second r : ℕ) (hfirst : 1 ≤ first) (hsecond : 1 ≤ second)
    (hr : 0 < r)
    (horder : (cellRho n hn * (cellG n hn) ^ second *
      cellRho n hn * (cellG n hn) ^ first) ^ r = 1) :
    ¬ CellFactor (n - 2) (repeatedCells (completedPair first second) r)
      segment.deficitString := by
  apply actual_identity_cell_avoidance n hn p hp segment
  · apply repeatedCells_ne_nil (r := r) _ hr
    simp [completedPair, completedChain]
  · rw [repeatedCells_normalization,
      completedPair_normalization n hn first second hfirst hsecond]
    exact horder

end SuperpermutationLowerBound.Refinement
