module

public import pairs.GreedyChunks

@[expose] public section

namespace ChainReturns

theorem bounded_pair_loss (μ : ℚ) (A B x y : ℕ)
    (hμ : 2 * μ = (A : ℚ) + B) (hx : x ≤ A) (hy : y ≤ B) :
    (x = A ∧ y = B ∧ (Chunk.pair x y).tile.loss μ = 0) ∨
      1 ≤ (Chunk.pair x y).tile.loss μ := by
  by_cases heq : x = A ∧ y = B
  · refine Or.inl ⟨heq.1, heq.2, ?_⟩
    simp only [Chunk.tile, Tile.loss, Nat.cast_ofNat]
    rw [heq.1, heq.2]
    linarith
  · right
    have hsum : x + y + 1 ≤ A + B := by omega
    have hsumQ : (x : ℚ) + y + 1 ≤ (A : ℚ) + B := by exact_mod_cast hsum
    simp only [Chunk.tile, Tile.loss, Nat.cast_ofNat]
    linarith

def onePeriod (m : ℕ) : ℕ := m * (2 * m + 1)
def oneMean (m : ℕ) : ℚ := (m : ℚ)^2 + m - 1

def OneInterior (m : ℕ) : Chunk → Prop
  | .single x => x ≤ m
  | .pair x y => x ≤ onePeriod m - 1 ∧ y ≤ m - 1

theorem oneMean_twice (m : ℕ) (hm : 1 ≤ m) :
    2 * oneMean m = ((onePeriod m - 1 : ℕ) : ℚ) + (m - 1 : ℕ) := by
  have hp : 1 ≤ onePeriod m := by dsimp [onePeriod]; nlinarith
  rw [Nat.cast_sub hp, Nat.cast_sub hm]
  simp only [oneMean, onePeriod, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  ring

/-- Zero loss identifies the literal efficient pair, retaining both lengths. -/
theorem oneInterior_loss (m : ℕ) (hm : 3 ≤ m) (chunk : Chunk)
    (h : OneInterior m chunk) :
    (chunk = .pair (onePeriod m - 1) (m - 1) ∧ chunk.tile.loss (oneMean m) = 0) ∨
      1 ≤ chunk.tile.loss (oneMean m) := by
  cases chunk with
  | single x =>
      right
      have hxQ : (x : ℚ) ≤ m := by exact_mod_cast h
      have hmQ : (3 : ℚ) ≤ m := by exact_mod_cast hm
      simp only [Chunk.tile, Tile.loss, Nat.cast_one, oneMean]
      nlinarith
  | pair x y =>
      have hd := bounded_pair_loss (oneMean m) (onePeriod m - 1) (m - 1) x y
        (oneMean_twice m (by omega)) h.1 h.2
      rcases hd with ⟨hx, hy, hz⟩ | hp
      · exact Or.inl ⟨by rw [hx, hy], hz⟩
      · exact Or.inr hp

theorem oneInterior_pay (m : ℕ) (hm : 3 ≤ m) (chunk : Chunk)
    (h : OneInterior m chunk) :
    chunk.tile.loss (oneMean m) = 0 ∨ 1 ≤ chunk.tile.loss (oneMean m) := by
  rcases oneInterior_loss m hm chunk h with ⟨_, hz⟩ | hp
  · exact Or.inl hz
  · exact Or.inr hp

theorem oneInterior_zero_iff (m : ℕ) (hm : 3 ≤ m) (chunk : Chunk)
    (h : OneInterior m chunk) :
    chunk.tile.loss (oneMean m) = 0 ↔ chunk = .pair (onePeriod m - 1) (m - 1) := by
  constructor
  · intro hz
    rcases oneInterior_loss m hm chunk h with ⟨heq, _⟩ | hp
    · exact heq
    · rw [hz] at hp
      norm_num at hp
  · intro heq
    subst chunk
    simp only [Chunk.tile, Tile.loss, Nat.cast_ofNat]
    have hh := oneMean_twice m (by omega)
    linarith

end ChainReturns
