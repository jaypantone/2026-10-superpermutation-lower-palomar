module

public import pairs.GreedyLocal

@[expose] public section

namespace ChainReturns

def twoThreshold (m : ℕ) : ℕ := 2 * m * (m + 1)
def twoMax (m : ℕ) : ℕ := 2 * m * m + 3 * m
def twoMean (m : ℕ) : ℚ := ((twoMax m : ℚ) + (twoThreshold m - 2 : ℕ)) / 2
def twoEpsilon (m : ℕ) : ℚ := min 1 (((m : ℚ) - 2) / 2)

def TwoInterior (m : ℕ) : Chunk → Prop
  | .single x => x ≤ twoThreshold m
  | .pair x y => x ≤ twoMax m ∧ twoThreshold m < x ∧
      y ≤ twoThreshold m - 1 ∧ (twoThreshold m + 2 ≤ x → y ≤ twoThreshold m - 2)

def TwoFinal (m : ℕ) : Chunk → Prop
  | .single x => x ≤ twoMax m
  | .pair x y => x ≤ twoMax m ∧ y ≤ twoThreshold m - 1

theorem twoMean_twice (m : ℕ) :
    2 * twoMean m = (twoMax m : ℚ) + (twoThreshold m - 2 : ℕ) := by
  dsimp [twoMean]
  ring

theorem twoMean_threshold (m : ℕ) (hm : 2 ≤ m) :
    twoMean m - twoThreshold m = ((m : ℚ) - 2) / 2 := by
  have hv : 2 ≤ twoThreshold m := by dsimp [twoThreshold]; nlinarith
  rw [twoMean, Nat.cast_sub hv]
  simp only [twoMax, twoThreshold, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring

theorem twoMean_max (m : ℕ) (hm : 2 ≤ m) :
    (twoMax m : ℚ) - twoMean m = ((m : ℚ) + 2) / 2 := by
  have h := twoMean_threshold m hm
  have hd : (twoMax m : ℚ) - twoThreshold m = m := by
    simp only [twoMax, twoThreshold, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring
  linarith

theorem twoEpsilon_pos (m : ℕ) (hm : 3 ≤ m) : 0 < twoEpsilon m := by
  have hmQ : (3 : ℚ) ≤ m := by exact_mod_cast hm
  dsimp [twoEpsilon]
  apply lt_min <;> linarith

theorem twoInterior_loss (m : ℕ) (hm : 3 ≤ m) (chunk : Chunk)
    (h : TwoInterior m chunk) :
    (chunk = .pair (twoMax m) (twoThreshold m - 2) ∧ chunk.tile.loss (twoMean m) = 0) ∨
      twoEpsilon m ≤ chunk.tile.loss (twoMean m) := by
  have hsmall : twoEpsilon m ≤ ((m : ℚ) - 2) / 2 := min_le_right _ _
  have hone : twoEpsilon m ≤ 1 := min_le_left _ _
  have hmean := twoMean_threshold m (by omega)
  have hmQ : (3 : ℚ) ≤ m := by exact_mod_cast hm
  have hv : 2 ≤ twoThreshold m := by dsimp [twoThreshold]; nlinarith
  cases chunk with
  | single x =>
      right
      have hx : (x : ℚ) ≤ twoThreshold m := by exact_mod_cast h
      simp only [Chunk.tile, Tile.loss, Nat.cast_one]
      linarith
  | pair x y =>
      simp only [TwoInterior] at h
      by_cases hx : x = twoThreshold m + 1
      · right
        have hs : x + y ≤ 2 * twoThreshold m := by omega
        have hsQ : (x : ℚ) + y ≤ 2 * (twoThreshold m : ℚ) := by exact_mod_cast hs
        simp only [Chunk.tile, Tile.loss, Nat.cast_ofNat]
        linarith
      · have hy := h.2.2.2 (by omega)
        rcases bounded_pair_loss (twoMean m) (twoMax m) (twoThreshold m - 2)
          x y (twoMean_twice m) h.1 hy with ⟨hx, hy, hz⟩ | hp
        · exact Or.inl ⟨by rw [hx, hy], hz⟩
        · exact Or.inr (hone.trans hp)

theorem twoFinal_loss (m : ℕ) (hm : 2 ≤ m) (chunk : Chunk)
    (h : TwoFinal m chunk) : -(((m : ℚ) + 2) / 2) ≤ chunk.tile.loss (twoMean m) := by
  have hmQ : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have hv : 2 ≤ twoThreshold m := by dsimp [twoThreshold]; nlinarith
  have hmax := twoMean_max m hm
  cases chunk with
  | single x =>
      have hx : (x : ℚ) ≤ twoMax m := by exact_mod_cast h
      simp only [Chunk.tile, Tile.loss, Nat.cast_one]
      linarith
  | pair x y =>
      simp only [TwoFinal] at h
      have hx : (x : ℚ) ≤ twoMax m := by exact_mod_cast h.1
      have hy : (y : ℚ) ≤ (twoThreshold m : ℚ) - 1 := by
        have hy' : y + 1 ≤ twoThreshold m := by omega
        have hyQ : (y : ℚ) + 1 ≤ twoThreshold m := by exact_mod_cast hy'
        linarith
      have hmean := twoMean_threshold m hm
      simp only [Chunk.tile, Tile.loss, Nat.cast_ofNat]
      linarith

def SmallTwoEfficient (chunk : Chunk) : Prop :=
  chunk = .single 12 ∨ chunk = .pair 13 11 ∨ chunk = .pair 14 10

theorem smallTwoInterior_loss (chunk : Chunk) (h : TwoInterior 2 chunk) :
    (SmallTwoEfficient chunk ∧ chunk.tile.loss 12 = 0) ∨ 1 ≤ chunk.tile.loss 12 := by
  cases chunk with
  | single x =>
      have hx : x ≤ 12 := by norm_num [TwoInterior, twoThreshold] at h; exact h
      by_cases he : x = 12
      · subst x
        left
        norm_num [SmallTwoEfficient, Chunk.tile, Tile.loss]
      · right
        have hx' : x + 1 ≤ 12 := by omega
        have hxQ : (x : ℚ) + 1 ≤ 12 := by exact_mod_cast hx'
        norm_num [Chunk.tile, Tile.loss]
        linarith
  | pair x y =>
      norm_num [TwoInterior, twoThreshold, twoMax] at h
      have hcases : x = 13 ∨ x = 14 := by omega
      rcases hcases with rfl | rfl
      · rcases bounded_pair_loss 12 13 11 13 y (by norm_num) (by omega) h.2.2.1 with
          ⟨_, hy, hz⟩ | hp
        · exact Or.inl ⟨Or.inr (Or.inl (by rw [hy])), hz⟩
        · exact Or.inr hp
      · rcases bounded_pair_loss 12 14 10 14 y (by norm_num) (by omega)
          (h.2.2.2 (by omega)) with ⟨_, hy, hz⟩ | hp
        · exact Or.inl ⟨Or.inr (Or.inr (by rw [hy])), hz⟩
        · exact Or.inr hp

end ChainReturns
