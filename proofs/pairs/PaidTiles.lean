module

public import Mathlib.Tactic

@[expose] public section

/-!
The ordered loss count in Lemma 4.1 of the frozen manuscript.

`ShortZeroRuns` is the literal contiguous-factor hypothesis: every zero
string, including an initial or final one, has fewer than `R` entries.
The proof constructs the intervening marked gaps. No numerical packing
inequality or fractional substitute is assumed.
-/

namespace ChainReturns

def ShortZeroRuns (R : ℕ) (xs : List ℚ) : Prop :=
  ∀ (before after : List ℚ) (k : ℕ),
    xs = before ++ List.replicate k 0 ++ after → k < R

/-- A loss list decomposed into zero strings followed by marked entries. -/
inductive SeparatedLosses (ε : ℚ) (R : ℕ) : List ℚ → Prop
  | zeros (k : ℕ) (hk : k < R) :
      SeparatedLosses ε R (List.replicate k 0)
  | mark (k : ℕ) (hk : k < R) (x : ℚ) (hx : ε ≤ x)
      (xs : List ℚ) (hxs : SeparatedLosses ε R xs) :
      SeparatedLosses ε R (List.replicate k 0 ++ x :: xs)

theorem ShortZeroRuns.tail {R : ℕ} {x : ℚ} {xs : List ℚ}
    (h : ShortZeroRuns R (x :: xs)) : ShortZeroRuns R xs := by
  intro before after k he
  apply h (x :: before) after k
  simp [he, List.append_assoc]

theorem separatedLosses_of_shortZeroRuns {ε : ℚ} {R : ℕ}
    (xs : List ℚ) (hpay : ∀ x ∈ xs, x = 0 ∨ ε ≤ x)
    (hzero : ShortZeroRuns R xs) : SeparatedLosses ε R xs := by
  induction xs with
  | nil =>
      have hR := hzero [] [] 0 (by simp)
      simpa using SeparatedLosses.zeros (ε := ε) 0 hR
  | cons x xs ih =>
      have ht := ih (by intro y hy; exact hpay y (by simp [hy])) hzero.tail
      rcases hpay x (by simp) with hx | hx
      · subst x
        cases ht with
        | zeros k hk =>
            have hnew := hzero [] [] (k + 1) (by simp [List.replicate_succ])
            simpa [List.replicate_succ] using
              SeparatedLosses.zeros (ε := ε) (k + 1) hnew
        | mark k hk y hy ys hys =>
            have hnew := hzero [] (y :: ys) (k + 1)
              (by simp [List.replicate_succ])
            simpa [List.replicate_succ] using
              SeparatedLosses.mark (k + 1) hnew y hy ys hys
      · have hR := hzero [] (x :: xs) 0 (by simp)
        simpa using SeparatedLosses.mark 0 hR x hx xs ht

/-- Counting all zero strings and marked entries, including both ends. -/
theorem SeparatedLosses.length_loss {ε : ℚ} {R : ℕ} {xs : List ℚ}
    (h : SeparatedLosses ε R xs) (hε : 0 ≤ ε) :
    ε * ((xs.length : ℚ) + 1) ≤ (R : ℚ) * (xs.sum + ε) := by
  induction h with
  | zeros k hk =>
      have hkQ : (k : ℚ) + 1 ≤ R := by exact_mod_cast Nat.succ_le_of_lt hk
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hkQ hε
  | mark k hk x hx xs hxs ih =>
      have hkQ : (k : ℚ) + 1 ≤ R := by exact_mod_cast Nat.succ_le_of_lt hk
      have hR : (0 : ℚ) ≤ R := Nat.cast_nonneg R
      have hgap : ε * ((k : ℚ) + 1) ≤ (R : ℚ) * x := by
        calc
          ε * ((k : ℚ) + 1) ≤ ε * R := mul_le_mul_of_nonneg_left hkQ hε
          _ ≤ (R : ℚ) * x := by nlinarith
      simp only [List.length_append, List.length_replicate, List.length_cons,
        Nat.cast_add, Nat.cast_one, List.sum_append, List.sum_replicate,
        nsmul_eq_mul, mul_zero, List.sum_cons, zero_add]
      nlinarith

theorem shortZeroRuns_length_loss {ε : ℚ} {R : ℕ} (xs : List ℚ)
    (hε : 0 ≤ ε) (hpay : ∀ x ∈ xs, x = 0 ∨ ε ≤ x)
    (hzero : ShortZeroRuns R xs) :
    ε * ((xs.length : ℚ) + 1) ≤ (R : ℚ) * (xs.sum + ε) :=
  (separatedLosses_of_shortZeroRuns xs hpay hzero).length_loss hε

/-- A tile records how many chains it contains and their combined length. -/
structure Tile where
  chains : ℕ
  chainLength : ℚ

def Tile.loss (μ : ℚ) (tile : Tile) : ℚ := μ * tile.chains - tile.chainLength

def tileChainCount (tiles : List Tile) : ℕ := (tiles.map Tile.chains).sum

def tileLength (tiles : List Tile) : ℚ := (tiles.map Tile.chainLength).sum

theorem tile_count_le_twice_length (tiles : List Tile)
    (hsize : ∀ tile ∈ tiles, tile.chains ≤ 2) :
    tileChainCount tiles ≤ 2 * tiles.length := by
  induction tiles with
  | nil => simp [tileChainCount]
  | cons tile tiles ih =>
      have ht := hsize tile (by simp)
      have hi := ih (by intro t ht; exact hsize t (by simp [ht]))
      simp only [tileChainCount, List.map_cons, List.sum_cons, List.length_cons] at *
      omega

theorem tile_loss_sum (μ : ℚ) (tiles : List Tile) :
    (tiles.map (Tile.loss μ)).sum = μ * tileChainCount tiles - tileLength tiles := by
  induction tiles with
  | nil => simp [tileChainCount, tileLength]
  | cons tile tiles ih =>
      simp only [List.map_cons, List.sum_cons, tileChainCount, tileLength,
        Nat.cast_add, Tile.loss] at *
      nlinarith

/-- Greedily pair a chain above the threshold with its successor. The last
chain remains a singleton if it has no successor. -/
def greedyTiles (threshold : ℕ) : List ℕ → List Tile
  | [] => []
  | [x] => [⟨1, x⟩]
  | x :: y :: xs =>
      if x ≤ threshold then ⟨1, x⟩ :: greedyTiles threshold (y :: xs)
      else ⟨2, (x : ℚ) + y⟩ :: greedyTiles threshold xs

theorem greedyTiles_sizes (threshold : ℕ) (xs : List ℕ) :
    ∀ tile ∈ greedyTiles threshold xs, tile.chains = 1 ∨ tile.chains = 2 := by
  induction xs using List.twoStepInduction with
  | nil => simp [greedyTiles]
  | singleton x => simp [greedyTiles]
  | cons_cons x y xs ihAfter ihCons =>
      by_cases h : x ≤ threshold
      · simp only [greedyTiles, if_pos h, List.mem_cons]
        intro tile ht
        rcases ht with rfl | ht
        · exact Or.inl rfl
        · exact ihCons y tile ht
      · simp only [greedyTiles, if_neg h, List.mem_cons]
        intro tile ht
        rcases ht with rfl | ht
        · exact Or.inr rfl
        · exact ihAfter tile ht

theorem greedyTiles_chainCount (threshold : ℕ) (xs : List ℕ) :
    tileChainCount (greedyTiles threshold xs) = xs.length := by
  induction xs using List.twoStepInduction with
  | nil => simp [greedyTiles, tileChainCount]
  | singleton x => simp [greedyTiles, tileChainCount]
  | cons_cons x y xs ihAfter ihCons =>
      by_cases h : x ≤ threshold
      · simp only [greedyTiles, if_pos h, tileChainCount, List.map_cons,
          List.sum_cons, List.length_cons] at *
        have hi := ihCons y
        omega
      · simp only [greedyTiles, if_neg h, tileChainCount, List.map_cons,
          List.sum_cons, List.length_cons] at *
        omega

theorem greedyTiles_chainLength (threshold : ℕ) (xs : List ℕ) :
    tileLength (greedyTiles threshold xs) = (xs.sum : ℚ) := by
  induction xs using List.twoStepInduction with
  | nil => simp [greedyTiles, tileLength]
  | singleton x => simp [greedyTiles, tileLength]
  | cons_cons x y xs ihAfter ihCons =>
      by_cases h : x ≤ threshold
      · simp only [greedyTiles, if_pos h, tileLength, List.map_cons,
          List.sum_cons, Nat.cast_add] at *
        have hi := ihCons y
        linarith
      · simp only [greedyTiles, if_neg h, tileLength, List.map_cons,
          List.sum_cons, Nat.cast_add] at *
        linarith

/-- The manuscript's paid-tile bound, with the terminal tile kept separate.
The assumptions concern actual ordered tiles; in particular, `hzero` bounds
literal zero-loss factors of the interior list.
-/
theorem paid_tile_bound (μ ε c : ℚ) (R : ℕ)
    (interior : List Tile) (last : Tile)
    (hε : 0 < ε) (hR : 0 < R)
    (hsize : ∀ tile ∈ interior ++ [last], tile.chains ≤ 2)
    (hpay : ∀ x ∈ interior.map (Tile.loss μ), x = 0 ∨ ε ≤ x)
    (hzero : ShortZeroRuns R (interior.map (Tile.loss μ)))
    (hlast : -c ≤ last.loss μ) :
    tileLength (interior ++ [last]) ≤
      (μ - ε / (2 * R)) * tileChainCount (interior ++ [last]) + c + ε := by
  have hcount := tile_count_le_twice_length (interior ++ [last]) hsize
  simp only [List.length_append, List.length_singleton] at hcount
  have hcountQ : (tileChainCount (interior ++ [last]) : ℚ) ≤
      2 * ((interior.length : ℚ) + 1) := by
    exact_mod_cast hcount
  have hpaid := shortZeroRuns_length_loss (interior.map (Tile.loss μ))
    hε.le hpay hzero
  simp only [List.length_map] at hpaid
  have hRpos : (0 : ℚ) < R := by exact_mod_cast hR
  have hcharge : ε * tileChainCount (interior ++ [last]) ≤
      2 * (R : ℚ) * ((interior.map (Tile.loss μ)).sum + ε) := by
    nlinarith [mul_le_mul_of_nonneg_left hcountQ hε.le]
  have hloss := tile_loss_sum μ (interior ++ [last])
  simp only [List.map_append, List.map_singleton, List.sum_append,
    List.sum_singleton] at hloss
  have hdiv : ε / (2 * (R : ℚ)) * tileChainCount (interior ++ [last]) ≤
      (interior.map (Tile.loss μ)).sum + ε := by
    have hd : (ε * tileChainCount (interior ++ [last])) / (2 * (R : ℚ)) ≤
        (interior.map (Tile.loss μ)).sum + ε :=
      (div_le_iff₀ (by positivity : (0 : ℚ) < 2 * R)).mpr (by nlinarith)
    convert hd using 1 <;> ring
  nlinarith

end ChainReturns
