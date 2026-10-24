module

public import pairs.ChunkClassification

@[expose] public section

namespace ChainReturns

def ValidChunks (interior final : Chunk → Prop) : List Chunk → Prop
  | [] => True
  | [chunk] => final chunk
  | chunk :: next :: rest => interior chunk ∧ ValidChunks interior final (next :: rest)

theorem ValidChunks.cons {P Q : Chunk → Prop} {chunk : Chunk} {rest : List Chunk}
    (hrest : rest ≠ []) (hchunk : P chunk) (h : ValidChunks P Q rest) :
    ValidChunks P Q (chunk :: rest) := by
  cases rest with
  | nil => contradiction
  | cons next rest => exact ⟨hchunk, h⟩

theorem ValidChunks.interior {P Q : Chunk → Prop} {chunks : List Chunk}
    (h : ValidChunks P Q chunks) : ∀ chunk ∈ chunks.dropLast, P chunk := by
  induction chunks using List.twoStepInduction with
  | nil => simp
  | singleton chunk => simp
  | cons_cons chunk next rest ihAfter ihCons =>
      simp only [List.dropLast_cons_cons, List.mem_cons]
      intro c hc
      rcases hc with rfl | hc
      · exact h.1
      · exact ihCons next h.2 c hc

theorem ValidChunks.last {P Q : Chunk → Prop} {chunks : List Chunk}
    (h : ValidChunks P Q chunks) (hne : chunks ≠ []) : Q (chunks.getLast hne) := by
  induction chunks using List.twoStepInduction with
  | nil => contradiction
  | singleton chunk => exact h
  | cons_cons chunk next rest ihAfter ihCons =>
      exact ihCons next h.2 (by simp)

theorem greedyChunks_ne_nil (threshold : ℕ) {xs : List ℕ} (hxs : xs ≠ []) :
    greedyChunks threshold xs ≠ [] := by
  intro h
  have he := greedyChunks_flatten threshold xs
  rw [h] at he
  exact hxs (by simpa using he.symm)

/-- The local successor restrictions retained before passing to pair totals. -/
def OneSuccessors (m : ℕ) (xs : List ℕ) : Prop :=
  ∀ before after : List ℕ, ∀ x y : ℕ,
    xs = before ++ x :: y :: after → m < x →
      y ≤ m ∧ (after ≠ [] → y ≤ m - 1)

theorem OneSuccessors.suffix {m : ℕ} {xs before tail : List ℕ}
    (h : OneSuccessors m xs) (he : xs = before ++ tail) : OneSuccessors m tail := by
  intro pre post x y htail hx
  apply h (before ++ pre) post x y _ hx
  simp [he, htail, List.append_assoc]

def OneFinal (m : ℕ) : Chunk → Prop
  | .single x => x ≤ onePeriod m - 1
  | .pair x y => x ≤ onePeriod m - 1 ∧ y ≤ m

theorem greedy_one_valid (m : ℕ) (xs : List ℕ)
    (hbound : ∀ x ∈ xs, x ≤ onePeriod m - 1)
    (hsucc : OneSuccessors m xs) :
    ValidChunks (OneInterior m) (OneFinal m) (greedyChunks m xs) := by
  induction xs using List.twoStepInduction with
  | nil => trivial
  | singleton x => exact hbound x (by simp)
  | cons_cons x y xs ihAfter ihCons =>
      by_cases hx : x ≤ m
      · simp only [greedyChunks, if_pos hx]
        apply ValidChunks.cons (greedyChunks_ne_nil m (by simp)) hx
        apply ihCons y
        · intro z hz
          exact hbound z (by simp [hz])
        · exact hsucc.suffix (before := [x]) (by simp)
      · have hs := hsucc [] xs x y (by simp) (by omega)
        simp only [greedyChunks, if_neg hx]
        by_cases hxs : xs = []
        · subst xs
          exact ⟨hbound x (by simp), hs.1⟩
        · apply ValidChunks.cons (greedyChunks_ne_nil m hxs)
          · exact ⟨hbound x (by simp), hs.2 hxs⟩
          · apply ihAfter
            · intro z hz
              exact hbound z (by simp [hz])
            · exact hsucc.suffix (before := [x, y]) (by simp)

theorem oneFinal_loss (m : ℕ) (hm : 3 ≤ m) (chunk : Chunk)
    (h : OneFinal m chunk) : -(m : ℚ)^2 ≤ chunk.tile.loss (oneMean m) := by
  have hp : 1 ≤ onePeriod m := by dsimp [onePeriod]; nlinarith
  have hpQ : ((onePeriod m - 1 : ℕ) : ℚ) = (m : ℚ) * (2 * m + 1) - 1 := by
    rw [Nat.cast_sub hp]
    norm_num [onePeriod]
  have hmQ : (3 : ℚ) ≤ m := by exact_mod_cast hm
  cases chunk with
  | single x =>
      have hx : (x : ℚ) ≤ (m : ℚ) * (2 * m + 1) - 1 := by
        rw [← hpQ]
        exact_mod_cast h
      simp only [Chunk.tile, Tile.loss, oneMean, Nat.cast_one]
      nlinarith
  | pair x y =>
      have hx : (x : ℚ) ≤ (m : ℚ) * (2 * m + 1) - 1 := by
        rw [← hpQ]
        exact_mod_cast h.1
      have hy : (y : ℚ) ≤ m := by exact_mod_cast h.2
      simp only [Chunk.tile, Tile.loss, oneMean, Nat.cast_ofNat]
      nlinarith

end ChainReturns
