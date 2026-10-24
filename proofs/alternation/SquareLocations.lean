module

public import pairs.PeriodicReturns
public import pairs.TwoClassification

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

open _root_.ChainReturns

def squareCells (m : ℕ) : List Bool :=
  completedPair (twoMax m) (twoThreshold m - 2) ++
    completedPair (twoMax m) (twoThreshold m - 2)

def squarePrefixOne (m : ℕ) : List Bool :=
  completedChain (twoMax m) ++ List.replicate (twoThreshold m - m - 4) false

def squarePrefixTwo (m : ℕ) : List Bool :=
  completedPair (twoMax m) (twoThreshold m - 2) ++
    completedChain (twoMax m) ++ List.replicate m false

theorem completedChain_internal_split (c j : ℕ) (hj : j < c - 1) :
    completedChain c = List.replicate j false ++
      false :: (List.replicate (c - j - 2) false ++ [true]) := by
  have he : c - 1 = j + ((c - j - 2) + 1) := by omega
  simp only [completedChain, he, List.replicate_add, List.replicate_succ,
    List.append_assoc, List.cons_append]

theorem square_selected_cells_internal (m : ℕ) (hm : 2 ≤ m) :
    twoThreshold m - m - 4 < (twoThreshold m - 2) - 1 ∧
      m < (twoThreshold m - 2) - 1 := by
  have hv : m + 4 ≤ twoThreshold m := by dsimp [twoThreshold]; nlinarith
  have hv' : m + 4 < twoThreshold m := by dsimp [twoThreshold]; nlinarith
  omega

theorem squareCells_prefixOne (m : ℕ) (hm : 2 ≤ m) :
    ∃ tail, squareCells m = squarePrefixOne m ++ false :: tail := by
  have hc := completedChain_internal_split (twoThreshold m - 2)
    (twoThreshold m - m - 4) (square_selected_cells_internal m hm).1
  refine ⟨(List.replicate ((twoThreshold m - 2) - (twoThreshold m - m - 4) - 2)
    false ++ [true]) ++ completedPair (twoMax m) (twoThreshold m - 2), ?_⟩
  unfold squareCells squarePrefixOne
  conv_lhs => arg 1; unfold completedPair; arg 2; rw [hc]
  simp only [List.append_assoc, List.cons_append]

theorem squareCells_prefixTwo (m : ℕ) (hm : 2 ≤ m) :
    ∃ tail, squareCells m = squarePrefixTwo m ++ false :: tail := by
  have hc := completedChain_internal_split (twoThreshold m - 2) m
    (square_selected_cells_internal m hm).2
  refine ⟨List.replicate ((twoThreshold m - 2) - m - 2) false ++ [true], ?_⟩
  unfold squareCells squarePrefixTwo
  conv_lhs => arg 2; unfold completedPair; arg 2; rw [hc]
  simp only [List.append_assoc, List.cons_append]

theorem squarePrefixes_order (m : ℕ) (hm : 2 ≤ m) :
    ∃ between, squarePrefixTwo m = squarePrefixOne m ++ false :: between := by
  have hc := completedChain_internal_split (twoThreshold m - 2)
    (twoThreshold m - m - 4) (square_selected_cells_internal m hm).1
  refine ⟨(List.replicate ((twoThreshold m - 2) - (twoThreshold m - m - 4) - 2)
    false ++ [true]) ++ completedChain (twoMax m) ++ List.replicate m false, ?_⟩
  unfold squarePrefixOne squarePrefixTwo completedPair
  rw [hc]
  simp only [List.append_assoc, List.cons_append]

theorem square_full_row_order (m : ℕ) (hm : 2 ≤ m) :
    (cellWord (3 * m + 2 - 2) (squarePrefixOne m)).length + 1 + (3 * m + 2 - 4) <
      (cellWord (3 * m + 2 - 2) (squarePrefixTwo m)).length + 1 := by
  obtain ⟨between, he⟩ := squarePrefixes_order m hm
  rw [he]
  simp only [cellWord_append, cellWord_cons, List.length_append, cellDigits,
    Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_replicate]
  omega

theorem squarePrefixOne_normalization (m : ℕ) (hm : 2 ≤ m)
    (hn : 7 ≤ 3 * m + 2) :
    cellNormalization (3 * m + 2) hn (squarePrefixOne m) =
      cellG (3 * m + 2) hn ^ (twoThreshold m - m - 4) *
        cellRho (3 * m + 2) hn * cellG (3 * m + 2) hn ^ twoMax m := by
  have hb : 1 ≤ twoMax m := by dsimp [twoMax]; nlinarith
  simp only [squarePrefixOne, cellNormalization_append,
    completedChain_normalization _ hn _ hb, cellNormalization_replicate_false]
  exact (mul_assoc _ _ _).symm

theorem squarePrefixTwo_normalization (m : ℕ) (hm : 2 ≤ m)
    (hn : 7 ≤ 3 * m + 2) :
    cellNormalization (3 * m + 2) hn (squarePrefixTwo m) =
      cellG (3 * m + 2) hn ^ m * cellRho (3 * m + 2) hn *
        cellG (3 * m + 2) hn ^ twoMax m * cellRho (3 * m + 2) hn *
        cellG (3 * m + 2) hn ^ (twoThreshold m - 2) *
        cellRho (3 * m + 2) hn * cellG (3 * m + 2) hn ^ twoMax m := by
  have hb : 1 ≤ twoMax m := by dsimp [twoMax]; nlinarith
  have hv : 3 ≤ twoThreshold m := by dsimp [twoThreshold]; nlinarith
  have hc : 1 ≤ twoThreshold m - 2 := by omega
  simp only [squarePrefixTwo, cellNormalization_append,
    completedChain_normalization _ hn _ hb, completedPair_normalization _ hn _ _ hb hc,
    cellNormalization_replicate_false, mul_assoc]

end SuperpermutationLowerBound.Refinement
