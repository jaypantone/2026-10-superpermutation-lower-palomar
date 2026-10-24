module

public import SuperpermutationLowerBound.Refinement.ReturnMaps
public import SuperpermutationLowerBound.Refinement.ChainPatterns

@[expose] public section

/-! Normalizations act in the reverse order of the chronological cell list.
The actual entry chart is obtained by applying the inverse normalization. -/
namespace SuperpermutationLowerBound.Refinement

def cellNormalization (n : ℕ) (hn : 7 ≤ n) : List Bool → Equiv.Perm (Fin (n+1))
  | [] => 1
  | b :: bs => cellNormalization n hn bs *
      (if b then cellRho n hn * cellG n hn else cellG n hn)

@[simp] theorem cellNormalization_nil (n : ℕ) (hn : 7 ≤ n) :
    cellNormalization n hn [] = 1 := rfl

@[simp] theorem cellNormalization_cons (n : ℕ) (hn : 7 ≤ n)
    (b : Bool) (bs : List Bool) :
    cellNormalization n hn (b :: bs) = cellNormalization n hn bs *
      (if b then cellRho n hn * cellG n hn else cellG n hn) := rfl

@[simp] theorem cellNormalization_append (n : ℕ) (hn : 7 ≤ n)
    (xs ys : List Bool) :
    cellNormalization n hn (xs ++ ys) =
      cellNormalization n hn ys * cellNormalization n hn xs := by
  induction xs with
  | nil => simp
  | cons b bs ih => simp only [List.cons_append, cellNormalization_cons, ih, mul_assoc]

@[simp] theorem cellNormalization_replicate_false (n : ℕ) (hn : 7 ≤ n) (r : ℕ) :
    cellNormalization n hn (List.replicate r false) = (cellG n hn)^r := by
  induction r with
  | zero => simp
  | succ r ih => simp [List.replicate_succ, ih, pow_succ]

@[simp] theorem cellNormalization_singleton_true (n : ℕ) (hn : 7 ≤ n) :
    cellNormalization n hn [true] = cellRho n hn * cellG n hn := by simp

/-- The inverse chart after appending a cell sequence composes with the
inverse chart of the earlier sequence. -/
theorem cellNormalization_append_chart {α : Type*} (n : ℕ) (hn : 7 ≤ n)
    (xs ys : List Bool) (e : Fin (n+1) ≃ α) :
    (cellNormalization n hn (xs ++ ys)).symm.trans e =
      (cellNormalization n hn ys).symm.trans
        ((cellNormalization n hn xs).symm.trans e) := by
  rw [cellNormalization_append]
  ext i
  rfl

theorem cellNormalization_chainWindow_empty (n : ℕ) (hn : 7 ≤ n) (r s : ℕ) :
    cellNormalization n hn (chainWindow r s []) =
      (cellG n hn)^s * cellRho n hn * (cellG n hn)^(r+1) := by
  simp [chainWindow, pow_succ', mul_assoc]

theorem cellNormalization_chainWindow_one (n : ℕ) (hn : 7 ≤ n)
    (r s l : ℕ) (hl : 1 ≤ l) :
    cellNormalization n hn (chainWindow r s [l]) =
      (cellG n hn)^s * cellRho n hn * (cellG n hn)^l *
        cellRho n hn * (cellG n hn)^(r+1) := by
  have hl' : l-1+1 = l := by omega
  simp [chainWindow, chainCells, mul_assoc, ← pow_succ', hl']

theorem cellNormalization_chainWindow_two (n : ℕ) (hn : 7 ≤ n)
    (r s l j : ℕ) (hl : 1 ≤ l) (hj : 1 ≤ j) :
    cellNormalization n hn (chainWindow r s [l,j]) =
      (cellG n hn)^s * cellRho n hn * (cellG n hn)^j *
        cellRho n hn * (cellG n hn)^l * cellRho n hn *
          (cellG n hn)^(r+1) := by
  have hl' : l-1+1 = l := by omega
  have hj' : j-1+1 = j := by omega
  simp [chainWindow, chainCells, mul_assoc, ← pow_succ', hl', hj']

end SuperpermutationLowerBound.Refinement
