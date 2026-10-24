module

public import Challenge
public import Mathlib.Data.Rat.Floor

@[expose] public section

/-!
The general lower bound, stated independently of its proof library.

`Covers` is the same contiguous-coverage predicate used for the upper bounds
in `Challenge.lean`. Every finite covering word on `Fin K` is included.
The fraction is rational and the ceiling is Mathlib's natural ceiling.
This theorem is formalized for every `K >= 7`. The stronger period refinements
described in the paper are not asserted here.
-/

namespace SuperpermutationBounds

noncomputable def LowerBound (K : ℕ) : ℕ :=
  K + (K + 1) * (K - 1).factorial - 3 +
    ⌈(((((K - 3 : ℕ) : ℚ) * ((K - 1).factorial : ℚ) -
          2 * ((K - 1 : ℕ) : ℚ)) /
        ((K : ℚ) ^ 2 - 4 * (K : ℚ) + 1)))⌉₊

def GeneralLower : Prop :=
  ∀ K : ℕ, 7 ≤ K → ∀ w : List (Fin K), Covers w → LowerBound K ≤ w.length

end SuperpermutationBounds
