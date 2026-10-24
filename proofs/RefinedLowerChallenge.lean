module

public import LowerChallenge
public import SuperpermutationLowerBound.Refinement.Definitions

@[expose] public section

/-!
The refined lower bound, stated independently of its proof. `Covers` is the
existing contiguous-coverage predicate, so repeated letters and repeated
permutation occurrences in the word are allowed. The ceiling is exact.
-/

namespace SuperpermutationBounds

/-- The consolidated lower bound for alphabet sizes at least eight. -/
noncomputable def RefinedLowerBound (K : ℕ) : ℕ :=
  let n := K - 1
  let lam := SuperpermutationLowerBound.Refinement.scalarLambda n
  let B := SuperpermutationLowerBound.Refinement.scalarInterceptNumerator n
  let t := SuperpermutationLowerBound.Refinement.effectiveAllowance n
  K + (K + 1) * n.factorial - 3 +
    ⌈((lam * (n.factorial : ℚ) - B) / ((n : ℚ) * lam - 2 * t))⌉₊

/-- An arbitrary finite covering word satisfies the refined lower bound. -/
def RefinedGeneralLower : Prop :=
  ∀ K : ℕ, 8 ≤ K → ∀ w : List (Fin K), Covers w → RefinedLowerBound K ≤ w.length

end SuperpermutationBounds
