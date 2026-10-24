module

public import Mathlib.Data.Rat.Floor

@[expose] public section

/-!
Exact parameters of the consolidated general lower bound. Here `n = K - 1`,
where `K` is the alphabet size. All divisions and scalar subtractions are in
the rationals. The theorem's domain is `n ≥ 7`.
-/

namespace SuperpermutationLowerBound.Refinement

/-- Order of the regular-cell return permutation. -/
def period (n : ℕ) : ℕ :=
  if n % 3 = 0 then 2 * (n / 3)
  else if n % 3 = 1 then (n / 3) * (2 * (n / 3) + 1)
  else (n / 3 + 1) * (2 * (n / 3) + 1)

/-- Geometric chain allowance, before the scalar small-parameter adjustment. -/
def chainAllowance (n : ℕ) : ℚ :=
  if n % 3 = 0 then 2 * (period n : ℚ) - 3
  else if n % 3 = 1 then (period n : ℚ) + (n / 3 : ℕ) - 2
  else 2 * (period n : ℚ) - (n / 3 : ℕ) - 4

/-- The sole scalar margin, automatically satisfied by the larger of these
two allowances. It changes the geometric allowance only at `n = 7`. -/
def effectiveAllowance (n : ℕ) : ℚ :=
  max (chainAllowance n) ((4 * (period n : ℚ) + 6) / ((n : ℚ) - 4))

def scalarLambda (n : ℕ) : ℚ :=
  ((n : ℚ) - 2) * effectiveAllowance n - 2

def scalarInterceptNumerator (n : ℕ) : ℚ :=
  2 * effectiveAllowance n * ((n : ℚ) - 1) + 4 * (period n : ℚ)

def scalarDelta (n : ℕ) : ℚ :=
  2 * effectiveAllowance n / scalarLambda n

def scalarBeta (n : ℕ) : ℚ :=
  scalarInterceptNumerator n / scalarLambda n

end SuperpermutationLowerBound.Refinement
