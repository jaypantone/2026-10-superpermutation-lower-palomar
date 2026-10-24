module

public import Challenge
public import Mathlib.Data.Rat.Floor

@[expose] public section

/-!
The frozen manuscript's statement, independently of its proof.

`Covers` is the inherited contiguous-subword predicate on arbitrary lists.
The definitions below make no assertion that the target proposition holds.
In particular, numerical evaluation is not a proof of a word-length bound.
-/

namespace SuperpermutationBounds.ChainReturns

/-- The representative in `0,...,n-1` of the inverse of seven, when it exists. -/
def inverseSeven (n : ℕ) : ℕ :=
  ((List.range n).find? (fun u => (7 * u) % n == 1)).getD 0

/-- Return order for the alternating pair, at `n` divisible by three. -/
def returnZero (n : ℕ) : ℕ :=
  if n % 7 = 0 then 2 * n / 7
  else inverseSeven n * (n - inverseSeven n)

/-- Return order for the efficient pair at `n = 3m+1`. -/
def returnOne (m : ℕ) : ℕ :=
  match m % 6 with
  | 0 => 3 * m + 1
  | 1 => Nat.lcm ((2 * m + 1) / 3) ((7 * m + 2) / 3)
  | 2 => 3 * m + 1
  | 3 => Nat.lcm ((7 * m + 3) / 6) ((11 * m + 3) / 6)
  | 4 => Nat.lcm ((2 * m + 1) / 3) ((7 * m + 2) / 6)
  | _ => Nat.lcm ((7 * m + 1) / 6) ((11 * m + 5) / 6)

/-- Parameters in the general table, with the two return bounds supplied. -/
def generalParameters (n : ℕ) (R₀ R₁ : ℚ) : ℚ × ℚ :=
  let m : ℚ := (n / 3 : ℕ)
  match n % 3 with
  | 0 => (2 * m + 1 / 2 + 1 / (4 * R₀), 4 * m - 3 - 1 / (2 * R₀))
  | 1 => (m * (2 * m + 1), 2 * m ^ 2 + 2 * m - 2 - 1 / R₁)
  | _ => ((m + 1) * (2 * m + 1), 4 * m ^ 2 + 5 * m - 5 / 2)

/-- The five initial rows and then the exact-order general parameters. -/
def exactParameters (K : ℕ) : ℚ × ℚ :=
  match K with
  | 8 => (10, 46 / 3)
  | 9 => (15, 287 / 12)
  | 10 => (521 / 80, 359 / 40)
  | 11 => (21, 263 / 12)
  | 12 => (28, 195 / 4)
  | _ => generalParameters (K - 1) (returnZero (K - 1)) (returnOne ((K - 1) / 3))

/-- The alternative general parameters obtained from the quadratic return bound. -/
def quadraticParameters (K : ℕ) : ℚ × ℚ :=
  if K < 13 then exactParameters K
  else
    let U : ℚ := ((K - 1 : ℕ) : ℚ) ^ 2 / 4
    generalParameters (K - 1) U U

/-- The displayed word-length formula of the manuscript. -/
noncomputable def paperBound (K : ℕ) (p t : ℚ) : ℕ :=
  K.factorial + (K - 1).factorial + (K - 2).factorial + K - 3 +
    ⌈((2 * ((K - 2).factorial : ℚ) - 2 * ((K : ℚ) - 2) - 4 * p / t) /
      ((K : ℚ) ^ 2 - 4 * K + 1 - 2 * ((K : ℚ) - 1) / t))⌉₊

/-- The exact-order theorem to be proved; no chain or path premise is present. -/
def ExactWordBound : Prop :=
  ∀ K : ℕ, 8 ≤ K → ∀ w : List (Fin K), Covers w →
    paperBound K (exactParameters K).1 (exactParameters K).2 ≤ w.length

/-- The manuscript's quadratic-order alternative, with the same word semantics. -/
def QuadraticWordBound : Prop :=
  ∀ K : ℕ, 8 ≤ K → ∀ w : List (Fin K), Covers w →
    paperBound K (quadraticParameters K).1 (quadraticParameters K).2 ≤ w.length

end SuperpermutationBounds.ChainReturns
