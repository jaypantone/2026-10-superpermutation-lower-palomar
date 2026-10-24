module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Rat.Floor

@[expose] public section

/-!
Comparator specification. This file imports only Mathlib and states the target
theorems with placeholders; it is never imported by a submitted proof.
The matching solution environment proves these exact names.
-/

namespace SuperpermutationResults
/-- Every permutation of the alphabet occurs as a contiguous factor. -/
def Covers {K : ℕ} (w : List (Fin K)) : Prop :=
  ∀ p : List (Fin K), p.length = K → p.Nodup →
    ∃ u v : List (Fin K), w = u ++ p ++ v

/-- The first three factorial terms. -/
def F3Nat (K : ℕ) : ℕ :=
  K.factorial + (K - 1).factorial + (K - 2).factorial
end SuperpermutationResults

/-!
Every superpermutation on 14 symbols has at least 93,891,141,150 letters.
`Covers` is the independent contiguous-factor definition above.
This statement has a proof using only the three standard Lean axioms.
No search, path, or normalization hypothesis is imposed on the word.
-/
namespace SuperpermutationResults.Lower14

def WordBound : Prop :=
  ∀ w : List (Fin 14), Covers w → 93891141150 ≤ w.length

end SuperpermutationResults.Lower14

namespace SuperpermutationResults.Lower14

theorem word_lower_bound : WordBound := by
  sorry

end SuperpermutationResults.Lower14
