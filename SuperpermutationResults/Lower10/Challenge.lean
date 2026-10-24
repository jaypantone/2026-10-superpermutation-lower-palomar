module

public import SuperpermutationResults.Definitions

@[expose] public section

/-!
Every superpermutation on 10 symbols has at least 4,033,379 letters.
`Covers` is the independent contiguous-factor definition in `Definitions.lean`.
This statement has a proof using only the three standard Lean axioms.
No search, path, or normalization hypothesis is imposed on the word.
-/
namespace SuperpermutationResults.Lower10

def WordBound : Prop :=
  ∀ w : List (Fin 10), Covers w → 4033379 ≤ w.length

end SuperpermutationResults.Lower10
