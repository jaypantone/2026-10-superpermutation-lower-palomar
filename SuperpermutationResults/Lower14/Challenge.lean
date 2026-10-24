module

public import SuperpermutationResults.Definitions

@[expose] public section

/-!
Every superpermutation on 14 symbols has at least 93,891,141,150 letters.
`Covers` is the independent contiguous-factor definition in `Definitions.lean`.
This statement has a proof using only the three standard Lean axioms.
No search, path, or normalization hypothesis is imposed on the word.
-/
namespace SuperpermutationResults.Lower14

def WordBound : Prop :=
  ∀ w : List (Fin 14), Covers w → 93891141150 ≤ w.length

end SuperpermutationResults.Lower14
