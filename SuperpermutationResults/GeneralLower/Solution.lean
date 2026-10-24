module

public import SuperpermutationResults.GeneralLower.Challenge
public import bridge.FrozenBounds

@[expose] public section

/-! The public formulas and coverage predicate are definitionally identical
to those in the audited development. The equalities below check that bridge
by reflexivity; there is no additional mathematical hypothesis. -/
namespace SuperpermutationResults.GeneralLower

theorem exact_statement_eq :
    ExactWordBound = SuperpermutationBounds.ChainReturns.ExactWordBound := rfl

theorem quadratic_statement_eq :
    QuadraticWordBound = SuperpermutationBounds.ChainReturns.QuadraticWordBound := rfl

theorem exact_word_bound : ExactWordBound := by
  rw [exact_statement_eq]
  exact SuperpermutationLowerBound.ChainReturns.exact_word_bound

theorem quadratic_word_bound : QuadraticWordBound := by
  rw [quadratic_statement_eq]
  exact SuperpermutationLowerBound.ChainReturns.quadratic_word_bound

end SuperpermutationResults.GeneralLower
