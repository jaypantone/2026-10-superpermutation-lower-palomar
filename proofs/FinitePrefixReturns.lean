module

public import Mathlib.Tactic
public import Mathlib.Data.Fintype.Card

@[expose] public section

/-! A finite set of possible prefix maps forces a return. The order of
multiplication matches normalization maps, which act on the rightmost
block first. No closure or group-cardinality assertion is hidden here. -/
namespace SuperpermutationLowerBound.Refinement.ChainReturns

theorem finite_prefix_bound {α G : Type*} [Group G]
    (xs : List α) (N : List α → G) (_h_nil : N [] = 1)
    (h_append : ∀ l r, N (l ++ r) = N r * N l) (S : Finset G)
    (hmem : ∀ i ≤ xs.length, N (xs.take i) ∈ S)
    (havoid : ∀ before middle after, xs = before ++ middle ++ after →
      middle ≠ [] → N middle ≠ 1) : xs.length < S.card := by
  classical
  have hdistinct : ∀ i j : ℕ, i < j → j ≤ xs.length →
      N (xs.take i) ≠ N (xs.take j) := by
    intro i j hij hj he
    let middle := (xs.drop i).take (j-i)
    have hpref : xs.take j = xs.take i ++ middle := by
      rw [show j = i + (j-i) by omega, List.take_add]
    have hsplit : xs = xs.take i ++ middle ++ xs.drop j := by
      rw [← hpref, List.take_append_drop]
    have hlength : middle.length = j-i := by
      simp only [middle, List.length_take, List.length_drop]
      omega
    have hne : middle ≠ [] := by
      intro hz
      rw [hz, List.length_nil] at hlength
      omega
    have hmul : N middle * N (xs.take i) = N (xs.take i) := by
      rw [← h_append, ← hpref]
      exact he.symm
    have hidentity : N middle = 1 := by
      apply mul_right_cancel (b := N (xs.take i))
      simpa only [one_mul] using hmul
    exact havoid _ _ _ hsplit hne hidentity
  let f : Fin (xs.length + 1) → {g // g ∈ S} :=
    fun i => ⟨N (xs.take i.val), hmem i.val (by omega)⟩
  have hf : Function.Injective f := by
    intro i j hij
    have he : N (xs.take i.val) = N (xs.take j.val) := congrArg Subtype.val hij
    rcases lt_trichotomy i.val j.val with h | h | h
    · exact False.elim (hdistinct _ _ h (by omega) he)
    · exact Fin.ext h
    · exact False.elim (hdistinct _ _ h (by omega) he.symm)
  have hc := Fintype.card_le_of_injective f hf
  simpa using hc

end SuperpermutationLowerBound.Refinement.ChainReturns
