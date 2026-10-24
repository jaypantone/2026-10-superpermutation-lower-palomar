module

public import SuperpermutationLowerBound.Refinement.ReturnResidueTwo
public import SuperpermutationLowerBound.Refinement.ReturnGeometry

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

open PermutationVertex

/-- Lift the literal return calculation to an equality of actual permutation
vertices, in arbitrary coordinates. -/
theorem shortEntry_eq_runMapPower_of_values (n : ℕ) (hn : 7 ≤ n)
    (Q : Equiv.Perm (Fin (n + 1))) (shift : ℕ)
    (hcore : ∀ i : ℕ, ∀ hi : i < n,
      (Q (cellY n hn ⟨i, by omega⟩)).val = cellUValue n ((shift + i) % n))
    (hlast : (Q (cellY n hn ⟨n, by omega⟩)).val = 0)
    (e : Fin (n + 1) ≃ Alphabet (n + 1)) :
    shortEntry n hn (Q.trans e) = runMapPower (by omega) shift (fullEntry n hn e) := by
  apply PermutationVertex.ext
  apply List.ext_getElem
  · simp [PermutationVertex.length]
  · intro i hi hj
    have hilim : i < n + 1 := by simpa [PermutationVertex.length] using hi
    by_cases hicore : i < n
    · have hget := runMapPower_get_core (by omega : 2 ≤ n + 1)
        (fullEntry n hn e) shift i (by omega)
      simp only [Nat.add_sub_cancel] at hget
      rw [hget]
      simp only [shortEntry_word, fullEntry_word, List.getElem_ofFn, Equiv.trans_apply]
      apply congrArg e
      exact Fin.ext (hcore i hicore)
    · have hin : i = n := by omega
      subst i
      have hget := runMapPower_get_last (by omega : 2 ≤ n + 1) (fullEntry n hn e) shift
      simp only [Nat.add_sub_cancel] at hget
      rw [hget]
      simp only [shortEntry_word, fullEntry_word, List.getElem_ofFn, Equiv.trans_apply]
      apply congrArg e
      apply Fin.ext
      have hu : cellUValue n n = 0 := by unfold cellUValue; split_ifs <;> omega
      simpa only [cellU_apply_val, hu] using hlast

theorem shortened_return_shortEntry (m : ℕ) (hm : 2 ≤ m) (hn : 7 ≤ 3 * m + 2)
    (e : Fin (3 * m + 2 + 1) ≃ Alphabet (3 * m + 2 + 1)) :
    shortEntry (3 * m + 2) hn
      ((cellRho (3 * m + 2) hn * (cellG (3 * m + 2) hn) ^ (2 * m * (m + 1) - 1) *
        cellRho (3 * m + 2) hn * (cellG (3 * m + 2) hn) ^ (2 * m * (m + 1) + 2)).trans e) =
      runMapPower (by omega) 4 (fullEntry (3 * m + 2) hn e) := by
  apply shortEntry_eq_runMapPower_of_values (3 * m + 2) hn _ 4
  · exact shortened_return_y_core m hm hn
  · exact shortened_return_y_last m hm hn

end SuperpermutationLowerBound.Refinement
