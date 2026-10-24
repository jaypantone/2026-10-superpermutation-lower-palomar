module

public import SuperpermutationLowerBound.Refinement.ReturnResidueOne
public import SuperpermutationLowerBound.Refinement.ReturnGeometry

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

open PermutationVertex

/-- The first full row contains a block that becomes the new short entry
under the residue-one return. The equality holds for literal words. -/
theorem shortened_return_residueOne_entry (m : ℕ) (hm : 2 ≤ m) (hn : 7 ≤ 3*m+1)
    (e : Fin (3*m+1+1) ≃ Alphabet (3*m+1+1)) :
    shortEntry (3*m+1) hn e = runMapPower (by omega) (3*m+1-2)
      (fullEntry (3*m+1) hn
        ((cellRho (3*m+1) hn * (cellG (3*m+1) hn)^m * cellRho (3*m+1) hn *
          (cellG (3*m+1) hn)^(m+1)).trans e)) := by
  let n := 3*m+1
  let Q := cellRho n hn * (cellG n hn)^m * cellRho n hn * (cellG n hn)^(m+1)
  change shortEntry n hn e = runMapPower _ (n-2) (fullEntry n hn (Q.trans e))
  apply PermutationVertex.ext
  apply List.ext_getElem
  · simp [PermutationVertex.length, n]
  · intro i hi hj
    have hilim : i < n+1 := by simpa [PermutationVertex.length] using hi
    by_cases hicore : i < n
    · have hget := runMapPower_get_core (by omega : 2 ≤ n+1)
        (fullEntry n hn (Q.trans e)) (n-2) i (by omega)
      simp only [Nat.add_sub_cancel] at hget
      rw [hget]
      simp only [shortEntry_word, fullEntry_word, List.getElem_ofFn, Equiv.trans_apply]
      apply congrArg e
      apply Fin.ext
      rw [show ∀ j, (Q j).val = cellQOneValue n j.val from
        shortened_return_residueOne_val m hm hn]
      exact (cellQOne_u_core_value n hn i hicore).symm
    · have hin : i = n := by omega
      subst i
      have hget := runMapPower_get_last (by omega : 2 ≤ n+1)
        (fullEntry n hn (Q.trans e)) (n-2)
      simp only [Nat.add_sub_cancel] at hget
      rw [hget]
      simp only [shortEntry_word, fullEntry_word, List.getElem_ofFn, Equiv.trans_apply]
      apply congrArg e
      apply Fin.ext
      rw [show ∀ j, (Q j).val = cellQOneValue n j.val from
        shortened_return_residueOne_val m hm hn]
      exact (cellQOne_u_last_value n hn).symm

end SuperpermutationLowerBound.Refinement
