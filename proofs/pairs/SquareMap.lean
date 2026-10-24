module

public import SuperpermutationLowerBound.Refinement.ReturnResidueTwo

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

set_option maxHeartbeats 3000000

def squareHalfValue (n i : ℕ) : ℕ :=
  if i = 0 then 0 else if i = 1 then n else if i = 2 then n - 1
  else if i = 3 then 2 else if i = 5 then 1
  else if i % 3 = 1 then i - 1 else if i % 3 = 2 then i - 3 else i - 2

theorem squareHalf_a2 (m j : ℕ) (hm : 2 ≤ m) (hj : j < m + 1) :
    ReturnCycle.a2 m (if m + j ≤ m + 1 then m + j else m + j - (m + 1)) =
      squareHalfValue (3 * m + 2) (ReturnCycle.a2 m j) := by
  unfold ReturnCycle.a2 squareHalfValue
  split_ifs <;> (first | contradiction | omega)

theorem squareHalf_b2 (m j : ℕ) (hm : 2 ≤ m) (hj : j < 2 * m + 1) :
    ReturnCycle.b2 m (if m + j ≤ 2 * m + 1 then m + j else m + j - (2 * m + 1)) =
      squareHalfValue (3 * m + 2) (ReturnCycle.b2 m j) := by
  unfold ReturnCycle.b2 squareHalfValue
  split_ifs <;> (first | contradiction | omega)

theorem cellG_pow_m_residueTwo (m : ℕ) (hm : 2 ≤ m) (hn : 7 ≤ 3 * m + 2)
    (i : Fin (3 * m + 2 + 1)) :
    (((cellG (3 * m + 2) hn)^m) i).val = squareHalfValue (3 * m + 2) i.val := by
  let n := 3 * m + 2
  let g := cellG n hn
  rcases ReturnCycle.cover2 m i.val hm (by omega) with hz | hA | hB
  · have hi : i = 0 := Fin.ext hz
    subst i
    simp [squareHalfValue]
  · obtain ⟨j, hj, hv⟩ := hA
    let w : ℕ → Fin (n + 1) := fun k =>
      ⟨ReturnCycle.a2 m k, by have := ReturnCycle.a2_le m k hm; dsimp [n]; omega⟩
    have hi : i = w j := Fin.ext hv.symm
    have hstep : ∀ k < m + 1, g (w k) = w (k + 1) := by
      intro k hk
      exact Fin.ext (ReturnCycle.a2_step m k hm hk)
    have hclosed : w (m + 1) = w 0 := Fin.ext (ReturnCycle.a2_closed m hm)
    have hshift := ReturnCycle.pow_shift_walk g w (m + 1) hstep hclosed j m
      (by omega) (by omega)
    change ((g^m) i).val = squareHalfValue n i.val
    rw [hi, hshift]
    exact squareHalf_a2 m j hm hj
  · obtain ⟨j, hj, hv⟩ := hB
    let w : ℕ → Fin (n + 1) := fun k =>
      ⟨ReturnCycle.b2 m k, by have := ReturnCycle.b2_le m k hm; dsimp [n]; omega⟩
    have hi : i = w j := Fin.ext hv.symm
    have hstep : ∀ k < 2 * m + 1, g (w k) = w (k + 1) := by
      intro k hk
      exact Fin.ext (ReturnCycle.b2_step m k hm hk)
    have hclosed : w (2 * m + 1) = w 0 := Fin.ext (ReturnCycle.b2_closed m hm)
    have hshift := ReturnCycle.pow_shift_walk g w (2 * m + 1) hstep hclosed j m
      (by omega) (by omega)
    change ((g^m) i).val = squareHalfValue n i.val
    rw [hi, hshift]
    exact squareHalf_b2 m j hm hj

end SuperpermutationLowerBound.Refinement
