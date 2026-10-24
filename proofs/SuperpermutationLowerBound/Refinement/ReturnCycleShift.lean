module

public import SuperpermutationLowerBound.Refinement.ReturnPeriod

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

namespace ReturnCycle

/-- A power starting at any point of a closed walk, with at most one wrap. -/
theorem pow_shift_walk {α : Type*} (g : Equiv.Perm α) (v : ℕ → α) (L : ℕ)
    (step : ∀ i < L, g (v i) = v (i + 1)) (closed : v L = v 0)
    (j r : ℕ) (hj : j ≤ L) (hsum : r + j ≤ 2 * L) :
    (g ^ r) (v j) = v (if r + j ≤ L then r + j else r + j - L) := by
  rw [← pow_walk g v L step j hj, ← Equiv.Perm.mul_apply, ← pow_add]
  by_cases h : r + j ≤ L
  · simpa [h] using pow_walk g v L step (r + j) h
  · have hL : (g ^ L) (v 0) = v 0 := (pow_walk g v L step L le_rfl).trans closed
    have heq : r + j = (r + j - L) + L := by omega
    rw [if_neg h, heq, pow_add, Equiv.Perm.mul_apply, hL]
    simpa only [Nat.add_sub_cancel] using pow_walk g v L step (r + j - L) (by omega)

end ReturnCycle

end SuperpermutationLowerBound.Refinement
