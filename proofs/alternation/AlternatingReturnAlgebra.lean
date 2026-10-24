module

public import Mathlib.Tactic

@[expose] public section

/-! Group algebra in the alternating return calculation.  These lemmas do
not assume the desired return order: the order of the cycle/transposition
product remains a separate geometric and permutation-theoretic obligation. -/

namespace SuperpermutationLowerBound.Refinement.ChainReturns

variable {G : Type*} [Group G]

/-- After writing `rho = tau * s` and `g = tau * s^3`, the pair map has
this short product expression. -/
theorem alternating_pair_expansion (s tau : G) (htau : tau * tau = 1) :
    (tau * s) * ((tau * s ^ 3)⁻¹) ^ 2 *
      (tau * s) * (tau * s ^ 3)⁻¹ =
        tau * (s⁻¹) ^ 2 * tau * (s⁻¹) ^ 5 * tau := by
  have hinv : tau⁻¹ = tau := by
    calc
      tau⁻¹ = tau⁻¹ * (tau * tau) := by rw [htau]; simp
      _ = tau := by group
  calc
    _ = tau * (s⁻¹) ^ 2 * tau⁻¹ * (s⁻¹) ^ 5 * tau⁻¹ := by
      rw [pow_two]
      group
    _ = _ := by rw [hinv]

/-- The conjugacy used in the manuscript: one alternating pair becomes
one backward seven-step rotation followed by the transposition. -/
theorem alternating_pair_conjugacy (s tau : G) (htau : tau * tau = 1) :
    (s ^ 2 * tau) *
      ((tau * s) * ((tau * s ^ 3)⁻¹) ^ 2 * (tau * s) * (tau * s ^ 3)⁻¹) *
        (s ^ 2 * tau)⁻¹ = tau * (s⁻¹) ^ 7 := by
  rw [alternating_pair_expansion s tau htau]
  calc
    _ = s ^ 2 * (tau * tau) * (s⁻¹) ^ 2 * tau * (s⁻¹) ^ 7 := by group
    _ = _ := by rw [htau]; group

theorem conjugate_pow (a x : G) (r : ℕ) :
    (a * x * a⁻¹) ^ r = a * x ^ r * a⁻¹ := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ, ih, pow_succ]
      group

theorem return_of_conjugate_return {a x y : G} {r : ℕ}
    (hconj : a * x * a⁻¹ = y) (hreturn : y ^ r = 1) : x ^ r = 1 := by
  have h : a * x ^ r * a⁻¹ = 1 := by
    rw [← conjugate_pow, hconj, hreturn]
  have hcancel := congrArg (fun z => a⁻¹ * z * a) h
  simpa [mul_assoc] using hcancel

theorem alternating_pair_return_of_rotation_return (s tau : G)
    (htau : tau * tau = 1) (r : ℕ) (hreturn : (tau * (s⁻¹) ^ 7) ^ r = 1) :
    ((tau * s) * ((tau * s ^ 3)⁻¹) ^ 2 *
      (tau * s) * (tau * s ^ 3)⁻¹) ^ r = 1 := by
  exact return_of_conjugate_return (alternating_pair_conjugacy s tau htau) hreturn

/-- Reversing the two chains does not change a valid return exponent. -/
theorem reversed_pair_return (u v : G) (r : ℕ) (h : (v * u) ^ r = 1) :
    (u * v) ^ r = 1 := by
  apply return_of_conjugate_return (a := u⁻¹) (y := v * u)
  · group
  · exact h

end SuperpermutationLowerBound.Refinement.ChainReturns
