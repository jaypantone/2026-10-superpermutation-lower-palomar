module

public import bridge.FrozenParameters
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! Leading real asymptotics of the frozen rational parameter table. -/
noncomputable section
open Filter Topology
open SuperpermutationBounds.ChainReturns
open SuperpermutationLowerBound.ChainReturns
namespace SuperpermutationBounds.ChainReturns.Asymptotic

theorem bounded_div_nat_tendsto_zero {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ᶠ m in atTop, 0 ≤ f m ∧ f m ≤ C) :
    Tendsto (fun m => f m / m) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ (tendsto_const_div_atTop_nhds_zero_nat C)
  · filter_upwards [hf] with m hm
    exact div_nonneg hm.1 (Nat.cast_nonneg m)
  · filter_upwards [hf] with m hm
    exact div_le_div_of_nonneg_right hm.2 (Nat.cast_nonneg m)

theorem bounded_div_nat_sq_tendsto_zero {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ᶠ m in atTop, 0 ≤ f m ∧ f m ≤ C) :
    Tendsto (fun m => f m / (m : ℝ)^2) atTop (𝓝 0) := by
  simpa [pow_two, div_eq_mul_inv, mul_assoc] using
    (bounded_div_nat_tendsto_zero hf).mul
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem reciprocal_bounded {R : ℕ → ℚ} (hR : ∀ᶠ m in atTop, 1 ≤ R m) :
    ∀ᶠ m in atTop, 0 ≤ (1 / R m : ℚ) ∧ (1 / R m : ℚ) ≤ 1 := by
  filter_upwards [hR] with m hm
  constructor
  · positivity
  · exact (div_le_one (lt_of_lt_of_le (by norm_num) hm)).2 hm

theorem reciprocal_cast_bounded {R : ℕ → ℚ} (hR : ∀ᶠ m in atTop, 1 ≤ R m) :
    ∀ᶠ m in atTop, 0 ≤ ((1 / R m : ℚ) : ℝ) ∧ ((1 / R m : ℚ) : ℝ) ≤ 1 := by
  filter_upwards [reciprocal_bounded hR] with m hm
  exact_mod_cast hm

theorem general_t_zero_limit {R S : ℕ → ℚ}
    (hR : ∀ᶠ m in atTop, 1 ≤ R m) :
    Tendsto (fun m => ((generalParameters (3*m) (R m) (S m)).2 : ℝ) / (3*m))
      atTop (𝓝 (4/3)) := by
  have h1 := tendsto_const_div_atTop_nhds_zero_nat (3 : ℝ)
  have h2 := (bounded_div_nat_tendsto_zero (reciprocal_cast_bounded hR)).div_const 2
  have hh := ((tendsto_const_nhds (x := (4:ℝ))).sub h1).sub h2
  have hh := hh.div_const 3
  convert hh.congr' ?_ using 1 <;> try norm_num
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  simp only [generalParameters, Nat.mul_div_cancel_left _ (by omega : 0 < 3),
    Nat.mul_mod_right, Nat.cast_mul, Nat.cast_ofNat, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_ofNat, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  try dsimp only [Pi.div_apply]
  push_cast
  field_simp
  <;> ring

theorem general_t_one_limit {R S : ℕ → ℚ}
    (hS : ∀ᶠ m in atTop, 1 ≤ S m) :
    Tendsto (fun m => ((generalParameters (3*m+1) (R m) (S m)).2 : ℝ) /
      (3*(m : ℝ)+1)^2) atTop (𝓝 (2/9)) := by
  have h1 := tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
  have hi := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h2 := (bounded_div_nat_sq_tendsto_zero (reciprocal_cast_bounded hS))
  have h3 := ((tendsto_const_nhds (x := (2:ℝ))).add h1).sub ((hi.pow 2).const_mul 2)
  have hn := h3.sub h2
  have hd := ((tendsto_const_nhds (x := (3:ℝ))).add hi).pow 2
  have hh := hn.div hd (by norm_num)
  convert hh.congr' ?_ using 1 <;> try norm_num
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hdiv : (3*m+1)/3 = m := by omega
  have hmod : (3*m+1)%3 = 1 := by omega
  simp only [generalParameters, hdiv, hmod]
  try dsimp only [Pi.div_apply]
  push_cast
  field_simp
  <;> ring

theorem general_t_two_limit (R S : ℕ → ℚ) :
    Tendsto (fun m => ((generalParameters (3*m+2) (R m) (S m)).2 : ℝ) /
      (3*(m : ℝ)+2)^2) atTop (𝓝 (4/9)) := by
  have hi := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hn := ((tendsto_const_nhds (x := (4:ℝ))).add (hi.const_mul 5)).sub
    ((hi.pow 2).const_mul (5/2))
  have hd := ((tendsto_const_nhds (x := (3:ℝ))).add (hi.const_mul 2)).pow 2
  have hh := hn.div hd (by norm_num)
  convert hh.congr' ?_ using 1 <;> try norm_num
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hdiv : (3*m+2)/3 = m := by omega
  have hmod : (3*m+2)%3 = 2 := by omega
  simp only [generalParameters, hdiv, hmod]
  try dsimp only [Pi.div_apply]
  push_cast
  field_simp
  <;> ring

/-- The common quadratic denominator polynomial at its natural scale. -/
theorem normalized_kappa_limit {x : ℕ → ℝ} (hx : Tendsto x atTop atTop) :
    Tendsto (fun m => (x m ^ 2 - 2*x m - 2) / x m ^ 2) atTop (𝓝 1) := by
  have hi := tendsto_inv_atTop_zero.comp hx
  have hh := ((tendsto_const_nhds (x := (1:ℝ))).sub (hi.const_mul 2)).sub
    ((hi.pow 2).const_mul 2)
  convert hh.congr' ?_ using 1 <;> try norm_num
  filter_upwards [hx.eventually (eventually_gt_atTop 0)] with m hm
  have hne := ne_of_gt hm
  try dsimp
  field_simp
  <;> ring

/-- A denominator with a parameter of degree `d`, uniformly in the residue class. -/
theorem normalized_denominator_limit {x t : ℕ → ℝ} {c : ℝ} (d : ℕ)
    (hx : Tendsto x atTop atTop)
    (ht : Tendsto (fun m => t m / x m ^ d) atTop (𝓝 c)) :
    Tendsto (fun m => ((x m ^ 2 - 2*x m - 2) * t m - 2*x m) /
      x m ^ (d+2)) atTop (𝓝 c) := by
  have hi := tendsto_inv_atTop_zero.comp hx
  have hh := ((normalized_kappa_limit hx).mul ht).sub
    ((hi.pow (d+1)).const_mul 2)
  convert hh.congr' ?_ using 1 <;> try simp
  filter_upwards [hx.eventually (eventually_gt_atTop 0)] with m hm
  have hne := ne_of_gt hm
  try dsimp
  simp only [pow_add, pow_one, pow_two]
  field_simp
  <;> ring

end SuperpermutationBounds.ChainReturns.Asymptotic
