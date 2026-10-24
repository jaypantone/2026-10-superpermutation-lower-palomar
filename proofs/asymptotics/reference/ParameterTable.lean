module

public import asymptotics.reference.Parameters
public import asymptotics.Definitions

@[expose] public section

noncomputable section
open Filter Topology
open SuperpermutationBounds.ChainReturns
open SuperpermutationLowerBound.ChainReturns
namespace SuperpermutationBounds.ChainReturns.Asymptotic

theorem general_p_zero_limit {R S : ℕ → ℚ}
    (hR : ∀ᶠ m in atTop, 1 ≤ R m) :
    Tendsto (fun m => ((generalParameters (3*m) (R m) (S m)).1 : ℝ) / (3*m)^2)
      atTop (𝓝 0) := by
  have hi := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hh := ((hi.const_mul (2/9)).add ((hi.pow 2).const_mul (1/18))).add
    ((bounded_div_nat_sq_tendsto_zero (reciprocal_cast_bounded hR)).div_const 36)
  convert hh.congr' ?_ using 1 <;> try norm_num
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  simp only [generalParameters, Nat.mul_div_cancel_left _ (by omega : 0 < 3),
    Nat.mul_mod_right]
  push_cast
  field_simp
  <;> ring

theorem general_p_one_limit (R S : ℕ → ℚ) :
    Tendsto (fun m => ((generalParameters (3*m+1) (R m) (S m)).1 : ℝ) /
      (3*(m : ℝ)+1)^2) atTop (𝓝 (2/9)) := by
  have hi := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hh := ((tendsto_const_nhds (x := (2:ℝ))).add hi).div
    (((tendsto_const_nhds (x := (3:ℝ))).add hi).pow 2) (by norm_num)
  convert hh.congr' ?_ using 1 <;> try norm_num
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hdiv : (3*m+1)/3 = m := by omega
  have hmod : (3*m+1)%3 = 1 := by omega
  simp only [generalParameters, hdiv, hmod, Pi.div_apply]
  push_cast
  field_simp
  <;> ring

theorem general_p_two_limit (R S : ℕ → ℚ) :
    Tendsto (fun m => ((generalParameters (3*m+2) (R m) (S m)).1 : ℝ) /
      (3*(m : ℝ)+2)^2) atTop (𝓝 (2/9)) := by
  have hi := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hh := (((tendsto_const_nhds (x := (1:ℝ))).add hi).mul
    ((tendsto_const_nhds (x := (2:ℝ))).add hi)).div
    (((tendsto_const_nhds (x := (3:ℝ))).add (hi.const_mul 2)).pow 2) (by norm_num)
  convert hh.congr' ?_ using 1 <;> try norm_num
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hdiv : (3*m+2)/3 = m := by omega
  have hmod : (3*m+2)%3 = 2 := by omega
  simp only [generalParameters, hdiv, hmod, Pi.div_apply]
  push_cast
  field_simp
  <;> ring

theorem residue_tendsto (r : ℕ) : Tendsto (fun m : ℕ => 3*m+r) atTop atTop := by
  apply tendsto_atTop_mono (fun m => show m ≤ 3*m+r by omega) tendsto_id

theorem residue_cast_tendsto (r : ℕ) :
    Tendsto (fun m : ℕ => (3*(m : ℝ)+r)) atTop atTop := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).comp (residue_tendsto r)
  change Tendsto (fun m : ℕ => ((3*m+r : ℕ) : ℝ)) atTop atTop at h
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h

theorem exact_table_eventually (r : ℕ) (hr : r < 3) :
    ∀ᶠ m in atTop, exactParameters (3*m+r+1) =
      generalParameters (3*m+r) (returnZero (3*m+r)) (returnOne m) := by
  filter_upwards [eventually_ge_atTop 4] with m hm
  rw [exactParameters_large (by omega)]
  simp only [Nat.add_sub_cancel]
  rw [show (3*m+r)/3=m by omega]

theorem quadratic_table_eventually (r : ℕ) :
    ∀ᶠ m in atTop, quadraticParameters (3*m+r+1) =
      generalParameters (3*m+r) ((3*(m:ℚ)+r)^2/4) ((3*(m:ℚ)+r)^2/4) := by
  filter_upwards [eventually_ge_atTop 4] with m hm
  simp only [quadraticParameters, show ¬ 3*m+r+1 < 13 by omega, if_false]
  congr 1 <;> push_cast <;> congr 1 <;> omega

theorem exact_zero_return_ge_one (r : ℕ) :
    ∀ᶠ m in atTop, (1:ℚ) ≤ returnZero (3*m+r) := by
  filter_upwards [eventually_ge_atTop 4] with m hm
  exact_mod_cast returnZero_pos (by omega : 2 ≤ 3*m+r)

theorem exact_one_return_ge_one :
    ∀ᶠ m in atTop, (1:ℚ) ≤ returnOne m := by
  filter_upwards [eventually_ge_atTop 4] with m hm
  exact_mod_cast returnOne_pos (by omega : 3 ≤ m)

theorem quadratic_return_ge_one (r : ℕ) :
    ∀ᶠ m : ℕ in atTop, (1:ℚ) ≤ (3*(m:ℚ)+r)^2/4 := by
  filter_upwards [eventually_ge_atTop 4] with m hm
  have hmQ : (4:ℚ) ≤ m := by exact_mod_cast hm
  have hrQ : (0:ℚ) ≤ r := Nat.cast_nonneg r
  nlinarith

end SuperpermutationBounds.ChainReturns.Asymptotic
