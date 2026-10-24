module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! Elementary factorial normalizations used in the manuscript's limits. -/
noncomputable section
open Filter Topology
namespace SuperpermutationLowerBound.ChainReturns.Asymptotics

/-- A fixed natural subtraction is asymptotic to the original index. -/
theorem tendsto_nat_sub_div (j : ℕ) :
    Tendsto (fun n : ℕ => ((n - j : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_const_div_atTop_nhds_zero_nat (j : ℝ))
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop j, eventually_gt_atTop 0] with n hj hn
  rw [Nat.cast_sub hj]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp

/-- The descending product has the expected leading power. -/
theorem tendsto_descFactorial_div_pow (j : ℕ) :
    Tendsto (fun n : ℕ => (n.descFactorial j : ℝ) / (n : ℝ)^j) atTop (𝓝 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have h := (tendsto_nat_sub_div j).mul ih
      simp only [one_mul] at h
      convert h using 1
      ext n
      simp only [Nat.descFactorial_succ, Nat.cast_mul, pow_succ]
      ring

/-- Fixed factorial shifts agree asymptotically with powers of the index. -/
theorem tendsto_factorial_div_pow_mul_factorial_sub (j : ℕ) :
    Tendsto (fun n : ℕ => (n.factorial : ℝ) /
      ((n : ℝ)^j * ((n-j).factorial : ℝ))) atTop (𝓝 1) := by
  apply (tendsto_descFactorial_div_pow j).congr'
  filter_upwards [eventually_ge_atTop j] with n hn
  have hf : (((n-j).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have he : ((n-j).factorial : ℝ) * (n.descFactorial j : ℝ) = (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_mul_descFactorial hn
  rw [← he]
  field_simp

/-- A fixed backward factorial shift tends to infinity. -/
theorem tendsto_factorial_sub_atTop (j : ℕ) :
    Tendsto (fun n : ℕ => ((n-j).factorial : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (factorial_tendsto_atTop.comp (tendsto_sub_atTop_nat j))

/-- A fixed power is negligible compared with a factorial. -/
theorem tendsto_pow_div_factorial (d : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ)^d / (n.factorial : ℝ)) atTop (𝓝 0) := by
  have h := ((tendsto_factorial_div_pow_mul_factorial_sub d).inv₀ (by norm_num)).mul
    (tendsto_inv_atTop_zero.comp (tendsto_factorial_sub_atTop d))
  simp only [inv_one, one_mul] at h
  apply h.congr'
  filter_upwards [] with n
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hg : ((n-d).factorial : ℝ) ≠ 0 := by positivity
  simp only [Function.comp_apply]
  field_simp

/-- Any fixed power is negligible compared with any fixed backward factorial shift. -/
theorem tendsto_pow_div_factorial_sub (d j : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ)^d / ((n-j).factorial : ℝ)) atTop (𝓝 0) := by
  have h := (tendsto_pow_div_factorial (d+j)).mul
    (tendsto_factorial_div_pow_mul_factorial_sub j)
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hg : ((n-j).factorial : ℝ) ≠ 0 := by positivity
  simp only [pow_add]
  field_simp

/-- Convert a limit with normalization n!/n^j to the equivalent (n-j)! scale. -/
theorem tendsto_normalize_factorial_sub {f : ℕ → ℝ} {L : ℝ} (j : ℕ)
    (h : Tendsto (fun n => f n * (n : ℝ)^j / (n.factorial : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun n => f n / ((n-j).factorial : ℝ)) atTop (𝓝 L) := by
  have ht := h.mul (tendsto_factorial_div_pow_mul_factorial_sub j)
  simp only [mul_one] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hg : ((n-j).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- The factorial normalization transfer along any sequence of natural indices. -/
theorem tendsto_normalize_factorial_sub_along {α : Type*} {l : Filter α}
    {N : α → ℕ} (hN : Tendsto N l atTop) {f : α → ℝ} {L : ℝ} (j : ℕ)
    (h : Tendsto (fun x => f x * (N x : ℝ)^j / ((N x).factorial : ℝ)) l (𝓝 L)) :
    Tendsto (fun x => f x / ((N x-j).factorial : ℝ)) l (𝓝 L) := by
  have ht := h.mul ((tendsto_factorial_div_pow_mul_factorial_sub j).comp hN)
  simp only [mul_one] at ht
  apply ht.congr'
  filter_upwards [hN.eventually (eventually_gt_atTop 0)] with x hx
  have hn0 : (N x : ℝ) ≠ 0 := by positivity
  have hf : ((N x).factorial : ℝ) ≠ 0 := by positivity
  have hg : ((N x-j).factorial : ℝ) ≠ 0 := by positivity
  simp only [Function.comp_apply]
  field_simp

/-- A function bounded in absolute value by a fixed power is factorially negligible.
This form covers piecewise or exact-order parameter formulas without requiring
that the numerator itself be a polynomial. -/
theorem tendsto_div_factorial_sub_of_abs_le {α : Type*} {l : Filter α}
    {N : α → ℕ} (hN : Tendsto N l atTop) {f : α → ℝ}
    (d j : ℕ) (C : ℝ) (hf : ∀ᶠ x in l, |f x| ≤ C * (N x : ℝ)^d) :
    Tendsto (fun x => f x / ((N x-j).factorial : ℝ)) l (𝓝 0) := by
  have hp := (tendsto_pow_div_factorial_sub d j).comp hN
  have hp' := hp.const_mul C
  have hn' := hp.const_mul (-C)
  simp only [mul_zero] at hp' hn'
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hn' hp'
  · filter_upwards [hf] with x hx
    have hden : (0 : ℝ) < ((N x-j).factorial : ℝ) := by positivity
    have hb := (abs_le.mp hx).1
    dsimp
    rw [← mul_div_assoc]
    apply (div_le_div_iff_of_pos_right hden).mpr
    linarith
  · filter_upwards [hf] with x hx
    have hden : (0 : ℝ) < ((N x-j).factorial : ℝ) := by positivity
    have hb := (abs_le.mp hx).2
    dsimp
    rw [← mul_div_assoc]
    exact (div_le_div_iff_of_pos_right hden).mpr hb

end SuperpermutationLowerBound.ChainReturns.Asymptotics
