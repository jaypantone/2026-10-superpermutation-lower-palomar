module

public import asymptotics.gains.IntegerGains

@[expose] public section

noncomputable section
open Filter Topology
open SuperpermutationLowerBound.ChainReturns
open SuperpermutationLowerBound.ChainReturns.Asymptotics
namespace SuperpermutationBounds.ChainReturns.Asymptotic

theorem fraction_denominator_pos {n : ℕ} {p t : ℚ} (h : Admissible n p t) :
    0 < kappa (n:ℝ)*(t:ℝ)-2*n := by
  have hh := denominator_pos h
  have he : (n:ℚ)*lam n t-2*t = ((n:ℚ)^2-2*n-2)*t-2*n := by
    unfold lam
    ring
  rw [he] at hh
  dsimp [kappa]
  exact_mod_cast hh

theorem zero_slope_eventually_pos :
    ∀ᶠ n : ℕ in atTop, 0 ≤ (n:ℝ)*factorialA n/2 -
      kappa n*(zeroOldP n+1/2) - (1/2)*(kappa n*zeroOldT n-2*n) := by
  let J : ℝ → ℝ := fun x => x*(x-1)+kappa x*(zeroOldP x+1/2)+
    (1/2)*(kappa x*zeroOldT x-2*x)
  have hJ : Tendsto (fun n : ℕ => J n/(n.factorial:ℝ)) atTop (𝓝 0) := by
    have hh := (((tendsto_pow_div_factorial 3).const_mul (4/3)).sub
      ((tendsto_pow_div_factorial 2).const_mul (8/3))).sub
      ((tendsto_pow_div_factorial 1).const_mul (8/3))
    have hh := hh.add ((tendsto_pow_div_factorial 0).const_mul 2)
    convert hh using 1 <;> try norm_num
    ext n
    dsimp [J, kappa, zeroOldP, zeroOldT]
    ring
  filter_upwards [eventually_ge_atTop 1,
    hJ.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with n hn hlt
  have hJlt : J n < (n.factorial:ℝ) := (div_lt_one (by positivity)).mp hlt
  rw [show (n:ℝ)*factorialA n/2 = (n.factorial:ℝ)-(n:ℝ)*(n-1)
    from factorial_gain_numerator n hn]
  dsimp [J] at hJlt
  linarith

theorem one_slope_eventually_pos :
    ∀ᶠ n : ℕ in atTop, 0 ≤ (n:ℝ)*factorialA n/2 - kappa n*oneOldP n := by
  have hJ : Tendsto (fun n : ℕ =>
      ((n:ℝ)*(n-1)+kappa n*oneOldP n)/(n.factorial:ℝ)) atTop (𝓝 0) := by
    have hh := one_gain_polynomial_negligible.div_const 16
    convert hh using 1 <;> try norm_num
    ext n
    dsimp [oneGainPolynomial]
    ring
  filter_upwards [eventually_ge_atTop 1,
    hJ.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with n hn hlt
  have hJlt : (n:ℝ)*(n-1)+kappa n*oneOldP n < (n.factorial:ℝ) :=
    (div_lt_one (by positivity)).mp hlt
  rw [show (n:ℝ)*factorialA n/2 = (n.factorial:ℝ)-(n:ℝ)*(n-1)
    from factorial_gain_numerator n hn]
  linarith

theorem exact_zero_parameters (m : ℕ) (hm : 4 ≤ m) :
    ((exactParameters (3*m+1)).1:ℝ) =
      zeroOldP (3*m)+1/2+(1/2)*(1/(2*(returnZero (3*m):ℝ))) ∧
    ((exactParameters (3*m+1)).2:ℝ) =
      zeroOldT (3*m)-1/(2*(returnZero (3*m):ℝ)) := by
  rw [exactParameters_large (by omega)]
  have he : 3*m+1-1=3*m := by omega
  simp only [he, generalParameters, Nat.mul_mod_right,
    Nat.mul_div_cancel_left _ (by omega : 0<3)]
  push_cast
  constructor <;> dsimp [zeroOldP, zeroOldT] <;> ring

theorem exact_one_parameters (m : ℕ) (hm : 4 ≤ m) :
    ((exactParameters (3*m+2)).1:ℝ) = oneOldP (3*(m:ℝ)+1) ∧
    ((exactParameters (3*m+2)).2:ℝ) =
      oneOldT (3*(m:ℝ)+1)-1/(returnOne m:ℝ) := by
  rw [exactParameters_large (by omega)]
  have he : 3*m+2-1=3*m+1 := by omega
  have hmod : (3*m+1)%3=1 := by omega
  have hdiv : (3*m+1)/3=m := by omega
  simp only [he, generalParameters, hmod, hdiv]
  push_cast
  constructor <;> dsimp [oneOldP, oneOldT] <;> ring

theorem paperBound_mono_correction {K : ℕ} {p t p' t' : ℚ}
    (h : correctionReal K (p:ℝ) (t:ℝ) ≤ correctionReal K (p':ℝ) (t':ℝ)) :
    paperBound K p t ≤ paperBound K p' t' := by
  have hQ : correctionQ K p t ≤ correctionQ K p' t' := by
    have hc : (correctionQ K p t:ℝ) ≤ (correctionQ K p' t':ℝ) := by
      simpa only [correctionQ_cast] using h
    exact_mod_cast hc
  simpa only [paperBound_eq_base_ceil] using
    Nat.add_le_add_left (Nat.ceil_mono hQ) (F3Nat K+K-3)

theorem exact_ge_quadratic_zero_eventually :
    ∀ᶠ m : ℕ in atTop, quadraticNat (3*m+1) ≤ exactNat (3*m+1) := by
  have hN : Tendsto (fun m : ℕ => 3*m) atTop atTop := by
    simpa only [Nat.add_zero] using gain_residue_tendsto 0
  filter_upwards [eventually_ge_atTop 4, hN.eventually zero_slope_eventually_pos]
    with m hm hslope
  have hqa := quadraticParameters_admissible (show 8≤3*m+1 by omega)
  have hea := exactParameters_admissible (show 8≤3*m+1 by omega)
  have hq : Admissible (3*m) (quadraticParameters (3*m+1)).1
      (quadraticParameters (3*m+1)).2 := by simpa using hqa
  have he : Admissible (3*m) (exactParameters (3*m+1)).1
      (exactParameters (3*m+1)).2 := by simpa using hea
  have hqt : ((quadraticParameters (3*m+1)).2:ℝ) ≠ 0 := by exact_mod_cast hq.t_pos.ne'
  have het : ((exactParameters (3*m+1)).2:ℝ) ≠ 0 := by exact_mod_cast he.t_pos.ne'
  have hDq := fraction_denominator_pos hq
  have hDe := fraction_denominator_pos he
  rw [(quadratic_zero_parameters m hm).2] at hDq
  rw [(exact_zero_parameters m hm).2] at hDe
  have hRp : 0 < (returnZero (3*m):ℝ) := by
    exact_mod_cast returnZero_pos (show 2≤3*m by omega)
  have hRb : 4*(returnZero (3*m):ℝ) ≤ (3*(m:ℝ))^2 := by
    exact_mod_cast returnZero_quadratic (show 2≤3*m by omega)
  have hh : 2/(3*(m:ℝ))^2 ≤ 1/(2*(returnZero (3*m):ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  apply paperBound_mono_correction
  rw [correctionReal_succ_fraction (3*m) (by omega) _ _ hqt,
    correctionReal_succ_fraction (3*m) (by omega) _ _ het,
    (quadratic_zero_parameters m hm).1, (quadratic_zero_parameters m hm).2,
    (exact_zero_parameters m hm).1, (exact_zero_parameters m hm).2]
  have hp : zeroOldP (3*m)+1/2+1/(3*(m:ℝ))^2 =
      (zeroOldP (3*m)+1/2)+(1/2)*(2/(3*(m:ℝ))^2) := by ring
  rw [hp]
  apply correctionFraction_mono_on_line _ _ _ _ _ _ _ _ hh
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using hDq
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using hDe
  · simpa only [factorialA, Nat.cast_mul, Nat.cast_ofNat] using hslope

theorem exact_ge_quadratic_one_eventually :
    ∀ᶠ m : ℕ in atTop, quadraticNat (3*m+2) ≤ exactNat (3*m+2) := by
  filter_upwards [eventually_ge_atTop 4,
    (gain_residue_tendsto 1).eventually one_slope_eventually_pos] with m hm hslope
  have hqa := quadraticParameters_admissible (show 8≤3*m+2 by omega)
  have hea := exactParameters_admissible (show 8≤3*m+2 by omega)
  have hq : Admissible (3*m+1) (quadraticParameters (3*m+2)).1
      (quadraticParameters (3*m+2)).2 := by simpa using hqa
  have he : Admissible (3*m+1) (exactParameters (3*m+2)).1
      (exactParameters (3*m+2)).2 := by simpa using hea
  have hqt : ((quadraticParameters (3*m+2)).2:ℝ) ≠ 0 := by exact_mod_cast hq.t_pos.ne'
  have het : ((exactParameters (3*m+2)).2:ℝ) ≠ 0 := by exact_mod_cast he.t_pos.ne'
  have hDq := fraction_denominator_pos hq
  have hDe := fraction_denominator_pos he
  rw [(quadratic_one_parameters m hm).2] at hDq
  rw [(exact_one_parameters m hm).2] at hDe
  have hRp : 0 < (returnOne m:ℝ) := by exact_mod_cast returnOne_pos (by omega : 3≤m)
  have hRb : 4*(returnOne m:ℝ) ≤ (3*(m:ℝ)+1)^2 := by
    exact_mod_cast returnOne_quadratic (by omega : 3≤m)
  have hh : 4/(3*(m:ℝ)+1)^2 ≤ 1/(returnOne m:ℝ) := by
    apply (div_le_div_iff₀ (by positivity) hRp).2
    nlinarith
  apply paperBound_mono_correction
  rw [show 3*m+2=(3*m+1)+1 by omega,
    correctionReal_succ_fraction (3*m+1) (by omega) _ _ hqt,
    correctionReal_succ_fraction (3*m+1) (by omega) _ _ het,
    (quadratic_one_parameters m hm).1, (quadratic_one_parameters m hm).2,
    (exact_one_parameters m hm).1, (exact_one_parameters m hm).2]
  have hhmono := correctionFraction_mono_on_line (factorialA (3*m+1))
    (kappa (3*m+1)) (3*m+1) (oneOldP (3*(m:ℝ)+1)) (oneOldT (3*(m:ℝ)+1))
    0 (4/(3*(m:ℝ)+1)^2) (1/(returnOne m:ℝ)) hh
  simp only [zero_mul, add_zero, sub_zero] at hhmono
  have hresult := hhmono
    (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hDq)
    (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hDe)
    (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hslope)
  simpa only [factorialA, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hresult

end SuperpermutationBounds.ChainReturns.Asymptotic
