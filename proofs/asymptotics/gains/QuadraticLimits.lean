module

public import asymptotics.gains.Algebra
public import asymptotics.reference.Parameters
public import asymptotics.foundation.Factorial

@[expose] public section

noncomputable section
open Filter Topology
open SuperpermutationLowerBound.ChainReturns.Asymptotics
namespace SuperpermutationBounds.ChainReturns.Asymptotic

def zeroOldP (x : ℝ) : ℝ := 2*x/3
def zeroOldT (x : ℝ) : ℝ := 4*x/3-3
def oneOldP (x : ℝ) : ℝ := (x-1)*(2*x+1)/9
def oneOldT (x : ℝ) : ℝ := 2*x^2/9+2*x/9-22/9
def factorialA (n : ℕ) : ℝ := 2*((n-1).factorial:ℝ)-2*((n:ℝ)-1)
def zeroQuadraticGain (n : ℕ) : ℝ :=
  correctionFraction (factorialA n) (kappa n) n
    (zeroOldP n+1/2+1/(n:ℝ)^2) (zeroOldT n-2/(n:ℝ)^2) -
  correctionFraction (factorialA n) (kappa n) n (zeroOldP n) (zeroOldT n)
def oneQuadraticGain (n : ℕ) : ℝ :=
  correctionFraction (factorialA n) (kappa n) n
    (oneOldP n) (oneOldT n-4/(n:ℝ)^2) -
  correctionFraction (factorialA n) (kappa n) n (oneOldP n) (oneOldT n)

theorem zero_old_t_limit :
    Tendsto (fun n : ℕ => zeroOldT n / (n:ℝ)) atTop (𝓝 (4/3)) := by
  have hh := (tendsto_const_nhds (x := (4/3:ℝ))).sub
    (tendsto_const_div_atTop_nhds_zero_nat (3:ℝ))
  simpa [zeroOldT, sub_div] using hh.congr' (by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n:ℝ) ≠ 0 := by positivity
    field_simp
    <;> ring)

theorem zero_new_t_limit :
    Tendsto (fun n : ℕ => (zeroOldT n-2/(n:ℝ)^2) / (n:ℝ))
      atTop (𝓝 (4/3)) := by
  have hi := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hh := zero_old_t_limit.sub ((hi.pow 3).const_mul 2)
  convert hh.congr' ?_ using 1 <;> try norm_num
  filter_upwards [] with n
  simp only [Pi.sub_apply, zeroOldT]
  ring

theorem one_old_t_limit :
    Tendsto (fun n : ℕ => oneOldT n / (n:ℝ)^2) atTop (𝓝 (2/9)) := by
  have hi := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hh := ((tendsto_const_nhds (x := (2/9:ℝ))).add (hi.const_mul (2/9))).sub
    ((hi.pow 2).const_mul (22/9))
  convert hh.congr' ?_ using 1 <;> try norm_num
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  simp only [oneOldT]
  field_simp
  <;> ring

theorem one_new_t_limit :
    Tendsto (fun n : ℕ => (oneOldT n-4/(n:ℝ)^2)/(n:ℝ)^2)
      atTop (𝓝 (2/9)) := by
  have hi := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hh := one_old_t_limit.sub ((hi.pow 4).const_mul 4)
  convert hh.congr' ?_ using 1 <;> try norm_num
  filter_upwards [] with n
  simp only [oneOldT]
  ring

def zeroGainPolynomial (x : ℝ) : ℝ :=
  8*(x*(x-1)+kappa x*zeroOldP x) +
    2*(kappa x*zeroOldT x-2*x)*x^2+4*(kappa x*zeroOldT x-2*x)
def oneGainPolynomial (x : ℝ) : ℝ :=
  16*(x*(x-1)+kappa x*oneOldP x)

theorem zero_gain_polynomial_negligible :
    Tendsto (fun n : ℕ => zeroGainPolynomial n/(n.factorial:ℝ)) atTop (𝓝 0) := by
  have hh := (((((tendsto_pow_div_factorial 5).const_mul (8/3)).sub
    ((tendsto_pow_div_factorial 4).const_mul (34/3))).add
    ((tendsto_pow_div_factorial 3).const_mul (40/3))).sub
    ((tendsto_pow_div_factorial 2).const_mul (40/3))).sub
    ((tendsto_pow_div_factorial 1).const_mul (40/3))
  have hh := hh.add ((tendsto_pow_div_factorial 0).const_mul 24)
  convert hh using 1 <;> try norm_num
  ext n
  simp only [zeroGainPolynomial, kappa, zeroOldP, zeroOldT]
  ring

theorem one_gain_polynomial_negligible :
    Tendsto (fun n : ℕ => oneGainPolynomial n/(n.factorial:ℝ)) atTop (𝓝 0) := by
  have hh := ((((tendsto_pow_div_factorial 4).const_mul (32/9)).sub
    ((tendsto_pow_div_factorial 3).const_mul (80/9))).add
    ((tendsto_pow_div_factorial 2).const_mul (32/3))).sub
    ((tendsto_pow_div_factorial 1).const_mul (80/9))
  have hh := hh.add ((tendsto_pow_div_factorial 0).const_mul (32/9))
  convert hh using 1 <;> try norm_num
  ext n
  simp only [oneGainPolynomial, kappa, oneOldP]
  ring


theorem zero_old_denominator_limit :
    Tendsto (fun n : ℕ => (kappa n*zeroOldT n-2*n)/(n:ℝ)^3)
      atTop (𝓝 (4/3)) := by
  simpa only [kappa, pow_one] using normalized_denominator_limit 1
    tendsto_natCast_atTop_atTop (by simpa only [pow_one] using zero_old_t_limit)

theorem zero_new_denominator_limit :
    Tendsto (fun n : ℕ => (kappa n*(zeroOldT n-2/(n:ℝ)^2)-2*n)/(n:ℝ)^3)
      atTop (𝓝 (4/3)) := by
  simpa only [kappa, pow_one] using normalized_denominator_limit 1
    tendsto_natCast_atTop_atTop (by simpa only [pow_one] using zero_new_t_limit)

theorem one_old_denominator_limit :
    Tendsto (fun n : ℕ => (kappa n*oneOldT n-2*n)/(n:ℝ)^4)
      atTop (𝓝 (2/9)) := by
  simpa only [kappa] using normalized_denominator_limit 2
    tendsto_natCast_atTop_atTop one_old_t_limit

theorem one_new_denominator_limit :
    Tendsto (fun n : ℕ => (kappa n*(oneOldT n-4/(n:ℝ)^2)-2*n)/(n:ℝ)^4)
      atTop (𝓝 (2/9)) := by
  simpa only [kappa] using normalized_denominator_limit 2
    tendsto_natCast_atTop_atTop one_new_t_limit

theorem zero_quadratic_gain_power_limit :
    Tendsto (fun n : ℕ => zeroQuadraticGain n*(n:ℝ)^8/(n.factorial:ℝ))
      atTop (𝓝 (9/2)) := by
  have hnum := (tendsto_const_nhds (x := (8:ℝ))).sub zero_gain_polynomial_negligible
  have hh := hnum.div (zero_old_denominator_limit.mul zero_new_denominator_limit)
    (by norm_num)
  convert hh.congr' ?_ using 1 <;> try norm_num
  filter_upwards [eventually_ge_atTop 1,
    zero_old_denominator_limit.eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<4/3)),
    zero_new_denominator_limit.eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<4/3))]
    with n hn hD hD'
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  have hF : (n.factorial:ℝ) ≠ 0 := by positivity
  have hA : kappa n*zeroOldT n-2*n ≠ 0 := by intro h; simp [h] at hD
  have hB : kappa n*(zeroOldT n-2/(n:ℝ)^2)-2*n ≠ 0 := by intro h; simp [h] at hD'
  have hg : zeroQuadraticGain n =
      (4*(2/(n:ℝ)^2)*((n.factorial:ℝ)-((n:ℝ)*(n-1)+kappa n*zeroOldP n))-
        4*(1/2+1/(n:ℝ)^2)*(kappa n*zeroOldT n-2*n)) /
      ((kappa n*(zeroOldT n-2/(n:ℝ)^2)-2*n)*(kappa n*zeroOldT n-2*n)) := by
    unfold zeroQuadraticGain
    rw [show zeroOldP n+1/2+1/(n:ℝ)^2 = zeroOldP n+(1/2+1/(n:ℝ)^2) by ring]
    rw [correctionFraction_sub _ _ _ _ _ _ _ hA hB]
    rw [show (n:ℝ)*factorialA n/2 = (n.factorial:ℝ)-(n:ℝ)*(n-1)
      from factorial_gain_numerator n hn]
    congr 2 <;> ring
  rw [hg]
  exact (normalize_zero_quotient (n:ℝ) (n.factorial:ℝ)
    (kappa n*zeroOldT n-2*n) (kappa n*(zeroOldT n-2/(n:ℝ)^2)-2*n)
    ((n:ℝ)*(n-1)+kappa n*zeroOldP n) hn0 hF hA hB).symm

theorem one_quadratic_gain_power_limit :
    Tendsto (fun n : ℕ => oneQuadraticGain n*(n:ℝ)^10/(n.factorial:ℝ))
      atTop (𝓝 324) := by
  have hnum := (tendsto_const_nhds (x := (16:ℝ))).sub one_gain_polynomial_negligible
  have hh := hnum.div (one_old_denominator_limit.mul one_new_denominator_limit)
    (by norm_num)
  convert hh.congr' ?_ using 1 <;> try norm_num
  filter_upwards [eventually_ge_atTop 1,
    one_old_denominator_limit.eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<2/9)),
    one_new_denominator_limit.eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<2/9))]
    with n hn hD hD'
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  have hF : (n.factorial:ℝ) ≠ 0 := by positivity
  have hA : kappa n*oneOldT n-2*n ≠ 0 := by intro h; simp [h] at hD
  have hB : kappa n*(oneOldT n-4/(n:ℝ)^2)-2*n ≠ 0 := by intro h; simp [h] at hD'
  have hg : oneQuadraticGain n =
      4*(4/(n:ℝ)^2)*((n.factorial:ℝ)-((n:ℝ)*(n-1)+kappa n*oneOldP n)) /
      ((kappa n*(oneOldT n-4/(n:ℝ)^2)-2*n)*(kappa n*oneOldT n-2*n)) := by
    have he := correctionFraction_sub (factorialA n) (kappa n) n
      (oneOldP n) (oneOldT n) (4/(n:ℝ)^2) 0 hA hB
    simp only [add_zero, mul_zero, zero_mul, sub_zero] at he
    rw [oneQuadraticGain, he]
    rw [show (n:ℝ)*factorialA n/2 = (n.factorial:ℝ)-(n:ℝ)*(n-1)
      from factorial_gain_numerator n hn]
    congr 2 <;> ring
  rw [hg]
  exact (normalize_one_quotient (n:ℝ) (n.factorial:ℝ)
    (kappa n*oneOldT n-2*n) (kappa n*(oneOldT n-4/(n:ℝ)^2)-2*n)
    ((n:ℝ)*(n-1)+kappa n*oneOldP n) hn0 hF hA hB).symm

theorem zero_quadratic_gain_factorial_limit :
    Tendsto (fun n : ℕ => zeroQuadraticGain n/((n-8).factorial:ℝ))
      atTop (𝓝 (9/2)) :=
  tendsto_normalize_factorial_sub 8 zero_quadratic_gain_power_limit

theorem one_quadratic_gain_factorial_limit :
    Tendsto (fun n : ℕ => oneQuadraticGain n/((n-10).factorial:ℝ))
      atTop (𝓝 324) :=
  tendsto_normalize_factorial_sub 10 one_quadratic_gain_power_limit

end SuperpermutationBounds.ChainReturns.Asymptotic
