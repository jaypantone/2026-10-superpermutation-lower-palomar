module

public import asymptotics.reference.Parameters
public import asymptotics.Definitions
public import asymptotics.foundation.Rounding

@[expose] public section

noncomputable section
open Filter Topology
open SuperpermutationBounds.ChainReturns
open SuperpermutationLowerBound.ChainReturns
open SuperpermutationLowerBound.ChainReturns.Asymptotics
namespace SuperpermutationBounds.ChainReturns.Asymptotic

private theorem subtraction_identity (n f p t k : ℝ)
    (ht : t ≠ 0) (hk : k ≠ 0) (hd : k*t-2*n ≠ 0) :
    (2*f-2*(n-1)-4*p/t)/(k-2*n/t) - 2*(f-(n-1))/k =
      4*(n*f-n*(n-1)-p*k)/(k*(k*t-2*n)) := by
  have heq : k-2*n/t = (k*t-2*n)/t := by field_simp
  rw [heq]
  generalize hD : k*t-2*n = D at *
  field_simp [ht, hk, hd]
  rw [← hD]
  ring

/-- The exact subtraction in the manuscript's reference comparison. -/
theorem reference_difference_algebra {n : ℕ} (hn : 1 ≤ n) (p t : ℝ)
    (ht : t ≠ 0) (hk : (n:ℝ)^2-2*n-2 ≠ 0)
    (hd : ((n:ℝ)^2-2*n-2)*t-2*n ≠ 0) :
    correctionReal (n+1) p t - referenceCorrectionReal (n+1) =
      4 * ((n.factorial : ℝ) - n*((n:ℝ)-1) - p*((n:ℝ)^2-2*n-2)) /
        (((n:ℝ)^2-2*n-2)*(((n:ℝ)^2-2*n-2)*t-2*n)) := by
  have hnf : (n.factorial : ℝ) = (n:ℝ) * ((n-1).factorial : ℝ) := by
    have he := Nat.factorial_succ (n-1)
    rw [show n-1+1=n by omega] at he
    exact_mod_cast he
  unfold correctionReal referenceCorrectionReal
  rw [show n+1-2=n-1 by omega]
  push_cast
  rw [hnf]
  have hpoly : ((n:ℝ)+1)^2-4*((n:ℝ)+1)+1 = (n:ℝ)^2-2*n-2 := by ring
  rw [hpoly]
  convert subtraction_identity (n:ℝ) ((n-1).factorial:ℝ) p t
    ((n:ℝ)^2-2*n-2) ht hk hd using 1 <;> congr 1 <;> ring

/-- The polynomial terms in the reference numerator are negligible against n!. -/
theorem reference_numerator_limit {N : ℕ → ℕ} {p : ℕ → ℝ} {a : ℝ}
    (hN : Tendsto N atTop atTop)
    (hp : Tendsto (fun m => p m / (N m : ℝ)^2) atTop (𝓝 a)) :
    Tendsto (fun m => (((N m).factorial : ℝ) - N m*((N m : ℝ)-1) -
      p m*((N m : ℝ)^2-2*N m-2)) / ((N m).factorial : ℝ)) atTop (𝓝 1) := by
  have hx : Tendsto (fun m => (N m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have h2 := (tendsto_pow_div_factorial 2).comp hN
  have h1 := (tendsto_pow_div_factorial 1).comp hN
  have h4 := (tendsto_pow_div_factorial 4).comp hN
  have hsmall := (hp.mul (normalized_kappa_limit hx)).mul h4
  have hh := ((tendsto_const_nhds (x := (1:ℝ))).sub (h2.sub h1)).sub hsmall
  convert hh.congr' ?_ using 1 <;> try norm_num
  filter_upwards [hN.eventually (eventually_gt_atTop 0)] with m hm
  have hne : (N m : ℝ) ≠ 0 := by positivity
  have hfac : ((N m).factorial : ℝ) ≠ 0 := by positivity
  try dsimp only [Function.comp_apply]
  field_simp
  <;> ring

/-- A generic reference gain: parameter degree d gives the constant 4/c. -/
theorem reference_gap_limit {N : ℕ → ℕ} {p t : ℕ → ℝ} {a c : ℝ}
    (hN : Tendsto N atTop atTop) (d : ℕ) (hc : c ≠ 0)
    (hp : Tendsto (fun m => p m / (N m : ℝ)^2) atTop (𝓝 a))
    (ht : Tendsto (fun m => t m / (N m : ℝ)^d) atTop (𝓝 c)) :
    Tendsto (fun m => (4 * (((N m).factorial : ℝ) - N m*((N m : ℝ)-1) -
      p m*((N m : ℝ)^2-2*N m-2)) /
      (((N m : ℝ)^2-2*N m-2)*(((N m : ℝ)^2-2*N m-2)*t m-2*N m))) /
      ((N m-(d+4)).factorial : ℝ)) atTop (𝓝 (4/c)) := by
  apply tendsto_normalize_factorial_sub_along hN (d+4)
  have hx : Tendsto (fun m => (N m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hden := (normalized_kappa_limit hx).mul (normalized_denominator_limit d hx ht)
  have hh := ((reference_numerator_limit hN hp).const_mul 4).div hden (by simpa using hc)
  convert hh.congr' ?_ using 1 <;> try simp
  filter_upwards [hN.eventually (eventually_gt_atTop 0)] with m hm
  have hne : (N m : ℝ) ≠ 0 := by positivity
  have hfac : ((N m).factorial : ℝ) ≠ 0 := by positivity
  dsimp only [Pi.div_apply]
  simp only [pow_add]
  field_simp
  <;> ring

end SuperpermutationBounds.ChainReturns.Asymptotic
