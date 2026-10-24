module

public import asymptotics.Definitions

@[expose] public section

noncomputable section
open Filter Topology
namespace SuperpermutationBounds.ChainReturns.Asymptotic

/-- The correction after multiplying numerator and denominator by `t`.
Keeping the factorial term abstract makes both subtraction identities transparent. -/
def correctionFraction (A k n p t : ℝ) : ℝ := (A*t-4*p)/(k*t-2*n)

theorem correctionFraction_sub (A k n p t h d : ℝ)
    (hD : k*t-2*n ≠ 0) (hD' : k*(t-h)-2*n ≠ 0) :
    correctionFraction A k n (p+d) (t-h) - correctionFraction A k n p t =
      (4*h*(n*A/2-k*p)-4*d*(k*t-2*n)) /
        ((k*(t-h)-2*n)*(k*t-2*n)) := by
  unfold correctionFraction
  rw [div_sub_div _ _ hD' hD]
  congr 1
  ring

theorem correctionFraction_sub_on_line (A k n p t a h₀ h₁ : ℝ)
    (hD₀ : k*(t-h₀)-2*n ≠ 0) (hD₁ : k*(t-h₁)-2*n ≠ 0) :
    correctionFraction A k n (p+a*h₁) (t-h₁) -
      correctionFraction A k n (p+a*h₀) (t-h₀) =
      4*(h₁-h₀)*(n*A/2-k*p-a*(k*t-2*n)) /
        ((k*(t-h₁)-2*n)*(k*(t-h₀)-2*n)) := by
  unfold correctionFraction
  rw [div_sub_div _ _ hD₁ hD₀]
  congr 1
  ring

theorem correctionFraction_mono_on_line (A k n p t a h₀ h₁ : ℝ)
    (hh : h₀ ≤ h₁) (hD₀ : 0 < k*(t-h₀)-2*n)
    (hD₁ : 0 < k*(t-h₁)-2*n)
    (hnum : 0 ≤ n*A/2-k*p-a*(k*t-2*n)) :
    correctionFraction A k n (p+a*h₀) (t-h₀) ≤
      correctionFraction A k n (p+a*h₁) (t-h₁) := by
  apply sub_nonneg.mp
  rw [correctionFraction_sub_on_line A k n p t a h₀ h₁ hD₀.ne' hD₁.ne']
  positivity

/-- In geometric indexing `n=K-1`, the denominator is `n²-2n-2`. -/
def kappa (n : ℝ) : ℝ := n^2-2*n-2

theorem correctionReal_succ_fraction (n : ℕ) (hn : 1 ≤ n) (p t : ℝ)
    (ht : t ≠ 0) :
    correctionReal (n+1) p t = correctionFraction
      (2*((n-1).factorial:ℝ)-2*((n:ℝ)-1)) (kappa n) n p t := by
  have he : n+1-2 = n-1 := by omega
  simp only [correctionReal, he, Nat.cast_add, Nat.cast_one, correctionFraction, kappa]
  field_simp
  <;> ring

theorem factorial_gain_numerator (n : ℕ) (hn : 1 ≤ n) :
    (n:ℝ)*(2*((n-1).factorial:ℝ)-2*((n:ℝ)-1))/2 =
      (n.factorial:ℝ)-(n:ℝ)*(n-1) := by
  have hf : n.factorial = n * (n-1).factorial := by
    conv_lhs => rw [show n = (n-1)+1 by omega]
    rw [Nat.factorial_succ]
    congr 1 <;> omega
  rw [hf, Nat.cast_mul]
  ring


theorem normalize_zero_quotient (x F A B C : ℝ)
    (hx : x ≠ 0) (hF : F ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) :
    ((4*(2/x^2)*(F-C)-4*(1/2+1/x^2)*A)/(B*A))*x^8/F =
      (8-(8*C+2*A*x^2+4*A)/F)/((A/x^3)*(B/x^3)) := by
  field_simp
  <;> ring

theorem normalize_one_quotient (x F A B C : ℝ)
    (hx : x ≠ 0) (hF : F ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) :
    (4*(4/x^2)*(F-C)/(B*A))*x^10/F =
      (16-16*C/F)/((A/x^4)*(B/x^4)) := by
  field_simp
  <;> ring

end SuperpermutationBounds.ChainReturns.Asymptotic
