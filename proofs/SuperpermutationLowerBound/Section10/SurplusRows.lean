module

public import SuperpermutationLowerBound.Section09.ResidualInequality

@[expose] public section

namespace SuperpermutationLowerBound

/-! Frozen Section 10 through Lemma `lem:surplusrows`.  Surplus and the
dual profile `G` are genuinely integer-valued: every subtraction below is
subtraction in `Int`, never truncated natural subtraction. -/

variable {k n z : ℕ}

/-! ## The two coefficients -/

/-- The coefficient `λ=n-2`. -/
def surplusLambda (n : ℕ) : ℕ := n - 2

/-- The coefficient `κ=n(n-2)-2`.  Its defining natural subtraction is
proved exact below on the frozen range `n≥6`. -/
def surplusKappa (n : ℕ) : ℕ := n * (n - 2) - 2

@[simp] theorem surplusLambda_eq (n : ℕ) :
    surplusLambda n = n - 2 := rfl

/-- Exact range and subtraction facts for `λ` on the frozen domain. -/
theorem surplusLambda_range (hn : 6 ≤ n) :
    4 ≤ surplusLambda n ∧ surplusLambda n + 2 = n := by
  simp only [surplusLambda]
  omega

/-- The subtraction of `2` in `κ` is exact. -/
theorem surplusKappa_subtraction_exact (hn : 6 ≤ n) :
    2 ≤ n * surplusLambda n ∧
      surplusKappa n + 2 = n * surplusLambda n := by
  simp only [surplusLambda, surplusKappa]
  constructor
  · have hfour : 4 ≤ n - 2 := by omega
    have hmul : 6 * 4 ≤ n * (n - 2) := Nat.mul_le_mul hn hfour
    omega
  · have hfour : 4 ≤ n - 2 := by omega
    have hmul : 6 * 4 ≤ n * (n - 2) := Nat.mul_le_mul hn hfour
    have htwo : 2 ≤ n * (n - 2) := by omega
    omega

/-- The second displayed natural form `κ=n²-2n-2`, with both natural
subtractions justified by `n≥6`. -/
theorem surplusKappa_eq_square_sub (_hn : 6 ≤ n) :
    surplusKappa n = n ^ 2 - 2 * n - 2 := by
  unfold surplusKappa
  rw [Nat.mul_sub_left_distrib]
  simp only [pow_two]
  have htwoMul : n * 2 = 2 * n := Nat.mul_comm n 2
  rw [htwoMul]

/-- Both displayed forms of `κ`, now read in signed arithmetic. -/
theorem surplusKappa_int_forms (hn : 6 ≤ n) :
    (surplusKappa n : ℤ) =
        (n : ℤ) * ((n : ℤ) - 2) - 2 ∧
      (surplusKappa n : ℤ) =
        (n : ℤ) ^ 2 - 2 * (n : ℤ) - 2 := by
  have hlambdaNat := (surplusLambda_range hn).2
  have hkappaNat := (surplusKappa_subtraction_exact hn).2
  have hlambdaInt : (surplusLambda n : ℤ) + 2 = (n : ℤ) := by
    exact_mod_cast hlambdaNat
  have hkappaInt : (surplusKappa n : ℤ) + 2 =
      (n : ℤ) * (surplusLambda n : ℤ) := by
    exact_mod_cast hkappaNat
  constructor <;> nlinarith [sq_nonneg ((n : ℤ) - 1)]

/-- `κ` is positive on the frozen range. -/
theorem surplusKappa_pos (hn : 6 ≤ n) : 0 < surplusKappa n := by
  have hforms := (surplusKappa_int_forms hn).1
  have hnInt : (6 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have hpositive : (0 : ℤ) < (surplusKappa n : ℤ) := by
    nlinarith
  exact_mod_cast hpositive

/-- The strict comparison used in the fourth surplus row. -/
theorem surplusKappa_gt_two_mul_sub_two (hn : 6 ≤ n) :
    2 * (n : ℤ) - 2 < (surplusKappa n : ℤ) := by
  have hforms := (surplusKappa_int_forms hn).2
  have hnInt : (6 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  nlinarith [mul_nonneg (show (0 : ℤ) ≤ n by omega)
    (show (0 : ℤ) ≤ n - 4 by omega)]

/-! ## Signed `G` and its sharp maximum -/

/-- The elementary upper bound needed to cast the natural subtraction in
`h_n(z)=nz-φ_n(z)` into `Int` exactly. -/
theorem phiN_le_n_mul (hn : 6 ≤ n) (hz : 1 ≤ z) :
    phiN n z hn hz ≤ n * z := by
  obtain ⟨d, hdLength, hdLegal, hdTotal⟩ := phiN_attained hn hz
  have hentries : ∀ x ∈ d, x ≤ n := by
    intro x hx
    exact (hdLegal.entries_lt x hx).le.trans (by omega)
  have listSumBound : ∀ (xs : List ℕ),
      (∀ x ∈ xs, x ≤ n) → xs.sum ≤ n * xs.length := by
    intro xs hxs
    induction xs with
    | nil => simp
    | cons x tail ih =>
        have hx : x ≤ n := hxs x (by simp)
        have htail : ∀ y ∈ tail, y ≤ n := by
          intro y hy
          exact hxs y (by simp [hy])
        have hih := ih htail
        simp only [List.sum_cons, List.length_cons, Nat.mul_succ]
        omega
  have hsum := listSumBound d hentries
  rw [hdLength] at hsum
  change d.sum = phiN n z hn hz at hdTotal
  omega

/-- Exact signed reading of the natural definition of `h_n`. -/
theorem hN_int_eq (hn : 6 ≤ n) (hz : 1 ≤ z) :
    (hN n z hn hz : ℤ) =
      (n : ℤ) * (z : ℤ) - (phiN n z hn hz : ℤ) := by
  unfold hN
  rw [Int.ofNat_sub (phiN_le_n_mul hn hz)]
  norm_cast

/-- The dual profile in its first displayed form,
`G(z)=λh_n(z)-κz`. -/
noncomputable def surplusG (n z : ℕ) (hn : 6 ≤ n) (hz : 1 ≤ z) : ℤ :=
  (surplusLambda n : ℤ) * (hN n z hn hz : ℤ) -
    (surplusKappa n : ℤ) * (z : ℤ)

@[simp] theorem surplusG_first_form (hn : 6 ≤ n) (hz : 1 ≤ z) :
    surplusG n z hn hz =
      (surplusLambda n : ℤ) * (hN n z hn hz : ℤ) -
        (surplusKappa n : ℤ) * (z : ℤ) := rfl

/-- The exact second displayed form,
`G(z)=2z-(n-2)φ_n(z)`. -/
theorem surplusG_second_form (hn : 6 ≤ n) (hz : 1 ≤ z) :
    surplusG n z hn hz =
      2 * (z : ℤ) -
        (surplusLambda n : ℤ) * (phiN n z hn hz : ℤ) := by
  rw [surplusG_first_form, hN_int_eq]
  have hlambda := (surplusLambda_range hn).2
  have hlambdaInt : (surplusLambda n : ℤ) + 2 = (n : ℤ) := by
    exact_mod_cast hlambda
  have hkappa := (surplusKappa_int_forms hn).1
  have hlambdaEq : (surplusLambda n : ℤ) = (n : ℤ) - 2 := by omega
  rw [hlambdaEq, hkappa]
  ring

/-- The small-range branch of the exact `φ_n` formula, including its
right endpoint `z=n-1`. -/
theorem surplusG_small_branch (hn : 6 ≤ n) (hz : 1 ≤ z)
    (hsmall : z ≤ n - 1) :
    phiN n z hn hz = 0 ∧ surplusG n z hn hz = 2 * (z : ℤ) := by
  have hnotExceptional :
      ¬(n + (n - 2) ≤ z ∧ Nat.ModEq (n - 2) z n) := by
    intro hexceptional
    omega
  have hPhi : PhiN n z hz = 0 := by
    simp [PhiN, hsmall]
  have hphi : phiN n z hn hz = 0 := by
    rw [phiN_closed_form hn hz, if_neg hnotExceptional, hPhi]
  refine ⟨hphi, ?_⟩
  rw [surplusG_second_form, hphi]
  norm_num

/-- The isolated endpoint `z=n` is ordinary, not exceptional: exactly
`φ_n(n)=2` and `G(n)=4`. -/
theorem surplusG_at_n_endpoint (hn : 6 ≤ n) :
    phiN n n hn (by omega) = 2 ∧
      surplusG n n hn (by omega) = 4 := by
  have hnotSmall : ¬n ≤ n - 1 := by omega
  have hnotExceptional :
      ¬(n + (n - 2) ≤ n ∧ Nat.ModEq (n - 2) n n) := by
    intro hexceptional
    omega
  have hPhi : PhiN n n (by omega) = 2 := by
    simp [PhiN, hnotSmall, Nat.div_self (by omega : 0 < n - 2)]
  have hphi : phiN n n hn (by omega) = 2 := by
    rw [phiN_closed_form hn (by omega), if_neg hnotExceptional, hPhi]
  refine ⟨hphi, ?_⟩
  rw [surplusG_second_form, hphi]
  have hlambdaNat := (surplusLambda_range hn).2
  have hlambdaInt : (surplusLambda n : ℤ) + 2 = (n : ℤ) := by
    exact_mod_cast hlambdaNat
  norm_num only [Nat.cast_ofNat]
  nlinarith

/-- The nonexceptional large branch of the exact `φ_n` formula.  This
branch deliberately includes the isolated endpoint `z=n`. -/
theorem surplusG_regular_large_branch (hn : 6 ≤ n) (hz : 1 ≤ z)
    (hlarge : n ≤ z)
    (hregular : ¬(n + (n - 2) ≤ z ∧ Nat.ModEq (n - 2) z n)) :
    phiN n z hn hz = 2 * ((z - 2) / (n - 2)) ∧
      surplusG n z hn hz =
        2 * (z : ℤ) - (surplusLambda n : ℤ) *
          (2 * (((z - 2) / (n - 2) : ℕ) : ℤ)) := by
  have hnotSmall : ¬z ≤ n - 1 := by omega
  have hnum : z - n + (n - 2) = z - 2 := by omega
  have hPhi : PhiN n z hz = 2 * ((z - 2) / (n - 2)) := by
    simp [PhiN, hnotSmall, hnum]
  have hphi : phiN n z hn hz = 2 * ((z - 2) / (n - 2)) := by
    rw [phiN_closed_form hn hz, if_neg hregular, hPhi]
  refine ⟨hphi, ?_⟩
  rw [surplusG_second_form, hphi]
  norm_num

/-- The exceptional congruence branch of the exact `φ_n` formula.
Both its threshold and its literal congruence modulo `n-2` are retained;
on this branch `G(z)=n+2`, strictly below the sharp maximum. -/
theorem surplusG_exceptional_branch (hn : 6 ≤ n) (hz : 1 ≤ z)
    (hexceptional :
      n + (n - 2) ≤ z ∧ Nat.ModEq (n - 2) z n) :
    phiN n z hn hz = 2 * ((z - 2) / (n - 2)) - 1 ∧
      surplusG n z hn hz = (n : ℤ) + 2 ∧
      surplusG n z hn hz < 2 * (n : ℤ) - 2 := by
  let mu := n - 2
  let q := (z - 2) / mu
  have hmu : 4 ≤ mu := by dsimp [mu]; omega
  have hmuPos : 0 < mu := by omega
  have hnotSmall : ¬z ≤ n - 1 := by omega
  have hnum : z - n + (n - 2) = z - 2 := by omega
  have hPhi : PhiN n z hz = 2 * q := by
    simp [PhiN, hnotSmall, hnum, q, mu]
  have hqTwo : 2 ≤ q := by
    apply (Nat.le_div_iff_mul_le hmuPos).2
    dsimp [q, mu]
    omega
  have hremZero : (z - 2) % mu = 0 := by
    have hadd : Nat.ModEq mu (2 + (z - 2)) (2 + (n - 2)) := by
      simpa [mu, show 2 + (z - 2) = z by omega,
        show 2 + (n - 2) = n by omega] using hexceptional.2
    have hsub := Nat.ModEq.add_left_cancel
      (show Nat.ModEq mu 2 2 from Nat.ModEq.rfl) hadd
    unfold Nat.ModEq at hsub
    change (z - 2) % mu = (n - 2) % mu at hsub
    simpa [mu] using hsub
  have hdivision := Nat.mod_add_div (z - 2) mu
  have hzDecompNat : z = 2 + mu * q := by
    change (z - 2) % mu + mu * q = z - 2 at hdivision
    rw [hremZero] at hdivision
    omega
  have hphi : phiN n z hn hz = 2 * q - 1 := by
    rw [phiN_closed_form hn hz, if_pos hexceptional, hPhi]
  have hGvalue : surplusG n z hn hz = (n : ℤ) + 2 := by
    rw [surplusG_second_form, hphi]
    have hlambdaNat := (surplusLambda_range hn).2
    have hlambdaInt : (surplusLambda n : ℤ) = (n : ℤ) - 2 := by
      have hcast : (surplusLambda n : ℤ) + 2 = (n : ℤ) := by
        exact_mod_cast hlambdaNat
      omega
    have hzDecompInt : (z : ℤ) =
        2 + ((n : ℤ) - 2) * (q : ℤ) := by
      have hcast : (z : ℤ) = 2 + (mu : ℤ) * (q : ℤ) := by
        exact_mod_cast hzDecompNat
      have hmuInt : (mu : ℤ) = (n : ℤ) - 2 := by
        dsimp [mu]
        rw [Int.ofNat_sub (by omega : 2 ≤ n)]
        norm_num
      rwa [hmuInt] at hcast
    rw [Int.ofNat_sub (by omega : 1 ≤ 2 * q)]
    push_cast
    rw [hlambdaInt, hzDecompInt]
    ring
  refine ⟨by simpa [q, mu] using hphi, hGvalue, ?_⟩
  rw [hGvalue]
  have hnInt : (6 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  nlinarith

private theorem phiN_ne_one (hn : 6 ≤ n) (hz : 1 ≤ z) :
    phiN n z hn hz ≠ 1 := by
  intro hone
  have hminimum := phiN_is_minimum_maxLegalLength hn hz
  have hzeroOne := maxLegalLength_zero_eq_one n
  have hadmissibleZero : z ≤ maxLegalLength n 0 := by
    rw [hzeroOne]
    simpa [hone] using hminimum.1
  have := hminimum.2 0 hadmissibleZero
  omega

private theorem maxLegalLength_even_J1 (_hn : 6 ≤ n) {t : ℕ}
    (ht : 1 ≤ t) :
    maxLegalLength n (2 * t) = (n - 1) + (n - 2) * t := by
  have hlarge : ¬2 * t ≤ 1 := by omega
  have hdiv : (2 * t) / 2 = t := by omega
  have hmod : (2 * t) % 2 = 0 := by omega
  simp [maxLegalLength, hlarge, hdiv, hmod]

private theorem maxLegalLength_odd_J1 (_hn : 6 ≤ n) {t : ℕ}
    (ht : 1 ≤ t) :
    maxLegalLength n (2 * t + 1) = n + (n - 2) * t := by
  have hlarge : ¬2 * t + 1 ≤ 1 := by omega
  have hdiv : (2 * t + 1) / 2 = t := by omega
  have hmod : (2 * t + 1) % 2 = 1 := by omega
  simp [maxLegalLength, hlarge, hdiv, hmod]
  omega

private theorem phiN_at_G_boundary (hn : 6 ≤ n) (t : ℕ) :
    phiN n ((n - 1) + t * (n - 2)) hn (by omega) = 2 * t := by
  let boundary := (n - 1) + t * (n - 2)
  have hminimum := phiN_is_minimum_maxLegalLength hn
    (show 1 ≤ boundary by dsimp [boundary]; omega)
  by_cases htZero : t = 0
  · subst t
    have hadmissible : boundary ≤ maxLegalLength n 0 := by
      simp [boundary, maxLegalLength]
    have hle := hminimum.2 0 hadmissible
    have hzero : phiN n boundary hn (by omega) = 0 := by omega
    simpa [boundary] using hzero
  · have ht : 1 ≤ t := by omega
    have hboundary : boundary = maxLegalLength n (2 * t) := by
      rw [maxLegalLength_even_J1 hn ht]
      simp [boundary, Nat.mul_comm]
    have hle : phiN n boundary hn (by omega) ≤ 2 * t :=
      hminimum.2 (2 * t) (by rw [hboundary])
    have hprevPos : 1 ≤ 2 * t - 1 := by omega
    have hprevStrict : maxLegalLength n (2 * t - 1) < boundary := by
      have hstep := maxLegalLength_lt_succ hn hprevPos
      have hsucc : 2 * t - 1 + 1 = 2 * t := by omega
      rw [hsucc, ← hboundary] at hstep
      exact hstep
    have hlower : 2 * t ≤ phiN n boundary hn (by omega) := by
      by_contra hnot
      have hDle : phiN n boundary hn (by omega) ≤ 2 * t - 1 := by omega
      have hmono := maxLegalLength_mono hn hDle
      have hadmissible := hminimum.1
      have hchain : boundary ≤ maxLegalLength n (2 * t - 1) :=
        hadmissible.trans hmono
      exact (not_lt_of_ge hchain hprevStrict).elim
    have heq := Nat.le_antisymm hle hlower
    simpa [boundary] using heq

private theorem surplusG_at_boundary (hn : 6 ≤ n) (t : ℕ) :
    surplusG n ((n - 1) + t * (n - 2)) hn (by omega) =
      2 * (n : ℤ) - 2 := by
  rw [surplusG_second_form,
    phiN_at_G_boundary hn t]
  have hlambdaNat := (surplusLambda_range hn).2
  have hlambdaInt : (surplusLambda n : ℤ) = (n : ℤ) - 2 := by
    have : (surplusLambda n : ℤ) + 2 = (n : ℤ) := by
      exact_mod_cast hlambdaNat
    omega
  rw [hlambdaInt]
  push_cast
  rw [Int.ofNat_sub (by omega : 1 ≤ n),
    Int.ofNat_sub (by omega : 2 ≤ n)]
  norm_num
  ring

private theorem surplusG_upper (hn : 6 ≤ n) (hz : 1 ≤ z) :
    surplusG n z hn hz ≤ 2 * (n : ℤ) - 2 := by
  let D := phiN n z hn hz
  have hminimum := phiN_is_minimum_maxLegalLength hn hz
  have hDneOne : D ≠ 1 := by
    simpa [D] using phiN_ne_one hn hz
  have hG : surplusG n z hn hz =
      2 * (z : ℤ) - (surplusLambda n : ℤ) * (D : ℤ) := by
    simpa [D] using surplusG_second_form hn hz
  have hlambdaNat := (surplusLambda_range hn).2
  have hlambdaInt : (surplusLambda n : ℤ) = (n : ℤ) - 2 := by
    have : (surplusLambda n : ℤ) + 2 = (n : ℤ) := by
      exact_mod_cast hlambdaNat
    omega
  by_cases hDzero : D = 0
  · have hzUpper : z ≤ n - 1 := by
      have hadmissible := hminimum.1
      simpa [D, hDzero, maxLegalLength] using hadmissible
    have hzUpperInt : (z : ℤ) ≤ (n : ℤ) - 1 := by
      have hcast : (z : ℤ) ≤ ((n - 1 : ℕ) : ℤ) := by exact_mod_cast hzUpper
      rwa [Int.ofNat_sub (by omega : 1 ≤ n)] at hcast
    rw [hG, hDzero]
    norm_num
    nlinarith
  · have hDtwo : 2 ≤ D := by omega
    rcases Nat.mod_two_eq_zero_or_one D with hEven | hOdd
    · let t := D / 2
      have hDshape : D = 2 * t := by
        dsimp [t]
        have hdivision := Nat.mod_add_div D 2
        omega
      have ht : 1 ≤ t := by omega
      have hzUpper : z ≤ (n - 1) + (n - 2) * t := by
        have hadmissible := hminimum.1
        rw [show phiN n z hn hz = D by rfl, hDshape,
          maxLegalLength_even_J1 hn ht] at hadmissible
        exact hadmissible
      have hzUpperInt : (z : ℤ) ≤
          (n : ℤ) - 1 + ((n : ℤ) - 2) * (t : ℤ) := by
        have hcast : (z : ℤ) ≤
            (((n - 1) + (n - 2) * t : ℕ) : ℤ) := by
          exact_mod_cast hzUpper
        push_cast at hcast
        rwa [Int.ofNat_sub (by omega : 1 ≤ n),
          Int.ofNat_sub (by omega : 2 ≤ n)] at hcast
      rw [hG, hDshape, hlambdaInt]
      push_cast
      nlinarith
    · let t := D / 2
      have hDshape : D = 2 * t + 1 := by
        dsimp [t]
        have hdivision := Nat.mod_add_div D 2
        omega
      have ht : 1 ≤ t := by omega
      have hzUpper : z ≤ n + (n - 2) * t := by
        have hadmissible := hminimum.1
        rw [show phiN n z hn hz = D by rfl, hDshape,
          maxLegalLength_odd_J1 hn ht] at hadmissible
        exact hadmissible
      have hzUpperInt : (z : ℤ) ≤
          (n : ℤ) + ((n : ℤ) - 2) * (t : ℤ) := by
        have hcast : (z : ℤ) ≤
            ((n + (n - 2) * t : ℕ) : ℤ) := by exact_mod_cast hzUpper
        push_cast at hcast
        rwa [Int.ofNat_sub (by omega : 2 ≤ n)] at hcast
      rw [hG, hDshape, hlambdaInt]
      push_cast
      nlinarith

private theorem surplusG_eq_boundary_of_eq_max (hn : 6 ≤ n) (hz : 1 ≤ z)
    (heq : surplusG n z hn hz = 2 * (n : ℤ) - 2) :
    ∃ t : ℕ, z = (n - 1) + t * (n - 2) := by
  let D := phiN n z hn hz
  have hDneOne : D ≠ 1 := by
    simpa [D] using phiN_ne_one hn hz
  have hG : surplusG n z hn hz =
      2 * (z : ℤ) - (surplusLambda n : ℤ) * (D : ℤ) := by
    simpa [D] using surplusG_second_form hn hz
  have hlambdaNat := (surplusLambda_range hn).2
  have hlambdaInt : (surplusLambda n : ℤ) = (n : ℤ) - 2 := by
    have : (surplusLambda n : ℤ) + 2 = (n : ℤ) := by
      exact_mod_cast hlambdaNat
    omega
  by_cases hDzero : D = 0
  · have hzEqInt : (z : ℤ) = (n : ℤ) - 1 := by
      rw [hG, hDzero] at heq
      norm_num at heq
      nlinarith
    have hzEq : z = n - 1 := by
      have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
        rw [Int.ofNat_sub (by omega : 1 ≤ n)]
        norm_num
      exact_mod_cast hzEqInt.trans hcast.symm
    exact ⟨0, by simpa using hzEq⟩
  · have hDtwo : 2 ≤ D := by omega
    rcases Nat.mod_two_eq_zero_or_one D with hEven | hOdd
    · let t := D / 2
      have hDshape : D = 2 * t := by
        dsimp [t]
        have hdivision := Nat.mod_add_div D 2
        omega
      have hzEqInt : (z : ℤ) =
          (n : ℤ) - 1 + (t : ℤ) * ((n : ℤ) - 2) := by
        rw [hG, hDshape, hlambdaInt] at heq
        push_cast at heq
        nlinarith
      have hboundaryCast :
          (((n - 1) + t * (n - 2) : ℕ) : ℤ) =
            (n : ℤ) - 1 + (t : ℤ) * ((n : ℤ) - 2) := by
        push_cast
        rw [Int.ofNat_sub (by omega : 1 ≤ n),
          Int.ofNat_sub (by omega : 2 ≤ n)]
        ring
      have hzEq : z = (n - 1) + t * (n - 2) := by
        exact_mod_cast hzEqInt.trans hboundaryCast.symm
      exact ⟨t, hzEq⟩
    · let t := D / 2
      have hDshape : D = 2 * t + 1 := by
        dsimp [t]
        have hdivision := Nat.mod_add_div D 2
        omega
      have ht : 1 ≤ t := by omega
      have hminimum := phiN_is_minimum_maxLegalLength hn hz
      have hzUpper : z ≤ n + (n - 2) * t := by
        have hadmissible := hminimum.1
        rw [show phiN n z hn hz = D by rfl, hDshape,
          maxLegalLength_odd_J1 hn ht] at hadmissible
        exact hadmissible
      have hzUpperInt : (z : ℤ) ≤
          (n : ℤ) + ((n : ℤ) - 2) * (t : ℤ) := by
        have hcast : (z : ℤ) ≤ ((n + (n - 2) * t : ℕ) : ℤ) := by
          exact_mod_cast hzUpper
        push_cast at hcast
        rwa [Int.ofNat_sub (by omega : 2 ≤ n)] at hcast
      rw [hG, hDshape, hlambdaInt] at heq
      push_cast at heq
      have hnInt : (6 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
      nlinarith

/-- **Sharp maximum of `G` (Lemma `lem:Gmax`).**  The equality witness
`t : ℕ` is the frozen nonnegative integer parameter. -/
theorem surplusG_max (hn : 6 ≤ n) (hz : 1 ≤ z) :
    surplusG n z hn hz ≤ 2 * (n : ℤ) - 2 ∧
      (surplusG n z hn hz = 2 * (n : ℤ) - 2 ↔
        ∃ t : ℕ, z = (n - 1) + t * (n - 2)) := by
  refine ⟨surplusG_upper hn hz, ?_⟩
  constructor
  · exact surplusG_eq_boundary_of_eq_max hn hz
  · rintro ⟨t, rfl⟩
    exact surplusG_at_boundary hn t

/-! ## Actual component surplus and the global signed identity -/

/-- The actual component surplus
`s_p=λb_p-κy_p`, formed in `Int`. -/
noncomputable def pathForestComponentSurplus (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) : ℤ :=
  (surplusLambda (k - 1) : ℤ) *
      (pathForestComponentBlockCount (by omega) P C : ℤ) -
    (surplusKappa (k - 1) : ℤ) *
      (pathForestComponentBudget (by omega) P C : ℤ)

@[simp] theorem pathForestComponentSurplus_eq (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    pathForestComponentSurplus hk P C =
      (surplusLambda (k - 1) : ℤ) *
          (pathForestComponentBlockCount (by omega) P C : ℤ) -
        (surplusKappa (k - 1) : ℤ) *
          (pathForestComponentBudget (by omega) P C : ℤ) := rfl

/-- The sum over every genuine weak component of `F(P)`. -/
noncomputable def pathForestTotalSurplus (hk : 7 ≤ k)
    (P : HamiltonianPath k) : ℤ :=
  ∑ C : WeakComponent (pathForest (by omega) P),
    pathForestComponentSurplus hk P C

/-- **Exact signed surplus-sum identity (`eq:surplussum`).**  The two sums
are the actual component block counts and actual component budgets. -/
theorem pathForest_surplusSum (hk : 7 ≤ k) (P : HamiltonianPath k) :
    pathForestTotalSurplus hk P =
      (surplusLambda (k - 1) : ℤ) * ((k - 1).factorial : ℤ) -
        (surplusKappa (k - 1) : ℤ) *
          (pathForestTotalBudget (by omega) P : ℤ) := by
  classical
  have hblocksNat := pathForestComponentBlockCount_sum hk P
  have hblocksInt :
      (∑ C : WeakComponent (pathForest (by omega) P),
        (pathForestComponentBlockCount (by omega) P C : ℤ)) =
          ((k - 1).factorial : ℤ) := by
    exact_mod_cast hblocksNat
  have hbudgetNat :
      (∑ C : WeakComponent (pathForest (by omega) P),
        pathForestComponentBudget (by omega) P C) =
          pathForestTotalBudget (by omega) P := by
    simp [pathForestTotalBudget, weakComponents]
  have hbudgetInt :
      (∑ C : WeakComponent (pathForest (by omega) P),
        (pathForestComponentBudget (by omega) P C : ℤ)) =
          (pathForestTotalBudget (by omega) P : ℤ) := by
    exact_mod_cast hbudgetNat
  unfold pathForestTotalSurplus
  simp_rw [pathForestComponentSurplus_eq]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    hblocksInt, hbudgetInt]

/-! ## Actual `z=1` data and signed capacity transport -/

/-- The `z=1` component conclusion needed in the root and noncheap rows,
without any cheap-entry hypothesis. -/
theorem pathForestComponentZOneData (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (hz : pathForestComponentZ (by omega) P C = 1) :
    pathForestComponentFirstDeficit hk P C =
        pathForestComponentLastDeficit hk P C ∧
      pathForestComponentBlockCount (by omega) P C =
        (k - 1) - pathForestComponentFirstDeficit hk P C ∧
      pathForestComponentFirstDeficit hk P C ≤ k - 2 := by
  let p := pathForestComponentPath (by omega) P C
  let hp := pathForestComponentPath_blockAligned (by omega) P C
  have hzGeneric : blockAlignedZ p hp = 1 := by
    change pathForestComponentZ (by omega) P C = 1
    exact hz
  have hone := blockAlignedCapacity_eq_of_z_one hk p hp hzGeneric
  have hfirstBridge : pathForestComponentFirstDeficit hk P C =
      blockAlignedFirstDeficit hk p hp := by
    simp [pathForestComponentFirstDeficit, blockAlignedFirstDeficit, p,
      pathForestComponentDeficitString_eq_blockAlignedDeficitString hk P C]
  have hlastBridge : pathForestComponentLastDeficit hk P C =
      blockAlignedLastDeficit hk p hp := by
    simp [pathForestComponentLastDeficit, blockAlignedLastDeficit, p,
      pathForestComponentDeficitString_eq_blockAlignedDeficitString hk P C]
  have hfirstLast : pathForestComponentFirstDeficit hk P C =
      pathForestComponentLastDeficit hk P C := by
    rw [hfirstBridge, hlastBridge]
    exact hone.2.1
  have hblocks : pathForestComponentBlockCount (by omega) P C =
      (k - 1) - pathForestComponentFirstDeficit hk P C := by
    change pathBlockCount p = _
    rw [hfirstLast, hlastBridge]
    exact hone.2.2
  have hblocksPos := pathForestComponentBlockCount_pos (by omega) P C
  exact ⟨hfirstLast, hblocks, by omega⟩

private theorem endpointChargeB_le_self_J1 (d : ℕ) :
    endpointChargeB d ≤ d := by
  by_cases hd0 : d = 0
  · subst d
    simp
  by_cases hd1 : d = 1
  · subst d
    simp
  have hd2 : 2 ≤ d := by omega
  rw [endpointChargeB_eq_sub_one hd2]
  omega

private theorem endpointChargeA_le_self_J1 (d : ℕ) :
    endpointChargeA d ≤ d := by
  simp [endpointChargeA]

private theorem cheapZOne_precise_arithmetic (hn : 6 ≤ n)
    (d : ℕ) (hd : 1 ≤ d) :
    2 - (surplusLambda n : ℤ) * (d : ℤ) ≤
      (n : ℤ) - (surplusLambda n : ℤ) *
          ((endpointChargeA d : ℤ) + (endpointChargeB d : ℤ)) +
        (surplusLambda n : ℤ) * max (0 : ℤ) ((d : ℤ) - 4) := by
  have hlambdaNat := (surplusLambda_range hn).2
  have hlambdaInt : (surplusLambda n : ℤ) + 2 = (n : ℤ) := by
    exact_mod_cast hlambdaNat
  have hlambdaNonnegative : (0 : ℤ) ≤ surplusLambda n := by omega
  by_cases hdFive : 5 ≤ d
  · have hA : endpointChargeA d = d - 2 := by
      simp [endpointChargeA]
    have hB : endpointChargeB d = d - 1 :=
      endpointChargeB_eq_sub_one (by omega)
    have hchargesNat :
        endpointChargeA d + endpointChargeB d + 3 = 2 * d := by
      rw [hA, hB]
      omega
    have hchargesInt :
        (endpointChargeA d : ℤ) + (endpointChargeB d : ℤ) + 3 =
          2 * (d : ℤ) := by
      exact_mod_cast hchargesNat
    have hcharges :
        (endpointChargeA d : ℤ) + (endpointChargeB d : ℤ) =
          2 * (d : ℤ) - 3 := by
      omega
    have hmax : max (0 : ℤ) ((d : ℤ) - 4) = (d : ℤ) - 4 :=
      max_eq_right (by omega)
    rw [hcharges, hmax]
    nlinarith
  · have hdFour : d ≤ 4 := by omega
    have hchargesNat :
        endpointChargeA d + endpointChargeB d ≤ d + 1 := by
      interval_cases d <;> norm_num [endpointChargeA, endpointChargeB]
    have hchargesInt :
        (endpointChargeA d : ℤ) + (endpointChargeB d : ℤ) ≤
          (d : ℤ) + 1 := by
      exact_mod_cast hchargesNat
    have hscaled :=
      Int.mul_le_mul_of_nonneg_left hchargesInt hlambdaNonnegative
    have hmax : max (0 : ℤ) ((d : ℤ) - 4) = 0 :=
      max_eq_left (by omega)
    rw [hmax]
    simp only [mul_zero, add_zero]
    nlinarith

private theorem add_le_of_pos_le_sub_J1 {a cap charge : ℕ}
    (ha : 0 < a) (h : a ≤ cap - charge) :
    a + charge ≤ cap := by
  have hcharge : charge ≤ cap := by
    by_contra hnot
    have hzero : cap - charge = 0 := Nat.sub_eq_zero_of_le (by omega)
    rw [hzero] at h
    omega
  exact Nat.add_le_of_le_sub hcharge h

private theorem pathForestComponentBudget_eq_z_of_mem_U (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P)
    (hpU : p ∈ pathForestU hk P) :
    pathForestComponentBudget (by omega) P p.1 =
      pathForestComponentZ (by omega) P p.1 := by
  have hminto : pathForestNonrootMinto hk P p = 2 :=
    (mem_pathForestU hk P p).mp hpU
  rw [pathForestComponentBudget_nonroot_split (by omega) P p.1 p.2]
  change pathForestComponentZ (by omega) P p.1 +
      (pathForestNonrootMinto hk P p - 2) = _
  rw [hminto]
  simp

private theorem pathForestComponentBudget_ge_z_add_one_of_minto_ge_three
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (hnonroot : C ≠ pathForestRootComponent (by omega) P)
    (hminto : 3 ≤ pathForestMinto (by omega) P C
      (pathForestComponent_vertexSet_ne_univ_of_nonroot
        (by omega) P C hnonroot)) :
    pathForestComponentZ (by omega) P C + 1 ≤
      pathForestComponentBudget (by omega) P C := by
  rw [pathForestComponentBudget_nonroot_split (by omega) P C hnonroot]
  omega

private theorem pathForestComponentSurplus_le_G_sub
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (charge extra : ℕ)
    (hcapacity : pathForestComponentBlockCount (by omega) P C + charge ≤
      hN (k - 1) (pathForestComponentZ (by omega) P C)
        (by omega) (pathForestComponentZ_pos (by omega) P C))
    (hbudget : pathForestComponentZ (by omega) P C + extra ≤
      pathForestComponentBudget (by omega) P C) :
    pathForestComponentSurplus hk P C ≤
      surplusG (k - 1) (pathForestComponentZ (by omega) P C)
          (by omega) (pathForestComponentZ_pos (by omega) P C) -
        (surplusLambda (k - 1) : ℤ) * (charge : ℤ) -
        (surplusKappa (k - 1) : ℤ) * (extra : ℤ) := by
  let lambda : ℤ := surplusLambda (k - 1)
  let kappa : ℤ := surplusKappa (k - 1)
  let b : ℤ := pathForestComponentBlockCount (by omega) P C
  let y : ℤ := pathForestComponentBudget (by omega) P C
  let componentZ : ℤ := pathForestComponentZ (by omega) P C
  let capacity : ℤ := hN (k - 1)
    (pathForestComponentZ (by omega) P C)
    (by omega) (pathForestComponentZ_pos (by omega) P C)
  have hcapacityInt : b + (charge : ℤ) ≤ capacity := by
    have hcast :
        (pathForestComponentBlockCount (by omega) P C : ℤ) +
            (charge : ℤ) ≤
          (hN (k - 1) (pathForestComponentZ (by omega) P C)
            (by omega) (pathForestComponentZ_pos (by omega) P C) : ℤ) := by
      exact_mod_cast hcapacity
    simpa [b, capacity] using hcast
  have hbudgetInt : componentZ + (extra : ℤ) ≤ y := by
    have hcast :
        (pathForestComponentZ (by omega) P C : ℤ) + (extra : ℤ) ≤
          (pathForestComponentBudget (by omega) P C : ℤ) := by
      exact_mod_cast hbudget
    simpa [componentZ, y] using hcast
  have hlambdaNonnegative : 0 ≤ lambda := by
    dsimp [lambda]
    omega
  have hkappaNonnegative : 0 ≤ kappa := by
    dsimp [kappa]
    omega
  have hleft : lambda * b ≤ lambda * (capacity - (charge : ℤ)) :=
    Int.mul_le_mul_of_nonneg_left (by omega) hlambdaNonnegative
  have hright : kappa * (componentZ + (extra : ℤ)) ≤ kappa * y :=
    Int.mul_le_mul_of_nonneg_left hbudgetInt hkappaNonnegative
  change lambda * b - kappa * y ≤ _
  rw [surplusG_first_form]
  change lambda * b - kappa * y ≤
    lambda * capacity - kappa * componentZ - lambda * (charge : ℤ) -
      kappa * (extra : ℤ)
  nlinarith

private theorem pathForestComponentZOne_base (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (hz : pathForestComponentZ (by omega) P C = 1) :
    (surplusLambda (k - 1) : ℤ) *
        (pathForestComponentBlockCount (by omega) P C : ℤ) -
      (surplusKappa (k - 1) : ℤ) =
        2 - (surplusLambda (k - 1) : ℤ) *
          (pathForestComponentFirstDeficit hk P C : ℤ) := by
  have hdata := pathForestComponentZOneData hk P C hz
  have hbPos := pathForestComponentBlockCount_pos (by omega) P C
  have hbAdd : pathForestComponentBlockCount (by omega) P C +
      pathForestComponentFirstDeficit hk P C = k - 1 := by
    omega
  have hbInt :
      (pathForestComponentBlockCount (by omega) P C : ℤ) =
        ((k - 1 : ℕ) : ℤ) -
          (pathForestComponentFirstDeficit hk P C : ℤ) := by
    have hcast :
        (pathForestComponentBlockCount (by omega) P C : ℤ) +
            (pathForestComponentFirstDeficit hk P C : ℤ) =
          ((k - 1 : ℕ) : ℤ) := by
      exact_mod_cast hbAdd
    omega
  have hlambda := (surplusLambda_range (show 6 ≤ k - 1 by omega)).2
  have hlambdaInt : (surplusLambda (k - 1) : ℤ) =
      ((k - 1 : ℕ) : ℤ) - 2 := by
    have hcast : (surplusLambda (k - 1) : ℤ) + 2 =
        ((k - 1 : ℕ) : ℤ) := by exact_mod_cast hlambda
    omega
  have hkappa :=
    (surplusKappa_int_forms (show 6 ≤ k - 1 by omega)).1
  rw [hbInt, hlambdaInt, hkappa]
  ring

private theorem pathForestComponentSurplus_eq_z_one_budget_one
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (hz : pathForestComponentZ (by omega) P C = 1)
    (hbudget : pathForestComponentBudget (by omega) P C = 1) :
    pathForestComponentSurplus hk P C =
      2 - (surplusLambda (k - 1) : ℤ) *
        (pathForestComponentFirstDeficit hk P C : ℤ) := by
  rw [pathForestComponentSurplus_eq, hbudget]
  norm_num
  exact pathForestComponentZOne_base hk P C hz

/-! ## The four actual surplus rows -/

/-- First row of Lemma `lem:surplusrows`, for the actual root component.
The proof treats `z=1` separately from the `z≥2` capacity theorem. -/
theorem pathForestRootSurplus_le (hk : 7 ≤ k) (P : HamiltonianPath k) :
    pathForestComponentSurplus hk P
        (pathForestRootComponent (by omega) P) ≤
      2 * ((k - 1 : ℕ) : ℤ) - 2 -
        (surplusLambda (k - 1) : ℤ) *
          (endpointChargeB
            (pathForestComponentLastDeficit hk P
              (pathForestRootComponent (by omega) P)) : ℤ) := by
  let root := pathForestRootComponent (by omega) P
  let componentZ := pathForestComponentZ (by omega) P root
  let dplus := pathForestComponentLastDeficit hk P root
  have hzPos : 1 ≤ componentZ := pathForestComponentZ_pos (by omega) P root
  by_cases hzOne : componentZ = 1
  · have hdata := pathForestComponentZOneData hk P root hzOne
    have hbudget : pathForestComponentBudget (by omega) P root = 1 := by
      rw [show root = pathForestRootComponent (by omega) P by rfl,
        pathForestComponentBudget_root]
      exact hzOne
    have hs := pathForestComponentSurplus_eq_z_one_budget_one
      hk P root hzOne hbudget
    have hfirstLast := hdata.1
    have hBLe : endpointChargeB dplus ≤
        pathForestComponentFirstDeficit hk P root := by
      rw [hfirstLast]
      exact endpointChargeB_le_self_J1 dplus
    have hlambdaNonnegative : (0 : ℤ) ≤ surplusLambda (k - 1) := by omega
    have hBLeInt : (endpointChargeB dplus : ℤ) ≤
        (pathForestComponentFirstDeficit hk P root : ℤ) := by
      exact_mod_cast hBLe
    have hmul := Int.mul_le_mul_of_nonneg_left hBLeInt hlambdaNonnegative
    have hnInt : (2 : ℤ) ≤ ((k - 1 : ℕ) : ℤ) := by omega
    change pathForestComponentSurplus hk P root ≤ _
    rw [hs]
    dsimp [dplus]
    simp only [surplusLambda] at hmul ⊢
    nlinarith
  · have hzTwo : 2 ≤ componentZ := by omega
    have hcapacityRaw := pathForestComponentCapacity hk P root hzTwo
    have hcapacity : pathForestComponentBlockCount (by omega) P root +
        endpointChargeB dplus ≤
          hN (k - 1) componentZ (by omega) hzPos := by
      have hbPos := pathForestComponentBlockCount_pos (by omega) P root
      dsimp [root, componentZ, dplus] at hcapacityRaw ⊢
      exact add_le_of_pos_le_sub_J1 hbPos hcapacityRaw
    have hbudgetEq : pathForestComponentBudget (by omega) P root =
        componentZ := by
      rw [show root = pathForestRootComponent (by omega) P by rfl,
        pathForestComponentBudget_root]
    have hbudget : componentZ + 0 ≤
        pathForestComponentBudget (by omega) P root := by omega
    have hs := pathForestComponentSurplus_le_G_sub hk P root
      (endpointChargeB dplus) 0 hcapacity hbudget
    have hs' : pathForestComponentSurplus hk P root ≤
        surplusG (k - 1) componentZ (by omega) hzPos -
          (surplusLambda (k - 1) : ℤ) * (endpointChargeB dplus : ℤ) := by
      simpa only [Nat.cast_zero, mul_zero, sub_zero] using hs
    have hG := (surplusG_max (show 6 ≤ k - 1 by omega) hzPos).1
    change pathForestComponentSurplus hk P root ≤ _
    dsimp [dplus] at hs' ⊢
    exact hs'.trans (sub_le_sub_right hG _)

/-- Second row of Lemma `lem:surplusrows`, for an actual member of `U`
with `z≥2`. -/
theorem pathForestCheapSurplus_ge_two_le (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P)
    (hpU : p ∈ pathForestU hk P)
    (hz : 2 ≤ pathForestComponentZ (by omega) P p.1) :
    pathForestComponentSurplus hk P p.1 ≤
      ((k - 1 : ℕ) : ℤ) -
        (surplusLambda (k - 1) : ℤ) *
          ((endpointChargeA (pathForestComponentFirstDeficit hk P p.1) : ℤ) +
            (endpointChargeB (pathForestComponentLastDeficit hk P p.1) : ℤ)) := by
  have hmintoNonroot : pathForestNonrootMinto hk P p = 2 :=
    (mem_pathForestU hk P p).mp hpU
  have hminto : pathForestMinto (by omega) P p.1
      (pathForestComponent_vertexSet_ne_univ_of_nonroot
        (by omega) P p.1 p.2) = 2 := by
    simpa [pathForestNonrootMinto] using hmintoNonroot
  have hcapacityRaw := pathForestComponentCheapCapacity hk P p.1 p.2 hminto hz
  let dminus := pathForestComponentFirstDeficit hk P p.1
  let dplus := pathForestComponentLastDeficit hk P p.1
  let componentZ := pathForestComponentZ (by omega) P p.1
  have hzPos : 1 ≤ componentZ := pathForestComponentZ_pos (by omega) P p.1
  have hcapacity : pathForestComponentBlockCount (by omega) P p.1 +
      (1 + endpointChargeA dminus + endpointChargeB dplus) ≤
        hN (k - 1) componentZ (by omega) hzPos := by
    have hbPos := pathForestComponentBlockCount_pos (by omega) P p.1
    dsimp [dminus, dplus, componentZ] at hcapacityRaw ⊢
    have hB := add_le_of_pos_le_sub_J1 hbPos hcapacityRaw
    have hA := add_le_of_pos_le_sub_J1 (by omega) hB
    have hOne := add_le_of_pos_le_sub_J1 (by omega) hA
    omega
  have hbudgetEq := pathForestComponentBudget_eq_z_of_mem_U hk P p hpU
  have hbudget : componentZ + 0 ≤
      pathForestComponentBudget (by omega) P p.1 := by
    dsimp [componentZ]
    omega
  have hs := pathForestComponentSurplus_le_G_sub hk P p.1
    (1 + endpointChargeA dminus + endpointChargeB dplus) 0
    hcapacity hbudget
  have hs' : pathForestComponentSurplus hk P p.1 ≤
      surplusG (k - 1) componentZ (by omega) hzPos -
        (surplusLambda (k - 1) : ℤ) *
          (1 + endpointChargeA dminus + endpointChargeB dplus : ℕ) := by
    simpa only [Nat.cast_zero, mul_zero, sub_zero] using hs
  have hG := (surplusG_max (show 6 ≤ k - 1 by omega) hzPos).1
  have hlambda := (surplusLambda_range (show 6 ≤ k - 1 by omega)).2
  have hlambdaInt : (surplusLambda (k - 1) : ℤ) + 2 =
      ((k - 1 : ℕ) : ℤ) := by exact_mod_cast hlambda
  have hchargeCast :
      ((1 + endpointChargeA dminus + endpointChargeB dplus : ℕ) : ℤ) =
        1 + (endpointChargeA dminus : ℤ) +
          (endpointChargeB dplus : ℤ) := by
    norm_num
  calc
    pathForestComponentSurplus hk P p.1 ≤
        surplusG (k - 1) componentZ (by omega) hzPos -
          (surplusLambda (k - 1) : ℤ) *
            ((1 + endpointChargeA dminus + endpointChargeB dplus : ℕ) : ℤ) := hs'
    _ = surplusG (k - 1) componentZ (by omega) hzPos -
          (surplusLambda (k - 1) : ℤ) *
            (1 + (endpointChargeA dminus : ℤ) +
              (endpointChargeB dplus : ℤ)) := by rw [hchargeCast]
    _ ≤ 2 * ((k - 1 : ℕ) : ℤ) - 2 -
          (surplusLambda (k - 1) : ℤ) *
            (1 + (endpointChargeA dminus : ℤ) +
              (endpointChargeB dplus : ℤ)) :=
      sub_le_sub_right hG _
    _ = ((k - 1 : ℕ) : ℤ) -
          (surplusLambda (k - 1) : ℤ) *
            ((endpointChargeA dminus : ℤ) +
              (endpointChargeB dplus : ℤ)) := by
      nlinarith
    _ = ((k - 1 : ℕ) : ℤ) -
          (surplusLambda (k - 1) : ℤ) *
            ((endpointChargeA
                (pathForestComponentFirstDeficit hk P p.1) : ℤ) +
              (endpointChargeB
                (pathForestComponentLastDeficit hk P p.1) : ℤ)) := by
      rfl

/-- Third row of Lemma `lem:surplusrows`, together with both stated
minimum bounds and the precise `max(0,d-4)` correction.  The common
endpoint deficit and its positivity come from the actual cheap component,
and the surplus equality is stronger than the displayed row inequality. -/
theorem pathForestCheapSurplus_z_one (hk : 7 ≤ k)
    (P : HamiltonianPath k) (p : PathForestNonrootComponent hk P)
    (hpU : p ∈ pathForestU hk P)
    (hz : pathForestComponentZ (by omega) P p.1 = 1) :
    pathForestComponentFirstDeficit hk P p.1 =
        pathForestComponentLastDeficit hk P p.1 ∧
      1 ≤ pathForestComponentFirstDeficit hk P p.1 ∧
      pathForestComponentSurplus hk P p.1 =
        2 - (surplusLambda (k - 1) : ℤ) *
          (pathForestComponentFirstDeficit hk P p.1 : ℤ) ∧
      pathForestComponentSurplus hk P p.1 ≤
        2 - (surplusLambda (k - 1) : ℤ) *
          (pathForestComponentFirstDeficit hk P p.1 : ℤ) ∧
      pathForestComponentSurplus hk P p.1 ≤
        min
          (((k - 1 : ℕ) : ℤ) -
            (surplusLambda (k - 1) : ℤ) *
              (endpointChargeB
                (pathForestComponentLastDeficit hk P p.1) : ℤ))
          (((k - 1 : ℕ) : ℤ) -
            (surplusLambda (k - 1) : ℤ) *
              (endpointChargeA
                (pathForestComponentFirstDeficit hk P p.1) : ℤ)) ∧
      pathForestComponentSurplus hk P p.1 ≤
        ((k - 1 : ℕ) : ℤ) -
          (surplusLambda (k - 1) : ℤ) *
            ((endpointChargeA
                (pathForestComponentFirstDeficit hk P p.1) : ℤ) +
              (endpointChargeB
                (pathForestComponentLastDeficit hk P p.1) : ℤ)) +
          (surplusLambda (k - 1) : ℤ) *
            max (0 : ℤ)
              ((pathForestComponentFirstDeficit hk P p.1 : ℤ) - 4) := by
  have hmintoNonroot : pathForestNonrootMinto hk P p = 2 :=
    (mem_pathForestU hk P p).mp hpU
  have hminto : pathForestMinto (by omega) P p.1
      (pathForestComponent_vertexSet_ne_univ_of_nonroot
        (by omega) P p.1 p.2) = 2 := by
    simpa [pathForestNonrootMinto] using hmintoNonroot
  have hcheap := pathForestComponentCheapZOne hk P p.1 p.2 hminto hz
  have hfirstLast := hcheap.2.1
  have hdPos := hcheap.2.2.1
  have hbudgetEq := pathForestComponentBudget_eq_z_of_mem_U hk P p hpU
  have hbudgetOne : pathForestComponentBudget (by omega) P p.1 = 1 :=
    hbudgetEq.trans hz
  have hsEq := pathForestComponentSurplus_eq_z_one_budget_one
    hk P p.1 hz hbudgetOne
  have hlambdaNonnegative : (0 : ℤ) ≤ surplusLambda (k - 1) := by
    omega
  have hnInt : (2 : ℤ) ≤ ((k - 1 : ℕ) : ℤ) := by omega
  have hBLeNat :
      endpointChargeB (pathForestComponentLastDeficit hk P p.1) ≤
        pathForestComponentFirstDeficit hk P p.1 := by
    rw [hfirstLast]
    exact endpointChargeB_le_self_J1 _
  have hALeNat :
      endpointChargeA (pathForestComponentFirstDeficit hk P p.1) ≤
        pathForestComponentFirstDeficit hk P p.1 :=
    endpointChargeA_le_self_J1 _
  have hBLeInt :
      (endpointChargeB
          (pathForestComponentLastDeficit hk P p.1) : ℤ) ≤
        (pathForestComponentFirstDeficit hk P p.1 : ℤ) := by
    exact_mod_cast hBLeNat
  have hALeInt :
      (endpointChargeA
          (pathForestComponentFirstDeficit hk P p.1) : ℤ) ≤
        (pathForestComponentFirstDeficit hk P p.1 : ℤ) := by
    exact_mod_cast hALeNat
  have hBScaled :=
    Int.mul_le_mul_of_nonneg_left hBLeInt hlambdaNonnegative
  have hAScaled :=
    Int.mul_le_mul_of_nonneg_left hALeInt hlambdaNonnegative
  have hBbound : pathForestComponentSurplus hk P p.1 ≤
      ((k - 1 : ℕ) : ℤ) -
        (surplusLambda (k - 1) : ℤ) *
          (endpointChargeB
            (pathForestComponentLastDeficit hk P p.1) : ℤ) := by
    rw [hsEq]
    nlinarith
  have hAbound : pathForestComponentSurplus hk P p.1 ≤
      ((k - 1 : ℕ) : ℤ) -
        (surplusLambda (k - 1) : ℤ) *
          (endpointChargeA
            (pathForestComponentFirstDeficit hk P p.1) : ℤ) := by
    rw [hsEq]
    nlinarith
  have hminimum := le_min hBbound hAbound
  have hprecise : pathForestComponentSurplus hk P p.1 ≤
      ((k - 1 : ℕ) : ℤ) -
        (surplusLambda (k - 1) : ℤ) *
          ((endpointChargeA
              (pathForestComponentFirstDeficit hk P p.1) : ℤ) +
            (endpointChargeB
              (pathForestComponentLastDeficit hk P p.1) : ℤ)) +
        (surplusLambda (k - 1) : ℤ) *
          max (0 : ℤ)
            ((pathForestComponentFirstDeficit hk P p.1 : ℤ) - 4) := by
    rw [hsEq]
    have harithmetic := cheapZOne_precise_arithmetic
      (show 6 ≤ k - 1 by omega)
      (pathForestComponentFirstDeficit hk P p.1) hdPos
    simpa only [hfirstLast] using harithmetic
  exact ⟨hfirstLast, hdPos, hsEq, hsEq.le, hminimum, hprecise⟩

/-- Fourth row of Lemma `lem:surplusrows`, for an actual nonroot
component with `minto≥3`, together with its strict negativity conclusion.
The proof treats the noncheap `z=1` case separately from the capacity
theorem, whose domain is `z≥2`. -/
theorem pathForestNoncheapSurplus_le (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (hnonroot : C ≠ pathForestRootComponent (by omega) P)
    (hminto : 3 ≤ pathForestMinto (by omega) P C
      (pathForestComponent_vertexSet_ne_univ_of_nonroot
        (by omega) P C hnonroot)) :
    pathForestComponentSurplus hk P C ≤
        2 * ((k - 1 : ℕ) : ℤ) - 2 -
          (surplusKappa (k - 1) : ℤ) -
          (surplusLambda (k - 1) : ℤ) *
            (endpointChargeB
              (pathForestComponentLastDeficit hk P C) : ℤ) ∧
      pathForestComponentSurplus hk P C < 0 := by
  let componentZ := pathForestComponentZ (by omega) P C
  let dplus := pathForestComponentLastDeficit hk P C
  have hzPos : 1 ≤ componentZ := pathForestComponentZ_pos (by omega) P C
  have hbudget :=
    pathForestComponentBudget_ge_z_add_one_of_minto_ge_three
      hk P C hnonroot hminto
  have hrow : pathForestComponentSurplus hk P C ≤
      2 * ((k - 1 : ℕ) : ℤ) - 2 -
        (surplusKappa (k - 1) : ℤ) -
        (surplusLambda (k - 1) : ℤ) *
          (endpointChargeB dplus : ℤ) := by
    by_cases hzOne : componentZ = 1
    · have hdata := pathForestComponentZOneData hk P C hzOne
      have hfirstLast := hdata.1
      have hbudgetTwo : 2 ≤ pathForestComponentBudget (by omega) P C := by
        dsimp [componentZ] at hzOne hbudget
        omega
      have hbudgetTwoInt : (2 : ℤ) ≤
          (pathForestComponentBudget (by omega) P C : ℤ) := by
        exact_mod_cast hbudgetTwo
      have hkappaNonnegative : (0 : ℤ) ≤ surplusKappa (k - 1) := by
        omega
      have hbudgetScaled := Int.mul_le_mul_of_nonneg_left
        hbudgetTwoInt hkappaNonnegative
      have hbase := pathForestComponentZOne_base hk P C hzOne
      have hsIntermediate : pathForestComponentSurplus hk P C ≤
          2 - (surplusLambda (k - 1) : ℤ) *
              (pathForestComponentFirstDeficit hk P C : ℤ) -
            (surplusKappa (k - 1) : ℤ) := by
        rw [pathForestComponentSurplus_eq]
        nlinarith
      have hBLeNat : endpointChargeB dplus ≤
          pathForestComponentFirstDeficit hk P C := by
        dsimp [dplus]
        rw [hfirstLast]
        exact endpointChargeB_le_self_J1 _
      have hBLeInt : (endpointChargeB dplus : ℤ) ≤
          (pathForestComponentFirstDeficit hk P C : ℤ) := by
        exact_mod_cast hBLeNat
      have hlambdaNonnegative : (0 : ℤ) ≤ surplusLambda (k - 1) := by
        omega
      have hBScaled :=
        Int.mul_le_mul_of_nonneg_left hBLeInt hlambdaNonnegative
      have hnInt : (2 : ℤ) ≤ ((k - 1 : ℕ) : ℤ) := by omega
      nlinarith
    · have hzTwo : 2 ≤ componentZ := by omega
      have hcapacityRaw := pathForestComponentCapacity hk P C hzTwo
      have hcapacity : pathForestComponentBlockCount (by omega) P C +
          endpointChargeB dplus ≤
            hN (k - 1) componentZ (by omega) hzPos := by
        have hbPos := pathForestComponentBlockCount_pos (by omega) P C
        dsimp [componentZ, dplus] at hcapacityRaw ⊢
        exact add_le_of_pos_le_sub_J1 hbPos hcapacityRaw
      have hs := pathForestComponentSurplus_le_G_sub hk P C
        (endpointChargeB dplus) 1 hcapacity hbudget
      have hs' : pathForestComponentSurplus hk P C ≤
          surplusG (k - 1) componentZ (by omega) hzPos -
              (surplusLambda (k - 1) : ℤ) *
                (endpointChargeB dplus : ℤ) -
            (surplusKappa (k - 1) : ℤ) := by
        simpa only [Nat.cast_one, mul_one] using hs
      have hG := (surplusG_max (show 6 ≤ k - 1 by omega) hzPos).1
      calc
        pathForestComponentSurplus hk P C ≤
            surplusG (k - 1) componentZ (by omega) hzPos -
                (surplusLambda (k - 1) : ℤ) *
                  (endpointChargeB dplus : ℤ) -
              (surplusKappa (k - 1) : ℤ) := hs'
        _ ≤ (2 * ((k - 1 : ℕ) : ℤ) - 2 -
                (surplusLambda (k - 1) : ℤ) *
                  (endpointChargeB dplus : ℤ)) -
              (surplusKappa (k - 1) : ℤ) :=
          sub_le_sub_right (sub_le_sub_right hG _) _
        _ = 2 * ((k - 1 : ℕ) : ℤ) - 2 -
              (surplusKappa (k - 1) : ℤ) -
              (surplusLambda (k - 1) : ℤ) *
                (endpointChargeB dplus : ℤ) := by
          ring
  have hkappaLarge := surplusKappa_gt_two_mul_sub_two
    (show 6 ≤ k - 1 by omega)
  have hlambdaNonnegative : (0 : ℤ) ≤ surplusLambda (k - 1) := by
    omega
  have hchargeNonnegative : (0 : ℤ) ≤
      (surplusLambda (k - 1) : ℤ) *
        (endpointChargeB dplus : ℤ) :=
    mul_nonneg hlambdaNonnegative (by omega)
  have hrightNegative :
      2 * ((k - 1 : ℕ) : ℤ) - 2 -
          (surplusKappa (k - 1) : ℤ) -
          (surplusLambda (k - 1) : ℤ) *
            (endpointChargeB dplus : ℤ) < 0 := by
    nlinarith
  exact ⟨by simpa [dplus] using hrow,
    lt_of_le_of_lt hrow hrightNegative⟩

end SuperpermutationLowerBound
