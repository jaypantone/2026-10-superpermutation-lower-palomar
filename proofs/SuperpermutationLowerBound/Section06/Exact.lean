module

public import SuperpermutationLowerBound.Section06.Charging
public import Mathlib.Data.Nat.ModEq

@[expose] public section

-- Export private helpers used in exposed definitions; this adds no axiom.
set_option backward.privateInPublic true

namespace SuperpermutationLowerBound

/-! Corollary `cor:phiexact`: inversion of the charging/witness bounds,
the exceptional congruence, and the two regularity inequalities. -/

/-- The deliberately isolated values `D=0,1` have the same maximum
length. -/
theorem maxLegalLength_zero_eq_one (n : ℕ) :
    maxLegalLength n 0 = maxLegalLength n 1 := by
  simp [maxLegalLength]

/-- The four displayed differences in the paper, packaged as strict
increase at every positive argument. -/
theorem maxLegalLength_lt_succ {n D : ℕ} (hn : 6 ≤ n) (hD : 1 ≤ D) :
    maxLegalLength n D < maxLegalLength n (D + 1) := by
  by_cases hDone : D = 1
  · subst D
    simp [maxLegalLength]
    omega
  have hDlarge : 2 ≤ D := by omega
  have hmod := Nat.mod_two_eq_zero_or_one D
  let t := D / 2
  rcases hmod with heven | hodd
  · have hDeq : D = 2 * t := by
      dsimp [t]
      have hdivision := Nat.mod_add_div D 2
      omega
    have ht : 1 ≤ t := by omega
    rw [hDeq]
    have hdivEven : (2 * t) / 2 = t := by omega
    have hmodEven : (2 * t) % 2 = 0 := by omega
    have hdivOdd : (2 * t + 1) / 2 = t := by omega
    have hmodOdd : (2 * t + 1) % 2 = 1 := by omega
    simp [maxLegalLength, hdivEven, hmodEven, hdivOdd, hmodOdd,
      show ¬2 * t ≤ 1 by omega, show ¬2 * t + 1 ≤ 1 by omega]
  · have hDeq : D = 2 * t + 1 := by
      dsimp [t]
      have hdivision := Nat.mod_add_div D 2
      omega
    have ht : 1 ≤ t := by omega
    rw [hDeq]
    have hdivOdd : (2 * t + 1) / 2 = t := by omega
    have hmodOdd : (2 * t + 1) % 2 = 1 := by omega
    have hdivEven : (2 * t + 1 + 1) / 2 = t + 1 := by omega
    have hmodEven : (2 * t + 1 + 1) % 2 = 0 := by omega
    simp [maxLegalLength, hdivOdd, hmodOdd, hdivEven, hmodEven,
      show ¬2 * t + 1 ≤ 1 by omega, show ¬2 * t + 1 + 1 ≤ 1 by omega]
    rw [Nat.mul_add]
    omega

/-- `N_n` is strictly increasing on the positive integers. -/
theorem maxLegalLength_strict_on_positive {n a b : ℕ} (hn : 6 ≤ n)
    (ha : 1 ≤ a) (hab : a < b) :
    maxLegalLength n a < maxLegalLength n b := by
  have hshift : StrictMono (fun q => maxLegalLength n (q + 1)) :=
    strictMono_nat_of_lt_succ (fun q => maxLegalLength_lt_succ hn (by omega))
  cases a with
  | zero => omega
  | succ a =>
      cases b with
      | zero => omega
      | succ b =>
          simpa [Nat.succ_eq_add_one] using hshift (by omega : a < b)

/-- The non-strict form, including the equality `N_n(0)=N_n(1)`. -/
theorem maxLegalLength_mono {n a b : ℕ} (hn : 6 ≤ n) (hab : a ≤ b) :
    maxLegalLength n a ≤ maxLegalLength n b := by
  by_cases heq : a = b
  · subst b
    exact le_rfl
  have hlt : a < b := by omega
  by_cases ha0 : a = 0
  · subst a
    by_cases hb1 : b = 1
    · subst b
      exact le_of_eq (maxLegalLength_zero_eq_one n)
    · have hb : 1 < b := by omega
      rw [maxLegalLength_zero_eq_one]
      exact (maxLegalLength_strict_on_positive hn (by omega) hb).le
  · exact (maxLegalLength_strict_on_positive hn (by omega) hlt).le

private theorem exists_maxLegalLength_admissible {n r : ℕ}
    (hn : 6 ≤ n) (hr : 1 ≤ r) :
    ∃ D, r ≤ maxLegalLength n D := by
  obtain ⟨d, hlength, hlegal, htotal⟩ := phiN_attained hn hr
  have hcharge := legalDeficitSequence_length_le_maxLegalLength hlegal
  rw [hlength, htotal] at hcharge
  exact ⟨phiN n r hn hr, hcharge⟩

/-- The least `D` whose witness envelope reaches `r`. -/
noncomputable def leastAdmissibleDeficit (n r : ℕ) (hn : 6 ≤ n)
    (hr : 1 ≤ r) : ℕ :=
  Nat.find (exists_maxLegalLength_admissible hn hr)

theorem leastAdmissibleDeficit_spec {n r : ℕ} (hn : 6 ≤ n)
    (hr : 1 ≤ r) :
    r ≤ maxLegalLength n (leastAdmissibleDeficit n r hn hr) := by
  unfold leastAdmissibleDeficit
  exact Nat.find_spec (exists_maxLegalLength_admissible hn hr)

theorem leastAdmissibleDeficit_minimal {n r : ℕ} (hn : 6 ≤ n)
    (hr : 1 ≤ r) {D : ℕ} (hD : r ≤ maxLegalLength n D) :
    leastAdmissibleDeficit n r hn hr ≤ D := by
  unfold leastAdmissibleDeficit
  exact Nat.find_min' (exists_maxLegalLength_admissible hn hr) hD

/-- The first equality in Corollary `cor:phiexact`: the genuine finite
minimum over legal sequences is the least `D` with `N_n(D) ≥ r`. -/
theorem phiN_eq_leastAdmissibleDeficit {n r : ℕ} (hn : 6 ≤ n)
    (hr : 1 ≤ r) :
    phiN n r hn hr = leastAdmissibleDeficit n r hn hr := by
  let D := leastAdmissibleDeficit n r hn hr
  have hD : r ≤ maxLegalLength n D := leastAdmissibleDeficit_spec hn hr
  obtain ⟨w, hwlen, hwlegal, hwtotal⟩ :=
    exists_legal_deficit_witness_of_length_le hn hr hD
  have hphiLe : phiN n r hn hr ≤ D := by
    have hmin := phiN_le_total_of_legal hn hr hwlen hwlegal
    omega
  obtain ⟨d, hdlen, hdlegal, hdtotal⟩ := phiN_attained hn hr
  have hcharge := legalDeficitSequence_length_le_maxLegalLength hdlegal
  rw [hdlen, hdtotal] at hcharge
  have hDLe : D ≤ phiN n r hn hr :=
    leastAdmissibleDeficit_minimal hn hr hcharge
  exact Nat.le_antisymm hphiLe hDLe

/-- Set-minimum characterization without relying on notation for an
unbounded set: `φ` is admissible and is below every admissible `D`. -/
theorem phiN_is_minimum_maxLegalLength {n r : ℕ} (hn : 6 ≤ n)
    (hr : 1 ≤ r) :
    r ≤ maxLegalLength n (phiN n r hn hr) ∧
      ∀ D, r ≤ maxLegalLength n D → phiN n r hn hr ≤ D := by
  rw [phiN_eq_leastAdmissibleDeficit hn hr]
  exact ⟨leastAdmissibleDeficit_spec hn hr,
    fun D hD => leastAdmissibleDeficit_minimal hn hr hD⟩

private theorem maxLegalLength_even {n t : ℕ} (ht : 1 ≤ t) :
    maxLegalLength n (2 * t) = (n - 1) + (n - 2) * t := by
  have hlarge : ¬2 * t ≤ 1 := by omega
  have hdiv : (2 * t) / 2 = t := by omega
  have hmod : (2 * t) % 2 = 0 := by omega
  unfold maxLegalLength
  rw [if_neg hlarge, hdiv, hmod]
  omega

private theorem maxLegalLength_odd {n t : ℕ} (hnpos : 1 ≤ n) (ht : 1 ≤ t) :
    maxLegalLength n (2 * t + 1) = n + (n - 2) * t := by
  have ht0 : t ≠ 0 := by omega
  have hdiv : (t * 2 + 1) / 2 = t := by omega
  simp [maxLegalLength, ht0, hdiv, Nat.mul_comm]
  omega

private theorem leastAdmissibleDeficit_eq_of_boundary {n r C : ℕ}
    (hn : 6 ≤ n) (hr : 1 ≤ r) (hC : 1 ≤ C)
    (hprevious : maxLegalLength n (C - 1) < r)
    (hreaches : r ≤ maxLegalLength n C) :
    leastAdmissibleDeficit n r hn hr = C := by
  have hle : leastAdmissibleDeficit n r hn hr ≤ C :=
    leastAdmissibleDeficit_minimal hn hr hreaches
  apply Nat.le_antisymm hle
  by_contra hnot
  have hlt : leastAdmissibleDeficit n r hn hr < C := by omega
  have hprevLe : leastAdmissibleDeficit n r hn hr ≤ C - 1 := by omega
  have hNLe := maxLegalLength_mono hn hprevLe
  have hspec := leastAdmissibleDeficit_spec hn hr
  omega

/-- The exceptional-congruence closed form in Corollary `cor:phiexact`.
The congruence is the literal natural-number congruence modulo `n-2`, and
the threshold excludes the isolated value `D=1`. -/
theorem phiN_closed_form {n r : ℕ} (hn : 6 ≤ n) (hr : 1 ≤ r) :
    phiN n r hn hr =
      if n + (n - 2) ≤ r ∧ Nat.ModEq (n - 2) r n then
        PhiN n r hr - 1
      else PhiN n r hr := by
  rw [phiN_eq_leastAdmissibleDeficit hn hr]
  by_cases hsmall : r ≤ n - 1
  · have hNzero : r ≤ maxLegalLength n 0 := by
      simp [maxLegalLength]
      omega
    have hleast : leastAdmissibleDeficit n r hn hr = 0 := by
      have := leastAdmissibleDeficit_minimal hn hr hNzero
      omega
    have hnotExceptional :
        ¬(n + (n - 2) ≤ r ∧ Nat.ModEq (n - 2) r n) := by
      intro h
      omega
    rw [if_neg hnotExceptional, hleast]
    simp [PhiN, hsmall]
  · have hrn : n ≤ r := by omega
    have hr2 : 2 ≤ r := by omega
    let mu := n - 2
    let q := (r - 2) / mu
    let rem := (r - 2) % mu
    have hmu : 4 ≤ mu := by dsimp [mu]; omega
    have hmupos : 0 < mu := by omega
    have hqpos : 1 ≤ q := by
      apply (Nat.le_div_iff_mul_le hmupos).2
      dsimp [q, mu]
      omega
    have hrem : rem < mu := by
      exact Nat.mod_lt _ hmupos
    have hdivision := Nat.mod_add_div (r - 2) mu
    have hdecomp : r = 2 + mu * q + rem := by
      change rem + mu * q = r - 2 at hdivision
      omega
    have hPhi : PhiN n r hr = 2 * q := by
      unfold PhiN
      rw [if_neg hsmall]
      have hnum : r - n + (n - 2) = r - 2 := by omega
      rw [hnum]
    have hmodIff : Nat.ModEq mu r n ↔ rem = 0 := by
      constructor
      · intro hmod
        have hadd : Nat.ModEq mu (2 + (r - 2)) (2 + (n - 2)) := by
          simpa [show 2 + (r - 2) = r by omega,
            show 2 + (n - 2) = n by omega] using hmod
        have hsub := Nat.ModEq.add_left_cancel
          (show Nat.ModEq mu 2 2 from Nat.ModEq.rfl) hadd
        unfold Nat.ModEq at hsub
        change rem = (n - 2) % mu at hsub
        have hright : (n - 2) % mu = 0 := by simp [mu]
        exact hsub.trans hright
      · intro hremZero
        have hsub : Nat.ModEq mu (r - 2) (n - 2) := by
          unfold Nat.ModEq
          change rem = (n - 2) % mu
          rw [hremZero]
          simp [mu]
        have hadd := hsub.add_left 2
        simpa [show 2 + (r - 2) = r by omega,
          show 2 + (n - 2) = n by omega] using hadd
    by_cases hexceptional :
        n + (n - 2) ≤ r ∧ Nat.ModEq (n - 2) r n
    · have hq2 : 2 ≤ q := by
        apply (Nat.le_div_iff_mul_le hmupos).2
        dsimp [q, mu]
        omega
      have hremZero : rem = 0 := by
        apply hmodIff.mp
        simpa [mu] using hexceptional.2
      have hqsplit : q = (q - 1) + 1 := by omega
      have hmuq : mu * q = mu * (q - 1) + mu := by
        calc
          mu * q = mu * ((q - 1) + 1) := congrArg (fun z => mu * z) hqsplit
          _ = _ := by rw [Nat.mul_add]; simp
      let C := 2 * q - 1
      have hC : 1 ≤ C := by dsimp [C]; omega
      have hCshape : C = 2 * (q - 1) + 1 := by
        dsimp [C]
        omega
      have hpreviousShape : C - 1 = 2 * (q - 1) := by
        dsimp [C]
        omega
      have hNC : maxLegalLength n C = n + (n - 2) * (q - 1) := by
        rw [hCshape]
        exact maxLegalLength_odd (by omega) (by omega)
      have hNprevious : maxLegalLength n (C - 1) =
          (n - 1) + (n - 2) * (q - 1) := by
        rw [hpreviousShape]
        exact maxLegalLength_even (by omega)
      have hreaches : r ≤ maxLegalLength n C := by
        rw [hNC]
        dsimp [mu] at hmuq hdecomp
        omega
      have hprevious : maxLegalLength n (C - 1) < r := by
        rw [hNprevious]
        dsimp [mu] at hmuq hdecomp
        omega
      have hleast := leastAdmissibleDeficit_eq_of_boundary hn hr hC
        hprevious hreaches
      rw [if_pos hexceptional, hleast, hPhi]
    · have hNC : maxLegalLength n (2 * q) =
          (n - 1) + (n - 2) * q := maxLegalLength_even hqpos
      have hreaches : r ≤ maxLegalLength n (2 * q) := by
        rw [hNC]
        dsimp [mu] at hrem hdecomp
        omega
      have hprevious : maxLegalLength n (2 * q - 1) < r := by
        by_cases hq1 : q = 1
        · have harg : 2 * q - 1 = 1 := by omega
          rw [harg]
          simp [maxLegalLength]
          omega
        · have hq2 : 2 ≤ q := by omega
          have hremPos : 1 ≤ rem := by
            by_contra hnot
            have hremZero : rem = 0 := by omega
            apply hexceptional
            constructor
            · have hqsplit : q = (q - 1) + 1 := by omega
              have hmuq : mu * q = mu * (q - 1) + mu := by
                calc
                  mu * q = mu * ((q - 1) + 1) :=
                    congrArg (fun z => mu * z) hqsplit
                  _ = _ := by rw [Nat.mul_add]; simp
              have hmulLower : mu ≤ mu * (q - 1) := by
                have hmul := Nat.mul_le_mul_left mu (show 1 ≤ q - 1 by omega)
                simpa using hmul
              dsimp [mu] at hmuq hdecomp hmulLower
              omega
            · have : Nat.ModEq mu r n := hmodIff.mpr hremZero
              simpa [mu] using this
          have hshape : 2 * q - 1 = 2 * (q - 1) + 1 := by omega
          rw [hshape, maxLegalLength_odd (by omega) (by omega)]
          have hqsplit : q = (q - 1) + 1 := by omega
          have hmuq : mu * q = mu * (q - 1) + mu := by
            calc
              mu * q = mu * ((q - 1) + 1) :=
                congrArg (fun z => mu * z) hqsplit
              _ = _ := by rw [Nat.mul_add]; simp
          dsimp [mu] at hmuq hdecomp
          omega
      have hleast := leastAdmissibleDeficit_eq_of_boundary hn hr
        (show 1 ≤ 2 * q by omega) hprevious hreaches
      rw [if_neg hexceptional, hleast, hPhi]

/-- Monotonicity of `φ_n`, proved directly by taking a legal prefix of an
attaining sequence. -/
theorem phiN_le_succ {n r : ℕ} (hn : 6 ≤ n) (hr : 1 ≤ r) :
    phiN n r hn hr ≤ phiN n (r + 1) hn (by omega) := by
  obtain ⟨d, hlength, hlegal, htotal⟩ :=
    phiN_attained hn (show 1 ≤ r + 1 by omega)
  have hrLe : r ≤ d.length := by omega
  have hprefixLegal := hlegal.take hr hrLe
  have hprefixLength : (d.take r).length = r := by simp [hlength]
  have hminimal := phiN_le_total_of_legal hn hr hprefixLength hprefixLegal
  have hsum := List.sum_take_add_sum_drop d r
  simp only [deficitSequenceTotal] at hminimal htotal ⊢
  omega

/-- Raising the deficit allowance by two raises `N_n` by at least two,
including the isolated `D=0` case. -/
theorem maxLegalLength_add_two {n D : ℕ} (hn : 6 ≤ n) :
    maxLegalLength n D + 2 ≤ maxLegalLength n (D + 2) := by
  by_cases hzero : D = 0
  · subst D
    simp [maxLegalLength]
    omega
  · have hD : 1 ≤ D := by omega
    have hfirst := maxLegalLength_lt_succ hn hD
    have hsecond := maxLegalLength_lt_succ hn (D := D + 1) (by omega)
    have hindex : D + 1 + 1 = D + 2 := by omega
    rw [hindex] at hsecond
    omega

/-- The two-step regularity inequality, with `r≥3` ensuring that natural
subtraction really denotes the positive length `r-2`. -/
theorem phiN_le_sub_two_add_two {n r : ℕ} (hn : 6 ≤ n) (hr : 3 ≤ r) :
    phiN n r hn (by omega) ≤ phiN n (r - 2) hn (by omega) + 2 := by
  let D := phiN n (r - 2) hn (by omega)
  have hsubPositive : 1 ≤ r - 2 := by omega
  have hsubAdmissible := (phiN_is_minimum_maxLegalLength hn hsubPositive).1
  change r - 2 ≤ maxLegalLength n D at hsubAdmissible
  have hstep := maxLegalLength_add_two (D := D) hn
  have hreaches : r ≤ maxLegalLength n (D + 2) := by omega
  have hminimal := (phiN_is_minimum_maxLegalLength hn
    (show 1 ≤ r by omega)).2 (D + 2) hreaches
  exact hminimal

end SuperpermutationLowerBound
