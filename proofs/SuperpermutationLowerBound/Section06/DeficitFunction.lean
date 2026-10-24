module

public import SuperpermutationLowerBound.Section05.LegalDeficits
public import Mathlib.Data.List.TakeWhile

@[expose] public section

namespace SuperpermutationLowerBound

/-! The opening definitions and legality-heredity facts of Section 6.  The
positive-length domain of `PhiN` and `phiN` is carried by an explicit proof
argument; no public theorem can obtain information from a totalized value at
length zero. -/

/-- The ceiling envelope `Φ_n(r)`, on its exact domain `r ≥ 1`.  In the
second branch `r ≥ n`, so the natural subtraction is ordinary subtraction;
`(a + μ - 1) / μ` is the integer ceiling of `a / μ`. -/
def PhiN (n r : ℕ) (_hr : 1 ≤ r) : ℕ :=
  if r ≤ n - 1 then 0
  else 2 * ((r - n + (n - 2)) / (n - 2))

/-- The exact maximum-length function `N_n(D)`.  The isolated values
`D = 0,1` are kept in a separate branch.  For `D ≥ 2`, `D / 2` is the
floor and `D % 2` supplies the odd-case extra unit. -/
def maxLegalLength (n D : ℕ) : ℕ :=
  if D ≤ 1 then n - 1
  else (n - 1) + (n - 2) * (D / 2) + D % 2

/-- A literal contiguous slice, used to state legality heredity without any
implicit endpoint convention. -/
def deficitSlice (d : List ℕ) (start sliceLength : ℕ) : List ℕ :=
  (d.drop start).take sliceLength

theorem deficitSlice_length {d : List ℕ} {start sliceLength : ℕ}
    (hwithin : start + sliceLength ≤ d.length) :
    (deficitSlice d start sliceLength).length = sliceLength := by
  simp [deficitSlice]
  omega

theorem deficitAt_deficitSlice {d : List ℕ} {start sliceLength i : ℕ}
    (hwithin : start + sliceLength ≤ d.length) (hi : i < sliceLength) :
    deficitAt (deficitSlice d start sliceLength) i =
      deficitAt d (start + i) := by
  have hslen : (deficitSlice d start sliceLength).length = sliceLength :=
    deficitSlice_length hwithin
  rw [deficitAt_eq_get _ i (by omega), deficitAt_eq_get _ (start + i) (by omega)]
  simp [deficitSlice]

private def leftZeroBoundary (d : List ℕ) (start t : ℕ) : Prop :=
  t = start ∨
    (t < start ∧ 0 < deficitAt d (start - t - 1))

private instance leftZeroBoundary_decidable (d : List ℕ) (start t : ℕ) :
    Decidable (leftZeroBoundary d start t) := by
  unfold leftZeroBoundary
  infer_instance

private theorem leftZeroBoundary_exists (d : List ℕ) (start : ℕ) :
    ∃ t, leftZeroBoundary d start t :=
  ⟨start, Or.inl rfl⟩

private noncomputable def leftZeroExtension (d : List ℕ) (start : ℕ) : ℕ :=
  Nat.find (leftZeroBoundary_exists d start)

private theorem leftZeroExtension_le (d : List ℕ) (start : ℕ) :
    leftZeroExtension d start ≤ start := by
  simpa [leftZeroExtension] using
    (Nat.find_min' (leftZeroBoundary_exists d start)
      (show leftZeroBoundary d start start from Or.inl rfl))

private theorem leftZeroExtension_boundary (d : List ℕ) (start : ℕ) :
    leftZeroExtension d start = start ∨
      (leftZeroExtension d start < start ∧
        0 < deficitAt d (start - leftZeroExtension d start - 1)) := by
  change leftZeroBoundary d start (leftZeroExtension d start)
  unfold leftZeroExtension
  exact Nat.find_spec (leftZeroBoundary_exists d start)

private theorem leftZeroExtension_zero (d : List ℕ) (start j : ℕ)
    (hj : j < leftZeroExtension d start) :
    deficitAt d (start - j - 1) = 0 := by
  have hjstart : j < start :=
    lt_of_lt_of_le hj (leftZeroExtension_le d start)
  by_contra hne
  have hpos : 0 < deficitAt d (start - j - 1) := by omega
  have hfound : leftZeroBoundary d start j :=
    Or.inr ⟨hjstart, hpos⟩
  have hmin : leftZeroExtension d start ≤ j := by
    simpa [leftZeroExtension] using
      (Nat.find_min' (leftZeroBoundary_exists d start) hfound)
  omega

private def rightZeroBoundary (d : List ℕ) (base t : ℕ) : Prop :=
  base + t = d.length ∨
    (base + t < d.length ∧ 0 < deficitAt d (base + t))

private instance rightZeroBoundary_decidable (d : List ℕ) (base t : ℕ) :
    Decidable (rightZeroBoundary d base t) := by
  unfold rightZeroBoundary
  infer_instance

private theorem rightZeroBoundary_exists (d : List ℕ) (base : ℕ)
    (hbase : base ≤ d.length) :
    ∃ t, rightZeroBoundary d base t := by
  refine ⟨d.length - base, Or.inl ?_⟩
  omega

private noncomputable def rightZeroExtension (d : List ℕ) (base : ℕ)
    (hbase : base ≤ d.length) : ℕ :=
  Nat.find (rightZeroBoundary_exists d base hbase)

private theorem rightZeroExtension_le (d : List ℕ) (base : ℕ)
    (hbase : base ≤ d.length) :
    rightZeroExtension d base hbase ≤ d.length - base := by
  simpa [rightZeroExtension] using
    (Nat.find_min' (rightZeroBoundary_exists d base hbase)
      (show rightZeroBoundary d base (d.length - base) by
        left
        omega))

private theorem rightZeroExtension_boundary (d : List ℕ) (base : ℕ)
    (hbase : base ≤ d.length) :
    base + rightZeroExtension d base hbase = d.length ∨
      (base + rightZeroExtension d base hbase < d.length ∧
        0 < deficitAt d (base + rightZeroExtension d base hbase)) := by
  change rightZeroBoundary d base (rightZeroExtension d base hbase)
  unfold rightZeroExtension
  exact Nat.find_spec (rightZeroBoundary_exists d base hbase)

private theorem rightZeroExtension_zero (d : List ℕ) (base : ℕ)
    (hbase : base ≤ d.length) (j : ℕ)
    (hj : j < rightZeroExtension d base hbase) :
    deficitAt d (base + j) = 0 := by
  have hright := rightZeroExtension_le d base hbase
  have hindex : base + j < d.length := by omega
  by_contra hne
  have hpos : 0 < deficitAt d (base + j) := by omega
  have hfound : rightZeroBoundary d base j :=
    Or.inr ⟨hindex, hpos⟩
  have hmin : rightZeroExtension d base hbase ≤ j := by
    simpa [rightZeroExtension] using
      (Nat.find_min' (rightZeroBoundary_exists d base hbase) hfound)
  omega

/-- Every nonempty interval of zeros extends to an actual maximal zero
block.  This is the endpoint fact needed to make legality hereditary; it is
not an assumption of any later charging argument. -/
theorem exists_maximalZeroBlock_containing {d : List ℕ}
    {start blockLength : ℕ} (hpositive : 0 < blockLength)
    (hwithin : start + blockLength ≤ d.length)
    (hzeros : ∀ j, j < blockLength → deficitAt d (start + j) = 0) :
    ∃ maximalStart maximalLength,
      IsMaximalZeroBlock d maximalStart maximalLength ∧
      maximalStart ≤ start ∧
      start + blockLength ≤ maximalStart + maximalLength := by
  let left := leftZeroExtension d start
  let base := start + blockLength
  let right := rightZeroExtension d base hwithin
  let maximalStart := start - left
  let maximalLength := left + blockLength + right
  have hleftLe : left ≤ start := leftZeroExtension_le d start
  have hrightLe : right ≤ d.length - base :=
    rightZeroExtension_le d base hwithin
  have hstartLeft : maximalStart + left = start := by
    dsimp [maximalStart, left]
    omega
  have hendEq : maximalStart + maximalLength = base + right := by
    dsimp [maximalLength]
    omega
  have hendLe : base + right ≤ d.length := by omega
  refine ⟨maximalStart, maximalLength, ?_, by dsimp [maximalStart]; omega, ?_⟩
  · refine ⟨by dsimp [maximalLength]; omega, ?_, ?_, ?_, ?_⟩
    · rw [hendEq]
      exact hendLe
    · intro j hj
      dsimp [maximalStart, maximalLength, left, base, right] at hj ⊢
      by_cases hleft : j < leftZeroExtension d start
      · let q := leftZeroExtension d start - j - 1
        have hq : q < leftZeroExtension d start := by
          dsimp [q]
          omega
        have hz := leftZeroExtension_zero d start q hq
        have hindex : start - leftZeroExtension d start + j =
            start - q - 1 := by
          dsimp [q]
          omega
        simpa [hindex] using hz
      · by_cases hmiddle : j < leftZeroExtension d start + blockLength
        · let q := j - leftZeroExtension d start
          have hq : q < blockLength := by
            dsimp [q]
            omega
          have hz := hzeros q hq
          have hindex : start - leftZeroExtension d start + j =
              start + q := by
            dsimp [q]
            omega
          simpa [hindex] using hz
        · let q := j - leftZeroExtension d start - blockLength
          have hq : q < rightZeroExtension d (start + blockLength) hwithin := by
            dsimp [q]
            omega
          have hz := rightZeroExtension_zero d (start + blockLength)
            hwithin q hq
          have hindex : start - leftZeroExtension d start + j =
              start + blockLength + q := by
            dsimp [q]
            omega
          simpa [hindex] using hz
    · rcases leftZeroExtension_boundary d start with hboundary | hboundary
      · left
        dsimp [maximalStart, left]
        omega
      · right
        refine ⟨by dsimp [maximalStart, left]; omega, ?_⟩
        simpa [maximalStart, left] using hboundary.2
    · rcases rightZeroExtension_boundary d base hwithin with hboundary | hboundary
      · left
        rw [hendEq]
        exact hboundary
      · right
        refine ⟨by rw [hendEq]; exact hboundary.1, ?_⟩
        rw [hendEq]
        exact hboundary.2
  · rw [hendEq]
    dsimp [base]
    omega

/-- Any nonempty zero interval in a legal sequence has length at most
`n-1`; if the whole sequence is not all zero, the sharper bound is `n-2`. -/
theorem legal_zeroInterval_bounds {n : ℕ} {d : List ℕ}
    (hlegal : IsLegalDeficitSequence n d) {start blockLength : ℕ}
    (hpositive : 0 < blockLength)
    (hwithin : start + blockLength ≤ d.length)
    (hzeros : ∀ j, j < blockLength → deficitAt d (start + j) = 0) :
    blockLength ≤ n - 1 ∧
      ((¬ ∀ x ∈ d, x = 0) → blockLength ≤ n - 2) := by
  by_cases hall : ∀ x ∈ d, x = 0
  · have hlen : d.length ≤ n - 1 := by
      simpa only [if_pos hall] using hlegal.rule1
    have hblockLe : blockLength ≤ d.length := by omega
    constructor
    · omega
    · intro hnot
      exact (hnot hall).elim
  · obtain ⟨maximalStart, maximalLength, hmax, _hstart, hcontains⟩ :=
      exists_maximalZeroBlock_containing hpositive hwithin hzeros
    have hmaxLength : maximalLength ≤ n - 2 := by
      have hrule : ∀ start blockLength,
          IsMaximalZeroBlock d start blockLength → blockLength ≤ n - 2 := by
        simpa [hall] using hlegal.rule1
      exact hrule maximalStart maximalLength hmax
    constructor <;> omega

/-- Every nonempty contiguous subsequence of a legal sequence is legal.
Endpoint zero blocks are handled through `legal_zeroInterval_bounds`, so the
all-zero `n-1` exception is preserved exactly. -/
theorem IsLegalDeficitSequence.slice {n : ℕ} {d : List ℕ}
    (hlegal : IsLegalDeficitSequence n d) {start sliceLength : ℕ}
    (hpositive : 0 < sliceLength)
    (hwithin : start + sliceLength ≤ d.length) :
    IsLegalDeficitSequence n (deficitSlice d start sliceLength) where
  six_le := hlegal.six_le
  nonempty := by
    have hlen := deficitSlice_length hwithin
    intro hnil
    have := congrArg List.length hnil
    simp_all
  entries_lt := by
    intro x hx
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
    have hislice : i.1 < sliceLength := by
      simpa [deficitSlice_length hwithin] using i.2
    have hget := deficitAt_deficitSlice hwithin hislice
    rw [deficitAt_eq_get _ i.1 (by simpa [deficitSlice_length hwithin] using i.2)] at hget
    have hdmem : deficitAt d (start + i.1) ∈ d := by
      rw [deficitAt_eq_get _ (start + i.1) (by omega)]
      exact List.get_mem _ _
    rw [← hi, hget]
    exact hlegal.entries_lt _ hdmem
  rule1 := by
    by_cases hallSlice : ∀ x ∈ deficitSlice d start sliceLength, x = 0
    · simp only [if_pos hallSlice]
      have hzeros : ∀ j, j < sliceLength →
          deficitAt d (start + j) = 0 := by
        intro j hj
        rw [← deficitAt_deficitSlice hwithin hj]
        rw [deficitAt_eq_get _ j (by rw [deficitSlice_length hwithin]; exact hj)]
        exact hallSlice _ (List.get_mem _ _)
      rw [deficitSlice_length hwithin]
      exact (legal_zeroInterval_bounds hlegal hpositive hwithin hzeros).1
    · simp only [if_neg hallSlice]
      have hnotAll : ¬ ∀ x ∈ d, x = 0 := by
        intro hall
        apply hallSlice
        intro x hx
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
        have hislice : i.1 < sliceLength := by
          simpa [deficitSlice_length hwithin] using i.2
        have hget := deficitAt_deficitSlice hwithin hislice
        rw [deficitAt_eq_get _ i.1 (by simpa [deficitSlice_length hwithin] using i.2)] at hget
        rw [← hi, hget]
        apply hall
        rw [deficitAt_eq_get _ (start + i.1) (by omega)]
        exact List.get_mem _ _
      intro localStart blockLength hblock
      rcases hblock with ⟨hblockPos, hblockWithin, hzeros, _hleft, _hright⟩
      have hzerosOriginal : ∀ j, j < blockLength →
          deficitAt d (start + localStart + j) = 0 := by
        intro j hj
        have hz := hzeros j hj
        rw [deficitAt_deficitSlice hwithin (by
          rw [deficitSlice_length hwithin] at hblockWithin
          omega)] at hz
        simpa [Nat.add_assoc] using hz
      apply (legal_zeroInterval_bounds hlegal hblockPos (by
        rw [deficitSlice_length hwithin] at hblockWithin
        omega) hzerosOriginal).2 hnotAll
  rule2 := by
    intro i hi hpattern
    have hslen := deficitSlice_length hwithin
    have hi0 : i < sliceLength := by omega
    have hi1 : i + 1 < sliceLength := by omega
    have hi2 : i + 2 < sliceLength := by omega
    have hsource := hlegal.rule2 (start + i) (by omega)
    apply hsource
    simpa [deficitAt_deficitSlice hwithin hi0,
      deficitAt_deficitSlice hwithin hi1,
      deficitAt_deficitSlice hwithin hi2, Nat.add_assoc] using hpattern
  rule3 := by
    intro localStart hblock hleft hright
    have hslen := deficitSlice_length hwithin
    rcases hblock with
      ⟨hblockPos, hblockWithin, hzeros, hmaxLeft, hmaxRight⟩
    have hsourceBlock : IsMaximalZeroBlock d (start + localStart) (n - 2) := by
      refine ⟨hblockPos, by omega, ?_, ?_, ?_⟩
      · intro j hj
        have hz := hzeros j hj
        rw [deficitAt_deficitSlice hwithin (by omega)] at hz
        simpa [Nat.add_assoc] using hz
      · right
        refine ⟨by omega, ?_⟩
        rcases hmaxLeft with hzero | ⟨_hpos, hvalue⟩
        · omega
        · have hmap := deficitAt_deficitSlice hwithin (i := localStart - 1) (by omega)
          rw [hmap] at hvalue
          have heq : start + (localStart - 1) =
              start + localStart - 1 := by omega
          simpa [heq] using hvalue
      · right
        refine ⟨by omega, ?_⟩
        rcases hmaxRight with hend | ⟨_hpos, hvalue⟩
        · omega
        · have hmap := deficitAt_deficitSlice hwithin
            (i := localStart + (n - 2)) (by omega)
          rw [hmap] at hvalue
          simpa [Nat.add_assoc] using hvalue
    have hsource := hlegal.rule3 (start + localStart) hsourceBlock
      (by omega) (by omega)
    have hleftMap := deficitAt_deficitSlice hwithin
      (i := localStart - 1) (by omega)
    have hrightMap := deficitAt_deficitSlice hwithin
      (i := localStart + (n - 2)) (by omega)
    rw [hleftMap, hrightMap]
    have heq : start + (localStart - 1) =
        start + localStart - 1 := by omega
    simpa [Nat.add_assoc, heq] using hsource

/-- Prefix legality, with the positive prefix length explicit. -/
theorem IsLegalDeficitSequence.take {n : ℕ} {d : List ℕ}
    (hlegal : IsLegalDeficitSequence n d) {r : ℕ}
    (hr : 1 ≤ r) (hrd : r ≤ d.length) :
    IsLegalDeficitSequence n (d.take r) := by
  simpa [deficitSlice] using hlegal.slice (start := 0)
    (sliceLength := r) hr (by omega)

/-- A named contiguous-subsequence form of legality heredity. -/
theorem legal_contiguousSubsequence {n : ℕ} {d : List ℕ}
    (hlegal : IsLegalDeficitSequence n d) {start sliceLength : ℕ}
    (hpositive : 0 < sliceLength)
    (hwithin : start + sliceLength ≤ d.length) :
    IsLegalDeficitSequence n (deficitSlice d start sliceLength) :=
  hlegal.slice hpositive hwithin

/-- A deliberately non-extremal legal sequence of every positive length.
It supplies nonemptiness for the finite minimum without encoding its value. -/
def legalExistenceWitness (r : ℕ) : List ℕ := List.replicate r 2

theorem legalExistenceWitness_length (r : ℕ) :
    (legalExistenceWitness r).length = r := by
  simp [legalExistenceWitness]

theorem legalExistenceWitness_legal {n r : ℕ} (hn : 6 ≤ n)
    (hr : 1 ≤ r) :
    IsLegalDeficitSequence n (legalExistenceWitness r) where
  six_le := hn
  nonempty := by
    have hr0 : r ≠ 0 := by omega
    simp [legalExistenceWitness, hr0]
  entries_lt := by
    intro x hx
    simp [legalExistenceWitness] at hx
    omega
  rule1 := by
    have hnotAll : ¬ ∀ x ∈ legalExistenceWitness r, x = 0 := by
      intro hall
      have hr0 : r ≠ 0 := by omega
      have htwo := hall 2 (by simp [legalExistenceWitness, hr0])
      omega
    simp only [if_neg hnotAll]
    intro start blockLength hblock
    rcases hblock with ⟨hpos, hwithin, hzeros, _hleft, _hright⟩
    have hz : deficitAt (legalExistenceWitness r) start = 0 := by
      simpa using hzeros 0 hpos
    rw [deficitAt_eq_get _ start (by omega)] at hz
    simp [legalExistenceWitness] at hz
  rule2 := by
    intro i hi hpattern
    have hi0 : i < (legalExistenceWitness r).length := by omega
    have hzero := hpattern.1
    rw [deficitAt_eq_get _ i hi0] at hzero
    simp [legalExistenceWitness] at hzero
  rule3 := by
    intro start hblock _hleft _hright
    rcases hblock with ⟨hpos, hwithin, hzeros, _hmaxLeft, _hmaxRight⟩
    have hz : deficitAt (legalExistenceWitness r) start = 0 := by
      simpa using hzeros 0 hpos
    rw [deficitAt_eq_get _ start (by omega)] at hz
    simp [legalExistenceWitness] at hz

/-- Turn a bounded vector into the corresponding list of natural deficits. -/
def deficitVectorList {n r : ℕ} (v : Fin r → Fin n) : List ℕ :=
  List.ofFn fun i => (v i : ℕ)

theorem deficitVectorList_length {n r : ℕ} (v : Fin r → Fin n) :
    (deficitVectorList v).length = r := by
  simp [deficitVectorList]

/-- The finite set of totals of all legal length-`r` vectors with entries
in `0,…,n-1`. -/
noncomputable def legalDeficitTotals (n r : ℕ) : Finset ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin r → Fin n)).filter fun v =>
    IsLegalDeficitSequence n (deficitVectorList v)).image fun v =>
      deficitSequenceTotal (deficitVectorList v)

theorem legalDeficitTotals_nonempty {n r : ℕ} (hn : 6 ≤ n)
    (hr : 1 ≤ r) : (legalDeficitTotals n r).Nonempty := by
  classical
  let v : Fin r → Fin n := fun _ => ⟨2, by omega⟩
  refine ⟨deficitSequenceTotal (deficitVectorList v), ?_⟩
  simp only [legalDeficitTotals, Finset.mem_image]
  refine ⟨v, ?_, rfl⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hlist : deficitVectorList v = legalExistenceWitness r := by
    apply List.ext_get
    · simp [deficitVectorList, legalExistenceWitness]
    · intro i hi₁ hi₂
      simp [deficitVectorList, legalExistenceWitness, v]
  rw [hlist]
  exact legalExistenceWitness_legal hn hr

/-- The genuine finite, nonempty minimum `φ_n(r)`, on the exact domain
`n ≥ 6`, `r ≥ 1`. -/
noncomputable def phiN (n r : ℕ) (hn : 6 ≤ n) (hr : 1 ≤ r) : ℕ :=
  (legalDeficitTotals n r).min' (legalDeficitTotals_nonempty hn hr)

theorem phiN_mem_legalDeficitTotals {n r : ℕ} (hn : 6 ≤ n)
    (hr : 1 ≤ r) :
    phiN n r hn hr ∈ legalDeficitTotals n r := by
  exact Finset.min'_mem _ _

/-- Attainment follows from the finite minimum; it is a theorem, not part of
the definition of `phiN`. -/
theorem phiN_attained {n r : ℕ} (hn : 6 ≤ n) (hr : 1 ≤ r) :
    ∃ d : List ℕ,
      d.length = r ∧ IsLegalDeficitSequence n d ∧
        deficitSequenceTotal d = phiN n r hn hr := by
  classical
  have hmem := phiN_mem_legalDeficitTotals hn hr
  simp only [legalDeficitTotals, Finset.mem_image] at hmem
  obtain ⟨v, hv, htotal⟩ := hmem
  refine ⟨deficitVectorList v, deficitVectorList_length v, ?_, htotal⟩
  simpa using (Finset.mem_filter.mp hv).2

/-- Universal minimality of the finite minimum over actual legal lists. -/
theorem phiN_le_total_of_legal {n r : ℕ} (hn : 6 ≤ n) (hr : 1 ≤ r)
    {d : List ℕ} (hlength : d.length = r)
    (hlegal : IsLegalDeficitSequence n d) :
    phiN n r hn hr ≤ deficitSequenceTotal d := by
  classical
  let v : Fin r → Fin n := fun i =>
    ⟨d.get ⟨i.1, by simpa [hlength] using i.2⟩,
      hlegal.entries_lt _ (List.get_mem _ _)⟩
  have hlist : deficitVectorList v = d := by
    apply List.ext_get
    · simp [deficitVectorList, hlength]
    · intro i hi₁ hi₂
      simp [deficitVectorList, v]
  have hmem : deficitSequenceTotal d ∈ legalDeficitTotals n r := by
    simp only [legalDeficitTotals, Finset.mem_image]
    refine ⟨v, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [hlist] using hlegal
    · simpa [hlist]
  exact Finset.min'_le _ _ hmem

end SuperpermutationLowerBound
