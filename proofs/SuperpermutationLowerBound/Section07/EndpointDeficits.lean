module

public import SuperpermutationLowerBound.Section06.TerminalNonfull

@[expose] public section

namespace SuperpermutationLowerBound

/-! Endpoint-constrained deficit minima, through Remark `rem:endpointsharp`.
This module works throughout with actual legal lists.  All positions in the
public surgery statements are zero-based; thus the TeX support
`{1,...,n-1}` is represented by `i < n-1`. -/

/-- The left endpoint charge `A(x)=max(0,x-2)`. -/
def endpointChargeA (x : ℕ) : ℕ := max 0 (x - 2)

/-- The right endpoint charge, with the three literal branches from the
paper. -/
def endpointChargeB (y : ℕ) : ℕ :=
  if y = 0 then 0 else if y = 1 then 1 else y - 1

@[simp] theorem endpointChargeA_eq (x : ℕ) :
    endpointChargeA x = max 0 (x - 2) := rfl

@[simp] theorem endpointChargeB_zero : endpointChargeB 0 = 0 := by
  simp [endpointChargeB]

@[simp] theorem endpointChargeB_one : endpointChargeB 1 = 1 := by
  simp [endpointChargeB]

theorem endpointChargeB_eq_sub_one {y : ℕ} (hy : 2 ≤ y) :
    endpointChargeB y = y - 1 := by
  simp [endpointChargeB, show y ≠ 0 by omega, show y ≠ 1 by omega]

private theorem deficitAt_set (d : List ℕ) (j x i : ℕ)
    (hj : j < d.length) :
    deficitAt (d.set j x) i = if i = j then x else deficitAt d i := by
  unfold deficitAt
  rw [List.getElem?_set_of_lt' x d hj]
  by_cases hij : i = j
  · subst i
    simp
  · simp [hij, Ne.symm hij]

private theorem deficitAt_set_of_ne (d : List ℕ) (j x i : ℕ)
    (hj : j < d.length) (hij : i ≠ j) :
    deficitAt (d.set j x) i = deficitAt d i := by
  rw [deficitAt_set d j x i hj, if_neg hij]

private theorem deficitAt_set_self (d : List ℕ) (j x : ℕ)
    (hj : j < d.length) :
    deficitAt (d.set j x) j = x := by
  rw [deficitAt_set d j x j hj, if_pos rfl]

/-- Literal Case A left surgery: replace the first entry by `1`. -/
def leftSurgeryCaseA (d : List ℕ) : List ℕ := d.set 0 1

/-- Literal Case B1 left surgery.  Zero-based index `n-2` is TeX position
`n-1`; the entries strictly between it and the first entry were already
zero. -/
def leftSurgeryCaseB1 (n : ℕ) (d : List ℕ) : List ℕ :=
  (d.set 0 0).set (n - 2) 1

/-- Literal Case B2 left surgery.  Zero-based index `n-3` is TeX position
`n-2`; the following `0,1` are deliberately left untouched. -/
def leftSurgeryCaseB2 (n : ℕ) (d : List ℕ) : List ℕ :=
  (d.set 0 0).set (n - 3) 2

@[simp] theorem leftSurgeryCaseA_length (d : List ℕ) :
    (leftSurgeryCaseA d).length = d.length := by
  simp [leftSurgeryCaseA]

@[simp] theorem leftSurgeryCaseB1_length (n : ℕ) (d : List ℕ) :
    (leftSurgeryCaseB1 n d).length = d.length := by
  simp [leftSurgeryCaseB1]

@[simp] theorem leftSurgeryCaseB2_length (n : ℕ) (d : List ℕ) :
    (leftSurgeryCaseB2 n d).length = d.length := by
  simp [leftSurgeryCaseB2]

private theorem sum_set_balance {d : List ℕ} {j x old : ℕ}
    (hj : j < d.length) (hold : deficitAt d j = old) :
    (d.set j x).sum + old = d.sum + x := by
  have hsplit := List.sum_take_add_sum_drop d (j + 1)
  rw [List.sum_take_succ d j hj] at hsplit
  have hget : d[j] = old := by
    rw [deficitAt_eq_get d j hj] at hold
    exact hold
  rw [hget] at hsplit
  rw [List.sum_set, if_pos hj]
  omega

theorem leftSurgeryCaseA_support {d : List ℕ} {i : ℕ} (hi : i ≠ 0) :
    deficitAt (leftSurgeryCaseA d) i = deficitAt d i := by
  cases d with
  | nil => simp [leftSurgeryCaseA, deficitAt]
  | cons x xs => exact deficitAt_set_of_ne (x :: xs) 0 1 i (by simp) hi

theorem leftSurgeryCaseB1_support {n : ℕ} {d : List ℕ} {i : ℕ}
    (hzero : 0 < d.length) (hnidx : n - 2 < d.length)
    (hi0 : i ≠ 0) (hin : i ≠ n - 2) :
    deficitAt (leftSurgeryCaseB1 n d) i = deficitAt d i := by
  unfold leftSurgeryCaseB1
  rw [deficitAt_set_of_ne (d.set 0 0) (n - 2) 1 i (by simpa) hin]
  exact deficitAt_set_of_ne d 0 0 i hzero hi0

theorem leftSurgeryCaseB2_support {n : ℕ} {d : List ℕ} {i : ℕ}
    (hzero : 0 < d.length) (hnidx : n - 3 < d.length)
    (hi0 : i ≠ 0) (hin : i ≠ n - 3) :
    deficitAt (leftSurgeryCaseB2 n d) i = deficitAt d i := by
  unfold leftSurgeryCaseB2
  rw [deficitAt_set_of_ne (d.set 0 0) (n - 3) 2 i (by simpa) hin]
  exact deficitAt_set_of_ne d 0 0 i hzero hi0

private def IsLeftExceptionalConfiguration (n : ℕ) (d : List ℕ) : Prop :=
  n ≤ d.length ∧
    (∀ i, 1 ≤ i → i ≤ n - 2 → deficitAt d i = 0) ∧
    1 ≤ deficitAt d (n - 1) ∧
    deficitAt d (n - 1) ≤ n - 2

private theorem leftSurgeryCaseA_legal {n : ℕ} {d : List ℕ}
    (hlegal : IsLegalDeficitSequence n d)
    (hfirst : 2 ≤ deficitAt d 0)
    (hordinary : ¬ IsLeftExceptionalConfiguration n d) :
    IsLegalDeficitSequence n (leftSurgeryCaseA d) := by
  have hlen0 : 0 < d.length := by
    by_contra h
    have : d = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst d
    simp [deficitAt] at hfirst
  have hfirstPos : 0 < deficitAt d 0 := by omega
  have hnotAllOld : ¬ ∀ x ∈ d, x = 0 := by
    intro hall
    have hmem : deficitAt d 0 ∈ d := by
      rw [deficitAt_eq_get d 0 hlen0]
      exact List.get_mem _ _
    have := hall _ hmem
    omega
  have hmap (i : ℕ) :
      deficitAt (leftSurgeryCaseA d) i =
        if i = 0 then 1 else deficitAt d i := by
    exact deficitAt_set d 0 1 i hlen0
  have hzeroIff (i : ℕ) :
      deficitAt (leftSurgeryCaseA d) i = 0 ↔ deficitAt d i = 0 := by
    rw [hmap]
    by_cases hi : i = 0
    · subst i
      simp
      omega
    · simp [hi]
  refine {
    six_le := hlegal.six_le
    nonempty := by
      intro hnil
      have := congrArg List.length hnil
      simp at this
      apply hlegal.nonempty
      exact this
    entries_lt := ?_
    rule1 := ?_
    rule2 := ?_
    rule3 := ?_ }
  · intro x hx
    rcases List.mem_or_eq_of_mem_set hx with hxold | rfl
    · exact hlegal.entries_lt x hxold
    · have hn := hlegal.six_le
      omega
  · have hnotAllNew : ¬ ∀ x ∈ leftSurgeryCaseA d, x = 0 := by
      intro hall
      have honeMem : 1 ∈ leftSurgeryCaseA d := by
        exact List.mem_set hlen0 1
      have := hall 1 honeMem
      omega
    simp only [if_neg hnotAllNew]
    intro start blockLength hblock
    rcases hblock with ⟨hpos, hwithin, hzeros, hleft, hright⟩
    have hOldBlock : IsMaximalZeroBlock d start blockLength := by
      refine ⟨hpos, by simpa using hwithin, ?_, ?_, ?_⟩
      · intro j hj
        exact (hzeroIff (start + j)).mp (hzeros j hj)
      · rcases hleft with hstart | ⟨hstart, hvalue⟩
        · exact Or.inl hstart
        · right
          refine ⟨hstart, ?_⟩
          by_cases hi : start - 1 = 0
          · exact hi ▸ hfirstPos
          · rw [hmap, if_neg hi] at hvalue
            exact hvalue
      · rcases hright with hend | ⟨hindex, hvalue⟩
        · exact Or.inl (by simpa using hend)
        · right
          refine ⟨by simpa using hindex, ?_⟩
          have hne : start + blockLength ≠ 0 := by omega
          rw [hmap, if_neg hne] at hvalue
          exact hvalue
    have hrule : ∀ start blockLength,
        IsMaximalZeroBlock d start blockLength → blockLength ≤ n - 2 := by
      simpa [hnotAllOld] using hlegal.rule1
    exact hrule start blockLength hOldBlock
  · intro i hi hpattern
    rcases hpattern with ⟨hz, hone, hsmall⟩
    by_cases hi0 : i = 0
    · subst i
      rw [hmap, if_pos rfl] at hz
      omega
    · have hi1 : i + 1 ≠ 0 := by omega
      have hi2 : i + 2 ≠ 0 := by omega
      apply hlegal.rule2 i (by simpa using hi)
      rw [hmap, if_neg hi0] at hz
      rw [hmap, if_neg hi1] at hone
      rw [hmap, if_neg hi2] at hsmall
      exact ⟨hz, hone, hsmall⟩
  · intro start hblock hleftIndex hrightIndex
    rcases hblock with ⟨hpos, hwithin, hzeros, hleft, hright⟩
    have hOldBlock : IsMaximalZeroBlock d start (n - 2) := by
      refine ⟨hpos, by simpa using hwithin, ?_, ?_, ?_⟩
      · intro j hj
        exact (hzeroIff (start + j)).mp (hzeros j hj)
      · rcases hleft with hstart | ⟨hstart, hvalue⟩
        · exact Or.inl hstart
        · right
          refine ⟨hstart, ?_⟩
          by_cases hi : start - 1 = 0
          · exact hi ▸ hfirstPos
          · rw [hmap, if_neg hi] at hvalue
            exact hvalue
      · rcases hright with hend | ⟨hindex, hvalue⟩
        · exact Or.inl (by simpa using hend)
        · right
          refine ⟨by simpa using hindex, ?_⟩
          have hne : start + (n - 2) ≠ 0 := by omega
          rw [hmap, if_neg hne] at hvalue
          exact hvalue
    by_cases hstart : start = 1
    · subst start
      have hnle : n ≤ d.length := by
        simp at hrightIndex
        omega
      have hzerosOld : ∀ i, 1 ≤ i → i ≤ n - 2 →
          deficitAt d i = 0 := by
        intro i hi1 hin
        let j := i - 1
        have hj : j < n - 2 := by
          dsimp [j]
          omega
        have hz := hzeros j hj
        have hindex : 1 + j = i := by
          dsimp [j]
          omega
        rw [hindex] at hz
        exact (hzeroIff i).mp hz
      have hvpos : 1 ≤ deficitAt d (n - 1) := by
        rcases hright with hend | ⟨_, hvalue⟩
        · omega
        · have hne : 1 + (n - 2) ≠ 0 := by omega
          rw [hmap, if_neg hne] at hvalue
          have hindex : 1 + (n - 2) = n - 1 := by omega
          simp only [hindex] at hvalue
          omega
      have hvlt : deficitAt d (n - 1) < n := by
        rw [deficitAt_eq_get d (n - 1) (by omega)]
        exact hlegal.entries_lt _ (List.get_mem _ _)
      have hvlarge : n - 1 ≤ deficitAt d (n - 1) := by
        by_contra hsmall
        apply hordinary
        refine ⟨hnle, hzerosOld, hvpos, ?_⟩
        omega
      have hleftNew : deficitAt (leftSurgeryCaseA d) 0 = 1 := by
        rw [hmap, if_pos rfl]
      have hrightNew :
          deficitAt (leftSurgeryCaseA d) (1 + (n - 2)) =
            deficitAt d (n - 1) := by
        rw [hmap, if_neg (by omega)]
        congr 1
        omega
      rw [hleftNew, hrightNew]
      omega
    · have hsource := hlegal.rule3 start hOldBlock
        hleftIndex (by simpa using hrightIndex)
      have hleftNe : start - 1 ≠ 0 := by omega
      have hrightNe : start + (n - 2) ≠ 0 := by omega
      rw [hmap, if_neg hleftNe, hmap, if_neg hrightNe]
      exact hsource

/-- Legality of the literal B1 replacement
`(a,0^(n-2),v,...) ↦ (0^(n-2),1,v,...)`, where TeX positions
`1,...,n-1` are zero-based indices `0,...,n-2`. -/
theorem leftSurgeryCaseB1_legal {n : ℕ} {d : List ℕ}
    (hlegal : IsLegalDeficitSequence n d)
    (hnlen : n ≤ d.length)
    (hfirst : 2 ≤ deficitAt d 0)
    (hzeros : ∀ i, 1 ≤ i → i ≤ n - 2 → deficitAt d i = 0)
    (hv : 2 ≤ deficitAt d (n - 1)) :
    IsLegalDeficitSequence n (leftSurgeryCaseB1 n d) := by
  have hn := hlegal.six_le
  have hlen0 : 0 < d.length := by omega
  have hj : n - 2 < d.length := by omega
  have hj0 : n - 2 ≠ 0 := by omega
  have hvIndex : n - 1 < d.length := by omega
  have hmap (i : ℕ) :
      deficitAt (leftSurgeryCaseB1 n d) i =
        if i = n - 2 then 1 else if i = 0 then 0 else deficitAt d i := by
    unfold leftSurgeryCaseB1
    rw [deficitAt_set (d.set 0 0) (n - 2) 1 i (by simpa)]
    rw [deficitAt_set d 0 0 i hlen0]
  have hnewJ : deficitAt (leftSurgeryCaseB1 n d) (n - 2) = 1 := by
    rw [hmap, if_pos rfl]
  have hnewZero : deficitAt (leftSurgeryCaseB1 n d) 0 = 0 := by
    rw [hmap, if_neg (Ne.symm hj0), if_pos rfl]
  have hnewV : deficitAt (leftSurgeryCaseB1 n d) (n - 1) =
      deficitAt d (n - 1) := by
    rw [hmap, if_neg (by omega), if_neg (by omega)]
  have hnotAllNew : ¬ ∀ x ∈ leftSurgeryCaseB1 n d, x = 0 := by
    intro hall
    have honeMem : 1 ∈ leftSurgeryCaseB1 n d := by
      unfold leftSurgeryCaseB1
      exact List.mem_set (by simpa) 1
    have := hall 1 honeMem
    omega
  refine {
    six_le := hn
    nonempty := by
      intro hnil
      have hlength := congrArg List.length hnil
      simp at hlength
      apply hlegal.nonempty
      exact hlength
    entries_lt := ?_
    rule1 := ?_
    rule2 := ?_
    rule3 := ?_ }
  · intro x hx
    unfold leftSurgeryCaseB1 at hx
    rcases List.mem_or_eq_of_mem_set hx with hxfirst | rfl
    · rcases List.mem_or_eq_of_mem_set hxfirst with hxold | rfl
      · exact hlegal.entries_lt x hxold
      · omega
    · omega
  · simp only [if_neg hnotAllNew]
    intro start blockLength hblock
    rcases hblock with ⟨hpos, hwithin, hblockZeros, hleft, hright⟩
    by_cases hstart0 : start = 0
    · subst start
      by_contra hlarge
      have hjBlock : n - 2 < blockLength := by omega
      have hz := hblockZeros (n - 2) hjBlock
      simp only [Nat.zero_add] at hz
      omega
    · have hstartLarge : n ≤ start := by
        have hleftPos : 0 < deficitAt (leftSurgeryCaseB1 n d) (start - 1) := by
          rcases hleft with hzero | ⟨_, hvalue⟩
          · contradiction
          · exact hvalue
        by_contra hsmall
        by_cases heq : start = n - 1
        · have hz := hblockZeros 0 hpos
          simp only [Nat.add_zero] at hz
          rw [heq, hnewV] at hz
          omega
        · have hindex : start - 1 ≤ n - 2 := by omega
          by_cases hpred0 : start - 1 = 0
          · rw [hpred0, hnewZero] at hleftPos
            omega
          · have hpred1 : 1 ≤ start - 1 := by omega
            have holdZero := hzeros (start - 1) hpred1 hindex
            have hpredJ : start - 1 ≠ n - 2 := by omega
            rw [hmap, if_neg hpredJ, if_neg hpred0, holdZero] at hleftPos
            omega
      have hOldBlock : IsMaximalZeroBlock d start blockLength := by
        refine ⟨hpos, by simpa using hwithin, ?_, ?_, ?_⟩
        · intro j' hj'
          have hidx0 : start + j' ≠ 0 := by omega
          have hidxJ : start + j' ≠ n - 2 := by omega
          have hz := hblockZeros j' hj'
          rw [hmap, if_neg hidxJ, if_neg hidx0] at hz
          exact hz
        · rcases hleft with hzero | ⟨hidx, hvalue⟩
          · exact Or.inl hzero
          · right
            refine ⟨hidx, ?_⟩
            have hpred0 : start - 1 ≠ 0 := by omega
            have hpredJ : start - 1 ≠ n - 2 := by omega
            rw [hmap, if_neg hpredJ, if_neg hpred0] at hvalue
            exact hvalue
        · rcases hright with hend | ⟨hidx, hvalue⟩
          · exact Or.inl (by simpa using hend)
          · right
            refine ⟨by simpa using hidx, ?_⟩
            have hafter0 : start + blockLength ≠ 0 := by omega
            have hafterJ : start + blockLength ≠ n - 2 := by omega
            rw [hmap, if_neg hafterJ, if_neg hafter0] at hvalue
            exact hvalue
      have hnotAllOld : ¬ ∀ x ∈ d, x = 0 := by
        intro hall
        have hmem : deficitAt d 0 ∈ d := by
          rw [deficitAt_eq_get d 0 hlen0]
          exact List.get_mem _ _
        have := hall _ hmem
        omega
      have hrule : ∀ s ell, IsMaximalZeroBlock d s ell → ell ≤ n - 2 := by
        simpa [hnotAllOld] using hlegal.rule1
      exact hrule start blockLength hOldBlock
  · intro i hi hpattern
    rcases hpattern with ⟨hz, hone, hsmall⟩
    by_cases hi0 : i = 0
    · subst i
      have hmiddle : deficitAt (leftSurgeryCaseB1 n d) 1 = 0 := by
        rw [hmap, if_neg (by omega), if_neg (by omega)]
        exact hzeros 1 (by omega) (by omega)
      simp [hmiddle] at hone
    · by_cases hiJ : i = n - 2
      · rw [hiJ, hnewJ] at hz
        omega
      · by_cases hi1J : i + 1 = n - 2
        · have hthird : deficitAt (leftSurgeryCaseB1 n d) (i + 2) =
              deficitAt d (n - 1) := by
            have hidx : i + 2 = n - 1 := by omega
            rw [hidx, hnewV]
          rw [hthird] at hsmall
          omega
        · by_cases hi2J : i + 2 = n - 2
          · have hmiddleZero : deficitAt (leftSurgeryCaseB1 n d) (i + 1) = 0 := by
              rw [hmap, if_neg (by omega), if_neg (by omega)]
              apply hzeros (i + 1) (by omega) (by omega)
            rw [hmiddleZero] at hone
            omega
          · have hi1Zero : i + 1 ≠ 0 := by omega
            have hi2Zero : i + 2 ≠ 0 := by omega
            apply hlegal.rule2 i (by simpa using hi)
            rw [hmap, if_neg hiJ, if_neg hi0] at hz
            rw [hmap, if_neg hi1J, if_neg hi1Zero] at hone
            rw [hmap, if_neg hi2J, if_neg hi2Zero] at hsmall
            exact ⟨hz, hone, hsmall⟩
  · intro start hblock hleftIndex hrightIndex
    rcases hblock with ⟨hpos, hwithin, hblockZeros, hleft, hright⟩
    have hstartLarge : n ≤ start := by
      have hstart0 : start ≠ 0 := by omega
      have hleftPos : 0 < deficitAt (leftSurgeryCaseB1 n d) (start - 1) := by
        rcases hleft with hzero | ⟨_, hvalue⟩
        · contradiction
        · exact hvalue
      by_contra hsmall
      by_cases heq : start = n - 1
      · have hz := hblockZeros 0 (by omega)
        simp only [Nat.add_zero] at hz
        rw [heq, hnewV] at hz
        omega
      · have hindex : start - 1 ≤ n - 2 := by omega
        by_cases hpred0 : start - 1 = 0
        · rw [hpred0, hnewZero] at hleftPos
          omega
        · have hpred1 : 1 ≤ start - 1 := by omega
          have holdZero := hzeros (start - 1) hpred1 hindex
          have hpredJ : start - 1 ≠ n - 2 := by omega
          rw [hmap, if_neg hpredJ, if_neg hpred0, holdZero] at hleftPos
          omega
    have hOldBlock : IsMaximalZeroBlock d start (n - 2) := by
      refine ⟨hpos, by simpa using hwithin, ?_, ?_, ?_⟩
      · intro j' hj'
        have hidx0 : start + j' ≠ 0 := by omega
        have hidxJ : start + j' ≠ n - 2 := by omega
        have hz := hblockZeros j' hj'
        rw [hmap, if_neg hidxJ, if_neg hidx0] at hz
        exact hz
      · rcases hleft with hzero | ⟨hidx, hvalue⟩
        · exact Or.inl hzero
        · right
          refine ⟨hidx, ?_⟩
          have hpred0 : start - 1 ≠ 0 := by omega
          have hpredJ : start - 1 ≠ n - 2 := by omega
          rw [hmap, if_neg hpredJ, if_neg hpred0] at hvalue
          exact hvalue
      · rcases hright with hend | ⟨hidx, hvalue⟩
        · exact Or.inl (by simpa using hend)
        · right
          refine ⟨by simpa using hidx, ?_⟩
          have hafter0 : start + (n - 2) ≠ 0 := by omega
          have hafterJ : start + (n - 2) ≠ n - 2 := by omega
          rw [hmap, if_neg hafterJ, if_neg hafter0] at hvalue
          exact hvalue
    have hsource := hlegal.rule3 start hOldBlock
      hleftIndex (by simpa using hrightIndex)
    have hleft0 : start - 1 ≠ 0 := by omega
    have hleftJ : start - 1 ≠ n - 2 := by omega
    have hright0 : start + (n - 2) ≠ 0 := by omega
    have hrightJ : start + (n - 2) ≠ n - 2 := by omega
    rw [hmap, if_neg hleftJ, if_neg hleft0,
      hmap, if_neg hrightJ, if_neg hright0]
    exact hsource

/-- Exact B1 total bookkeeping. -/
theorem leftSurgeryCaseB1_total {n D : ℕ} {d : List ℕ}
    (hn : 6 ≤ n) (hnlen : n ≤ d.length)
    (hfirst : 2 ≤ deficitAt d 0)
    (htotal : deficitSequenceTotal d = D)
    (hzeros : ∀ i, 1 ≤ i → i ≤ n - 2 → deficitAt d i = 0) :
    deficitSequenceTotal (leftSurgeryCaseB1 n d) +
        (deficitAt d 0 - 1) = D := by
  have hlen0 : 0 < d.length := by omega
  have hj : n - 2 < d.length := by omega
  have hfirstBalance := sum_set_balance (d := d) (j := 0) (x := 0)
    (old := deficitAt d 0) hlen0 rfl
  have hjOld : deficitAt d (n - 2) = 0 := hzeros _ (by omega) (by omega)
  have hjAfter : deficitAt (d.set 0 0) (n - 2) = 0 := by
    rw [deficitAt_set_of_ne d 0 0 (n - 2) hlen0 (by omega), hjOld]
  have hsecondBalance := sum_set_balance (d := d.set 0 0)
    (j := n - 2) (x := 1) (old := 0) (by simpa) hjAfter
  simp only [deficitSequenceTotal, leftSurgeryCaseB1]
  simp only [deficitSequenceTotal] at htotal
  omega

/-- In literal Case B2, R3 forces the first entry to be exactly `n-1`.
This is the arithmetic step that makes the drop exactly `n-3`. -/
theorem leftSurgeryCaseB2_first_eq {n : ℕ} {d : List ℕ}
    (hlegal : IsLegalDeficitSequence n d)
    (hnlen : n ≤ d.length)
    (hfirst : 2 ≤ deficitAt d 0)
    (hzeros : ∀ i, 1 ≤ i → i ≤ n - 2 → deficitAt d i = 0)
    (hv : deficitAt d (n - 1) = 1) :
    deficitAt d 0 = n - 1 := by
  have hn := hlegal.six_le
  have hblock : IsMaximalZeroBlock d 1 (n - 2) := by
    refine ⟨by omega, by omega, ?_, ?_, ?_⟩
    · intro j hj
      apply hzeros (1 + j) (by omega) (by omega)
    · right
      refine ⟨by omega, ?_⟩
      simpa using (show 0 < deficitAt d 0 by omega)
    · right
      refine ⟨by omega, ?_⟩
      have hindex : 1 + (n - 2) = n - 1 := by omega
      simp [hindex, hv]
  have hrule := hlegal.rule3 1 hblock (by omega) (by omega)
  have hfirstLt : deficitAt d 0 < n := by
    rw [deficitAt_eq_get d 0 (by omega)]
    exact hlegal.entries_lt _ (List.get_mem _ _)
  have hindex : 1 + (n - 2) = n - 1 := by omega
  have hrule' : n ≤ deficitAt d 0 + 1 := by
    simpa [hindex, hv] using hrule
  omega

/-- Legality of the literal B2 replacement
`(n-1,0^(n-2),1,...) ↦ (0^(n-3),2,0,1,...)`. -/
theorem leftSurgeryCaseB2_legal {n : ℕ} {d : List ℕ}
    (hlegal : IsLegalDeficitSequence n d)
    (hnlen : n ≤ d.length)
    (hfirst : 2 ≤ deficitAt d 0)
    (hzeros : ∀ i, 1 ≤ i → i ≤ n - 2 → deficitAt d i = 0)
    (hv : deficitAt d (n - 1) = 1) :
    IsLegalDeficitSequence n (leftSurgeryCaseB2 n d) := by
  have hn := hlegal.six_le
  have hlen0 : 0 < d.length := by omega
  have hj : n - 3 < d.length := by omega
  have hj0 : n - 3 ≠ 0 := by omega
  have hmap (i : ℕ) :
      deficitAt (leftSurgeryCaseB2 n d) i =
        if i = n - 3 then 2 else if i = 0 then 0 else deficitAt d i := by
    unfold leftSurgeryCaseB2
    rw [deficitAt_set (d.set 0 0) (n - 3) 2 i (by simpa)]
    rw [deficitAt_set d 0 0 i hlen0]
  have hnewJ : deficitAt (leftSurgeryCaseB2 n d) (n - 3) = 2 := by
    rw [hmap, if_pos rfl]
  have hnewZero : deficitAt (leftSurgeryCaseB2 n d) 0 = 0 := by
    rw [hmap, if_neg (Ne.symm hj0), if_pos rfl]
  have hnewPenultimate :
      deficitAt (leftSurgeryCaseB2 n d) (n - 2) = 0 := by
    rw [hmap, if_neg (by omega), if_neg (by omega)]
    exact hzeros _ (by omega) (by omega)
  have hnewV : deficitAt (leftSurgeryCaseB2 n d) (n - 1) = 1 := by
    rw [hmap, if_neg (by omega), if_neg (by omega), hv]
  have hnotAllNew : ¬ ∀ x ∈ leftSurgeryCaseB2 n d, x = 0 := by
    intro hall
    have htwoMem : 2 ∈ leftSurgeryCaseB2 n d := by
      unfold leftSurgeryCaseB2
      exact List.mem_set (by simpa) 2
    have := hall 2 htwoMem
    omega
  refine {
    six_le := hn
    nonempty := by
      intro hnil
      have hlength := congrArg List.length hnil
      simp at hlength
      apply hlegal.nonempty
      exact hlength
    entries_lt := ?_
    rule1 := ?_
    rule2 := ?_
    rule3 := ?_ }
  · intro x hx
    unfold leftSurgeryCaseB2 at hx
    rcases List.mem_or_eq_of_mem_set hx with hxfirst | rfl
    · rcases List.mem_or_eq_of_mem_set hxfirst with hxold | rfl
      · exact hlegal.entries_lt x hxold
      · omega
    · omega
  · simp only [if_neg hnotAllNew]
    intro start blockLength hblock
    rcases hblock with ⟨hpos, hwithin, hblockZeros, hleft, hright⟩
    by_cases hstart : n ≤ start
    · have hOldBlock : IsMaximalZeroBlock d start blockLength := by
        refine ⟨hpos, by simpa using hwithin, ?_, ?_, ?_⟩
        · intro j' hj'
          have hidx0 : start + j' ≠ 0 := by omega
          have hidxJ : start + j' ≠ n - 3 := by omega
          have hz := hblockZeros j' hj'
          rw [hmap, if_neg hidxJ, if_neg hidx0] at hz
          exact hz
        · rcases hleft with hzero | ⟨hidx, hvalue⟩
          · exact Or.inl hzero
          · right
            refine ⟨hidx, ?_⟩
            have hpred0 : start - 1 ≠ 0 := by omega
            have hpredJ : start - 1 ≠ n - 3 := by omega
            rw [hmap, if_neg hpredJ, if_neg hpred0] at hvalue
            exact hvalue
        · rcases hright with hend | ⟨hidx, hvalue⟩
          · exact Or.inl (by simpa using hend)
          · right
            refine ⟨by simpa using hidx, ?_⟩
            have hafter0 : start + blockLength ≠ 0 := by omega
            have hafterJ : start + blockLength ≠ n - 3 := by omega
            rw [hmap, if_neg hafterJ, if_neg hafter0] at hvalue
            exact hvalue
      have hnotAllOld : ¬ ∀ x ∈ d, x = 0 := by
        intro hall
        have hmem : deficitAt d 0 ∈ d := by
          rw [deficitAt_eq_get d 0 hlen0]
          exact List.get_mem _ _
        have := hall _ hmem
        omega
      have hrule : ∀ s ell, IsMaximalZeroBlock d s ell → ell ≤ n - 2 := by
        simpa [hnotAllOld] using hlegal.rule1
      exact hrule start blockLength hOldBlock
    · by_contra hlarge
      have hlenLarge : n - 2 < blockLength := by omega
      by_cases hbeforeJ : start ≤ n - 3
      · let off := n - 3 - start
        have hoff : off < blockLength := by
          dsimp [off]
          omega
        have hz := hblockZeros off hoff
        have hidx : start + off = n - 3 := by
          dsimp [off]
          omega
        rw [hidx, hnewJ] at hz
        omega
      · by_cases hstartPenultimate : start = n - 2
        · have hz := hblockZeros 1 (by omega)
          have hidx : start + 1 = n - 1 := by omega
          rw [hidx, hnewV] at hz
          omega
        · have hstartLast : start = n - 1 := by omega
          have hz := hblockZeros 0 hpos
          simp only [Nat.add_zero] at hz
          rw [hstartLast, hnewV] at hz
          omega
  · intro i hi hpattern
    rcases hpattern with ⟨hz, hone, hsmall⟩
    by_cases hi0 : i = 0
    · subst i
      have hmiddle : deficitAt (leftSurgeryCaseB2 n d) 1 = 0 := by
        rw [hmap, if_neg (by omega), if_neg (by omega)]
        exact hzeros 1 (by omega) (by omega)
      rw [hmiddle] at hone
      omega
    · by_cases hiJ : i = n - 3
      · rw [hiJ, hnewJ] at hz
        omega
      · by_cases hi1J : i + 1 = n - 3
        · have hmiddleTwo : deficitAt (leftSurgeryCaseB2 n d) (i + 1) = 2 := by
            rw [hi1J, hnewJ]
          rw [hmiddleTwo] at hone
          omega
        · by_cases hi2J : i + 2 = n - 3
          · have hthirdTwo : deficitAt (leftSurgeryCaseB2 n d) (i + 2) = 2 := by
              rw [hi2J, hnewJ]
            rw [hthirdTwo] at hsmall
            omega
          · have hi1Zero : i + 1 ≠ 0 := by omega
            have hi2Zero : i + 2 ≠ 0 := by omega
            apply hlegal.rule2 i (by simpa using hi)
            rw [hmap, if_neg hiJ, if_neg hi0] at hz
            rw [hmap, if_neg hi1J, if_neg hi1Zero] at hone
            rw [hmap, if_neg hi2J, if_neg hi2Zero] at hsmall
            exact ⟨hz, hone, hsmall⟩
  · intro start hblock hleftIndex hrightIndex
    rcases hblock with ⟨hpos, hwithin, hblockZeros, hleft, hright⟩
    have hstartLarge : n ≤ start := by
      by_contra hsmall
      by_cases hbeforeJ : start ≤ n - 3
      · let off := n - 3 - start
        have hoff : off < n - 2 := by
          dsimp [off]
          omega
        have hz := hblockZeros off hoff
        have hidx : start + off = n - 3 := by
          dsimp [off]
          omega
        rw [hidx, hnewJ] at hz
        omega
      · by_cases hstartPenultimate : start = n - 2
        · have hz := hblockZeros 1 (by omega)
          have hidx : start + 1 = n - 1 := by omega
          rw [hidx, hnewV] at hz
          omega
        · have hstartLast : start = n - 1 := by omega
          have hz := hblockZeros 0 (by omega)
          simp only [Nat.add_zero] at hz
          rw [hstartLast, hnewV] at hz
          omega
    have hOldBlock : IsMaximalZeroBlock d start (n - 2) := by
      refine ⟨hpos, by simpa using hwithin, ?_, ?_, ?_⟩
      · intro j' hj'
        have hidx0 : start + j' ≠ 0 := by omega
        have hidxJ : start + j' ≠ n - 3 := by omega
        have hz := hblockZeros j' hj'
        rw [hmap, if_neg hidxJ, if_neg hidx0] at hz
        exact hz
      · rcases hleft with hzero | ⟨hidx, hvalue⟩
        · exact Or.inl hzero
        · right
          refine ⟨hidx, ?_⟩
          have hpred0 : start - 1 ≠ 0 := by omega
          have hpredJ : start - 1 ≠ n - 3 := by omega
          rw [hmap, if_neg hpredJ, if_neg hpred0] at hvalue
          exact hvalue
      · rcases hright with hend | ⟨hidx, hvalue⟩
        · exact Or.inl (by simpa using hend)
        · right
          refine ⟨by simpa using hidx, ?_⟩
          have hafter0 : start + (n - 2) ≠ 0 := by omega
          have hafterJ : start + (n - 2) ≠ n - 3 := by omega
          rw [hmap, if_neg hafterJ, if_neg hafter0] at hvalue
          exact hvalue
    have hsource := hlegal.rule3 start hOldBlock
      hleftIndex (by simpa using hrightIndex)
    have hleft0 : start - 1 ≠ 0 := by omega
    have hleftJ : start - 1 ≠ n - 3 := by omega
    have hright0 : start + (n - 2) ≠ 0 := by omega
    have hrightJ : start + (n - 2) ≠ n - 3 := by omega
    rw [hmap, if_neg hleftJ, if_neg hleft0,
      hmap, if_neg hrightJ, if_neg hright0]
    exact hsource

/-- Exact B2 total bookkeeping. -/
theorem leftSurgeryCaseB2_total {n D : ℕ} {d : List ℕ}
    (hn : 6 ≤ n) (hnlen : n ≤ d.length)
    (hfirst : 2 ≤ deficitAt d 0)
    (htotal : deficitSequenceTotal d = D)
    (hzeros : ∀ i, 1 ≤ i → i ≤ n - 2 → deficitAt d i = 0) :
    deficitSequenceTotal (leftSurgeryCaseB2 n d) +
        (deficitAt d 0 - 2) = D := by
  have hlen0 : 0 < d.length := by omega
  have hj : n - 3 < d.length := by omega
  have hfirstBalance := sum_set_balance (d := d) (j := 0) (x := 0)
    (old := deficitAt d 0) hlen0 rfl
  have hjOld : deficitAt d (n - 3) = 0 := hzeros _ (by omega) (by omega)
  have hjAfter : deficitAt (d.set 0 0) (n - 3) = 0 := by
    rw [deficitAt_set_of_ne d 0 0 (n - 3) hlen0 (by omega), hjOld]
  have hsecondBalance := sum_set_balance (d := d.set 0 0)
    (j := n - 3) (x := 2) (old := 0) (by simpa) hjAfter
  simp only [deficitSequenceTotal, leftSurgeryCaseB2]
  simp only [deficitSequenceTotal] at htotal
  omega

private theorem leftSurgeryCaseA_total {D : ℕ} {d : List ℕ}
    (hfirst : 2 ≤ deficitAt d 0)
    (htotal : deficitSequenceTotal d = D) :
    deficitSequenceTotal (leftSurgeryCaseA d) +
        (deficitAt d 0 - 1) = D := by
  have hlen0 : 0 < d.length := by
    by_contra h
    have hdnil : d = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst d
    simp [deficitAt] at hfirst
  have hbalance := sum_set_balance (d := d) (j := 0) (x := 1)
    (old := deficitAt d 0) hlen0 rfl
  simp only [deficitSequenceTotal, leftSurgeryCaseA]
  simp only [deficitSequenceTotal] at htotal
  omega

/-- **Left surgery (Lemma `lem:leftsurgery`).**  This is an actual-list
existence theorem.  Its first support clause says that the result agrees
with the source outside zero-based indices `0,...,n-2`; its second says that
when `q≤n-1` it agrees outside index `0` alone. -/
theorem leftSurgery {n q D : ℕ} {d : List ℕ}
    (hn : 6 ≤ n) (hq : 2 ≤ q)
    (hlength : d.length = q)
    (hlegal : IsLegalDeficitSequence n d)
    (htotal : deficitSequenceTotal d = D)
    (hfirst : 2 ≤ deficitAt d 0) :
    ∃ d' : List ℕ,
      d'.length = q ∧
      IsLegalDeficitSequence n d' ∧
      deficitSequenceTotal d' ≤
        D - min (deficitAt d 0 - 1) (n - 3) ∧
      (∀ i, n - 1 ≤ i → deficitAt d' i = deficitAt d i) ∧
      (q ≤ n - 1 →
        ∀ i, i ≠ 0 → deficitAt d' i = deficitAt d i) := by
  by_cases hexceptional : IsLeftExceptionalConfiguration n d
  · rcases hexceptional with
      ⟨hnlen, hzeros, hvpos, hvle⟩
    by_cases hvone : deficitAt d (n - 1) = 1
    · let d' := leftSurgeryCaseB2 n d
      have hfirstEq := leftSurgeryCaseB2_first_eq hlegal hnlen hfirst hzeros hvone
      have hlegal' := leftSurgeryCaseB2_legal hlegal hnlen hfirst hzeros hvone
      have htotal' := leftSurgeryCaseB2_total hn hnlen hfirst htotal hzeros
      refine ⟨d', by simp [d', hlength], hlegal', ?_, ?_, ?_⟩
      · dsimp [d'] at htotal' ⊢
        omega
      · intro i hi
        apply leftSurgeryCaseB2_support (n := n) (d := d)
          (by omega) (by omega) (by omega) (by omega)
      · intro hshort
        exfalso
        omega
    · have hvtwo : 2 ≤ deficitAt d (n - 1) := by omega
      let d' := leftSurgeryCaseB1 n d
      have hlegal' := leftSurgeryCaseB1_legal hlegal hnlen hfirst hzeros hvtwo
      have htotal' := leftSurgeryCaseB1_total hn hnlen hfirst htotal hzeros
      refine ⟨d', by simp [d', hlength], hlegal', ?_, ?_, ?_⟩
      · dsimp [d'] at htotal' ⊢
        omega
      · intro i hi
        apply leftSurgeryCaseB1_support (n := n) (d := d)
          (by omega) (by omega) (by omega) (by omega)
      · intro hshort
        exfalso
        omega
  · let d' := leftSurgeryCaseA d
    have hlegal' := leftSurgeryCaseA_legal hlegal hfirst hexceptional
    have htotal' := leftSurgeryCaseA_total hfirst htotal
    refine ⟨d', by simp [d', hlength], hlegal', ?_, ?_, ?_⟩
    · dsimp [d'] at htotal' ⊢
      omega
    · intro i hi
      apply leftSurgeryCaseA_support
      omega
    · intro _hshort i hi
      exact leftSurgeryCaseA_support hi

/-- Ordinary right surgery: replace the actual last entry by `1`. -/
def rightSurgeryReplaceLast (d : List ℕ) : List ℕ :=
  d.set (d.length - 1) 1

/-- Exceptional trailing-block surgery.  `start` is the zero-based first
index of the trailing zero block of length `n-2`; it is changed to `1`, and
the old last entry is changed to `0`. -/
def rightSurgeryShiftTrailing (d : List ℕ) (start : ℕ) : List ℕ :=
  (d.set start 1).set (d.length - 1) 0

@[simp] theorem rightSurgeryReplaceLast_length (d : List ℕ) :
    (rightSurgeryReplaceLast d).length = d.length := by
  simp [rightSurgeryReplaceLast]

@[simp] theorem rightSurgeryShiftTrailing_length (d : List ℕ) (start : ℕ) :
    (rightSurgeryShiftTrailing d start).length = d.length := by
  simp [rightSurgeryShiftTrailing]

theorem rightSurgeryReplaceLast_support {d : List ℕ} {i : ℕ}
    (hlast : 0 < d.length) (hi : i ≠ d.length - 1) :
    deficitAt (rightSurgeryReplaceLast d) i = deficitAt d i := by
  unfold rightSurgeryReplaceLast
  exact deficitAt_set_of_ne d (d.length - 1) 1 i (by omega) hi

theorem rightSurgeryShiftTrailing_support {d : List ℕ} {start i : ℕ}
    (hlast : 0 < d.length) (hstart : start < d.length)
    (his : i ≠ start) (hilast : i ≠ d.length - 1) :
    deficitAt (rightSurgeryShiftTrailing d start) i = deficitAt d i := by
  unfold rightSurgeryShiftTrailing
  rw [deficitAt_set_of_ne (d.set start 1) (d.length - 1) 0 i
    (by simpa) hilast]
  exact deficitAt_set_of_ne d start 1 i hstart his

private theorem rightSurgeryReplaceLast_total {D b : ℕ} {d : List ℕ}
    (hlast : 0 < d.length)
    (hlastValue : deficitAt d (d.length - 1) = b)
    (hb : 2 ≤ b) (htotal : deficitSequenceTotal d = D) :
    deficitSequenceTotal (rightSurgeryReplaceLast d) + (b - 1) = D := by
  have hbalance := sum_set_balance (d := d) (j := d.length - 1)
    (x := 1) (old := b) (by omega) hlastValue
  simp only [deficitSequenceTotal, rightSurgeryReplaceLast]
  simp only [deficitSequenceTotal] at htotal
  omega

private theorem rightSurgeryShiftTrailing_total {D b : ℕ} {d : List ℕ}
    {start : ℕ} (hlast : 0 < d.length) (hstart : start < d.length)
    (hzero : deficitAt d start = 0)
    (hlastValue : deficitAt d (d.length - 1) = b)
    (hb : 2 ≤ b) (htotal : deficitSequenceTotal d = D)
    (hdistinct : start ≠ d.length - 1) :
    deficitSequenceTotal (rightSurgeryShiftTrailing d start) + (b - 1) = D := by
  have hfirstBalance := sum_set_balance (d := d) (j := start)
    (x := 1) (old := 0) hstart hzero
  have hlastAfter : deficitAt (d.set start 1) (d.length - 1) = b := by
    rw [deficitAt_set_of_ne d start 1 (d.length - 1) hstart
      (Ne.symm hdistinct), hlastValue]
  have hsecondBalance := sum_set_balance (d := d.set start 1)
    (j := d.length - 1) (x := 0) (old := b) (by simpa) hlastAfter
  simp only [deficitSequenceTotal, rightSurgeryShiftTrailing]
  simp only [deficitSequenceTotal] at htotal
  omega

private theorem rightSurgeryReplaceLast_legal {n : ℕ} {d : List ℕ}
    (hlegal : IsLegalDeficitSequence n d)
    (hlength : 2 ≤ d.length)
    (hlastPos : 0 < deficitAt d (d.length - 1))
    (hrule2 : ∀ i, i + 2 = d.length - 1 →
      ¬(deficitAt d i = 0 ∧ deficitAt d (i + 1) = 1))
    (hrule3 : ∀ start,
      IsMaximalZeroBlock d start (n - 2) →
      0 < start → start + (n - 2) = d.length - 1 →
      n ≤ deficitAt d (start - 1) + 1) :
    IsLegalDeficitSequence n (rightSurgeryReplaceLast d) := by
  have hn := hlegal.six_le
  have hlastIndex : d.length - 1 < d.length := by omega
  have hnewLength : (rightSurgeryReplaceLast d).length = d.length := by simp
  let last := d.length - 1
  have hmap (i : ℕ) :
      deficitAt (rightSurgeryReplaceLast d) i =
        if i = last then 1 else deficitAt d i := by
    unfold rightSurgeryReplaceLast
    exact deficitAt_set d (d.length - 1) 1 i hlastIndex
  have hzeroIff (i : ℕ) :
      deficitAt (rightSurgeryReplaceLast d) i = 0 ↔ deficitAt d i = 0 := by
    rw [hmap]
    by_cases hi : i = last
    · subst i
      simp [last]
      omega
    · simp [hi]
  have hnotAllOld : ¬ ∀ x ∈ d, x = 0 := by
    intro hall
    have hmem : deficitAt d (d.length - 1) ∈ d := by
      rw [deficitAt_eq_get d (d.length - 1) hlastIndex]
      exact List.get_mem _ _
    have := hall _ hmem
    omega
  have hnotAllNew : ¬ ∀ x ∈ rightSurgeryReplaceLast d, x = 0 := by
    intro hall
    have honeMem : 1 ∈ rightSurgeryReplaceLast d := by
      unfold rightSurgeryReplaceLast
      exact List.mem_set hlastIndex 1
    have := hall 1 honeMem
    omega
  refine {
    six_le := hn
    nonempty := by
      intro hnil
      have hlen := congrArg List.length hnil
      simp at hlen
      apply hlegal.nonempty
      exact hlen
    entries_lt := ?_
    rule1 := ?_
    rule2 := ?_
    rule3 := ?_ }
  · intro x hx
    unfold rightSurgeryReplaceLast at hx
    rcases List.mem_or_eq_of_mem_set hx with hxold | rfl
    · exact hlegal.entries_lt x hxold
    · omega
  · simp only [if_neg hnotAllNew]
    intro start blockLength hblock
    rcases hblock with ⟨hpos, hwithin, hzeros, hleft, hright⟩
    have hOldBlock : IsMaximalZeroBlock d start blockLength := by
      refine ⟨hpos, by simpa using hwithin, ?_, ?_, ?_⟩
      · intro j hj
        exact (hzeroIff (start + j)).mp (hzeros j hj)
      · rcases hleft with hstart | ⟨hstart, hvalue⟩
        · exact Or.inl hstart
        · right
          refine ⟨hstart, ?_⟩
          have hne : start - 1 ≠ last := by
            dsimp [last]
            rw [hnewLength] at hwithin
            omega
          rw [hmap, if_neg hne] at hvalue
          exact hvalue
      · rcases hright with hend | ⟨hidx, hvalue⟩
        · exact Or.inl (by simpa using hend)
        · right
          refine ⟨by simpa using hidx, ?_⟩
          by_cases heq : start + blockLength = last
          · have heq' : start + blockLength = d.length - 1 := by
              simpa [last] using heq
            rw [heq']
            exact hlastPos
          · rw [hmap, if_neg heq] at hvalue
            exact hvalue
    have hrule : ∀ s ell, IsMaximalZeroBlock d s ell → ell ≤ n - 2 := by
      simpa [hnotAllOld] using hlegal.rule1
    exact hrule start blockLength hOldBlock
  · intro i hi hpattern
    rcases hpattern with ⟨hz, hone, hsmall⟩
    by_cases hthird : i + 2 = last
    · have hfirstNe : i ≠ last := by omega
      have hmiddleNe : i + 1 ≠ last := by omega
      have hforbid := hrule2 i (by simpa [last] using hthird)
      apply hforbid
      rw [hmap, if_neg hfirstNe] at hz
      rw [hmap, if_neg hmiddleNe] at hone
      exact ⟨hz, hone⟩
    · have hfirstNe : i ≠ last := by
        dsimp [last]
        rw [hnewLength] at hi
        omega
      have hmiddleNe : i + 1 ≠ last := by
        dsimp [last]
        rw [hnewLength] at hi
        omega
      apply hlegal.rule2 i (by simpa using hi)
      rw [hmap, if_neg hfirstNe] at hz
      rw [hmap, if_neg hmiddleNe] at hone
      rw [hmap, if_neg hthird] at hsmall
      exact ⟨hz, hone, hsmall⟩
  · intro start hblock hleftIndex hrightIndex
    rcases hblock with ⟨hpos, hwithin, hzeros, hleft, hright⟩
    have hOldBlock : IsMaximalZeroBlock d start (n - 2) := by
      refine ⟨hpos, by simpa using hwithin, ?_, ?_, ?_⟩
      · intro j hj
        exact (hzeroIff (start + j)).mp (hzeros j hj)
      · rcases hleft with hstart | ⟨hstart, hvalue⟩
        · exact Or.inl hstart
        · right
          refine ⟨hstart, ?_⟩
          have hne : start - 1 ≠ last := by
            dsimp [last]
            rw [hnewLength] at hwithin
            omega
          rw [hmap, if_neg hne] at hvalue
          exact hvalue
      · rcases hright with hend | ⟨hidx, hvalue⟩
        · exact Or.inl (by simpa using hend)
        · right
          refine ⟨by simpa using hidx, ?_⟩
          by_cases heq : start + (n - 2) = last
          · have heq' : start + (n - 2) = d.length - 1 := by
              simpa [last] using heq
            rw [heq']
            exact hlastPos
          · rw [hmap, if_neg heq] at hvalue
            exact hvalue
    by_cases hrightLast : start + (n - 2) = last
    · have hbound := hrule3 start hOldBlock hleftIndex
        (by simpa [last] using hrightLast)
      have hleftNe : start - 1 ≠ last := by
        dsimp [last]
        rw [hnewLength] at hwithin
        omega
      rw [hmap, if_neg hleftNe, hmap, if_pos hrightLast]
      exact hbound
    · have hsource := hlegal.rule3 start hOldBlock hleftIndex
        (by simpa using hrightIndex)
      have hleftNe : start - 1 ≠ last := by
        dsimp [last]
        rw [hnewLength] at hwithin
        omega
      rw [hmap, if_neg hleftNe, hmap, if_neg hrightLast]
      exact hsource

private theorem rightSurgeryShiftTrailing_legal {n : ℕ} {d : List ℕ}
    {start : ℕ} (hlegal : IsLegalDeficitSequence n d)
    (hlength : 2 ≤ d.length)
    (hstart : 0 < start)
    (hblock : IsMaximalZeroBlock d start (n - 2))
    (hend : start + (n - 2) = d.length - 1)
    (hlastPos : 0 < deficitAt d (d.length - 1)) :
    IsLegalDeficitSequence n (rightSurgeryShiftTrailing d start) := by
  have hn := hlegal.six_le
  rcases hblock with ⟨hmuPos, hblockWithin, htailZeros, htailLeft, htailRight⟩
  have hstartIndex : start < d.length := by omega
  have hlastIndex : d.length - 1 < d.length := by omega
  have hdistinct : start ≠ d.length - 1 := by omega
  have hleftPos : 0 < deficitAt d (start - 1) := by
    rcases htailLeft with hzero | ⟨_, hpos⟩
    · omega
    · exact hpos
  have hnewLength : (rightSurgeryShiftTrailing d start).length = d.length := by
    simp
  have hmap (i : ℕ) :
      deficitAt (rightSurgeryShiftTrailing d start) i =
        if i = d.length - 1 then 0
        else if i = start then 1 else deficitAt d i := by
    unfold rightSurgeryShiftTrailing
    rw [deficitAt_set (d.set start 1) (d.length - 1) 0 i
      (by simpa using hlastIndex)]
    rw [deficitAt_set d start 1 i hstartIndex]
  have hnewStart : deficitAt (rightSurgeryShiftTrailing d start) start = 1 := by
    rw [hmap, if_neg hdistinct, if_pos rfl]
  have hnewLast : deficitAt (rightSurgeryShiftTrailing d start)
      (d.length - 1) = 0 := by
    rw [hmap, if_pos rfl]
  have htailNew : ∀ i, start + 1 ≤ i → i ≤ d.length - 1 →
      deficitAt (rightSurgeryShiftTrailing d start) i = 0 := by
    intro i hiLower hiUpper
    by_cases hiLast : i = d.length - 1
    · rw [hiLast, hnewLast]
    · have hiStart : i ≠ start := by omega
      rw [hmap, if_neg hiLast, if_neg hiStart]
      let j := i - start
      have hj : j < n - 2 := by
        dsimp [j]
        omega
      have hzero := htailZeros j hj
      have hindex : start + j = i := by
        dsimp [j]
        omega
      simpa [hindex] using hzero
  have hnotAllOld : ¬ ∀ x ∈ d, x = 0 := by
    intro hall
    have hmem : deficitAt d (d.length - 1) ∈ d := by
      rw [deficitAt_eq_get d (d.length - 1) hlastIndex]
      exact List.get_mem _ _
    have := hall _ hmem
    omega
  have hnotAllNew : ¬ ∀ x ∈ rightSurgeryShiftTrailing d start, x = 0 := by
    intro hall
    have honeMem : 1 ∈ rightSurgeryShiftTrailing d start := by
      have hget := hnewStart
      rw [deficitAt_eq_get _ start (by simpa using hstartIndex)] at hget
      rw [← hget]
      exact List.get_mem _ _
    have := hall 1 honeMem
    omega
  refine {
    six_le := hn
    nonempty := by
      intro hnil
      have hlen := congrArg List.length hnil
      simp at hlen
      apply hlegal.nonempty
      exact hlen
    entries_lt := ?_
    rule1 := ?_
    rule2 := ?_
    rule3 := ?_ }
  · intro x hx
    unfold rightSurgeryShiftTrailing at hx
    rcases List.mem_or_eq_of_mem_set hx with hxfirst | rfl
    · rcases List.mem_or_eq_of_mem_set hxfirst with hxold | rfl
      · exact hlegal.entries_lt x hxold
      · omega
    · omega
  · simp only [if_neg hnotAllNew]
    intro blockStart blockLength hmax
    rcases hmax with ⟨hpos, hwithin, hzeros, hleft, hright⟩
    rcases hright with hendNew | ⟨hrightIndex, hrightPos⟩
    · by_contra hlarge
      have hlenLarge : n - 2 < blockLength := by omega
      let off := start - blockStart
      have hoff : off < blockLength := by
        dsimp [off]
        rw [hnewLength] at hendNew
        omega
      have hindex : blockStart + off = start := by
        dsimp [off]
        rw [hnewLength] at hendNew
        omega
      have hz := hzeros off hoff
      rw [hindex, hnewStart] at hz
      omega
    · have havoidStart : ∀ j, j < blockLength → blockStart + j ≠ start := by
        intro j hj heq
        have hz := hzeros j hj
        rw [heq, hnewStart] at hz
        omega
      have havoidLast : ∀ j, j < blockLength →
          blockStart + j ≠ d.length - 1 := by
        intro j hj
        rw [hnewLength] at hwithin
        omega
      have hzerosOld : ∀ j, j < blockLength →
          deficitAt d (blockStart + j) = 0 := by
        intro j hj
        have hz := hzeros j hj
        rw [hmap, if_neg (havoidLast j hj), if_neg (havoidStart j hj)] at hz
        exact hz
      exact (legal_zeroInterval_bounds hlegal hpos
        (by simpa using hwithin) hzerosOld).2 hnotAllOld
  · intro i hi hpattern
    rcases hpattern with ⟨hz, hone, hsmall⟩
    by_cases hthirdLast : i + 2 = d.length - 1
    · have hiLower : start + 1 ≤ i + 1 := by omega
      have hmiddleZero := htailNew (i + 1) hiLower (by omega)
      rw [hmiddleZero] at hone
      omega
    · by_cases hiStart : i = start
      · rw [hiStart, hnewStart] at hz
        omega
      · by_cases hi1Start : i + 1 = start
        · have hfirstEq : deficitAt (rightSurgeryShiftTrailing d start) i =
              deficitAt d (start - 1) := by
            have hiEq : i = start - 1 := by omega
            rw [hiEq, hmap, if_neg (by omega), if_neg (by omega)]
          rw [hfirstEq] at hz
          omega
        · by_cases hi2Start : i + 2 = start
          · have hfirstLast : i ≠ d.length - 1 := by omega
            have hmiddleLast : i + 1 ≠ d.length - 1 := by omega
            apply hlegal.rule2 i (by rw [hnewLength] at hi; omega)
            rw [hmap, if_neg hfirstLast, if_neg hiStart] at hz
            rw [hmap, if_neg hmiddleLast, if_neg hi1Start] at hone
            have holdThird : deficitAt d (i + 2) = 0 := by
              rw [hi2Start]
              exact htailZeros 0 (by omega)
            exact ⟨hz, hone, by omega⟩
          · have hfirstLast : i ≠ d.length - 1 := by omega
            have hmiddleLast : i + 1 ≠ d.length - 1 := by omega
            apply hlegal.rule2 i (by rw [hnewLength] at hi; omega)
            rw [hmap, if_neg hfirstLast, if_neg hiStart] at hz
            rw [hmap, if_neg hmiddleLast, if_neg hi1Start] at hone
            rw [hmap, if_neg hthirdLast, if_neg hi2Start] at hsmall
            exact ⟨hz, hone, hsmall⟩
  · intro blockStart hmax hleftIndex hrightIndex
    rcases hmax with ⟨hpos, hwithin, hzeros, hleft, hright⟩
    have havoidLast : ∀ j, j < n - 2 →
        blockStart + j ≠ d.length - 1 := by
      intro j hj
      rw [hnewLength] at hrightIndex
      omega
    have havoidStart : ∀ j, j < n - 2 →
        blockStart + j ≠ start := by
      intro j hj heq
      have hz := hzeros j hj
      rw [heq, hnewStart] at hz
      omega
    have hOldBlock : IsMaximalZeroBlock d blockStart (n - 2) := by
      refine ⟨hpos, by simpa using hwithin, ?_, ?_, ?_⟩
      · intro j hj
        have hz := hzeros j hj
        rw [hmap, if_neg (havoidLast j hj), if_neg (havoidStart j hj)] at hz
        exact hz
      · rcases hleft with hzero | ⟨hidx, hvalue⟩
        · exact Or.inl hzero
        · right
          refine ⟨hidx, ?_⟩
          have hpredLast : blockStart - 1 ≠ d.length - 1 := by
            rw [hnewLength] at hwithin
            omega
          by_cases hpredStart : blockStart - 1 = start
          · have hblockStartEq : blockStart = start + 1 := by omega
            rw [hnewLength] at hrightIndex
            omega
          · rw [hmap, if_neg hpredLast, if_neg hpredStart] at hvalue
            exact hvalue
      · rcases hright with hendNew | ⟨hidx, hvalue⟩
        · exact Or.inl (by simpa using hendNew)
        · right
          refine ⟨by simpa using hidx, ?_⟩
          have hafterLast : blockStart + (n - 2) ≠ d.length - 1 := by
            intro heq
            rw [heq, hnewLast] at hvalue
            omega
          by_cases hafterStart : blockStart + (n - 2) = start
          · have hlastZero : deficitAt d (start - 1) = 0 := by
              have hj : n - 3 < n - 2 := by omega
              have hz := hzeros (n - 3) hj
              have hidxEq : blockStart + (n - 3) = start - 1 := by omega
              rw [hmap, if_neg (by omega), if_neg (by omega)] at hz
              simpa [hidxEq] using hz
            omega
          · rw [hmap, if_neg hafterLast, if_neg hafterStart] at hvalue
            exact hvalue
    have hsource := hlegal.rule3 blockStart hOldBlock
      hleftIndex (by simpa using hrightIndex)
    have hleftLast : blockStart - 1 ≠ d.length - 1 := by
      rw [hnewLength] at hwithin
      omega
    have hleftStart : blockStart - 1 ≠ start := by
      intro heq
      rw [hnewLength] at hrightIndex
      omega
    have hrightLast : blockStart + (n - 2) ≠ d.length - 1 := by
      intro heq
      rcases hright with hendNew | ⟨_, hvalue⟩
      · rw [hnewLength] at hendNew
        omega
      · rw [heq, hnewLast] at hvalue
        omega
    have hrightStart : blockStart + (n - 2) ≠ start := by
      intro heq
      have hlastZero : deficitAt d (start - 1) = 0 := by
        have hj : n - 3 < n - 2 := by omega
        have hz := hzeros (n - 3) hj
        have hidxEq : blockStart + (n - 3) = start - 1 := by omega
        rw [hmap, if_neg (by omega), if_neg (by omega)] at hz
        simpa [hidxEq] using hz
      omega
    rw [hmap, if_neg hleftLast, if_neg hleftStart,
      hmap, if_neg hrightLast, if_neg hrightStart]
    exact hsource

private theorem prefix_before_terminal_zero_one_total {q D b : ℕ}
    {d : List ℕ} (hq : 3 ≤ q) (hlength : d.length = q)
    (htotal : deficitSequenceTotal d = D)
    (hzero : deficitAt d (q - 3) = 0)
    (hone : deficitAt d (q - 2) = 1)
    (hlast : deficitAt d (q - 1) = b) :
    deficitSequenceTotal (d.take (q - 2)) + 1 + b = D := by
  have hprevIndex : q - 2 < d.length := by omega
  have hlastIndex : q - 1 < d.length := by omega
  have hprevGet : d[q - 2] = 1 := by
    rw [deficitAt_eq_get d (q - 2) hprevIndex] at hone
    exact hone
  have hlastGet : d[q - 1] = b := by
    rw [deficitAt_eq_get d (q - 1) hlastIndex] at hlast
    exact hlast
  have hdne : d ≠ [] := by
    intro hd
    subst d
    simp at hlength
    omega
  have hdropLast := List.drop_length_sub_one hdne
  have hlastSub : d.length - 1 = q - 1 := by omega
  rw [hlastSub] at hdropLast
  have hdrop : d.drop (q - 2) = [1, b] := by
    rw [List.drop_eq_getElem_cons hprevIndex, hprevGet]
    have hnext : q - 2 + 1 = q - 1 := by omega
    rw [hnext, hdropLast]
    have hgetLast : d.getLast hdne = b := by
      rw [List.getLast_eq_getElem]
      simpa [hlastSub] using hlastGet
    rw [hgetLast]
  have hsplit := List.sum_take_add_sum_drop d (q - 2)
  rw [hdrop] at hsplit
  simp only [deficitSequenceTotal] at htotal ⊢
  simp at hsplit
  omega

/-- **Right surgery (Lemma `lem:rightsurgery`).**  For an actual legal
length-`q` list with actual final entry `b≥2`, the subtraction-safe form of
`D ≥ φ_n(q)+b-1` is `φ_n(q)+(b-1) ≤ D`.  The proof contains the
ordinary predecessor case (including `q=2`), the terminal `(0,1,b)` prefix
case, every shorter trailing-zero case, and both variants of the exact
length-`n-2` trailing block. -/
theorem rightSurgery {n q D b : ℕ} {d : List ℕ}
    (hn : 6 ≤ n) (hq : 2 ≤ q)
    (hlength : d.length = q)
    (hlegal : IsLegalDeficitSequence n d)
    (htotal : deficitSequenceTotal d = D)
    (hlast : deficitAt d (q - 1) = b)
    (hb : 2 ≤ b) :
    phiN n q hn (by omega) + (b - 1) ≤ D := by
  have hlastIndex : q - 1 < d.length := by omega
  have hlastPos : 0 < deficitAt d (d.length - 1) := by
    have hindex : d.length - 1 = q - 1 := by omega
    rw [hindex, hlast]
    omega
  have hlastValue : deficitAt d (d.length - 1) = b := by
    have hindex : d.length - 1 = q - 1 := by omega
    simpa [hindex] using hlast
  have finishReplace
      (hr2 : ∀ i, i + 2 = d.length - 1 →
        ¬(deficitAt d i = 0 ∧ deficitAt d (i + 1) = 1))
      (hr3 : ∀ start,
        IsMaximalZeroBlock d start (n - 2) →
        0 < start → start + (n - 2) = d.length - 1 →
        n ≤ deficitAt d (start - 1) + 1) :
      phiN n q hn (by omega) + (b - 1) ≤ D := by
    let d' := rightSurgeryReplaceLast d
    have hlegal' := rightSurgeryReplaceLast_legal hlegal (by omega)
      hlastPos hr2 hr3
    have hlength' : d'.length = q := by simp [d', hlength]
    have htotal' := rightSurgeryReplaceLast_total (D := D) (b := b)
      (by omega : 0 < d.length) hlastValue hb htotal
    have hminimal := phiN_le_total_of_legal hn (show 1 ≤ q by omega)
      hlength' hlegal'
    dsimp [d'] at htotal' hminimal
    omega
  by_cases hpredZero : deficitAt d (q - 2) = 0
  · -- The final positive entry is preceded by a maximal trailing zero block.
    by_cases hlong : ∃ start,
        IsMaximalZeroBlock d start (n - 2) ∧
          start + (n - 2) = q - 1
    · obtain ⟨start, hblock, hend⟩ := hlong
      by_cases hstartZero : start = 0
      · -- Exact length `n-2`, with no positive left neighbour.
        have hr2 : ∀ i, i + 2 = d.length - 1 →
            ¬(deficitAt d i = 0 ∧ deficitAt d (i + 1) = 1) := by
          intro i hi hpair
          have hiMiddle : i + 1 = q - 2 := by omega
          rw [hiMiddle, hpredZero] at hpair
          omega
        have hr3 : ∀ other,
            IsMaximalZeroBlock d other (n - 2) →
            0 < other → other + (n - 2) = d.length - 1 →
            n ≤ deficitAt d (other - 1) + 1 := by
          intro other hother hotherPos hotherEnd
          have heq : other = start := by omega
          rw [heq, hstartZero] at hotherPos
          omega
        exact finishReplace hr2 hr3

      · -- Exact length `n-2`, with a positive left neighbour.
        have hstartPos : 0 < start := by omega
        have hstartIndex : start < d.length := by
          rcases hblock with ⟨_, hwithin, _, _, _⟩
          omega
        have hstartValue : deficitAt d start = 0 := by
          rcases hblock with ⟨hpos, _, hzeros, _, _⟩
          exact hzeros 0 hpos
        have hendLength : start + (n - 2) = d.length - 1 := by
          omega
        have hlegal' := rightSurgeryShiftTrailing_legal hlegal (by omega)
          hstartPos hblock hendLength hlastPos
        have hlength' : (rightSurgeryShiftTrailing d start).length = q := by
          simp [hlength]
        have htotal' := rightSurgeryShiftTrailing_total (D := D) (b := b)
          (by omega : 0 < d.length) hstartIndex hstartValue hlastValue hb
          htotal (by omega)
        have hminimal := phiN_le_total_of_legal hn (show 1 ≤ q by omega)
          hlength' hlegal'
        omega
    · -- Every trailing zero block shorter than `n-2` reaches this branch.
      have hr2 : ∀ i, i + 2 = d.length - 1 →
          ¬(deficitAt d i = 0 ∧ deficitAt d (i + 1) = 1) := by
        intro i hi hpair
        have hiMiddle : i + 1 = q - 2 := by omega
        rw [hiMiddle, hpredZero] at hpair
        omega
      have hr3 : ∀ start,
          IsMaximalZeroBlock d start (n - 2) →
          0 < start → start + (n - 2) = d.length - 1 →
          n ≤ deficitAt d (start - 1) + 1 := by
        intro start hblock hstartPos hend
        exfalso
        apply hlong
        exact ⟨start, hblock, by omega⟩
      exact finishReplace hr2 hr3
  · have hpredPos : 0 < deficitAt d (q - 2) := by omega
    by_cases hqTwo : q = 2
    · -- Ordinary positive predecessor, including the literal `q=2` case.
      have hr2 : ∀ i, i + 2 = d.length - 1 →
          ¬(deficitAt d i = 0 ∧ deficitAt d (i + 1) = 1) := by
        intro i hi hpair
        omega
      have hr3 : ∀ start,
          IsMaximalZeroBlock d start (n - 2) →
          0 < start → start + (n - 2) = d.length - 1 →
          n ≤ deficitAt d (start - 1) + 1 := by
        intro start hblock _hstartPos hend
        rcases hblock with ⟨hpos, _, hzeros, _, _⟩
        have hj : n - 3 < n - 2 := by omega
        have hz := hzeros (n - 3) hj
        have hidx : start + (n - 3) = q - 2 := by omega
        rw [hidx] at hz
        omega
      exact finishReplace hr2 hr3
    · have hqThree : 3 ≤ q := by omega
      by_cases hterminal :
          deficitAt d (q - 3) = 0 ∧ deficitAt d (q - 2) = 1
      · -- The terminal `(0,1,b)` case: use prefix legality and the
        -- accepted two-step `phiN` bound; no replacement is needed.
        let pref := d.take (q - 2)
        have hprefLength : pref.length = q - 2 := by
          simp [pref, hlength]
        have hprefLegal : IsLegalDeficitSequence n pref := by
          dsimp [pref]
          exact hlegal.take (by omega) (by omega)
        have hprefTotal := prefix_before_terminal_zero_one_total hqThree
          hlength htotal hterminal.1 hterminal.2 hlast
        have hprefMin := phiN_le_total_of_legal hn
          (show 1 ≤ q - 2 by omega) hprefLength hprefLegal
        have hstep := phiN_le_sub_two_add_two hn (r := q) (by omega)
        dsimp [pref] at hprefTotal hprefMin
        omega
      · -- Ordinary positive predecessor, with the forbidden terminal
        -- pair explicitly excluded.
        have hr2 : ∀ i, i + 2 = d.length - 1 →
            ¬(deficitAt d i = 0 ∧ deficitAt d (i + 1) = 1) := by
          intro i hi hpair
          have hiFirst : i = q - 3 := by omega
          have hiMiddle : i + 1 = q - 2 := by omega
          apply hterminal
          have hfirst := hpair.1
          have hmiddle := hpair.2
          rw [hiFirst] at hfirst
          rw [hiMiddle] at hmiddle
          exact ⟨hfirst, hmiddle⟩
        have hr3 : ∀ start,
            IsMaximalZeroBlock d start (n - 2) →
            0 < start → start + (n - 2) = d.length - 1 →
            n ≤ deficitAt d (start - 1) + 1 := by
          intro start hblock _hstartPos hend
          rcases hblock with ⟨hpos, _, hzeros, _, _⟩
          have hj : n - 3 < n - 2 := by omega
          have hz := hzeros (n - 3) hj
          have hidx : start + (n - 3) = q - 2 := by omega
          rw [hidx] at hz
          omega
        exact finishReplace hr2 hr3

/-- **Endpoint deficit bound (Theorem `thm:endpoint`).**  No endpoint
case is discarded: `a≤1`, `b=0`, `b=1`, `b≥2`, and `q=2` all remain in
the public domain. -/
theorem endpointDeficitBound {n q D a b : ℕ} {d : List ℕ}
    (hn : 6 ≤ n) (hq : 2 ≤ q)
    (ha : a ≤ n - 2) (hb : b ≤ n - 1)
    (hlength : d.length = q)
    (hlegal : IsLegalDeficitSequence n d)
    (htotal : deficitSequenceTotal d = D)
    (hfirst : a ≤ deficitAt d 0)
    (hlast : b ≤ deficitAt d (q - 1)) :
    phiN n q hn (by omega) + max 0 (a - 1) + endpointChargeB b ≤ D := by
  have rightOnly (e : List ℕ)
      (helength : e.length = q)
      (helegal : IsLegalDeficitSequence n e)
      (helast : b ≤ deficitAt e (q - 1)) :
      phiN n q hn (by omega) + endpointChargeB b ≤
        deficitSequenceTotal e := by
    by_cases hbzero : b = 0
    · subst b
      simp only [endpointChargeB_zero, Nat.add_zero]
      exact phiN_le_total_of_legal hn (show 1 ≤ q by omega)
        helength helegal
    by_cases hbone : b = 1
    · subst b
      have hene : e ≠ [] := by
        intro he
        subst e
        simp at helength
        omega
      have hfinalPos : 0 < deficitAt e (e.length - 1) := by
        have hindex : e.length - 1 = q - 1 := by omega
        rw [hindex]
        omega
      have hlastWitness : ∃ y, e.getLast? = some y ∧ 0 < y := by
        refine ⟨e.getLast hene, List.getLast?_eq_some_getLast hene, ?_⟩
        rw [List.getLast_eq_getElem]
        have hdef := deficitAt_eq_get e (e.length - 1) (by omega)
        rw [hdef] at hfinalPos
        exact hfinalPos
      have hterminal := terminalNonfull_phiN_add_one_le_total
        hn (show 1 ≤ q by omega) helength helegal rfl hlastWitness
      simpa using hterminal
    · have hbtwo : 2 ≤ b := by omega
      let x := deficitAt e (q - 1)
      have hxtwo : 2 ≤ x := by
        dsimp [x]
        omega
      have hsurgery := rightSurgery hn hq helength helegal rfl
        (b := x) rfl hxtwo
      rw [endpointChargeB_eq_sub_one hbtwo]
      dsimp [x] at hsurgery
      omega
  by_cases hasmall : a ≤ 1
  · have hright := rightOnly d hlength hlegal hlast
    have hchargeZero : max 0 (a - 1) = 0 := by
      simp
      omega
    rw [hchargeZero, Nat.add_zero]
    rw [htotal] at hright
    exact hright
  · have hatwo : 2 ≤ a := by omega
    have hdFirst : 2 ≤ deficitAt d 0 := by omega
    obtain ⟨d', hlength', hlegal', htotalBound, hsupport, hshortSupport⟩ :=
      leftSurgery hn hq hlength hlegal htotal hdFirst
    have hlastEq : deficitAt d' (q - 1) = deficitAt d (q - 1) := by
      by_cases hqn : n ≤ q
      · apply hsupport (q - 1)
        omega
      · have hqsmall : q ≤ n - 1 := by omega
        exact hshortSupport hqsmall (q - 1) (by omega)
    have hright : phiN n q hn (by omega) + endpointChargeB b ≤
        deficitSequenceTotal d' := by
      apply rightOnly d' hlength' hlegal'
      rw [hlastEq]
      exact hlast
    have hfirstMem : deficitAt d 0 ∈ d := by
      rw [deficitAt_eq_get d 0 (by omega)]
      exact List.get_mem _ _
    have hfirstLeTotal : deficitAt d 0 ≤ D := by
      have hfirstLeSum := List.le_sum_of_mem hfirstMem
      have hfirstLeDeficit : deficitAt d 0 ≤ deficitSequenceTotal d := by
        simpa only [deficitSequenceTotal] using hfirstLeSum
      rwa [htotal] at hfirstLeDeficit
    let reduction := min (deficitAt d 0 - 1) (n - 3)
    have hreductionLeD : reduction ≤ D := by
      dsimp [reduction]
      exact le_trans (min_le_left _ _) (by omega)
    have htotalAdd : deficitSequenceTotal d' + reduction ≤ D := by
      exact (Nat.le_sub_iff_add_le hreductionLeD).mp htotalBound
    have haLeReduction : a - 1 ≤ reduction := by
      dsimp [reduction]
      apply le_min
      · omega
      · omega
    have hcharge : max 0 (a - 1) = a - 1 := by simp
    rw [hcharge]
    omega

/-- The literal sharpness string from Remark `rem:endpointsharp`. -/
def endpointSharpWitness (n : ℕ) : List ℕ :=
  (n - 1) :: (List.replicate (n - 2) 0 ++ [1])

private theorem endpointSharpWitness_length {n : ℕ} (hn : 6 ≤ n) :
    (endpointSharpWitness n).length = n := by
  simp [endpointSharpWitness]
  omega

private theorem endpointSharpWitness_total {n : ℕ} (hn : 6 ≤ n) :
    deficitSequenceTotal (endpointSharpWitness n) = n := by
  simp [deficitSequenceTotal, endpointSharpWitness]
  omega

private theorem endpointSharpWitness_first {n : ℕ} (_hn : 6 ≤ n) :
    deficitAt (endpointSharpWitness n) 0 = n - 1 := by
  simp [deficitAt, endpointSharpWitness]

private theorem endpointSharpWitness_last {n : ℕ} (hn : 6 ≤ n) :
    deficitAt (endpointSharpWitness n) (n - 1) = 1 := by
  have hne : endpointSharpWitness n ≠ [] := by
    simp [endpointSharpWitness]
  have hindex : (endpointSharpWitness n).length - 1 = n - 1 := by
    rw [endpointSharpWitness_length hn]
  rw [← hindex]
  calc
    deficitAt (endpointSharpWitness n)
        ((endpointSharpWitness n).length - 1) =
        (endpointSharpWitness n).getLast hne := by
      rw [deficitAt_eq_get]
      exact (List.getLast_eq_getElem hne).symm
    _ = 1 := by simp [endpointSharpWitness]

private theorem endpointSharpWitness_zero {n j : ℕ} (hn : 6 ≤ n)
    (hlo : 1 ≤ j) (hhi : j ≤ n - 2) :
    deficitAt (endpointSharpWitness n) j = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hk : k < n - 2 := by omega
  have hindex : k + 1 < (endpointSharpWitness n).length := by
    rw [endpointSharpWitness_length hn]
    omega
  rw [deficitAt_eq_get _ _ hindex]
  simp [endpointSharpWitness, hk]

private theorem endpointSharpWitness_legal {n : ℕ} (hn : 6 ≤ n) :
    IsLegalDeficitSequence n (endpointSharpWitness n) where
  six_le := hn
  nonempty := by simp [endpointSharpWitness]
  entries_lt := by
    intro x hx
    simp [endpointSharpWitness] at hx
    omega
  rule1 := by
    have hnotAll : ¬ ∀ x ∈ endpointSharpWitness n, x = 0 := by
      intro hall
      have hfirst := hall (n - 1) (by simp [endpointSharpWitness])
      omega
    simp only [if_neg hnotAll]
    intro start blockLength hblock
    rcases hblock with ⟨hpos, hwithin, hzeros, _hleft, _hright⟩
    have hlength := endpointSharpWitness_length hn
    have hstartPos : 0 < start := by
      by_contra hnot
      have hstart : start = 0 := by omega
      have hz := hzeros 0 hpos
      rw [hstart, Nat.zero_add, endpointSharpWitness_first hn] at hz
      omega
    have hendStrict : start + blockLength <
        (endpointSharpWitness n).length := by
      by_contra hnot
      have hend : start + blockLength =
          (endpointSharpWitness n).length := by omega
      have hj : blockLength - 1 < blockLength := by omega
      have hz := hzeros (blockLength - 1) hj
      have hindex : start + (blockLength - 1) = n - 1 := by
        omega
      rw [hindex, endpointSharpWitness_last hn] at hz
      omega
    omega
  rule2 := by
    intro i hi hpattern
    have hlength := endpointSharpWitness_length hn
    have hmiddleZero := endpointSharpWitness_zero hn
      (show 1 ≤ i + 1 by omega) (show i + 1 ≤ n - 2 by omega)
    omega
  rule3 := by
    intro start _hblock hleft hright
    have hlength := endpointSharpWitness_length hn
    have hstart : start = 1 := by omega
    have hleftIndex : start - 1 = 0 := by omega
    have hrightIndex : start + (n - 2) = n - 1 := by omega
    rw [hleftIndex, hrightIndex, endpointSharpWitness_first hn,
      endpointSharpWitness_last hn]
    omega

private theorem phiN_self_eq_two {n : ℕ} (hn : 6 ≤ n) :
    phiN n n hn (by omega) = 2 := by
  rw [phiN_closed_form]
  have hnotExceptional :
      ¬(n + (n - 2) ≤ n ∧ Nat.ModEq (n - 2) n n) := by omega
  rw [if_neg hnotExceptional]
  have hnotSmall : ¬n ≤ n - 1 := by omega
  have hmu : 0 < n - 2 := by omega
  unfold PhiN
  rw [if_neg hnotSmall]
  simp only [Nat.sub_self, Nat.zero_add]
  rw [Nat.div_self hmu]

/-- **Sharpness at the excluded endpoint (Remark `rem:endpointsharp`).**
The legal string `((n-1),0^(n-2),1)` has length and total `n`, while the
endpoint expression obtained by allowing `a=n-1` is `n+1`; hence that
extension of `endpointDeficitBound` is false. -/
theorem endpointSharpCounterexample {n : ℕ} (hn : 6 ≤ n) :
    IsLegalDeficitSequence n (endpointSharpWitness n) ∧
      (endpointSharpWitness n).length = n ∧
      deficitSequenceTotal (endpointSharpWitness n) = n ∧
      deficitAt (endpointSharpWitness n) 0 = n - 1 ∧
      deficitAt (endpointSharpWitness n) (n - 1) = 1 ∧
      phiN n n hn (by omega) = 2 ∧
      phiN n n hn (by omega) + max 0 ((n - 1) - 1) +
          endpointChargeB 1 = n + 1 ∧
      ¬(phiN n n hn (by omega) + max 0 ((n - 1) - 1) +
          endpointChargeB 1 ≤
        deficitSequenceTotal (endpointSharpWitness n)) := by
  have hlegal := endpointSharpWitness_legal hn
  have hlength := endpointSharpWitness_length hn
  have htotal := endpointSharpWitness_total hn
  have hfirst := endpointSharpWitness_first hn
  have hlast := endpointSharpWitness_last hn
  have hphi := phiN_self_eq_two hn
  refine ⟨hlegal, hlength, htotal, hfirst, hlast, hphi, ?_, ?_⟩
  · rw [hphi, endpointChargeB_one]
    simp
    omega
  · rw [hphi, htotal, endpointChargeB_one]
    simp
    omega

end SuperpermutationLowerBound
