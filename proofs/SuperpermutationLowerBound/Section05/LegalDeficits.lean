module

public import SuperpermutationLowerBound.Section05.SatelliteCalculus

@[expose] public section

namespace SuperpermutationLowerBound

/-! The three exact deficit-string rules at the end of Section 5.  This
module stops before the abstract deficit function of Section 6. -/

/-- Total list indexing used in the rule predicates.  Every rule also
records the exact bounds that put its relevant indices in range. -/
def deficitAt (d : List ℕ) (i : ℕ) : ℕ := d[i]?.getD 0

/-- An exact maximal nonempty zero block, including both endpoint cases. -/
def IsMaximalZeroBlock (d : List ℕ) (start blockLength : ℕ) : Prop :=
  0 < blockLength ∧
  start + blockLength ≤ d.length ∧
  (∀ j, ∀ _hj : j < blockLength,
    deficitAt d (start + j) = 0) ∧
  (start = 0 ∨
    ∃ _hleft : 0 < start,
      0 < deficitAt d (start - 1)) ∧
  (start + blockLength = d.length ∨
    ∃ _hright : start + blockLength < d.length,
      0 < deficitAt d (start + blockLength))

/-- **Legal deficit sequence (Definition `def:legal`).**  This is the
literal nonempty/range condition together with R1--R3.  In R1 the all-zero
case is an explicit exception; R3 applies only when both positive neighbours
exist, while maximality records their positivity. -/
structure IsLegalDeficitSequence (n : ℕ) (d : List ℕ) : Prop where
  six_le : 6 ≤ n
  nonempty : d ≠ []
  entries_lt : ∀ x ∈ d, x < n
  rule1 :
    if ∀ x ∈ d, x = 0 then
      d.length ≤ n - 1
    else
      ∀ start blockLength,
        IsMaximalZeroBlock d start blockLength → blockLength ≤ n - 2
  rule2 : ∀ i, ∀ _hi : i + 2 < d.length,
    ¬(deficitAt d i = 0 ∧
      deficitAt d (i + 1) = 1 ∧
      deficitAt d (i + 2) ≤ 1)
  rule3 : ∀ start,
    IsMaximalZeroBlock d start (n - 2) →
    ∀ _hleft : 0 < start,
    ∀ _hright : start + (n - 2) < d.length,
      n ≤ deficitAt d (start - 1) +
        deficitAt d (start + (n - 2))

/-- The total deficit is exactly the ordinary sum of the entries. -/
def deficitSequenceTotal (d : List ℕ) : ℕ := d.sum

/-- In-range total indexing is the ordinary list entry. -/
theorem deficitAt_eq_get (d : List ℕ) (i : ℕ) (hi : i < d.length) :
    deficitAt d i = d.get ⟨i, hi⟩ := by
  simp [deficitAt, List.getElem?_eq_getElem hi]

namespace BlockAlignedLightSegment

variable {k : ℕ} {hk : 7 ≤ k} {p : OverlapPath k}
  {hp : IsBlockAligned p}

/-- The actual globally transported run at a local segment index. -/
noncomputable def actualRun (segment : BlockAlignedLightSegment hk p hp)
    (j : Fin segment.length) : BlockAlignedRun hk p hp :=
  blockAlignedRunAt hk p hp
    ⟨segment.globalStart + j.1, by
      have := blockAlignedLightSegment_globalStart_bounds hk p hp segment
      omega⟩

/-- Exact equality between the actual transported run and its local list. -/
theorem actualRun_blocks (segment : BlockAlignedLightSegment hk p hp)
    (j : Fin segment.length) :
    (segment.actualRun j).blocks = segment.runAt j := by
  simpa [actualRun] using
    (blockAlignedLightSegment_runAt_eq_globalRun hk p hp segment j).symm

/-- Every local run has positive length and at most `n=k-1` blocks. -/
theorem actualRun_length_bounds (segment : BlockAlignedLightSegment hk p hp)
    (j : Fin segment.length) :
    1 ≤ (segment.runAt j).length ∧
      (segment.runAt j).length ≤ k - 1 := by
  have hblocks := segment.actualRun_blocks j
  have hlength := congrArg List.length hblocks
  constructor
  · have := blockAlignedRun_length_pos hk p hp (segment.actualRun j)
    simpa [BlockAlignedRun.length] using hlength ▸ this
  · have := blockAlignedRun_length_le hk p hp (segment.actualRun j)
    simpa [BlockAlignedRun.length] using hlength ▸ this

/-- Exact local deficit formula. -/
theorem deficitString_get_eq (segment : BlockAlignedLightSegment hk p hp)
    (j : Fin segment.length) :
    segment.deficitString.get ⟨j.1, by simp⟩ =
      k - 1 - (segment.runAt j).length := by
  simp [BlockAlignedLightSegment.deficitString,
    BlockAlignedLightSegment.runAt, BlockAlignedLightSegment.length]

/-- A zero local deficit is equivalent to an actual full run. -/
theorem deficitString_get_eq_zero_iff
    (segment : BlockAlignedLightSegment hk p hp)
    (j : Fin segment.length) :
    segment.deficitString.get ⟨j.1, by simp⟩ = 0 ↔
      (segment.runAt j).length = k - 1 := by
  rw [segment.deficitString_get_eq j]
  have := segment.actualRun_length_bounds j
  omega

/-- A positive local deficit gives the exact nonfull bound. -/
theorem runAt_length_le_of_deficit_pos
    (segment : BlockAlignedLightSegment hk p hp)
    (j : Fin segment.length)
    (hpos : 0 < segment.deficitString.get
      ⟨j.1, by simp⟩) :
    (segment.runAt j).length ≤ k - 2 := by
  rw [segment.deficitString_get_eq j] at hpos
  have := segment.actualRun_length_bounds j
  omega

/-- A positive-deficit local run as the exact satellite context required by
L3. -/
noncomputable def satelliteContextAt
    (segment : BlockAlignedLightSegment hk p hp)
    (j : Fin segment.length)
    (hpos : 0 < segment.deficitString.get
      ⟨j.1, by simp⟩) :
    SatelliteContext hk p hp segment where
  localIndex := j
  nonfull := segment.runAt_length_le_of_deficit_pos j hpos

/-- The represented context has exactly the corresponding deficit-string
entry. -/
theorem satelliteContextAt_deficit
    (segment : BlockAlignedLightSegment hk p hp)
    (j : Fin segment.length)
    (hpos : 0 < segment.deficitString.get
      ⟨j.1, by simp⟩) :
    (segment.satelliteContextAt j hpos).deficit =
      segment.deficitString.get ⟨j.1, by simp⟩ := by
  rw [segment.deficitString_get_eq j]
  unfold satelliteContextAt SatelliteContext.deficit SatelliteContext.run
  have hrun := blockAlignedLightSegment_runAt_eq_globalRun hk p hp segment j
  have hlength := congrArg List.length hrun
  simpa [BlockAlignedRun.deficit, BlockAlignedRun.length] using
    congrArg (fun ell => k - 1 - ell) hlength.symm

/-- Total indexing of a segment deficit string at an in-range local index. -/
theorem deficitAt_deficitString_eq
    (segment : BlockAlignedLightSegment hk p hp)
    (i : ℕ) (hi : i < segment.length) :
    deficitAt segment.deficitString i =
      segment.deficitString.get ⟨i, by simpa using hi⟩ := by
  exact deficitAt_eq_get _ i (by simpa using hi)

/-- The segment deficit string is nonempty. -/
theorem deficitString_nonempty
    (segment : BlockAlignedLightSegment hk p hp) :
    segment.deficitString ≠ [] := by
  intro hnil
  have hzero := congrArg List.length hnil
  rw [blockAlignedLightSegment_deficitString_length] at hzero
  simp at hzero
  exact (Nat.ne_of_gt
    (blockAlignedLightSegment_length_pos hk p hp segment)) hzero

/-- Every segment deficit entry is in `0,…,n-1`, here stated as `<n`. -/
theorem deficitString_entries_lt
    (segment : BlockAlignedLightSegment hk p hp) :
    ∀ x ∈ segment.deficitString, x < k - 1 := by
  intro x hx
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
  let j : Fin segment.length :=
    ⟨i.1, by simpa using i.2⟩
  have hget : x = segment.deficitString.get
      ⟨j.1, by simp⟩ := by
    simpa [j] using hi.symm
  rw [hget, segment.deficitString_get_eq j]
  have hbounds := segment.actualRun_length_bounds j
  omega

/-- Rule R1 for an actual light segment, including the exact all-zero
exception and both endpoint cases for maximal zero blocks. -/
theorem deficitString_rule1
    (segment : BlockAlignedLightSegment hk p hp) :
    if ∀ x ∈ segment.deficitString, x = 0 then
      segment.deficitString.length ≤ (k - 1) - 1
    else
      ∀ start blockLength,
        IsMaximalZeroBlock segment.deficitString start blockLength →
          blockLength ≤ (k - 1) - 2 := by
  by_cases hall : ∀ x ∈ segment.deficitString, x = 0
  · simp only [if_pos hall]
    have hfull : ∀ j, ∀ hj : j < segment.length,
        (segment.runAt ⟨0 + j, by omega⟩).length = k - 1 := by
      intro j hj
      have hzero : segment.deficitString.get
          ⟨j, by simpa using hj⟩ = 0 :=
        hall _ (List.get_mem _ _)
      simpa using
        (segment.deficitString_get_eq_zero_iff ⟨j, hj⟩).mp hzero
    have hbound := blockAlignedLightSegment_fullInterval_runCount_le
      hk p hp segment 0 segment.length (by omega) hfull
    have harith : (k - 1) - 1 = k - 2 := by omega
    rw [harith]
    rw [blockAlignedLightSegment_deficitString_length]
    exact hbound
  · simp only [if_neg hall]
    intro start blockLength hblock
    rcases hblock with
      ⟨hpositive, hwithin, hzeros, hleft, hright⟩
    have hdefLen : segment.deficitString.length = segment.length :=
      blockAlignedLightSegment_deficitString_length hk p hp segment
    by_contra hnot
    have hlong : k - 2 ≤ blockLength := by omega
    have hzeroFull : ∀ j, ∀ hj : j < k - 2,
        (segment.runAt ⟨start + j, by omega⟩).length = k - 1 := by
      intro j hj
      have hz := hzeros j (by omega)
      rw [segment.deficitAt_deficitString_eq (start + j) (by omega)] at hz
      exact (segment.deficitString_get_eq_zero_iff
        ⟨start + j, by omega⟩).mp hz
    rcases hleft with hstart | ⟨hstartPos, hbeforePos⟩
    · subst start
      have hstrict : k - 2 < segment.length := by
        rcases hright with hend | ⟨hright, _hafterPos⟩
        · exfalso
          apply hall
          intro x hx
          obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
          have hiBlock : i.1 < blockLength := by
            omega
          have hz := hzeros i.1 hiBlock
          simp only [Nat.zero_add] at hz
          rw [deficitAt_eq_get _ i.1 i.2] at hz
          exact hi.symm.trans hz
        · have hdefLen := blockAlignedLightSegment_deficitString_length
            hk p hp segment
          omega
      have hnosuccessor :=
        blockAlignedLightSegment_fullInterval_no_successor hk p hp
          segment 0 (by omega) (by
            intro j hj
            simpa using hzeroFull j hj)
      exact hnosuccessor (by omega)
    · let j0 : Fin segment.length := ⟨start - 1, by omega⟩
      have hbeforeGet : 0 < segment.deficitString.get
          ⟨j0.1, by simp⟩ := by
        have htotal := hbeforePos
        rw [segment.deficitAt_deficitString_eq (start - 1) (by omega)] at htotal
        simpa [j0] using htotal
      let R := segment.satelliteContextAt j0 hbeforeGet
      have hin : R.localIndex.1 + 1 + (k - 2) ≤ segment.length := by
        dsimp [R, BlockAlignedLightSegment.satelliteContextAt, j0]
        omega
      have hfullAfter : ∀ j, ∀ hj : j < k - 2,
          (segment.runAt
            ⟨R.localIndex.1 + 1 + j, by omega⟩).length = k - 1 := by
        intro j hj
        have heq : R.localIndex.1 + 1 + j = start + j := by
          dsimp [R, BlockAlignedLightSegment.satelliteContextAt, j0]
          omega
        simpa [heq] using hzeroFull j hj
      exact R.noLongFullStreak hin hfullAfter

/-- Rule R2 for an actual light segment, derived from the accepted E1
sandwich at the exact transported global indices. -/
theorem deficitString_rule2
    (segment : BlockAlignedLightSegment hk p hp) :
    ∀ i, ∀ _hi : i + 2 < segment.deficitString.length,
      ¬(deficitAt segment.deficitString i = 0 ∧
        deficitAt segment.deficitString (i + 1) = 1 ∧
        deficitAt segment.deficitString (i + 2) ≤ 1) := by
  intro i hi hpattern
  rcases hpattern with ⟨hzero, hone, hsmall⟩
  have hdefLen : segment.deficitString.length = segment.length :=
    blockAlignedLightSegment_deficitString_length hk p hp segment
  have hi0 : i < segment.length := by omega
  have hi1 : i + 1 < segment.length := by omega
  have hi2 : i + 2 < segment.length := by omega
  rw [segment.deficitAt_deficitString_eq i hi0] at hzero
  rw [segment.deficitAt_deficitString_eq (i + 1) hi1] at hone
  rw [segment.deficitAt_deficitString_eq (i + 2) hi2] at hsmall
  let r0 := segment.actualRun ⟨i, hi0⟩
  let r1 := segment.actualRun ⟨i + 1, hi1⟩
  let r2 := segment.actualRun ⟨i + 2, hi2⟩
  have hr0Blocks := segment.actualRun_blocks ⟨i, hi0⟩
  have hr1Blocks := segment.actualRun_blocks ⟨i + 1, hi1⟩
  have hr2Blocks := segment.actualRun_blocks ⟨i + 2, hi2⟩
  have hr0Full : r0.IsFull := by
    have hlocal :=
      (segment.deficitString_get_eq_zero_iff ⟨i, hi0⟩).mp hzero
    have hlength := congrArg List.length hr0Blocks
    simpa [r0, BlockAlignedRun.IsFull, BlockAlignedRun.length] using
      hlength.trans hlocal
  have hr1Length : r1.length = k - 2 := by
    rw [segment.deficitString_get_eq ⟨i + 1, hi1⟩] at hone
    have hbounds := segment.actualRun_length_bounds ⟨i + 1, hi1⟩
    have hlength := congrArg List.length hr1Blocks
    have hlocal : (segment.runAt ⟨i + 1, hi1⟩).length = k - 2 := by
      omega
    simpa [r1, BlockAlignedRun.length] using hlength.trans hlocal
  let g := segment.globalStart + i
  have hg2 : g + 2 < (blockAlignedRuns hk p hp).length := by
    have hsegment := blockAlignedLightSegment_globalStart_bounds
      hk p hp segment
    dsimp [g]
    omega
  have hlight1Local := blockAlignedLightSegment_runAt_light
    hk p hp segment i (by omega)
  have hlight2Local := blockAlignedLightSegment_runAt_light
    hk p hp segment (i + 1) (by omega)
  rw [blockAlignedLightSegment_runAt_eq_globalRun,
    blockAlignedLightSegment_runAt_eq_globalRun] at hlight1Local
  rw [blockAlignedLightSegment_runAt_eq_globalRun,
    blockAlignedLightSegment_runAt_eq_globalRun] at hlight2Local
  have hlight1 : IsLightRunBoundary
      (blockAlignedRunAt hk p hp ⟨g, by omega⟩).blocks
      (blockAlignedRunAt hk p hp ⟨g + 1, by omega⟩).blocks := by
    simpa [g, Nat.add_assoc] using hlight1Local
  have hlight2 : IsLightRunBoundary
      (blockAlignedRunAt hk p hp ⟨g + 1, by omega⟩).blocks
      (blockAlignedRunAt hk p hp ⟨g + 2, hg2⟩).blocks := by
    simpa [g, Nat.add_assoc] using hlight2Local
  have hfullGlobal :
      (blockAlignedRunAt hk p hp ⟨g, by omega⟩).IsFull := by
    simpa [r0, BlockAlignedLightSegment.actualRun, g] using hr0Full
  have hmiddleGlobal :
      (blockAlignedRunAt hk p hp ⟨g + 1, by omega⟩).length = k - 2 := by
    simpa [r1, BlockAlignedLightSegment.actualRun, g, Nat.add_assoc] using
      hr1Length
  have hsandwich := blockAlignedSandwich hk p hp g hg2 hfullGlobal
    hlight1 hmiddleGlobal hlight2
  have hnextDeficit : 2 ≤ segment.deficitString.get
      ⟨i + 2, by simpa using hi2⟩ := by
    have hget := blockAlignedLightSegment_deficitString_get
      hk p hp segment ⟨i + 2, hi2⟩
    have hget' : segment.deficitString.get
        ⟨i + 2, by simpa using hi2⟩ =
        (blockAlignedRunAt hk p hp ⟨g + 2, hg2⟩).deficit := by
      simpa [g, Nat.add_assoc] using hget
    exact hget'.symm ▸ hsandwich.2
  omega

/-- Rule R3 for an actual light segment, with both neighbour hypotheses and
the exact maximal block of `n-2=k-3` zeros. -/
theorem deficitString_rule3
    (segment : BlockAlignedLightSegment hk p hp) :
    ∀ start,
      IsMaximalZeroBlock segment.deficitString start ((k - 1) - 2) →
      ∀ _hleft : 0 < start,
      ∀ _hright : start + ((k - 1) - 2) <
        segment.deficitString.length,
        k - 1 ≤ deficitAt segment.deficitString (start - 1) +
          deficitAt segment.deficitString (start + ((k - 1) - 2)) := by
  intro start hblock hleftIndex hrightIndex
  rcases hblock with
    ⟨hblockPositive, hwithin, hzeros, hleftMax, hrightMax⟩
  have hdefLen : segment.deficitString.length = segment.length :=
    blockAlignedLightSegment_deficitString_length hk p hp segment
  have hbeforePos : 0 < deficitAt segment.deficitString (start - 1) := by
    rcases hleftMax with hzero | ⟨_hleft, hpos⟩
    · omega
    · exact hpos
  have hafterPos :
      0 < deficitAt segment.deficitString (start + ((k - 1) - 2)) := by
    rcases hrightMax with hend | ⟨_hright, hpos⟩
    · omega
    · exact hpos
  have hbeforeBound : start - 1 < segment.length := by omega
  have hafterBound : start + ((k - 1) - 2) < segment.length := by omega
  let j0 : Fin segment.length := ⟨start - 1, hbeforeBound⟩
  have hbeforeGet : 0 < segment.deficitString.get
      ⟨j0.1, by simp⟩ := by
    have htotal := hbeforePos
    rw [segment.deficitAt_deficitString_eq (start - 1) hbeforeBound] at htotal
    simpa [j0] using htotal
  let R := segment.satelliteContextAt j0 hbeforeGet
  have hR1 : R.localIndex.1 + 1 + (k - 3) < segment.length := by
    dsimp [R, BlockAlignedLightSegment.satelliteContextAt, j0]
    omega
  have hfull : ∀ j, ∀ hj : j < k - 3,
      (segment.runAt
        ⟨R.localIndex.1 + 1 + j, by omega⟩).length = k - 1 := by
    intro j hj
    have hz := hzeros j (by omega)
    have hindex : R.localIndex.1 + 1 + j = start + j := by
      dsimp [R, BlockAlignedLightSegment.satelliteContextAt, j0]
      omega
    have hbound : start + j < segment.length := by omega
    rw [segment.deficitAt_deficitString_eq (start + j) hbound] at hz
    have hfullAt := (segment.deficitString_get_eq_zero_iff
      ⟨start + j, hbound⟩).mp hz
    simpa [hindex] using hfullAt
  have hgap := R.gapRule hR1 hfull
  have hb : R.deficit = deficitAt segment.deficitString (start - 1) := by
    calc
      R.deficit = segment.deficitString.get
          ⟨j0.1, by simp⟩ :=
        segment.satelliteContextAt_deficit j0 hbeforeGet
      _ = deficitAt segment.deficitString (start - 1) := by
        symm
        simpa [j0] using
          segment.deficitAt_deficitString_eq (start - 1) hbeforeBound
  have hR1Index : R.localIndex.1 + 1 + (k - 3) =
      start + ((k - 1) - 2) := by
    dsimp [R, BlockAlignedLightSegment.satelliteContextAt, j0]
    omega
  have ha : deficitAt segment.deficitString
      (start + ((k - 1) - 2)) =
      k - 1 - (segment.runAt
        ⟨R.localIndex.1 + 1 + (k - 3), hR1⟩).length := by
    have hformula := segment.deficitString_get_eq
      ⟨start + ((k - 1) - 2), hafterBound⟩
    have htotal := segment.deficitAt_deficitString_eq
      (start + ((k - 1) - 2)) hafterBound
    rw [htotal]
    simpa [hR1Index] using hformula
  have hdle : R.deficit ≤ k - 1 := by
    have := R.length_add_deficit
    omega
  rw [← hb, ha]
  exact (by
    have hlengthBound := hgap.1
    omega)

/-- **The three rules (Proposition `prop:rules`).**  The deficit string of
every generic actual light segment is legal, with R1 from closure/L3, R2
from the sandwich, and R3 from the exact L3 gap rule. -/
theorem deficitString_legal
    (segment : BlockAlignedLightSegment hk p hp) :
    IsLegalDeficitSequence (k - 1) segment.deficitString where
  six_le := by omega
  nonempty := segment.deficitString_nonempty
  entries_lt := segment.deficitString_entries_lt
  rule1 := segment.deficitString_rule1
  rule2 := segment.deficitString_rule2
  rule3 := segment.deficitString_rule3

/-- The abstract definition's total deficit agrees exactly with the
already accepted light-segment total. -/
theorem deficitSequenceTotal_deficitString
    (segment : BlockAlignedLightSegment hk p hp) :
    deficitSequenceTotal segment.deficitString = segment.totalDeficit := rfl

end BlockAlignedLightSegment

/-- Public proposition spelling `prop:rules` without namespace projection. -/
theorem blockAlignedLightSegment_deficitString_legal
    {k : ℕ} (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p)
    (segment : BlockAlignedLightSegment hk p hp) :
    IsLegalDeficitSequence (k - 1) segment.deficitString :=
  segment.deficitString_legal

end SuperpermutationLowerBound
