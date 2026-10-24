module

public import SuperpermutationLowerBound.Section06.Exact

@[expose] public section

-- Export private helpers used in exposed definitions; this adds no axiom.
set_option backward.privateInPublic true

namespace SuperpermutationLowerBound

/-! Lemma `lem:nf`, terminal-nonfull.  The upper bound below reuses the
literal positive-cluster decomposition, endpoint exceptions, critical gaps,
and odd-critical-run charge from Gate F1.  The sharp witnesses are added
after the upper bound. -/

private theorem total_pos_of_positive_last {d : List ℕ}
    (hlast : ∃ x, d.getLast? = some x ∧ 0 < x) :
    1 ≤ deficitSequenceTotal d := by
  obtain ⟨x, hxlast, hxpos⟩ := hlast
  have hxmem : x ∈ d.getLast? := by simp [hxlast]
  have hdecomp := List.dropLast_append_getLast? x hxmem
  have hsum : d.dropLast.sum + x = deficitSequenceTotal d := by
    rw [← hdecomp]
    simp [deficitSequenceTotal]
  omega

/-- The isolated `D=1` terminal-positive case has exactly the displayed
shape `0^(r-1) 1`. -/
theorem terminalTotalOne_eq_replicate_append_one {d : List ℕ} {r : ℕ}
    (hlength : d.length = r)
    (htotal : deficitSequenceTotal d = 1)
    (hlast : ∃ x, d.getLast? = some x ∧ 0 < x) :
    d = List.replicate (r - 1) 0 ++ [1] := by
  obtain ⟨x, hxlast, hxpos⟩ := hlast
  have hxmem : x ∈ d.getLast? := by simp [hxlast]
  have hdne : d ≠ [] := by
    intro hnil
    subst d
    simp at hxlast
  have hdecomp := List.dropLast_append_getLast? x hxmem
  have hsum : d.dropLast.sum + x = 1 := by
    have htotal' := htotal
    rw [← hdecomp] at htotal'
    simpa [deficitSequenceTotal] using htotal'
  have hx : x = 1 := by omega
  have hdropSum : d.dropLast.sum = 0 := by omega
  have hdropZero : ∀ y ∈ d.dropLast, y = 0 :=
    List.sum_eq_zero_iff.mp hdropSum
  have hdropShape : d.dropLast = List.replicate (r - 1) 0 := by
    apply List.eq_replicate_iff.mpr
    constructor
    · simp [hlength]
    · exact hdropZero
  rw [← hdecomp, hdropShape, hx]

private theorem decomposition_trailing_zero_of_positive_last
    {d : List ℕ} (dec : PositiveClusterDecomposition d)
    (hlast : ∃ x, d.getLast? = some x ∧ 0 < x) :
    dec.trailingZeros = 0 := by
  obtain ⟨x, hxlast, hxpos⟩ := hlast
  by_contra htrail
  have htrailPos : 0 < dec.trailingZeros := by omega
  have htrailNe : List.replicate dec.trailingZeros 0 ≠ [] := by
    simp [htrail]
  have hshapeLast : d.getLast? = some 0 := by
    rw [dec.rebuild]
    rw [List.getLast?_append_of_ne_nil _ htrailNe]
    rw [List.getLast?_replicate]
    simp [htrail]
  rw [hshapeLast] at hxlast
  simp at hxlast
  omega

private theorem shaped_not_all_zero_terminal {leading : ℕ}
    {chain : PositiveClusterChain}
    (hclusterNe : ∀ K ∈ chain.clusters, K ≠ [])
    (hclusterPos : ∀ K ∈ chain.clusters, ∀ x ∈ K, 0 < x) :
    ¬ ∀ x ∈ List.replicate leading 0 ++ chain.render, x = 0 := by
  have hrender : chain.render ≠ [] := chain.render_nonempty hclusterNe
  let x := chain.render.head hrender
  have hxmem : x ∈ chain.render := List.head_mem hrender
  have hxhead : x ∈ chain.render.head? := List.head?_eq_some_head hrender
  have hxpos : 0 < x :=
    chain.render_head_positive hclusterNe hclusterPos x hxhead
  intro hall
  have hxzero := hall x (by simp [hxmem])
  omega

/-- With no terminal zero block, R1 gives exactly one possible leading
zero-block allowance, deleted precisely by the left endpoint exception. -/
private theorem terminalLeadingZeroBlock_bound {n leading : ℕ}
    {chain : PositiveClusterChain}
    (hlegal : IsLegalDeficitSequence n
      (List.replicate leading 0 ++ chain.render))
    (hclusterNe : ∀ K ∈ chain.clusters, K ≠ [])
    (hclusterPos : ∀ K ∈ chain.clusters, ∀ x ∈ K, 0 < x) :
    leading ≤ (n - 2) * (1 - leftClusterException leading) := by
  have hleft := leftClusterException_le_one leading
  have hcases : leftClusterException leading = 0 ∨
      leftClusterException leading = 1 := by omega
  rcases hcases with hzero | hone
  · rw [hzero]
    simp only [Nat.sub_zero, Nat.mul_one]
    by_cases hleadZero : leading = 0
    · omega
    have hbounds := legal_zeroInterval_bounds hlegal
      (start := 0) (blockLength := leading) (by omega) (by simp) (by
        intro j hj
        simp [deficitAt, List.getElem?_append, hj])
    exact hbounds.2 (shaped_not_all_zero_terminal hclusterNe hclusterPos)
  · have hleading : leading = 0 := by
      simpa [leftClusterException] using hone
    simp [hleading]

/-- A terminal singleton exception cannot be the only positive cluster once
the total deficit is at least two. -/
theorem terminalRightException_not_onlyCluster {D : ℕ}
    {chain : PositiveClusterChain} (hD : 2 ≤ D)
    (htotal : (chain.clusters.map List.sum).sum = D)
    (hright : rightClusterException chain 0 = 1) :
    2 ≤ chain.clusters.length := by
  cases chain with
  | last K =>
      have hK : K = [1] := by
        simpa [rightClusterException] using hright
      subst K
      simp [PositiveClusterChain.clusters] at htotal
      omega
  | cons K gap tail =>
      cases tail <;> simp [PositiveClusterChain.clusters]

private theorem maxLegalLength_even_terminal {n t : ℕ} (ht : 1 ≤ t) :
    maxLegalLength n (2 * t) = (n - 1) + (n - 2) * t := by
  have hlarge : ¬2 * t ≤ 1 := by omega
  have hdiv : (2 * t) / 2 = t := by omega
  have hmod : (2 * t) % 2 = 0 := by omega
  unfold maxLegalLength
  rw [if_neg hlarge, hdiv, hmod]
  omega

private theorem maxLegalLength_odd_terminal {n t : ℕ}
    (hnpos : 1 ≤ n) (ht : 1 ≤ t) :
    maxLegalLength n (2 * t + 1) = n + (n - 2) * t := by
  have ht0 : t ≠ 0 := by omega
  have hdiv : (t * 2 + 1) / 2 = t := by omega
  simp [maxLegalLength, ht0, hdiv, Nat.mul_comm]
  omega

private theorem maxLegalLength_pred_even_terminal {n t : ℕ}
    (hn : 2 ≤ n) (ht : 2 ≤ t) :
    maxLegalLength n (2 * t - 1) = (n - 2) * t + 2 := by
  have harg : 2 * t - 1 = 2 * (t - 1) + 1 := by omega
  rw [harg, maxLegalLength_odd_terminal (by omega) (by omega)]
  have hsplit : t = (t - 1) + 1 := by omega
  calc
    n + (n - 2) * (t - 1) =
        (n - 2) + 2 + (n - 2) * (t - 1) := by omega
    _ = (n - 2) * ((t - 1) + 1) + 2 := by ring
    _ = (n - 2) * t + 2 := by rw [← hsplit]

/- Both terminal arithmetic closers live in `ℤ`.  In particular the left
exception produces the genuinely negative constants `4-n` and `1-(n-3)`;
no natural subtraction is used for those expressions. -/
private theorem terminal_no_right_exception_cases {n D left r : ℕ}
    (hn : 6 ≤ n) (hD : 2 ≤ D) (hleft : left ≤ 1)
    (hbound : (r : ℤ) ≤
      1 - (left : ℤ) * ((n : ℤ) - 3) +
        (((n - 4) * ((D + left) / 2) : ℕ) : ℤ) + (D : ℤ)) :
    r ≤ maxLegalLength n (D - 1) := by
  have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  have hn2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
  have hn4 : ((n - 4 : ℕ) : ℤ) = (n : ℤ) - 4 := by omega
  have hleftCases : left = 0 ∨ left = 1 := by omega
  have hmod := Nat.mod_two_eq_zero_or_one D
  let t := D / 2
  rcases hmod with heven | hodd
  · have hDeq : D = 2 * t := by
      dsimp [t]
      have hdivision := Nat.mod_add_div D 2
      omega
    have ht : 1 ≤ t := by omega
    rcases hleftCases with rfl | rfl
    · -- No right exception, no left exception, `D=2t`.
      have hfloor : (D + 0) / 2 = t := by omega
      rw [hfloor, hDeq] at hbound
      by_cases ht1 : t = 1
      · have hDtwo : D = 2 := by omega
        rw [ht1] at hbound
        have hN : maxLegalLength n (D - 1) = n - 1 := by
          rw [hDtwo]
          simp [maxLegalLength]
        rw [hN]
        have hgoal : (r : ℤ) ≤ ((n - 1 : ℕ) : ℤ) := by
          simp only [Nat.cast_mul, hn4, Nat.cast_ofNat] at hbound
          simp only [hn1]
          ring_nf at hbound ⊢
          nlinarith only [hbound, hn, ht]
        exact_mod_cast hgoal
      · have ht2 : 2 ≤ t := by omega
        have harg : D - 1 = 2 * t - 1 := by omega
        have hN : maxLegalLength n (D - 1) =
            (n - 2) * t + 2 := by
          rw [harg]
          exact maxLegalLength_pred_even_terminal (by omega) ht2
        rw [hN]
        clear hN
        have hgoal : (r : ℤ) ≤
            (((n - 2) * t + 2 : ℕ) : ℤ) := by
          simp only [Nat.cast_add, Nat.cast_mul, hn2, hn4,
            Nat.cast_ofNat] at hbound ⊢
          ring_nf at hbound ⊢
          nlinarith only [hbound, hn, ht]
        exact_mod_cast hgoal
    · -- No right exception, left exception, `D=2t`.
      have hfloor : (D + 1) / 2 = t := by omega
      rw [hfloor, hDeq] at hbound
      by_cases ht1 : t = 1
      · have hDtwo : D = 2 := by omega
        rw [ht1] at hbound
        have hN : maxLegalLength n (D - 1) = n - 1 := by
          rw [hDtwo]
          simp [maxLegalLength]
        rw [hN]
        have hgoal : (r : ℤ) ≤ ((n - 1 : ℕ) : ℤ) := by
          simp only [Nat.cast_mul, hn1, hn4, Nat.cast_ofNat] at hbound ⊢
          ring_nf at hbound ⊢
          omega
        exact_mod_cast hgoal
      · have ht2 : 2 ≤ t := by omega
        have harg : D - 1 = 2 * t - 1 := by omega
        have hN : maxLegalLength n (D - 1) =
            (n - 2) * t + 2 := by
          rw [harg]
          exact maxLegalLength_pred_even_terminal (by omega) ht2
        rw [hN]
        clear hN
        have hgoal : (r : ℤ) ≤
            (((n - 2) * t + 2 : ℕ) : ℤ) := by
          simp only [Nat.cast_add, Nat.cast_mul, hn2, hn4,
            Nat.cast_ofNat] at hbound ⊢
          ring_nf at hbound ⊢
          omega
        exact_mod_cast hgoal
  · have hDeq : D = 2 * t + 1 := by
      dsimp [t]
      have hdivision := Nat.mod_add_div D 2
      omega
    have ht : 1 ≤ t := by omega
    rcases hleftCases with rfl | rfl
    · -- No right exception, no left exception, `D=2t+1`.
      have hfloor : (D + 0) / 2 = t := by omega
      have harg : D - 1 = 2 * t := by omega
      have hN : maxLegalLength n (D - 1) =
          (n - 1) + (n - 2) * t := by
        rw [harg]
        exact maxLegalLength_even_terminal ht
      rw [hfloor, hDeq] at hbound
      rw [hN]
      have hgoal : (r : ℤ) ≤
          (((n - 1) + (n - 2) * t : ℕ) : ℤ) := by
        simp only [Nat.cast_add, Nat.cast_mul, hn1, hn2, hn4,
          Nat.cast_ofNat] at hbound ⊢
        ring_nf at hbound ⊢
        nlinarith only [hbound, hn, ht]
      exact_mod_cast hgoal
    · -- No right exception, left exception, `D=2t+1`.
      have hfloor : (D + 1) / 2 = t + 1 := by omega
      have harg : D - 1 = 2 * t := by omega
      have hN : maxLegalLength n (D - 1) =
          (n - 1) + (n - 2) * t := by
        rw [harg]
        exact maxLegalLength_even_terminal ht
      rw [hfloor, hDeq] at hbound
      rw [hN]
      have hgoal : (r : ℤ) ≤
          (((n - 1) + (n - 2) * t : ℕ) : ℤ) := by
        simp only [Nat.cast_add, Nat.cast_mul, hn1, hn2, hn4,
          Nat.cast_ofNat] at hbound ⊢
        ring_nf at hbound ⊢
        omega
      exact_mod_cast hgoal

private theorem terminal_right_exception_cases {n D left r : ℕ}
    (hn : 6 ≤ n) (hD : 2 ≤ D) (hleft : left ≤ 1)
    (hDmin : 4 - (left + 1) ≤ D)
    (hbound : (r : ℤ) ≤
      2 - (left : ℤ) * ((n : ℤ) - 3) +
        (((n - 4) * ((D + left + 1) / 2) : ℕ) : ℤ) + (D : ℤ)) :
    r ≤ maxLegalLength n (D - 1) := by
  have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  have hn2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
  have hn4 : ((n - 4 : ℕ) : ℤ) = (n : ℤ) - 4 := by omega
  have hleftCases : left = 0 ∨ left = 1 := by omega
  have hmod := Nat.mod_two_eq_zero_or_one D
  let t := D / 2
  rcases hmod with heven | hodd
  · have hDeq : D = 2 * t := by
      dsimp [t]
      have hdivision := Nat.mod_add_div D 2
      omega
    have ht : 1 ≤ t := by omega
    rcases hleftCases with rfl | rfl
    · -- Right exception, no left exception, `D=2t`; here `t≥2`.
      have ht2 : 2 ≤ t := by omega
      have hfloor : (D + 0 + 1) / 2 = t := by omega
      have harg : D - 1 = 2 * t - 1 := by omega
      have hN : maxLegalLength n (D - 1) =
          (n - 2) * t + 2 := by
        rw [harg]
        exact maxLegalLength_pred_even_terminal (by omega) ht2
      rw [hfloor, hDeq] at hbound
      rw [hN]
      clear hN
      have hgoal : (r : ℤ) ≤
          (((n - 2) * t + 2 : ℕ) : ℤ) := by
        simp only [Nat.cast_add, Nat.cast_mul, hn2, hn4,
          Nat.cast_ofNat] at hbound ⊢
        ring_nf at hbound ⊢
        omega
      exact_mod_cast hgoal
    · -- Right and left exceptions, `D=2t`.
      have hfloor : (D + 1 + 1) / 2 = t + 1 := by omega
      rw [hfloor, hDeq] at hbound
      by_cases ht1 : t = 1
      · have hDtwo : D = 2 := by omega
        rw [ht1] at hbound
        have hN : maxLegalLength n (D - 1) = n - 1 := by
          rw [hDtwo]
          simp [maxLegalLength]
        rw [hN]
        have hgoal : (r : ℤ) ≤ ((n - 1 : ℕ) : ℤ) := by
          simp only [Nat.cast_mul, hn1, hn4, Nat.cast_ofNat] at hbound ⊢
          ring_nf at hbound ⊢
          nlinarith only [hbound, hn, ht]
        exact_mod_cast hgoal
      · have ht2 : 2 ≤ t := by omega
        have harg : D - 1 = 2 * t - 1 := by omega
        have hN : maxLegalLength n (D - 1) =
            (n - 2) * t + 2 := by
          rw [harg]
          exact maxLegalLength_pred_even_terminal (by omega) ht2
        rw [hN]
        clear hN
        have hgoal : (r : ℤ) ≤
            (((n - 2) * t + 2 : ℕ) : ℤ) := by
          simp only [Nat.cast_add, Nat.cast_mul, hn2, hn4,
            Nat.cast_ofNat] at hbound ⊢
          ring_nf at hbound ⊢
          omega
        exact_mod_cast hgoal
  · have hDeq : D = 2 * t + 1 := by
      dsimp [t]
      have hdivision := Nat.mod_add_div D 2
      omega
    have ht : 1 ≤ t := by omega
    rcases hleftCases with rfl | rfl
    · -- Right exception, no left exception, `D=2t+1`.
      have hfloor : (D + 0 + 1) / 2 = t + 1 := by omega
      have harg : D - 1 = 2 * t := by omega
      have hN : maxLegalLength n (D - 1) =
          (n - 1) + (n - 2) * t := by
        rw [harg]
        exact maxLegalLength_even_terminal ht
      rw [hfloor, hDeq] at hbound
      rw [hN]
      have hgoal : (r : ℤ) ≤
          (((n - 1) + (n - 2) * t : ℕ) : ℤ) := by
        simp only [Nat.cast_add, Nat.cast_mul, hn1, hn2, hn4,
          Nat.cast_ofNat] at hbound ⊢
        ring_nf at hbound ⊢
        omega
      exact_mod_cast hgoal
    · -- Right and left exceptions, `D=2t+1`.
      have hfloor : (D + 1 + 1) / 2 = t + 1 := by omega
      have harg : D - 1 = 2 * t := by omega
      have hN : maxLegalLength n (D - 1) =
          (n - 1) + (n - 2) * t := by
        rw [harg]
        exact maxLegalLength_even_terminal ht
      rw [hfloor, hDeq] at hbound
      rw [hN]
      have hgoal : (r : ℤ) ≤
          (((n - 1) + (n - 2) * t : ℕ) : ℤ) := by
        simp only [Nat.cast_add, Nat.cast_mul, hn1, hn2, hn4,
          Nat.cast_ofNat] at hbound ⊢
        ring_nf at hbound ⊢
        omega
      exact_mod_cast hgoal

/-- **Lemma `lem:nf`, upper-bound assertion.**  Every actual legal sequence
of positive length `r`, actual total deficit `D`, and positive last entry has
`r ≤ N_n(D-1)`.  Positivity of `D` is derived before the subtraction is
used. -/
theorem terminalNonfull_length_le_maxLegalLength_sub_one
    {n r D : ℕ} {d : List ℕ} (hn : 6 ≤ n) (hr : 1 ≤ r)
    (hlength : d.length = r) (hlegal : IsLegalDeficitSequence n d)
    (htotal : deficitSequenceTotal d = D)
    (hlast : ∃ x, d.getLast? = some x ∧ 0 < x) :
    r ≤ maxLegalLength n (D - 1) := by
  have hDpos : 1 ≤ D := by
    have := total_pos_of_positive_last hlast
    omega
  by_cases hDone : D = 1
  · have htotalOne : deficitSequenceTotal d = 1 := htotal.trans hDone
    have hshape := terminalTotalOne_eq_replicate_append_one hlength htotalOne hlast
    by_cases hrOne : r = 1
    · rw [hrOne, hDone]
      simp [maxLegalLength]
      omega
    · have hzeroLength : r - 1 ≤ n - 2 := by
        have hnotAll : ¬ ∀ x ∈ d, x = 0 := by
          intro hall
          obtain ⟨x, hxlast, hxpos⟩ := hlast
          have hxmem : x ∈ d := List.mem_of_getLast? hxlast
          have hxzero := hall x hxmem
          omega
        have hrule := hlegal.rule1
        rw [if_neg hnotAll] at hrule
        have hblock : IsMaximalZeroBlock d 0 (r - 1) := by
          rw [hshape]
          refine ⟨by omega, by simp, ?_, Or.inl rfl, ?_⟩
          · intro j hj
            simp [deficitAt, List.getElem?_append, hj]
          · right
            have hrightIndex : 0 + (r - 1) <
                (List.replicate (r - 1) 0 ++ [1]).length := by
              simp
            refine ⟨hrightIndex, ?_⟩
            have hindex : 0 + (r - 1) <
                (List.replicate (r - 1) 0 ++ [1]).length := by simp
            rw [deficitAt_eq_get _ _ hindex]
            simp
        exact hrule 0 (r - 1) hblock
      rw [hDone]
      simp [maxLegalLength]
      omega
  have hDlarge : 2 ≤ D := by omega
  have hpositive : ∃ x ∈ d, 0 < x := by
    obtain ⟨x, hxlast, hxpos⟩ := hlast
    exact ⟨x, List.mem_of_getLast? hxlast, hxpos⟩
  obtain ⟨dec, _⟩ := exists_positiveClusterDecomposition hpositive
  have htrailing : dec.trailingZeros = 0 :=
    decomposition_trailing_zero_of_positive_last dec hlast
  have hlegalFullShape : IsLegalDeficitSequence n
      (List.replicate dec.leadingZeros 0 ++ dec.chain.render ++
        List.replicate dec.trailingZeros 0) := by
    rw [← dec.rebuild]
    exact hlegal
  have hlegalShape : IsLegalDeficitSequence n
      (List.replicate dec.leadingZeros 0 ++ dec.chain.render) := by
    simpa [htrailing] using hlegalFullShape
  have htotalClusters : (dec.chain.clusters.map List.sum).sum = D := by
    have hshapeSum :
        (List.replicate dec.leadingZeros 0 ++ dec.chain.render ++
          List.replicate dec.trailingZeros 0).sum = D := by
      rw [← dec.rebuild]
      simpa [deficitSequenceTotal] using htotal
    simpa using hshapeSum
  let s := dec.chain.clusters.length
  let M := (dec.chain.clusters.map List.length).sum
  let U := dec.chain.gaps.sum
  let left := leftClusterException dec.leadingZeros
  let right := rightClusterException dec.chain dec.trailingZeros
  let delta := left + right
  let g := criticalGapCount (n - 2) dec.chain.gaps
  let gOdd := oddCriticalRunCount (n - 2) dec.chain.gaps
  have hspos : 1 ≤ s := by
    dsimp [s]
    have hne := dec.chain.clusters_nonempty
    cases hclusters : dec.chain.clusters with
    | nil => contradiction
    | cons K rest => simp
  have hleftLe : left ≤ 1 := by
    exact leftClusterException_le_one _
  have hrightLe : right ≤ 1 := by
    exact rightClusterException_le_one _ _
  have hdeltaLe : delta ≤ 2 := by
    dsimp [delta]
    omega
  have hleading := terminalLeadingZeroBlock_bound hlegalShape
    dec.cluster_nonempty dec.cluster_positive
  change dec.leadingZeros ≤ (n - 2) * (1 - left) at hleading
  have hgapSum := internalGapSum_bound
    hlegalFullShape dec.cluster_nonempty
      dec.cluster_positive dec.gap_positive
  change U ≤ (s - 1) * (n - 3) + g at hgapSum
  have hcluster := cluster_length_charge
    hlegalFullShape dec.cluster_nonempty
      dec.cluster_positive dec.gap_positive
  change M + s ≤ (dec.chain.clusters.map List.sum).sum + delta at hcluster
  rw [htotalClusters] at hcluster
  have hcritical := clusterCriticalCharge_with_runs hn
    hlegalFullShape dec.cluster_nonempty
      dec.cluster_positive dec.gap_positive
  change 2 * s + g + gOdd ≤
    (dec.chain.clusters.map List.sum).sum + delta at hcritical
  rw [htotalClusters] at hcritical
  have hlength : r = dec.leadingZeros + M + U := by
    have hrebuildLength := congrArg List.length dec.rebuild
    simp [htrailing, hlength] at hrebuildLength
    omega
  have hraw : r + s ≤
      (n - 2) * (1 - left) +
        (s - 1) * (n - 3) + g + D + delta := by
    omega
  have hrawInt : (r : ℤ) + (s : ℤ) ≤
      (((n - 2) * (1 - left) +
        (s - 1) * (n - 3) + g + D + delta : ℕ) : ℤ) := by
    exact_mod_cast hraw
  have hn2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
  have hn3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := by omega
  have hn4 : ((n - 4 : ℕ) : ℤ) = (n : ℤ) - 4 := by omega
  have honeLeft : ((1 - left : ℕ) : ℤ) = 1 - (left : ℤ) :=
    Int.ofNat_sub hleftLe
  have hsPred : ((s - 1 : ℕ) : ℤ) = (s : ℤ) - 1 :=
    Int.ofNat_sub hspos
  simp only [Nat.cast_add, Nat.cast_mul, hn2, hn3, honeLeft, hsPred] at hrawInt
  have hlengthExpanded : (r : ℤ) ≤
      1 + (right : ℤ) - (left : ℤ) * ((n : ℤ) - 3) +
        ((n : ℤ) - 4) * (s : ℤ) + (g : ℤ) + (D : ℤ) := by
    dsimp [delta] at hrawInt
    have htemp : (r : ℤ) ≤
        ((n : ℤ) - 2) * (1 - (left : ℤ)) +
          ((s : ℤ) - 1) * ((n : ℤ) - 3) +
            (g : ℤ) + (D : ℤ) + (left : ℤ) + (right : ℤ) - (s : ℤ) := by
      omega
    calc
      (r : ℤ) ≤ _ := htemp
      _ = _ := by ring
  have hchargeInt : (2 * s : ℤ) ≤
      (D : ℤ) + (delta : ℤ) - (g : ℤ) - (gOdd : ℤ) := by
    have haddInt : ((2 * s + g + gOdd : ℕ) : ℤ) ≤
        ((D + delta : ℕ) : ℤ) := by
      exact_mod_cast hcritical
    simp only [Nat.cast_add, Nat.cast_mul] at haddInt
    omega
  have hodd : Odd g → 1 ≤ gOdd := by
    intro hg
    exact oddCriticalRunCount_pos_of_odd hg
  have hslack := criticalGapSlack hn hchargeInt hodd
  have hslackInt :
      (((n - 4) * s + g : ℕ) : ℤ) ≤
        (((n - 4) * ((D + delta) / 2) : ℕ) : ℤ) := by
    exact_mod_cast hslack
  have hleftCast : (((n - 4) * s + g : ℕ) : ℤ) =
      ((n : ℤ) - 4) * (s : ℤ) + (g : ℤ) := by
    simp only [Nat.cast_add, Nat.cast_mul, hn4]
  rw [hleftCast] at hslackInt
  have hrightCases : right = 0 ∨ right = 1 := by omega
  rcases hrightCases with hrightZero | hrightOne
  · have hdelta : delta = left := by
      dsimp [delta]
      omega
    have hbound : (r : ℤ) ≤
        1 - (left : ℤ) * ((n : ℤ) - 3) +
          (((n - 4) * ((D + left) / 2) : ℕ) : ℤ) + (D : ℤ) := by
      rw [hrightZero] at hlengthExpanded
      rw [hdelta] at hslackInt
      omega
    exact terminal_no_right_exception_cases hn hDlarge hleftLe hbound
  · have hdelta : delta = left + 1 := by
      dsimp [delta]
      omega
    have hsTwo : 2 ≤ s := by
      have hrightLiteral : rightClusterException dec.chain 0 = 1 := by
        simpa [right, htrailing] using hrightOne
      exact terminalRightException_not_onlyCluster hDlarge htotalClusters
        hrightLiteral
    have hDmin : 4 - (left + 1) ≤ D := by
      have hbase : 2 * s ≤ D + delta := by omega
      rw [hdelta] at hbase
      omega
    have hbound : (r : ℤ) ≤
        2 - (left : ℤ) * ((n : ℤ) - 3) +
          (((n - 4) * ((D + left + 1) / 2) : ℕ) : ℤ) + (D : ℤ) := by
      rw [hrightOne] at hlengthExpanded
      rw [hdelta] at hslackInt
      simp only [Nat.add_assoc] at hslackInt ⊢
      omega
    exact terminal_right_exception_cases hn hDlarge hleftLe hDmin hbound

/-- The terminal-positive deficit consequence `D ≥ φ_n(r)+1`, derived from
the actual `N_n(D-1)` bound after `D≥1` has been established. -/
theorem terminalNonfull_phiN_add_one_le_total
    {n r D : ℕ} {d : List ℕ} (hn : 6 ≤ n) (hr : 1 ≤ r)
    (hlength : d.length = r) (hlegal : IsLegalDeficitSequence n d)
    (htotal : deficitSequenceTotal d = D)
    (hlast : ∃ x, d.getLast? = some x ∧ 0 < x) :
    phiN n r hn hr + 1 ≤ D := by
  have hDpos : 1 ≤ D := by
    have := total_pos_of_positive_last hlast
    omega
  have hlengthBound := terminalNonfull_length_le_maxLegalLength_sub_one
    hn hr hlength hlegal htotal hlast
  have hminimal := (phiN_is_minimum_maxLegalLength hn hr).2 (D - 1) hlengthBound
  omega

/-! ## Literal sharpness witnesses

The following block lists are the three strings displayed in the TeX proof.
The local sign-block infrastructure is deliberately concrete: it lets R1 and
R3 inspect the actual zero blocks instead of importing a legality assumption.
-/

private def TerminalBlockAllZero (b : List ℕ) : Prop :=
  ∀ x ∈ b, x = 0

private def TerminalBlockAllPositive (b : List ℕ) : Prop :=
  ∀ x ∈ b, 0 < x

private def TerminalSignBlocksSeparated (a b : List ℕ) : Prop :=
  ∃ ha hb, sameZeroStatus (a.getLast ha) (b.head hb) = false

private theorem terminal_zero_positive_separated {z p : List ℕ}
    (hz : TerminalBlockAllZero z) (hp : TerminalBlockAllPositive p)
    (hzne : z ≠ []) (hpne : p ≠ []) : TerminalSignBlocksSeparated z p := by
  refine ⟨hzne, hpne, ?_⟩
  have hzlast : z.getLast hzne = 0 := hz _ (List.getLast_mem hzne)
  have hppos : 0 < p.head hpne := hp _ (List.head_mem hpne)
  simp [sameZeroStatus, hzlast]
  omega

private theorem terminal_positive_zero_separated {p z : List ℕ}
    (hp : TerminalBlockAllPositive p) (hz : TerminalBlockAllZero z)
    (hpne : p ≠ []) (hzne : z ≠ []) : TerminalSignBlocksSeparated p z := by
  refine ⟨hpne, hzne, ?_⟩
  have hplast : 0 < p.getLast hpne := hp _ (List.getLast_mem hpne)
  have hzhead : z.head hzne = 0 := hz _ (List.head_mem hzne)
  simp [sameZeroStatus, hzhead]
  omega

private theorem terminal_sameZeroStatus_chain_of_allZero {b : List ℕ}
    (hb : TerminalBlockAllZero b) :
    b.IsChain fun x y => sameZeroStatus x y := by
  induction b with
  | nil => exact List.isChain_nil
  | cons a b ih =>
      apply List.isChain_cons.2
      constructor
      · intro x hx
        have ha0 : a = 0 := hb a (by simp)
        have hx0 : x = 0 := hb x (by
          exact List.mem_cons_of_mem a (List.mem_of_mem_head? hx))
        simp [sameZeroStatus, ha0, hx0]
      · exact ih (by
          intro x hx
          exact hb x (List.mem_cons_of_mem a hx))

private theorem terminal_sameZeroStatus_chain_of_allPositive {b : List ℕ}
    (hb : TerminalBlockAllPositive b) :
    b.IsChain fun x y => sameZeroStatus x y := by
  induction b with
  | nil => exact List.isChain_nil
  | cons a b ih =>
      apply List.isChain_cons.2
      constructor
      · intro x hx
        have ha : 0 < a := hb a (by simp)
        have hxpos : 0 < x := hb x (by
          exact List.mem_cons_of_mem a (List.mem_of_mem_head? hx))
        simp [sameZeroStatus]
        omega
      · exact ih (by
          intro x hx
          exact hb x (List.mem_cons_of_mem a hx))

/-- Alternating nonempty zero/positive block pairs, ending in a positive
block.  This is precisely the endpoint convention of the sharp strings. -/
private inductive TerminalAlternatingBlocks : List (List ℕ) → Prop
  | last {z p : List ℕ}
      (hz : TerminalBlockAllZero z) (hp : TerminalBlockAllPositive p)
      (hzne : z ≠ []) (hpne : p ≠ []) :
      TerminalAlternatingBlocks [z, p]
  | step {z p : List ℕ} {rest : List (List ℕ)}
      (hz : TerminalBlockAllZero z) (hp : TerminalBlockAllPositive p)
      (hzne : z ≠ []) (hpne : p ≠ [])
      (hrest : TerminalAlternatingBlocks rest) :
      TerminalAlternatingBlocks (z :: p :: rest)

private theorem TerminalAlternatingBlocks.head_zero
    {blocks : List (List ℕ)} (h : TerminalAlternatingBlocks blocks) :
    ∀ b ∈ blocks.head?, b ≠ [] ∧ TerminalBlockAllZero b := by
  cases h with
  | last hz hp hzne hpne => simpa using ⟨hzne, hz⟩
  | step hz hp hzne hpne hrest => simpa using ⟨hzne, hz⟩

private theorem TerminalAlternatingBlocks.no_empty
    {blocks : List (List ℕ)} (h : TerminalAlternatingBlocks blocks) :
    [] ∉ blocks := by
  induction h with
  | last hz hp hzne hpne => simp [hzne, hpne]
  | step hz hp hzne hpne hrest ih => simp [hzne, hpne, ih]

private theorem TerminalAlternatingBlocks.blocks_chain
    {blocks : List (List ℕ)} (h : TerminalAlternatingBlocks blocks) :
    ∀ b ∈ blocks, b.IsChain fun x y => sameZeroStatus x y := by
  induction h with
  | last hz hp hzne hpne =>
      intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | rfl | hb
      · exact terminal_sameZeroStatus_chain_of_allZero hz
      · exact terminal_sameZeroStatus_chain_of_allPositive hp
      · simp at hb
  | step hz hp hzne hpne hrest ih =>
      intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | rfl | hb
      · exact terminal_sameZeroStatus_chain_of_allZero hz
      · exact terminal_sameZeroStatus_chain_of_allPositive hp
      · exact ih b hb

private theorem TerminalAlternatingBlocks.separated
    {blocks : List (List ℕ)} (h : TerminalAlternatingBlocks blocks) :
    blocks.IsChain TerminalSignBlocksSeparated := by
  induction h with
  | last hz hp hzne hpne =>
      apply List.isChain_cons.2
      constructor
      · simpa using terminal_zero_positive_separated hz hp hzne hpne
      · simp
  | step hz hp hzne hpne hrest ih =>
      apply List.isChain_cons.2
      constructor
      · simpa using terminal_zero_positive_separated hz hp hzne hpne
      · apply List.isChain_cons.2
        constructor
        · intro b hb
          have hhead := hrest.head_zero b hb
          exact terminal_positive_zero_separated hp hhead.2 hpne hhead.1
        · exact ih

private theorem terminal_maximalSignBlocks_eq_of_alternating
    {blocks : List (List ℕ)} (h : TerminalAlternatingBlocks blocks) :
    maximalSignBlocks blocks.flatten = blocks := by
  unfold maximalSignBlocks
  apply List.splitBy_flatten h.no_empty h.blocks_chain
  exact h.separated

/-- The common terminal string
`(0^(mu-1) 2)^q 0^(mu-1) 1`, represented by its sign blocks. -/
private def terminalTailBlocks (mu : ℕ) : ℕ → List (List ℕ)
  | 0 => [List.replicate (mu - 1) 0, [1]]
  | q + 1 => List.replicate (mu - 1) 0 :: [2] ::
      terminalTailBlocks mu q

private theorem terminalTailBlocks_alternating {mu q : ℕ} (hmu : 2 ≤ mu) :
    TerminalAlternatingBlocks (terminalTailBlocks mu q) := by
  induction q with
  | zero =>
      apply TerminalAlternatingBlocks.last
      · simp [TerminalBlockAllZero]
      · simp [TerminalBlockAllPositive]
      · simp
        omega
      · simp
  | succ q ih =>
      apply TerminalAlternatingBlocks.step
      · simp [TerminalBlockAllZero]
      · simp [TerminalBlockAllPositive]
      · simp
        omega
      · simp
      · exact ih

private theorem terminalTailBlocks_length (mu q : ℕ) (hmu : 1 ≤ mu) :
    (terminalTailBlocks mu q).flatten.length = (q + 1) * mu := by
  induction q with
  | zero =>
      simp [terminalTailBlocks]
      omega
  | succ q ih =>
      simp [terminalTailBlocks, ih]
      have hm : mu - 1 + 1 = mu := by omega
      nlinarith

private theorem terminalTailBlocks_sum (mu q : ℕ) :
    (terminalTailBlocks mu q).flatten.sum = 2 * q + 1 := by
  induction q with
  | zero => simp [terminalTailBlocks]
  | succ q ih =>
      simp [terminalTailBlocks, ih]
      omega

private theorem terminalTailBlocks_getLast (mu q : ℕ) :
    (terminalTailBlocks mu q).flatten.getLast? = some 1 := by
  induction q with
  | zero => simp [terminalTailBlocks]
  | succ q ih =>
      simp only [terminalTailBlocks, List.flatten_cons]
      let tail := (terminalTailBlocks mu q).flatten
      have htailNe : tail ≠ [] := by
        intro hnil
        simp [tail, hnil] at ih
      cases htail : tail with
      | nil => exact (htailNe htail).elim
      | cons a rest => simpa [tail, htail] using ih

private theorem terminalTailBlocks_entries {mu q x : ℕ}
    (hx : x ∈ (terminalTailBlocks mu q).flatten) :
    x = 0 ∨ x = 1 ∨ x = 2 := by
  induction q with
  | zero =>
      simp only [terminalTailBlocks, List.flatten_cons, List.mem_append,
        List.mem_replicate, List.mem_singleton] at hx
      rcases hx with ⟨_, rfl⟩ | rfl | hx
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · simp at hx
  | succ q ih =>
      simp only [terminalTailBlocks, List.flatten_cons, List.mem_append,
        List.mem_replicate, List.mem_singleton] at hx
      rcases hx with ⟨_, rfl⟩ | rfl | hx
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
      · exact ih hx

private theorem terminalTail_zero_block_length {mu q : ℕ} {b : List ℕ}
    (_hmu : 2 ≤ mu) (hb : b ∈ terminalTailBlocks mu q)
    (hz : TerminalBlockAllZero b) : b.length = mu - 1 := by
  induction q generalizing b with
  | zero =>
      simp only [terminalTailBlocks, List.mem_cons] at hb
      rcases hb with rfl | rfl | hb
      · simp
      · have hone := hz 1 (by simp)
        omega
      · simp at hb
  | succ q ih =>
      simp only [terminalTailBlocks, List.mem_cons] at hb
      rcases hb with rfl | rfl | hb
      · simp
      · have htwo := hz 2 (by simp)
        omega
      · exact ih hb hz

/-- The sharp witness in the regime `r ≤ n-1`: `0^(r-1) 1`. -/
def terminalSmallWitness (r : ℕ) : List ℕ :=
  List.replicate (r - 1) 0 ++ [1]

private def terminalEvenWitnessBlocks (n t L : ℕ) : List (List ℕ) :=
  List.replicate L 0 :: [2] :: terminalTailBlocks (n - 2) (t - 1)

/-- The sharp witness in the regular regime `phiN=2t`:
`0^L 2 (0^(n-3) 2)^(t-1) 0^(n-3) 1`. -/
def terminalEvenWitness (n t L : ℕ) : List ℕ :=
  (terminalEvenWitnessBlocks n t L).flatten

private def terminalExceptionalWitnessBlocks (n t : ℕ) : List (List ℕ) :=
  List.replicate (n - 2) 0 :: [1, 2] ::
    terminalTailBlocks (n - 2) (t - 2)

/-- The exceptional-congruence witness:
`0^(n-2) 1 2 (0^(n-3) 2)^(t-2) 0^(n-3) 1`. -/
def terminalExceptionalWitness (n t : ℕ) : List ℕ :=
  (terminalExceptionalWitnessBlocks n t).flatten

private theorem terminalEvenWitnessBlocks_alternating {n t L : ℕ}
    (hn : 6 ≤ n) (hL : 1 ≤ L) :
    TerminalAlternatingBlocks (terminalEvenWitnessBlocks n t L) := by
  apply TerminalAlternatingBlocks.step
  · simp [TerminalBlockAllZero]
  · simp [TerminalBlockAllPositive]
  · simp
    omega
  · simp
  · exact terminalTailBlocks_alternating (by omega)

private theorem terminalExceptionalWitnessBlocks_alternating {n t : ℕ}
    (hn : 6 ≤ n) :
    TerminalAlternatingBlocks (terminalExceptionalWitnessBlocks n t) := by
  apply TerminalAlternatingBlocks.step
  · simp [TerminalBlockAllZero]
  · simp [TerminalBlockAllPositive]
  · simp
    omega
  · simp
  · exact terminalTailBlocks_alternating (by omega)

private theorem terminalEvenWitness_maximalSignBlocks {n t L : ℕ}
    (hn : 6 ≤ n) (hL : 1 ≤ L) :
    maximalSignBlocks (terminalEvenWitness n t L) =
      terminalEvenWitnessBlocks n t L := by
  exact terminal_maximalSignBlocks_eq_of_alternating
    (terminalEvenWitnessBlocks_alternating hn hL)

private theorem terminalExceptionalWitness_maximalSignBlocks {n t : ℕ}
    (hn : 6 ≤ n) :
    maximalSignBlocks (terminalExceptionalWitness n t) =
      terminalExceptionalWitnessBlocks n t := by
  exact terminal_maximalSignBlocks_eq_of_alternating
    (terminalExceptionalWitnessBlocks_alternating hn)

private theorem terminalEvenWitness_entries {n t L x : ℕ}
    (hx : x ∈ terminalEvenWitness n t L) : x = 0 ∨ x = 1 ∨ x = 2 := by
  simp only [terminalEvenWitness, terminalEvenWitnessBlocks,
    List.flatten_cons, List.mem_append, List.mem_replicate,
    List.mem_singleton] at hx
  rcases hx with ⟨_, rfl⟩ | rfl | hx
  · exact Or.inl rfl
  · exact Or.inr (Or.inr rfl)
  · exact terminalTailBlocks_entries hx

private theorem terminalExceptionalWitness_entries {n t x : ℕ}
    (hx : x ∈ terminalExceptionalWitness n t) :
    x = 0 ∨ x = 1 ∨ x = 2 := by
  simp only [terminalExceptionalWitness, terminalExceptionalWitnessBlocks,
    List.flatten_cons, List.mem_append, List.mem_replicate,
    List.mem_cons] at hx
  rcases hx with ⟨_, rfl⟩ | hx | hx
  · exact Or.inl rfl
  · simp only [List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · exact terminalTailBlocks_entries hx

private theorem terminalEven_zero_block_length_le {n t L : ℕ}
    {b : List ℕ} (hn : 6 ≤ n) (hL : L ≤ n - 2)
    (hb : b ∈ terminalEvenWitnessBlocks n t L)
    (hz : TerminalBlockAllZero b) : b.length ≤ n - 2 := by
  simp only [terminalEvenWitnessBlocks, List.mem_cons] at hb
  rcases hb with rfl | rfl | hb
  · simp
    exact hL
  · have htwo := hz 2 (by simp)
    omega
  · have hlen := terminalTail_zero_block_length (by omega) hb hz
    omega

private theorem terminalExceptional_zero_block_length_le {n t : ℕ}
    {b : List ℕ} (hn : 6 ≤ n)
    (hb : b ∈ terminalExceptionalWitnessBlocks n t)
    (hz : TerminalBlockAllZero b) : b.length ≤ n - 2 := by
  simp only [terminalExceptionalWitnessBlocks, List.mem_cons] at hb
  rcases hb with rfl | rfl | hb
  · simp
  · have hone := hz 1 (by simp)
    omega
  · have hlen := terminalTail_zero_block_length (by omega) hb hz
    omega

private theorem mem_tail_of_internal_block_decomposition
    {alpha : Type*} {l pre suf : List alpha} {x : alpha}
    (hdecomp : l = pre ++ x :: suf) (hpre : pre ≠ []) : x ∈ l.tail := by
  rw [hdecomp]
  cases pre with
  | nil => contradiction
  | cons a pre =>
      simp only [List.cons_append, List.tail_cons]
      exact List.mem_append_right pre (by simp)

private theorem terminalEven_internal_zero_length {n t L : ℕ}
    {pre suf : List (List ℕ)} {b : List ℕ} (hn : 6 ≤ n)
    (hdecomp : terminalEvenWitnessBlocks n t L = pre ++ b :: suf)
    (hpre : pre ≠ []) (hz : TerminalBlockAllZero b) :
    b.length = n - 3 := by
  have hb := mem_tail_of_internal_block_decomposition hdecomp hpre
  simp only [terminalEvenWitnessBlocks, List.tail_cons, List.mem_cons] at hb
  rcases hb with rfl | hb
  · have htwo := hz 2 (by simp)
    omega
  · have hlen := terminalTail_zero_block_length (by omega) hb hz
    omega

private theorem terminalExceptional_internal_zero_length {n t : ℕ}
    {pre suf : List (List ℕ)} {b : List ℕ} (hn : 6 ≤ n)
    (hdecomp : terminalExceptionalWitnessBlocks n t = pre ++ b :: suf)
    (hpre : pre ≠ []) (hz : TerminalBlockAllZero b) :
    b.length = n - 3 := by
  have hb := mem_tail_of_internal_block_decomposition hdecomp hpre
  simp only [terminalExceptionalWitnessBlocks, List.tail_cons,
    List.mem_cons] at hb
  rcases hb with rfl | hb
  · have hone := hz 1 (by simp)
    omega
  · have hlen := terminalTail_zero_block_length (by omega) hb hz
    omega

theorem terminalSmallWitness_length {r : ℕ} (hr : 1 ≤ r) :
    (terminalSmallWitness r).length = r := by
  simp [terminalSmallWitness]
  omega

theorem terminalSmallWitness_total (r : ℕ) :
    deficitSequenceTotal (terminalSmallWitness r) = 1 := by
  simp [deficitSequenceTotal, terminalSmallWitness]

theorem terminalSmallWitness_positive_last (r : ℕ) :
    ∃ x, (terminalSmallWitness r).getLast? = some x ∧ 0 < x := by
  refine ⟨1, ?_, by omega⟩
  simp [terminalSmallWitness]

private theorem terminalSmallWitness_one_index {r j : ℕ} (hr : 1 ≤ r)
    (hj : j < (terminalSmallWitness r).length)
    (hone : deficitAt (terminalSmallWitness r) j = 1) : j = r - 1 := by
  by_cases hbefore : j < r - 1
  · have hzero : deficitAt (terminalSmallWitness r) j = 0 := by
      rw [deficitAt_eq_get _ j hj]
      simp [terminalSmallWitness, hbefore]
    omega
  have hlen := terminalSmallWitness_length hr
  omega

theorem terminalSmallWitness_legal {n r : ℕ} (hn : 6 ≤ n)
    (hr : 1 ≤ r) (hrsmall : r ≤ n - 1) :
    IsLegalDeficitSequence n (terminalSmallWitness r) where
  six_le := hn
  nonempty := by simp [terminalSmallWitness]
  entries_lt := by
    intro x hx
    simp [terminalSmallWitness] at hx
    rcases hx with ⟨_, rfl⟩ | rfl <;> omega
  rule1 := by
    have hnotAll : ¬ ∀ x ∈ terminalSmallWitness r, x = 0 := by
      intro hall
      have hone := hall 1 (by simp [terminalSmallWitness])
      omega
    simp only [if_neg hnotAll]
    intro start blockLength hblock
    rcases hblock with ⟨hpos, hwithin, hzeros, _hleft, _hright⟩
    have hlen := terminalSmallWitness_length hr
    have hblockLe : blockLength ≤ r - 1 := by
      by_contra hnot
      have hstart : start = 0 := by omega
      have hblockEq : blockLength = r := by omega
      have hz := hzeros (r - 1) (by omega)
      rw [hstart] at hz
      simp only [zero_add] at hz
      have hlast : deficitAt (terminalSmallWitness r) (r - 1) = 1 := by
        rw [deficitAt_eq_get _ _ (by omega)]
        simp [terminalSmallWitness]
      omega
    have hsmallPred := Nat.sub_le_sub_right hrsmall 1
    omega
  rule2 := by
    intro i hi hpattern
    have hi1 : i + 1 < (terminalSmallWitness r).length := by omega
    have honeIndex := terminalSmallWitness_one_index hr hi1 hpattern.2.1
    have hlen := terminalSmallWitness_length hr
    omega
  rule3 := by
    intro start hblock hleft hright
    have hlen := terminalSmallWitness_length hr
    omega

/-- Literal length calculation for the regular TeX string. -/
theorem terminalEvenWitness_length {n t L : ℕ} (hn : 6 ≤ n)
    (ht : 1 ≤ t) :
    (terminalEvenWitness n t L).length =
      L + 1 + (t - 1) * (n - 2) + (n - 3) + 1 := by
  have htail := terminalTailBlocks_length (n - 2) (t - 1) (by omega)
  have htSplit : t - 1 + 1 = t := by omega
  have hprod : (t - 1 + 1) * (n - 2) =
      (t - 1) * (n - 2) + (n - 2) := by
    rw [Nat.add_mul]
    simp
  simp [terminalEvenWitness, terminalEvenWitnessBlocks, htail]
  omega

theorem terminalEvenWitness_total (n t L : ℕ) (ht : 1 ≤ t) :
    deficitSequenceTotal (terminalEvenWitness n t L) = 2 * t + 1 := by
  have htail := terminalTailBlocks_sum (n - 2) (t - 1)
  simp [deficitSequenceTotal, terminalEvenWitness,
    terminalEvenWitnessBlocks, htail]
  omega

theorem terminalEvenWitness_positive_last (n t L : ℕ) :
    ∃ x, (terminalEvenWitness n t L).getLast? = some x ∧ 0 < x := by
  refine ⟨1, ?_, by omega⟩
  let tail := (terminalTailBlocks (n - 2) (t - 1)).flatten
  have htailLast : tail.getLast? = some 1 := by
    exact terminalTailBlocks_getLast _ _
  have htailNe : tail ≠ [] := by
    intro hnil
    simp [hnil] at htailLast
  change (List.replicate L 0 ++ ([2] ++ tail)).getLast? = some 1
  rw [List.getLast?_append_of_ne_nil _ (by simp)]
  rw [List.getLast?_append_of_ne_nil _ htailNe]
  exact htailLast

private theorem terminalTailBlocks_one_index {mu q j : ℕ} (hmu : 1 ≤ mu)
    (hj : j < (terminalTailBlocks mu q).flatten.length)
    (hone : deficitAt (terminalTailBlocks mu q).flatten j = 1) :
    j + 1 = (terminalTailBlocks mu q).flatten.length := by
  induction q generalizing j with
  | zero =>
      have hlen := terminalTailBlocks_length mu 0 hmu
      by_cases hbefore : j < mu - 1
      · have hzero : deficitAt (terminalTailBlocks mu 0).flatten j = 0 := by
          rw [deficitAt_eq_get _ j hj]
          simp [terminalTailBlocks, hbefore]
        omega
      · omega
  | succ q ih =>
      let pref := List.replicate (mu - 1) 0 ++ [2]
      let tail := (terminalTailBlocks mu q).flatten
      have hprefLength : pref.length = mu := by
        dsimp [pref]
        simp
        omega
      have hshape : (terminalTailBlocks mu (q + 1)).flatten = pref ++ tail := by
        simp [terminalTailBlocks, pref, tail, List.append_assoc]
      rw [hshape] at hone hj ⊢
      by_cases hpref : j < pref.length
      · have hmem : (pref ++ tail).get ⟨j, hj⟩ ∈ pref := by
          rw [List.get_eq_getElem, List.getElem_append_left hpref]
          exact List.getElem_mem _
        rw [deficitAt_eq_get _ j hj] at hone
        have hentry : (pref ++ tail).get ⟨j, hj⟩ = 0 ∨
            (pref ++ tail).get ⟨j, hj⟩ = 2 := by
          dsimp [pref] at hmem
          simp only [List.mem_append, List.mem_replicate,
            List.mem_singleton] at hmem
          rcases hmem with ⟨_, hzero⟩ | htwo
          · exact Or.inl hzero
          · exact Or.inr htwo
        rcases hentry with hzero | htwo <;> omega
      · let k := j - pref.length
        have hk : k < tail.length := by
          dsimp [k]
          simp only [List.length_append] at hj
          omega
        have hprefLe : pref.length ≤ j := by omega
        have htailOne : deficitAt tail k = 1 := by
          rw [deficitAt_eq_get _ j hj] at hone
          rw [deficitAt_eq_get _ k hk]
          simp only [List.get_eq_getElem] at hone ⊢
          rw [List.getElem_append_right hprefLe] at hone
          simpa [k] using hone
        have hlast := ih hk htailOne
        simp only [List.length_append] at hj ⊢
        change k + 1 = tail.length at hlast
        dsimp [k] at hlast
        omega

private theorem terminalEvenWitness_one_index {n t L j : ℕ}
    (hn : 6 ≤ n)
    (hj : j < (terminalEvenWitness n t L).length)
    (hone : deficitAt (terminalEvenWitness n t L) j = 1) :
    j + 1 = (terminalEvenWitness n t L).length := by
  let pref := List.replicate L 0 ++ [2]
  let tail := (terminalTailBlocks (n - 2) (t - 1)).flatten
  have hshape : terminalEvenWitness n t L = pref ++ tail := by
    simp [terminalEvenWitness, terminalEvenWitnessBlocks, pref, tail,
      List.append_assoc]
  rw [hshape] at hone hj ⊢
  by_cases hpref : j < pref.length
  · have hmem : (pref ++ tail).get ⟨j, hj⟩ ∈ pref := by
      rw [List.get_eq_getElem, List.getElem_append_left hpref]
      exact List.getElem_mem _
    rw [deficitAt_eq_get _ j hj] at hone
    have hentry : (pref ++ tail).get ⟨j, hj⟩ = 0 ∨
        (pref ++ tail).get ⟨j, hj⟩ = 2 := by
      dsimp [pref] at hmem
      simp only [List.mem_append, List.mem_replicate,
        List.mem_singleton] at hmem
      rcases hmem with ⟨_, hzero⟩ | htwo
      · exact Or.inl hzero
      · exact Or.inr htwo
    rcases hentry with hzero | htwo <;> omega
  · let k := j - pref.length
    have hk : k < tail.length := by
      dsimp [k]
      simp only [List.length_append] at hj
      omega
    have hprefLe : pref.length ≤ j := by omega
    have htailOne : deficitAt tail k = 1 := by
      rw [deficitAt_eq_get _ j hj] at hone
      rw [deficitAt_eq_get _ k hk]
      simp only [List.get_eq_getElem] at hone ⊢
      rw [List.getElem_append_right hprefLe] at hone
      simpa [k] using hone
    have hlast := terminalTailBlocks_one_index (mu := n - 2)
      (q := t - 1) (j := k) (by omega) hk htailOne
    simp only [List.length_append] at hj ⊢
    change k + 1 = tail.length at hlast
    dsimp [k] at hlast
    omega

theorem terminalEvenWitness_legal {n t L : ℕ} (hn : 6 ≤ n)
    (_ht : 1 ≤ t) (hLpos : 1 ≤ L) (hLle : L ≤ n - 2) :
    IsLegalDeficitSequence n (terminalEvenWitness n t L) where
  six_le := hn
  nonempty := by simp [terminalEvenWitness, terminalEvenWitnessBlocks]
  entries_lt := by
    intro x hx
    rcases terminalEvenWitness_entries hx with rfl | rfl | rfl <;> omega
  rule1 := by
    have hnotAll : ¬ ∀ x ∈ terminalEvenWitness n t L, x = 0 := by
      intro hall
      have htwo := hall 2 (by
        simp [terminalEvenWitness, terminalEvenWitnessBlocks])
      omega
    simp only [if_neg hnotAll]
    intro start blockLength hblock
    apply maximalZeroBlock_length_le_of_blocks (bound := n - 2) ?_ hblock
    intro b hb hz
    rw [terminalEvenWitness_maximalSignBlocks hn hLpos] at hb
    exact terminalEven_zero_block_length_le hn hLle hb hz
  rule2 := by
    intro i hi hpattern
    have hi1 : i + 1 < (terminalEvenWitness n t L).length := by omega
    have honeIndex := terminalEvenWitness_one_index hn hi1 hpattern.2.1
    omega
  rule3 := by
    intro start hblock hleft hright
    obtain ⟨pre, suf, hpre, hsuf, hdecomp⟩ :=
      maximalZeroBlock_internal_sign_decomposition hblock hleft hright
    rw [terminalEvenWitness_maximalSignBlocks hn hLpos] at hdecomp
    have hlen := terminalEven_internal_zero_length
      (b := List.replicate (n - 2) 0) hn
      (by simpa [List.append_assoc] using hdecomp) hpre
      (by simp [TerminalBlockAllZero])
    simp only [List.length_replicate] at hlen
    omega

/-- Literal length calculation for the exceptional TeX string. -/
theorem terminalExceptionalWitness_length {n t : ℕ} (hn : 6 ≤ n)
    (ht : 2 ≤ t) :
    (terminalExceptionalWitness n t).length = (n - 2) * t + 2 := by
  have htail := terminalTailBlocks_length (n - 2) (t - 2) (by omega)
  have htSplit : t - 2 + 1 = t - 1 := by omega
  have htDecomp : t = (t - 1) + 1 := by omega
  have htailProd : (t - 2 + 1) * (n - 2) =
      (t - 1) * (n - 2) := congrArg (fun z => z * (n - 2)) htSplit
  have hprod : (n - 2) * t =
      (n - 2) + (t - 1) * (n - 2) := by
    calc
      (n - 2) * t = (n - 2) * ((t - 1) + 1) := by rw [← htDecomp]
      _ = _ := by ring
  simp [terminalExceptionalWitness, terminalExceptionalWitnessBlocks, htail]
  omega

theorem terminalExceptionalWitness_total (n t : ℕ) (ht : 2 ≤ t) :
    deficitSequenceTotal (terminalExceptionalWitness n t) = 2 * t := by
  have htail := terminalTailBlocks_sum (n - 2) (t - 2)
  simp [deficitSequenceTotal, terminalExceptionalWitness,
    terminalExceptionalWitnessBlocks, htail]
  omega

theorem terminalExceptionalWitness_positive_last (n t : ℕ) :
    ∃ x, (terminalExceptionalWitness n t).getLast? = some x ∧ 0 < x := by
  refine ⟨1, ?_, by omega⟩
  let tail := (terminalTailBlocks (n - 2) (t - 2)).flatten
  have htailLast : tail.getLast? = some 1 := by
    exact terminalTailBlocks_getLast _ _
  have htailNe : tail ≠ [] := by
    intro hnil
    simp [hnil] at htailLast
  change (List.replicate (n - 2) 0 ++ ([1, 2] ++ tail)).getLast? = some 1
  rw [List.getLast?_append_of_ne_nil _ (by simp)]
  rw [List.getLast?_append_of_ne_nil _ htailNe]
  exact htailLast

private theorem terminalExceptionalWitness_one_index {n t j : ℕ}
    (hn : 6 ≤ n)
    (hj : j < (terminalExceptionalWitness n t).length)
    (hone : deficitAt (terminalExceptionalWitness n t) j = 1) :
    j = n - 2 ∨ j + 1 = (terminalExceptionalWitness n t).length := by
  let pref := List.replicate (n - 2) 0 ++ [1, 2]
  let tail := (terminalTailBlocks (n - 2) (t - 2)).flatten
  have hprefLength : pref.length = n := by
    dsimp [pref]
    simp
    omega
  have hshape : terminalExceptionalWitness n t = pref ++ tail := by
    simp [terminalExceptionalWitness, terminalExceptionalWitnessBlocks,
      pref, tail, List.append_assoc]
  rw [hshape] at hone hj ⊢
  by_cases hpref : j < pref.length
  · by_cases hzeros : j < n - 2
    · have hzero : deficitAt (pref ++ tail) j = 0 := by
        rw [deficitAt_eq_get _ j hj]
        simp [pref, hzeros]
      omega
    · by_cases honePlace : j = n - 2
      · exact Or.inl honePlace
      · have htwoPlace : j = n - 2 + 1 := by
          rw [hprefLength] at hpref
          omega
        have htwo : deficitAt (pref ++ tail) j = 2 := by
          rw [deficitAt_eq_get _ j hj]
          simp [pref, htwoPlace]
        omega
  · let k := j - pref.length
    have hk : k < tail.length := by
      dsimp [k]
      simp only [List.length_append] at hj
      omega
    have hprefLe : pref.length ≤ j := by omega
    have htailOne : deficitAt tail k = 1 := by
      rw [deficitAt_eq_get _ j hj] at hone
      rw [deficitAt_eq_get _ k hk]
      simp only [List.get_eq_getElem] at hone ⊢
      rw [List.getElem_append_right hprefLe] at hone
      simpa [k] using hone
    have hlast := terminalTailBlocks_one_index (mu := n - 2)
      (q := t - 2) (j := k) (by omega) hk htailOne
    right
    simp only [List.length_append] at hj ⊢
    change k + 1 = tail.length at hlast
    dsimp [k] at hlast
    omega

theorem terminalExceptionalWitness_legal {n t : ℕ} (hn : 6 ≤ n)
    (_ht : 2 ≤ t) :
    IsLegalDeficitSequence n (terminalExceptionalWitness n t) where
  six_le := hn
  nonempty := by
    simp [terminalExceptionalWitness, terminalExceptionalWitnessBlocks]
  entries_lt := by
    intro x hx
    rcases terminalExceptionalWitness_entries hx with rfl | rfl | rfl <;> omega
  rule1 := by
    have hnotAll : ¬ ∀ x ∈ terminalExceptionalWitness n t, x = 0 := by
      intro hall
      have hone := hall 1 (by
        simp [terminalExceptionalWitness, terminalExceptionalWitnessBlocks])
      omega
    simp only [if_neg hnotAll]
    intro start blockLength hblock
    apply maximalZeroBlock_length_le_of_blocks (bound := n - 2) ?_ hblock
    intro b hb hz
    rw [terminalExceptionalWitness_maximalSignBlocks hn] at hb
    exact terminalExceptional_zero_block_length_le hn hb hz
  rule2 := by
    intro i hi hpattern
    have hi1 : i + 1 < (terminalExceptionalWitness n t).length := by omega
    rcases terminalExceptionalWitness_one_index hn hi1 hpattern.2.1 with
      honeLeading | honeFinal
    · have hi2 : i + 2 < (terminalExceptionalWitness n t).length := by omega
      have hindex : i + 2 = n - 2 + 1 := by omega
      have htwo : deficitAt (terminalExceptionalWitness n t) (i + 2) = 2 := by
        rw [hindex]
        rw [deficitAt_eq_get _ _ (by omega)]
        simp [terminalExceptionalWitness, terminalExceptionalWitnessBlocks]
      omega
    · omega
  rule3 := by
    intro start hblock hleft hright
    obtain ⟨pre, suf, hpre, hsuf, hdecomp⟩ :=
      maximalZeroBlock_internal_sign_decomposition hblock hleft hright
    rw [terminalExceptionalWitness_maximalSignBlocks hn] at hdecomp
    have hlen := terminalExceptional_internal_zero_length
      (b := List.replicate (n - 2) 0) hn
      (by simpa [List.append_assoc] using hdecomp) hpre
      (by simp [TerminalBlockAllZero])
    simp only [List.length_replicate] at hlen
    omega

/-- Sharpness in Lemma `lem:nf`: at every positive length, the displayed
terminal-positive witness has total exactly `phiN n r + 1`.  The proof
splits into the three literal TeX regimes. -/
theorem exists_terminalNonfull_sharp {n r : ℕ} (hn : 6 ≤ n) (hr : 1 ≤ r) :
    ∃ d : List ℕ, d.length = r ∧ IsLegalDeficitSequence n d ∧
      (∃ x, d.getLast? = some x ∧ 0 < x) ∧
      deficitSequenceTotal d = phiN n r hn hr + 1 := by
  by_cases hsmall : r ≤ n - 1
  · -- Regime 1: `0^(r-1) 1`.
    have hnotExceptional :
        ¬(n + (n - 2) ≤ r ∧ Nat.ModEq (n - 2) r n) := by
      intro h
      omega
    have hPhi : PhiN n r hr = 0 := by
      simp [PhiN, hsmall]
    have hphi : phiN n r hn hr = 0 := by
      rw [phiN_closed_form hn hr, if_neg hnotExceptional, hPhi]
    refine ⟨terminalSmallWitness r, terminalSmallWitness_length hr,
      terminalSmallWitness_legal hn hr hsmall,
      terminalSmallWitness_positive_last r, ?_⟩
    rw [terminalSmallWitness_total, hphi]
  · have hrn : n ≤ r := by omega
    let mu := n - 2
    let t := (r - 2) / mu
    let rem := (r - 2) % mu
    have hmu : 4 ≤ mu := by
      dsimp [mu]
      omega
    have hmupos : 0 < mu := by omega
    have ht : 1 ≤ t := by
      apply (Nat.le_div_iff_mul_le hmupos).2
      dsimp [t, mu]
      omega
    have hrem : rem < mu := Nat.mod_lt _ hmupos
    have hdivision := Nat.mod_add_div (r - 2) mu
    have hdecomp : r = 2 + mu * t + rem := by
      change rem + mu * t = r - 2 at hdivision
      omega
    have hPhi : PhiN n r hr = 2 * t := by
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
    · -- Regime 3: the exceptional `0^(n-2) 1 2 ... 1` string.
      have ht2 : 2 ≤ t := by
        apply (Nat.le_div_iff_mul_le hmupos).2
        dsimp [t, mu]
        omega
      have hremZero : rem = 0 := by
        apply hmodIff.mp
        simpa [mu] using hexceptional.2
      have hrShape : r = (n - 2) * t + 2 := by
        dsimp [mu] at hdecomp
        rw [hremZero] at hdecomp
        omega
      have hphi : phiN n r hn hr = 2 * t - 1 := by
        rw [phiN_closed_form hn hr, if_pos hexceptional, hPhi]
      refine ⟨terminalExceptionalWitness n t, ?_,
        terminalExceptionalWitness_legal hn ht2,
        terminalExceptionalWitness_positive_last n t, ?_⟩
      · rw [terminalExceptionalWitness_length hn ht2, hrShape]
      · rw [terminalExceptionalWitness_total n t ht2, hphi]
        omega
    · -- Regime 2: `phiN=2t`, with the literal `L` from the TeX proof.
      have hphi : phiN n r hn hr = 2 * t := by
        rw [phiN_closed_form hn hr, if_neg hexceptional, hPhi]
      let L := r - (n - 2) * t - 1
      have hLShape : L = rem + 1 := by
        dsimp [L, mu] at hdecomp ⊢
        omega
      have hLpos : 1 ≤ L := by omega
      have hLle : L ≤ n - 2 := by
        dsimp [mu] at hrem
        omega
      have htDecomp : t = (t - 1) + 1 := by omega
      have hprod : (n - 2) * t =
          (t - 1) * (n - 2) + (n - 2) := by
        calc
          (n - 2) * t = (n - 2) * ((t - 1) + 1) := by rw [← htDecomp]
          _ = _ := by ring
      have hlength : (terminalEvenWitness n t L).length = r := by
        rw [terminalEvenWitness_length hn ht]
        dsimp [mu] at hdecomp
        omega
      refine ⟨terminalEvenWitness n t L, hlength,
        terminalEvenWitness_legal hn ht hLpos hLle,
        terminalEvenWitness_positive_last n t L, ?_⟩
      rw [terminalEvenWitness_total n t L ht, hphi]

end SuperpermutationLowerBound
