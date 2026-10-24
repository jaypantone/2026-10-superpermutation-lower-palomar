module

public import SuperpermutationLowerBound.Section07.EndpointDeficits

@[expose] public section

-- Export private helpers used in exposed definitions; this adds no axiom.
set_option backward.privateInPublic true

namespace SuperpermutationLowerBound

/-! Frozen Section 8, from the run-boundary excess through Remark
`rem:noqone`.  The primary capacity theory is stated for an arbitrary actual
block-aligned exitless path.  Forest components enter only in the two
cheap-entry results.
-/

open PermutationVertex

variable {k : ℕ}

/-! ## Literal adjacent-boundary sums -/

/-- Sum `weight(xᵢ,xᵢ₊₁)-base` over every adjacent pair of a list. -/
private def adjacentExcess {α : Type*} (weight : α → α → ℕ) (base : ℕ) :
    List α → ℕ
  | [] => 0
  | [_] => 0
  | x :: y :: rest =>
      weight x y - base + adjacentExcess weight base (y :: rest)

/-- The boundary weight between two lists, totalized only to make the
generic flattening identity convenient.  All mathematical uses have two
nonempty lists. -/
private def listBoundaryWeight {α : Type*} (weight : α → α → ℕ)
    (left right : List α) : ℕ :=
  match left.getLast?, right.head? with
  | some x, some y => weight x y
  | _, _ => 0

private theorem adjacentExcess_append {α : Type*}
    (weight : α → α → ℕ) (base : ℕ)
    {left right : List α} (hleft : left ≠ []) (hright : right ≠ []) :
    adjacentExcess weight base (left ++ right) =
      adjacentExcess weight base left +
        (listBoundaryWeight weight left right - base) +
          adjacentExcess weight base right := by
  induction left with
  | nil => exact (hleft rfl).elim
  | cons x tail ih =>
      cases tail with
      | nil =>
          cases right with
          | nil => exact (hright rfl).elim
          | cons y rest => simp [adjacentExcess, listBoundaryWeight]
      | cons y rest =>
          have htail : y :: rest ≠ [] := List.cons_ne_nil _ _
          change weight x y - base +
              adjacentExcess weight base ((y :: rest) ++ right) = _
          rw [ih htail]
          simp [adjacentExcess, listBoundaryWeight]
          omega

private theorem listBoundaryWeight_flatten_cons {α : Type*}
    (weight : α → α → ℕ) {left first : List α}
    {rest : List (List α)} (hleft : left ≠ []) (hfirst : first ≠ []) :
    listBoundaryWeight weight left ((first :: rest).flatten) =
      listBoundaryWeight weight left first := by
  simp [listBoundaryWeight, hleft, hfirst,
    List.getLast?_eq_some_getLast, List.head?_eq_some_head]

private theorem adjacentExcess_flatten {α : Type*}
    (weight : α → α → ℕ) (base : ℕ)
    (parts : List (List α)) (hnil : [] ∉ parts) :
    adjacentExcess weight base parts.flatten =
      (parts.map (adjacentExcess weight base)).sum +
        adjacentExcess (listBoundaryWeight weight) base parts := by
  induction parts with
  | nil => simp [adjacentExcess]
  | cons first rest ih =>
      have hfirst : first ≠ [] := by
        intro h
        apply hnil
        simp [h]
      have hrestNil : [] ∉ rest := by
        intro h
        exact hnil (by simp [h])
      cases rest with
      | nil => simp [adjacentExcess]
      | cons second tail =>
          have hsecond : second ≠ [] := by
            intro h
            apply hrestNil
            simp [h]
          have hflatTail : (second :: tail).flatten ≠ [] := by
            simp [hsecond]
          rw [List.flatten_cons,
            adjacentExcess_append weight base hfirst hflatTail]
          rw [ih hrestNil]
          rw [listBoundaryWeight_flatten_cons weight hfirst hsecond]
          simp [adjacentExcess, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm]

private theorem adjacentExcess_eq_zero_of_chain {α : Type*}
    (weight : α → α → ℕ) (base : ℕ) {xs : List α}
    (hchain : xs.IsChain fun x y => weight x y = base) :
    adjacentExcess weight base xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x tail ih =>
      cases tail with
      | nil => rfl
      | cons y rest =>
          rw [List.isChain_cons] at hchain
          simp only [List.head?_cons, Option.mem_def] at hchain
          simp [adjacentExcess, hchain.1, ih hchain.2]

private theorem adjacentExcess_shift_one {α : Type*}
    (weight : α → α → ℕ) (base : ℕ) {xs : List α}
    (hchain : xs.IsChain fun x y => base + 1 ≤ weight x y) :
    adjacentExcess weight base xs =
      (xs.length - 1) + adjacentExcess weight (base + 1) xs := by
  induction xs with
  | nil => simp [adjacentExcess]
  | cons x tail ih =>
      cases tail with
      | nil => simp [adjacentExcess]
      | cons y rest =>
          rw [List.isChain_cons] at hchain
          simp only [List.head?_cons, Option.mem_def] at hchain
          have hxy : base + 1 ≤ weight x y := by
            simpa using hchain.1
          have htail := ih hchain.2
          have htail' : adjacentExcess weight base (y :: rest) =
              rest.length + adjacentExcess weight (base + 1) (y :: rest) := by
            simpa using htail
          have hweight : weight x y - base =
              1 + (weight x y - (base + 1)) := by omega
          simp only [adjacentExcess, List.length_cons]
          rw [htail', hweight]
          simp only [Nat.add_sub_cancel]
          omega

private theorem adjacentExcess_ge_length_sub_one {α : Type*}
    (weight : α → α → ℕ) (base : ℕ) {xs : List α}
    (hchain : xs.IsChain fun x y => base + 1 ≤ weight x y) :
    xs.length - 1 ≤ adjacentExcess weight base xs := by
  rw [adjacentExcess_shift_one weight base hchain]
  omega

private noncomputable def blockEntryBoundaryWeight
    (u v : PermutationVertex k) : ℕ :=
  overlapWeight (blockExit u) v

private noncomputable def adjacentBlockBoundaryWeights :
    List (PermutationVertex k) → List ℕ
  | [] => []
  | [_] => []
  | u :: v :: rest =>
      blockEntryBoundaryWeight u v :: adjacentBlockBoundaryWeights (v :: rest)

private theorem adjacentBlockBoundaryWeights_sum_sub
    (entries : List (PermutationVertex k)) (base : ℕ) :
    ((adjacentBlockBoundaryWeights entries).map fun w => w - base).sum =
      adjacentExcess blockEntryBoundaryWeight base entries := by
  induction entries with
  | nil => rfl
  | cons u tail ih =>
      cases tail with
      | nil => rfl
      | cons v rest =>
          simp [adjacentBlockBoundaryWeights, adjacentExcess, ih]

@[simp] private theorem adjacentBlockBoundaryWeights_length
    (entries : List (PermutationVertex k)) :
    (adjacentBlockBoundaryWeights entries).length = entries.length - 1 := by
  induction entries with
  | nil => rfl
  | cons u tail ih =>
      cases tail with
      | nil => rfl
      | cons v rest =>
          simp [adjacentBlockBoundaryWeights, ih]

private theorem adjacentBlockBoundaryWeights_get
    (entries : List (PermutationVertex k)) (i : ℕ)
    (hi : i + 1 < entries.length) :
    (adjacentBlockBoundaryWeights entries).get
        ⟨i, by simp; omega⟩ =
      blockEntryBoundaryWeight
        (entries.get ⟨i, by omega⟩)
        (entries.get ⟨i + 1, hi⟩) := by
  induction entries generalizing i with
  | nil => simp at hi
  | cons u tail ih =>
      cases tail with
      | nil => simp at hi
      | cons v rest =>
          cases i with
          | zero => rfl
          | succ i =>
              simpa [adjacentBlockBoundaryWeights] using
                ih i (by simpa using hi)

private theorem blockBoundaryWeights_eq_adjacent (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    blockBoundaryWeights p hp =
      adjacentBlockBoundaryWeights (blockAlignedBlockEntries hk p hp) := by
  apply List.ext_get
  · simp
  · intro i hiLeft hiRight
    have hi0 : i < pathBlockCount p - 1 := by simpa using hiLeft
    have hi : i + 1 < pathBlockCount p := by omega
    rw [adjacentBlockBoundaryWeights_get _ i (by simpa using hi)]
    exact blockAlignedBoundaryWeight_eq hk p hp i hi

private theorem pathExcess_eq_adjacentRunsAboveTwo (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    pathExcess p hp =
      adjacentExcess runBoundaryWeight 2 (blockAlignedRuns hk p hp) := by
  let entries := blockAlignedBlockEntries hk p hp
  let runs := blockAlignedRuns hk p hp
  have hparts := adjacentExcess_flatten blockEntryBoundaryWeight 2 runs
    (blockAlignedRuns_spec hk p hp).2.1
  have hflatten : runs.flatten = entries := blockAlignedRuns_spec hk p hp |>.1
  have hinternal :
      (runs.map (adjacentExcess blockEntryBoundaryWeight 2)).sum = 0 := by
    apply List.sum_eq_zero
    intro value hvalue
    obtain ⟨run, hrun, rfl⟩ := List.mem_map.mp hvalue
    exact adjacentExcess_eq_zero_of_chain blockEntryBoundaryWeight 2
      ((blockAlignedRuns_spec hk p hp).2.2.1 run hrun)
  have hboundary :
      adjacentExcess
          (listBoundaryWeight blockEntryBoundaryWeight) 2 runs =
        adjacentExcess runBoundaryWeight 2 runs := by
    apply congrArg (fun weight => adjacentExcess weight 2 runs)
    funext left right
    unfold listBoundaryWeight blockEntryBoundaryWeight runBoundaryWeight
    cases left.getLast? <;> cases right.head? <;> rfl
  unfold pathExcess
  rw [blockBoundaryWeights_eq_adjacent hk p hp]
  rw [adjacentBlockBoundaryWeights_sum_sub]
  change adjacentExcess blockEntryBoundaryWeight 2 entries = _
  rw [← hflatten, hparts, hinternal, zero_add, hboundary]

/-! ## The frozen `A_h`, `z`, and `h_n` data -/

/-- The literal run-boundary excess
`A_h(p)=∑(w(e)-3)`, summed over all `q-1` actual canonical run
boundaries of a block-aligned path. -/
noncomputable def blockAlignedRunBoundaryExcess (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) : ℕ :=
  adjacentExcess runBoundaryWeight 3 (blockAlignedRuns hk p hp)

/-- The generic path parameter `z=ε+1`. -/
noncomputable def blockAlignedZ (p : OverlapPath k)
    (hp : IsBlockAligned p) : ℕ :=
  pathExcess p hp + 1

/-- The abstract block capacity `h_n(z)=nz-φ_n(z)`. -/
noncomputable def hN (n z : ℕ) (hn : 6 ≤ n) (hz : 1 ≤ z) : ℕ :=
  n * z - phiN n z hn hz

private theorem blockAlignedRunBoundaries_ge_three (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    (blockAlignedRuns hk p hp).IsChain
      (fun left right => 3 ≤ runBoundaryWeight left right) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  exact blockAlignedRunBoundary_weight_ge_three hk p hp i hi

/-- First identity in `eq:zdecomp`: `ε=(q-1)+A_h`. -/
theorem blockAlignedExcess_eq_runCount_sub_one_add_boundaryExcess
    (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p) :
    pathExcess p hp =
      (blockAlignedRunCount hk p hp - 1) +
        blockAlignedRunBoundaryExcess hk p hp := by
  rw [pathExcess_eq_adjacentRunsAboveTwo hk p hp]
  exact adjacentExcess_shift_one runBoundaryWeight 2
    (blockAlignedRunBoundaries_ge_three hk p hp)

/-- Second identity in `eq:zdecomp`: `z=q+A_h`. -/
theorem blockAlignedZ_eq_runCount_add_boundaryExcess
    (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p) :
    blockAlignedZ p hp =
      blockAlignedRunCount hk p hp +
        blockAlignedRunBoundaryExcess hk p hp := by
  have hq : 1 ≤ blockAlignedRunCount hk p hp := by
    unfold blockAlignedRunCount
    exact List.length_pos_of_ne_nil (blockAlignedRuns_nonempty hk p hp)
  rw [blockAlignedZ,
    blockAlignedExcess_eq_runCount_sub_one_add_boundaryExcess hk p hp]
  omega

/-- Exact last sentence of `eq:zdecomp`: `z=1` exactly for one run. -/
theorem blockAlignedZ_eq_one_iff_runCount_eq_one
    (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p) :
    blockAlignedZ p hp = 1 ↔ blockAlignedRunCount hk p hp = 1 := by
  rw [blockAlignedZ_eq_runCount_add_boundaryExcess hk p hp]
  have hq : 1 ≤ blockAlignedRunCount hk p hp := by
    unfold blockAlignedRunCount
    exact List.length_pos_of_ne_nil (blockAlignedRuns_nonempty hk p hp)
  constructor
  · omega
  · intro hrun
    have hruns : ∃ run, blockAlignedRuns hk p hp = [run] := by
      have hne := blockAlignedRuns_nonempty hk p hp
      cases h : blockAlignedRuns hk p hp with
      | nil => exact (hne h).elim
      | cons run rest =>
          have : rest = [] := by
            simpa [blockAlignedRunCount, h] using hrun
          subst rest
          exact ⟨run, rfl⟩
    obtain ⟨run, hruns⟩ := hruns
    simp [blockAlignedRunBoundaryExcess, hruns, adjacentExcess, hrun]

/-! ## Numerical aggregation -/

private theorem nat_add_div_le (a b m : ℕ) (hm : 0 < m) :
    (a + b) / m ≤ a / m + b / m + 1 := by
  rw [Nat.add_div hm]
  split <;> omega

private theorem phiN_le_PhiN {n r : ℕ} (hn : 6 ≤ n) (hr : 1 ≤ r) :
    phiN n r hn hr ≤ PhiN n r hr := by
  rw [phiN_closed_form hn hr]
  split <;> omega

private theorem PhiN_le_phiN_add_one {n r : ℕ}
    (hn : 6 ≤ n) (hr : 1 ≤ r) :
    PhiN n r hr ≤ phiN n r hn hr + 1 := by
  rw [phiN_closed_form hn hr]
  split
  · rename_i hexceptional
    have hrlarge : n ≤ r := by omega
    have hmu : 0 < n - 2 := by omega
    have hquot : 1 ≤ (r - n + (n - 2)) / (n - 2) := by
      apply (Nat.le_div_iff_mul_le hmu).2
      omega
    unfold PhiN
    rw [if_neg (by omega)]
    omega
  · omega

private theorem PhiN_add_add_one_le {n x y : ℕ}
    (hn : 6 ≤ n) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    PhiN n (x + y + 1) (by omega) ≤
      PhiN n x hx + PhiN n y hy + 4 := by
  let mu := n - 2
  have hmu : 4 ≤ mu := by dsimp [mu]; omega
  by_cases htarget : x + y + 1 ≤ n - 1
  · simp [PhiN, htarget]
  have htargetLarge : n ≤ x + y + 1 := by omega
  by_cases hxsmall : x ≤ n - 1
  · by_cases hysmall : y ≤ n - 1
    · have hnum : x + y + 1 - n + (n - 2) = x + y - 1 := by omega
      have hlt : x + y - 1 < 3 * mu := by dsimp [mu]; omega
      have hdiv : (x + y - 1) / mu < 3 :=
        (Nat.div_lt_iff_lt_mul (by omega)).2 (by simpa [Nat.mul_comm] using hlt)
      dsimp [mu] at hdiv
      simp only [PhiN, if_neg htarget, if_pos hxsmall, if_pos hysmall,
        Nat.zero_add]
      rw [hnum]
      omega
    · have hylarge : n ≤ y := by omega
      have hnumTarget : x + y + 1 - n + (n - 2) =
          (y - 2) + (x + 1) := by omega
      have hnumY : y - n + (n - 2) = y - 2 := by omega
      have hsmallAdd : x + 1 < 2 * mu := by dsimp [mu]; omega
      have hsmallDiv : (x + 1) / mu < 2 :=
        (Nat.div_lt_iff_lt_mul (by omega)).2
          (by simpa [Nat.mul_comm] using hsmallAdd)
      have hadd := nat_add_div_le (y - 2) (x + 1) mu (by omega)
      dsimp [mu] at hsmallDiv hadd
      simp only [PhiN, if_neg htarget, if_pos hxsmall, if_neg hysmall]
      rw [hnumTarget, hnumY]
      omega
  · have hxlarge : n ≤ x := by omega
    by_cases hysmall : y ≤ n - 1
    · have hnumTarget : x + y + 1 - n + (n - 2) =
          (x - 2) + (y + 1) := by omega
      have hnumX : x - n + (n - 2) = x - 2 := by omega
      have hsmallAdd : y + 1 < 2 * mu := by dsimp [mu]; omega
      have hsmallDiv : (y + 1) / mu < 2 :=
        (Nat.div_lt_iff_lt_mul (by omega)).2
          (by simpa [Nat.mul_comm] using hsmallAdd)
      have hadd := nat_add_div_le (x - 2) (y + 1) mu (by omega)
      dsimp [mu] at hsmallDiv hadd
      simp only [PhiN, if_neg htarget, if_neg hxsmall, if_pos hysmall]
      rw [hnumTarget, hnumX]
      omega
    · have hylarge : n ≤ y := by omega
      have hnumTarget : x + y + 1 - n + (n - 2) =
          (x - 2) + ((y - 2) + 3) := by omega
      have hnumX : x - n + (n - 2) = x - 2 := by omega
      have hnumY : y - n + (n - 2) = y - 2 := by omega
      have hthree : 3 / mu = 0 := Nat.div_eq_of_lt (by omega)
      have hfirst := nat_add_div_le (x - 2) ((y - 2) + 3) mu (by omega)
      have hsecond := nat_add_div_le (y - 2) 3 mu (by omega)
      dsimp [mu] at hfirst hsecond hthree
      simp only [PhiN, if_neg htarget, if_neg hxsmall, if_neg hysmall]
      rw [hnumTarget, hnumX, hnumY, hthree] at *
      omega

private theorem PhiN_succ_le {n x : ℕ} (hn : 6 ≤ n) (hx : 1 ≤ x) :
    PhiN n (x + 1) (by omega) ≤ PhiN n x hx + 2 := by
  let mu := n - 2
  have hmu : 4 ≤ mu := by dsimp [mu]; omega
  by_cases htarget : x + 1 ≤ n - 1
  · simp [PhiN, htarget]
  have htargetLarge : n ≤ x + 1 := by omega
  by_cases hxsmall : x ≤ n - 1
  · have hxexact : x = n - 1 := by omega
    subst x
    unfold PhiN
    rw [if_neg (by omega), if_pos (by omega)]
    have hnum : n - 1 + 1 - n + (n - 2) = n - 2 := by omega
    rw [hnum, Nat.div_self (by omega)]
  · have hxlarge : n ≤ x := by omega
    have hnumTarget : x + 1 - n + (n - 2) = (x - 2) + 1 := by omega
    have hnumX : x - n + (n - 2) = x - 2 := by omega
    have hone : 1 / mu = 0 := Nat.div_eq_of_lt (by omega)
    have hadd := nat_add_div_le (x - 2) 1 mu (by omega)
    dsimp [mu] at hone hadd
    simp only [PhiN, if_neg htarget, if_neg hxsmall]
    rw [hnumTarget, hnumX, hone] at *
    omega

private theorem phiN_add_add_one_le {n x y : ℕ}
    (hn : 6 ≤ n) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    phiN n (x + y + 1) hn (by omega) ≤
      phiN n x hn hx + phiN n y hn hy + n := by
  have htop := phiN_le_PhiN hn (show 1 ≤ x + y + 1 by omega)
  have hmerge := PhiN_add_add_one_le hn hx hy
  have hxclose := PhiN_le_phiN_add_one hn hx
  have hyclose := PhiN_le_phiN_add_one hn hy
  omega

private theorem phiN_succ_le_add_n {n x : ℕ}
    (hn : 6 ≤ n) (hx : 1 ≤ x) :
    phiN n (x + 1) hn (by omega) ≤ phiN n x hn hx + n := by
  have htop := phiN_le_PhiN hn (show 1 ≤ x + 1 by omega)
  have hstep := PhiN_succ_le hn hx
  have hxclose := PhiN_le_phiN_add_one hn hx
  omega

private theorem phiN_add_le_add_mul {n x t : ℕ}
    (hn : 6 ≤ n) (hx : 1 ≤ x) :
    phiN n (x + t) hn (by omega) ≤ phiN n x hn hx + n * t := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hstep := phiN_succ_le_add_n hn (show 1 ≤ x + t by omega)
      have hindex : x + (t + 1) = (x + t) + 1 := by omega
      have hstep' : phiN n (x + (t + 1)) hn (by omega) ≤
          phiN n (x + t) hn (by omega) + n := by
        simpa only [hindex] using hstep
      rw [Nat.mul_add, Nat.mul_one]
      omega

private theorem phiN_aggregation_minimal {n m : ℕ}
    (hn : 6 ≤ n) (r : Fin (m + 1) → ℕ)
    (hr : ∀ i, 1 ≤ r i) :
    phiN n ((∑ i, r i) + m) hn (by
      have hzero : r 0 ≤ ∑ i, r i :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ 0)
      have hpos := hr 0
      omega) ≤
      (∑ i, phiN n (r i) hn (hr i)) + n * m := by
  induction m with
  | zero => simp
  | succ m ih =>
      let tail : Fin (m + 1) → ℕ := fun i => r i.succ
      have htail : ∀ i, 1 ≤ tail i := fun i => hr i.succ
      have hih := ih tail htail
      have hmerge := phiN_add_add_one_le hn (hr 0)
        (show 1 ≤ (∑ i, tail i) + m by
          have hzero : tail 0 ≤ ∑ i, tail i :=
            Finset.single_le_sum (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ 0)
          have := htail 0
          omega)
      have hsumR : (∑ i, r i) = r 0 + ∑ i, tail i := by
        simpa [tail] using Fin.sum_univ_succ r
      have hsumPhi : (∑ i, phiN n (r i) hn (hr i)) =
          phiN n (r 0) hn (hr 0) +
            ∑ i, phiN n (tail i) hn (htail i) := by
        simpa [tail] using Fin.sum_univ_succ
          (fun i => phiN n (r i) hn (hr i))
      have harg : (∑ i, r i) + (m + 1) =
          r 0 + ((∑ i, tail i) + m) + 1 := by
        rw [hsumR]
        omega
      have hmerge' : phiN n ((∑ i, r i) + (m + 1)) hn (by
            have hzero : r 0 ≤ ∑ i, r i :=
              Finset.single_le_sum (fun _ _ => Nat.zero_le _)
                (Finset.mem_univ 0)
            have := hr 0
            omega) ≤
          phiN n (r 0) hn (hr 0) +
            phiN n ((∑ i, tail i) + m) hn (by
              have hzero : tail 0 ≤ ∑ i, tail i :=
                Finset.single_le_sum (fun _ _ => Nat.zero_le _)
                  (Finset.mem_univ 0)
              have := htail 0
              omega) + n := by
        simpa only [harg] using hmerge
      rw [hsumPhi, Nat.mul_add, Nat.mul_one]
      omega

/-- **Aggregation (Lemma `lem:aggregation`).**  The segment lengths are
positive, their `Fin`-sum is exactly `q`, and the literal hypothesis is
`A ≥ m-1`. -/
theorem phiN_aggregation {n m q A : ℕ} (hn : 6 ≤ n)
    (hm : 1 ≤ m) (r : Fin m → ℕ)
    (hr : ∀ i, 1 ≤ r i) (hsum : ∑ i, r i = q)
    (hA : m - 1 ≤ A) :
    phiN n (q + A) hn (by
      have hq : 1 ≤ q := by
        rw [← hsum]
        let j : Fin m := ⟨0, hm⟩
        have hj : r j ≤ ∑ i, r i :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ j)
        exact (hr j).trans hj
      omega) ≤
      (∑ i, phiN n (r i) hn (hr i)) + n * A := by
  cases m with
  | zero => omega
  | succ t =>
      have ht : t ≤ A := by simpa using hA
      have hminimal := phiN_aggregation_minimal hn r hr
      have hdelta : q + A = (q + t) + (A - t) := by omega
      have hq : 1 ≤ q := by
        rw [← hsum]
        have hzero : r 0 ≤ ∑ i, r i :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ 0)
        exact (hr 0).trans hzero
      have hstep := phiN_add_le_add_mul hn
        (show 1 ≤ q + t by omega) (t := A - t)
      have hstep' : phiN n (q + A) hn (by omega) ≤
          phiN n (q + t) hn (by omega) + n * (A - t) := by
        simpa only [hdelta] using hstep
      have hsum' : (∑ i, r i) + t = q + t := by rw [hsum]
      have hminimal' : phiN n (q + t) hn (by omega) ≤
          (∑ i, phiN n (r i) hn (hr i)) + n * t := by
        simpa only [hsum'] using hminimal
      have hmul : n * A = n * t + n * (A - t) := by
        rw [← Nat.mul_add]
        congr
        omega
      rw [hmul]
      omega

/-! ## Actual canonical light-segment data -/

private theorem blockAlignedLightSegments_nonempty (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    blockAlignedLightSegments hk p hp ≠ [] := by
  unfold blockAlignedLightSegments
  exact List.splitBy_ne_nil.mpr (blockAlignedRuns_nonempty hk p hp)

private theorem blockAlignedLightSegmentLengths_sum (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    ((blockAlignedLightSegments hk p hp).map List.length).sum =
      blockAlignedRunCount hk p hp := by
  have hlength := congrArg List.length
    (blockAlignedLightSegments_spec hk p hp).1
  simpa [blockAlignedRunCount] using hlength

private theorem blockAlignedLightSegmentLengths_fin_sum (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    (∑ i : Fin (blockAlignedLightSegments hk p hp).length,
      (blockAlignedLightSegmentAt hk p hp i).length) =
      blockAlignedRunCount hk p hp := by
  let segments := blockAlignedLightSegments hk p hp
  rw [← blockAlignedLightSegmentLengths_sum hk p hp]
  rw [← List.sum_ofFn]
  change (List.ofFn (fun i : Fin segments.length => segments[i].length)).sum =
    (segments.map List.length).sum
  exact congrArg List.sum
    (List.ofFn_getElem_eq_map segments List.length)

private theorem blockAlignedRunBoundaryExcess_ge_lightSegments_sub_one
    (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p) :
    (blockAlignedLightSegments hk p hp).length - 1 ≤
      blockAlignedRunBoundaryExcess hk p hp := by
  let segments := blockAlignedLightSegments hk p hp
  let runs := blockAlignedRuns hk p hp
  have hparts := adjacentExcess_flatten runBoundaryWeight 3 segments
    (blockAlignedLightSegments_spec hk p hp).2.1
  have hflatten : segments.flatten = runs :=
    (blockAlignedLightSegments_spec hk p hp).1
  have hinternal :
      (segments.map (adjacentExcess runBoundaryWeight 3)).sum = 0 := by
    apply List.sum_eq_zero
    intro value hvalue
    obtain ⟨segment, hsegment, rfl⟩ := List.mem_map.mp hvalue
    apply adjacentExcess_eq_zero_of_chain runBoundaryWeight 3
    exact ((blockAlignedLightSegments_spec hk p hp).2.2.1
      segment hsegment).imp (by
        intro left right hlight
        exact hlight)
  have hbetween : segments.IsChain
      (fun left right =>
        4 ≤ listBoundaryWeight runBoundaryWeight left right) := by
    rw [List.isChain_iff_getElem]
    intro i hi
    have hi0 : i < segments.length := by omega
    let left := blockAlignedLightSegmentAt hk p hp
      ⟨i, by simpa [segments] using hi0⟩
    let right := blockAlignedLightSegmentAt hk p hp
      ⟨i + 1, by simpa [segments] using hi⟩
    have hweight :=
      (blockAlignedLightSegmentAt_adjacent_boundary hk p hp i hi).2
    have hweight' := (Nat.succ_le_iff).2 hweight
    have hleft : left.runs ≠ [] := by
      exact List.ne_nil_of_mem_splitBy left.isSegment
    have hright : right.runs ≠ [] := by
      exact List.ne_nil_of_mem_splitBy right.isSegment
    change 4 ≤ listBoundaryWeight runBoundaryWeight left.runs right.runs
    simp [listBoundaryWeight, hleft, hright,
      List.getLast?_eq_some_getLast, List.head?_eq_some_head]
    simpa [left, right, BlockAlignedLightSegment.lastRun,
      BlockAlignedLightSegment.firstRun,
      BlockAlignedLightSegment.runAt, BlockAlignedLightSegment.length,
      List.getLast_eq_getElem, List.head_eq_getElem_zero] using hweight'
  have hbetweenLower := adjacentExcess_ge_length_sub_one
    (listBoundaryWeight runBoundaryWeight) 3 hbetween
  unfold blockAlignedRunBoundaryExcess
  change segments.length - 1 ≤ adjacentExcess runBoundaryWeight 3 runs
  rw [← hflatten, hparts, hinternal, zero_add]
  exact hbetweenLower

private theorem blockAlignedTotalDeficit_eq_sum_lightSegments
    (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p) :
    blockAlignedTotalDeficit hk p hp =
      ∑ i : Fin (blockAlignedLightSegments hk p hp).length,
        (blockAlignedLightSegmentAt hk p hp i).totalDeficit := by
  let segments := blockAlignedLightSegments hk p hp
  unfold blockAlignedTotalDeficit
  rw [blockAlignedDeficitString_eq_lightSegments hk p hp]
  change (segments.flatMap
      (fun segment => segment.map (fun run => (k - 1) - run.length))).sum = _
  have hsumFlat :
      (segments.flatMap
        (fun segment => segment.map (fun run => (k - 1) - run.length))).sum =
      (segments.map (fun segment =>
        (segment.map (fun run => (k - 1) - run.length)).sum)).sum := by
    induction segments with
    | nil => simp
    | cons segment segments ih => simp [ih]
  rw [hsumFlat]
  rw [← List.sum_ofFn]
  change (segments.map (fun segment =>
      (segment.map (fun run => (k - 1) - run.length)).sum)).sum =
    (List.ofFn (fun i : Fin segments.length =>
      ((segments[i]).map (fun run => (k - 1) - run.length)).sum)).sum
  exact congrArg List.sum
    (List.ofFn_getElem_eq_map segments (fun segment =>
      (segment.map (fun run => (k - 1) - run.length)).sum)).symm

private theorem blockAlignedLightSegment_deficitAt_eq_global
    (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p)
    (segment : BlockAlignedLightSegment hk p hp)
    (j : ℕ) (hj : j < segment.length) :
    deficitAt segment.deficitString j =
      deficitAt (blockAlignedDeficitString hk p hp)
        (segment.globalStart + j) := by
  rw [deficitAt_eq_get _ _ (by
      simpa using hj), deficitAt_eq_get _ _ (by
        have := blockAlignedLightSegment_globalStart_bounds hk p hp segment
        simpa [blockAlignedDeficitString] using (show
          segment.globalStart + j < (blockAlignedRuns hk p hp).length by omega))]
  have hlocal := blockAlignedLightSegment_deficitString_get hk p hp segment
    ⟨j, hj⟩
  simpa [blockAlignedDeficitString, blockAlignedRunAt,
    BlockAlignedRun.deficit, BlockAlignedRun.length] using hlocal

private theorem blockAlignedFirstDeficit_eq_deficitAt_zero
    (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p) :
    blockAlignedFirstDeficit hk p hp =
      deficitAt (blockAlignedDeficitString hk p hp) 0 := by
  let d := blockAlignedDeficitString hk p hp
  have hd : d ≠ [] := by
    simpa [d, blockAlignedDeficitString] using
      blockAlignedRuns_nonempty hk p hp
  rw [deficitAt_eq_get d 0 (List.length_pos_of_ne_nil hd)]
  change d.head hd = d.get ⟨0, List.length_pos_of_ne_nil hd⟩
  exact List.head_eq_getElem_zero hd

private theorem blockAlignedLastDeficit_eq_deficitAt_last
    (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p) :
    blockAlignedLastDeficit hk p hp =
      deficitAt (blockAlignedDeficitString hk p hp)
        (blockAlignedRunCount hk p hp - 1) := by
  let d := blockAlignedDeficitString hk p hp
  have hd : d ≠ [] := by
    simpa [d, blockAlignedDeficitString] using
      blockAlignedRuns_nonempty hk p hp
  have hlen : d.length = blockAlignedRunCount hk p hp := by
    exact blockAlignedDeficitString_length hk p hp
  rw [show blockAlignedRunCount hk p hp - 1 = d.length - 1 by rw [hlen]]
  rw [deficitAt_eq_get d (d.length - 1) (by
    exact Nat.sub_lt (List.length_pos_of_ne_nil hd) (by omega))]
  change d.getLast hd = d.get
    ⟨d.length - 1, Nat.sub_lt (List.length_pos_of_ne_nil hd) (by omega)⟩
  exact List.getLast_eq_getElem hd

private theorem firstLightSegment_globalStart_zero
    (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p) :
    (blockAlignedLightSegmentAt hk p hp
      ⟨0, List.length_pos_of_ne_nil
        (blockAlignedLightSegments_nonempty hk p hp)⟩).globalStart = 0 := by
  rw [blockAlignedLightSegmentAt_globalStart]
  simp

private theorem lastLightSegment_end_eq_runCount
    (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p) :
    let segments := blockAlignedLightSegments hk p hp
    let last : Fin segments.length :=
      ⟨segments.length - 1,
        Nat.sub_lt (List.length_pos_of_ne_nil
          (blockAlignedLightSegments_nonempty hk p hp)) (by omega)⟩
    (blockAlignedLightSegmentAt hk p hp last).globalStart +
        (blockAlignedLightSegmentAt hk p hp last).length =
      blockAlignedRunCount hk p hp := by
  dsimp only
  let segments := blockAlignedLightSegments hk p hp
  have hm : 0 < segments.length :=
    List.length_pos_of_ne_nil (blockAlignedLightSegments_nonempty hk p hp)
  let last : Fin segments.length := ⟨segments.length - 1, by omega⟩
  change (blockAlignedLightSegmentAt hk p hp last).globalStart +
      (blockAlignedLightSegmentAt hk p hp last).length =
    blockAlignedRunCount hk p hp
  rw [blockAlignedLightSegmentAt_globalStart]
  change (segments.take last).flatten.length +
      (segments.get last).length = blockAlignedRunCount hk p hp
  have htake := List.take_concat_get' segments last.1 last.2
  have hlast : last.1 + 1 = segments.length := by
    dsimp [last]
    omega
  rw [hlast, List.take_length] at htake
  have hlength := congrArg (fun xs => xs.flatten.length) htake
  have hflat := congrArg List.length
    (blockAlignedLightSegments_spec hk p hp).1
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.length_append] at hlength
  simpa [segments, blockAlignedRunCount] using hlength.trans hflat

private theorem firstLightSegment_firstDeficit
    (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p) :
    let first : Fin (blockAlignedLightSegments hk p hp).length :=
      ⟨0, List.length_pos_of_ne_nil
        (blockAlignedLightSegments_nonempty hk p hp)⟩
    deficitAt (blockAlignedLightSegmentAt hk p hp first).deficitString 0 =
      blockAlignedFirstDeficit hk p hp := by
  dsimp only
  let first : Fin (blockAlignedLightSegments hk p hp).length :=
    ⟨0, List.length_pos_of_ne_nil
      (blockAlignedLightSegments_nonempty hk p hp)⟩
  let segment := blockAlignedLightSegmentAt hk p hp first
  have hpos : 0 < segment.length :=
    blockAlignedLightSegment_length_pos hk p hp segment
  have hglobal := blockAlignedLightSegment_deficitAt_eq_global
    hk p hp segment 0 hpos
  have hstart : segment.globalStart = 0 := by
    simp [segment, first]
  calc
    deficitAt segment.deficitString 0 =
        deficitAt (blockAlignedDeficitString hk p hp) 0 := by
      simpa [hstart] using hglobal
    _ = blockAlignedFirstDeficit hk p hp :=
      (blockAlignedFirstDeficit_eq_deficitAt_zero hk p hp).symm

private theorem lastLightSegment_lastDeficit
    (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p) :
    let segments := blockAlignedLightSegments hk p hp
    let last : Fin segments.length :=
      ⟨segments.length - 1,
        Nat.sub_lt (List.length_pos_of_ne_nil
          (blockAlignedLightSegments_nonempty hk p hp)) (by omega)⟩
    deficitAt (blockAlignedLightSegmentAt hk p hp last).deficitString
        ((blockAlignedLightSegmentAt hk p hp last).length - 1) =
      blockAlignedLastDeficit hk p hp := by
  dsimp only
  let segments := blockAlignedLightSegments hk p hp
  have hm : 0 < segments.length :=
    List.length_pos_of_ne_nil (blockAlignedLightSegments_nonempty hk p hp)
  let last : Fin segments.length := ⟨segments.length - 1, by omega⟩
  let segment := blockAlignedLightSegmentAt hk p hp last
  have hpos : 0 < segment.length :=
    blockAlignedLightSegment_length_pos hk p hp segment
  have hglobal := blockAlignedLightSegment_deficitAt_eq_global
    hk p hp segment (segment.length - 1) (by omega)
  have hend : segment.globalStart + segment.length =
      blockAlignedRunCount hk p hp := by
    simpa [segments, last, segment] using
      lastLightSegment_end_eq_runCount hk p hp
  have hindex : segment.globalStart + (segment.length - 1) =
      blockAlignedRunCount hk p hp - 1 := by omega
  calc
    deficitAt segment.deficitString (segment.length - 1) =
        deficitAt (blockAlignedDeficitString hk p hp)
          (blockAlignedRunCount hk p hp - 1) := by
      simpa only [hindex] using hglobal
    _ = blockAlignedLastDeficit hk p hp :=
      (blockAlignedLastDeficit_eq_deficitAt_last hk p hp).symm

private theorem phiN_one_eq_zero (n : ℕ) (hn : 6 ≤ n) :
    phiN n 1 hn (by omega) = 0 := by
  rw [phiN_closed_form hn (show 1 ≤ 1 by omega)]
  rw [if_neg (by omega)]
  simp [PhiN, show 1 ≤ n - 1 by omega]

private theorem leftEndpointCharge_le_self (a : ℕ) :
    max 0 (a - 1) ≤ a := by
  simp

private theorem endpointChargeB_le_self (b : ℕ) :
    endpointChargeB b ≤ b := by
  by_cases hb0 : b = 0
  · subst b
    simp
  by_cases hb1 : b = 1
  · subst b
    simp
  have hb2 : 2 ≤ b := by omega
  rw [endpointChargeB_eq_sub_one hb2]
  omega

private theorem deficitSequenceTotal_eq_deficitAt_zero_of_length_one
    {d : List ℕ} (hlength : d.length = 1) :
    deficitSequenceTotal d = deficitAt d 0 := by
  cases d with
  | nil => simp at hlength
  | cons x xs =>
      have hnil : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlength)
      subst xs
      simp [deficitSequenceTotal, deficitAt]

/-! The endpoint theorem is now applied to the actual canonical segments.
The two singleton branches below are deliberately separate: the public
endpoint theorem has the exact domain `2 ≤ q`, so it cannot be invoked on a
one-run first or last segment. -/

private theorem blockAlignedSegmentEndpointSum {a b : ℕ}
    (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p)
    (hq : 2 ≤ blockAlignedRunCount hk p hp)
    (ha : a ≤ k - 3) (hb : b ≤ k - 2)
    (hfirst : a ≤ blockAlignedFirstDeficit hk p hp)
    (hlast : b ≤ blockAlignedLastDeficit hk p hp) :
    (∑ i : Fin (blockAlignedLightSegments hk p hp).length,
        phiN (k - 1) (blockAlignedLightSegmentAt hk p hp i).length
          (by omega)
          (blockAlignedLightSegment_length_pos hk p hp
            (blockAlignedLightSegmentAt hk p hp i))) +
      max 0 (a - 1) + endpointChargeB b ≤
        blockAlignedTotalDeficit hk p hp := by
  classical
  let segments := blockAlignedLightSegments hk p hp
  have hm : 0 < segments.length :=
    List.length_pos_of_ne_nil (blockAlignedLightSegments_nonempty hk p hp)
  let first : Fin segments.length := ⟨0, hm⟩
  let last : Fin segments.length := ⟨segments.length - 1, by omega⟩
  have hfirstValue :
      deficitAt (blockAlignedLightSegmentAt hk p hp first).deficitString 0 =
        blockAlignedFirstDeficit hk p hp := by
    simpa [segments, first] using firstLightSegment_firstDeficit hk p hp
  have hlastValue :
      deficitAt (blockAlignedLightSegmentAt hk p hp last).deficitString
          ((blockAlignedLightSegmentAt hk p hp last).length - 1) =
        blockAlignedLastDeficit hk p hp := by
    simpa [segments, last] using lastLightSegment_lastDeficit hk p hp
  have hpoint (i : Fin segments.length) :
      phiN (k - 1) (blockAlignedLightSegmentAt hk p hp i).length
          (by omega)
          (blockAlignedLightSegment_length_pos hk p hp
            (blockAlignedLightSegmentAt hk p hp i)) +
        (if i = first then max 0 (a - 1) else 0) +
        (if i = last then endpointChargeB b else 0) ≤
          (blockAlignedLightSegmentAt hk p hp i).totalDeficit := by
    let segment := blockAlignedLightSegmentAt hk p hp i
    have hr : 1 ≤ segment.length :=
      blockAlignedLightSegment_length_pos hk p hp segment
    by_cases hrTwo : 2 ≤ segment.length
    · let ai := if i = first then a else 0
      let bi := if i = last then b else 0
      have hai : ai ≤ k - 3 := by
        dsimp [ai]
        split <;> omega
      have hbi : bi ≤ k - 2 := by
        dsimp [bi]
        split <;> omega
      have haiLocal : ai ≤ deficitAt segment.deficitString 0 := by
        by_cases hi : i = first
        · subst i
          simpa [ai, segment] using hfirst.trans_eq hfirstValue.symm
        · simp [ai, hi]
      have hbiLocal : bi ≤
          deficitAt segment.deficitString (segment.length - 1) := by
        by_cases hi : i = last
        · subst i
          simpa [bi, segment] using hlast.trans_eq hlastValue.symm
        · simp [bi, hi]
      have hendpoint := endpointDeficitBound
        (n := k - 1) (q := segment.length)
        (D := segment.totalDeficit) (a := ai) (b := bi)
        (d := segment.deficitString)
        (by omega) hrTwo hai hbi
        (blockAlignedLightSegment_deficitString_length hk p hp segment)
        (blockAlignedLightSegment_deficitString_legal hk p hp segment)
        (BlockAlignedLightSegment.deficitSequenceTotal_deficitString segment)
        haiLocal hbiLocal
      have haiCharge : max 0 (ai - 1) =
          (if i = first then max 0 (a - 1) else 0) := by
        by_cases hi : i = first <;> simp [ai, hi]
      have hbiCharge : endpointChargeB bi =
          (if i = last then endpointChargeB b else 0) := by
        by_cases hi : i = last <;> simp [bi, hi]
      rw [haiCharge, hbiCharge] at hendpoint
      simpa [segment] using hendpoint
    · have hrOne : segment.length = 1 := by omega
      have hphi :
          phiN (k - 1) segment.length (by omega) hr = 0 := by
        simpa [hrOne] using phiN_one_eq_zero (k - 1) (by omega)
      have htotalEntry : segment.totalDeficit =
          deficitAt segment.deficitString 0 := by
        change deficitSequenceTotal segment.deficitString =
          deficitAt segment.deficitString 0
        exact deficitSequenceTotal_eq_deficitAt_zero_of_length_one
          (d := segment.deficitString) (by simpa using hrOne)
      by_cases hifirst : i = first
      · by_cases hilast : i = last
        · have hstart : segment.globalStart = 0 := by
            simp [segment, hifirst, segments, first]
          have hend : segment.globalStart + segment.length =
              blockAlignedRunCount hk p hp := by
            simpa [segment, hilast, segments, last] using
              lastLightSegment_end_eq_runCount hk p hp
          exfalso
          omega
        · have haLocal : a ≤ deficitAt segment.deficitString 0 := by
            subst i
            simpa [segment] using hfirst.trans_eq hfirstValue.symm
          rw [hphi, htotalEntry]
          simp only [zero_add, if_pos hifirst, if_neg hilast, add_zero]
          exact (leftEndpointCharge_le_self a).trans haLocal
      · by_cases hilast : i = last
        · have hbLocal : b ≤ deficitAt segment.deficitString 0 := by
            have hbLocalLast : b ≤
                deficitAt segment.deficitString (segment.length - 1) := by
              subst i
              simpa [segment] using hlast.trans_eq hlastValue.symm
            simpa [hrOne] using hbLocalLast
          rw [hphi, htotalEntry]
          simp only [zero_add, if_neg hifirst, if_pos hilast]
          exact (endpointChargeB_le_self b).trans hbLocal
        · have hbase := phiN_le_total_of_legal
            (n := k - 1) (r := segment.length) (d := segment.deficitString)
            (by omega) hr
            (blockAlignedLightSegment_deficitString_length hk p hp segment)
            (blockAlignedLightSegment_deficitString_legal hk p hp segment)
          rw [BlockAlignedLightSegment.deficitSequenceTotal_deficitString] at hbase
          simpa [segment, hifirst, hilast] using hbase
  have hsum := Finset.sum_le_sum (fun i (_hi : i ∈ Finset.univ) => hpoint i)
  simp only [Finset.sum_add_distrib] at hsum
  have hleftSum :
      (∑ i : Fin segments.length,
        if i = first then max 0 (a - 1) else 0) = max 0 (a - 1) := by
    simp
  have hrightSum :
      (∑ i : Fin segments.length,
        if i = last then endpointChargeB b else 0) = endpointChargeB b := by
    simp
  rw [hleftSum, hrightSum] at hsum
  rw [← blockAlignedTotalDeficit_eq_sum_lightSegments hk p hp] at hsum
  simpa [segments] using hsum

private theorem blockAlignedLastDeficit_le (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    blockAlignedLastDeficit hk p hp ≤ k - 2 := by
  let segments := blockAlignedLightSegments hk p hp
  have hm : 0 < segments.length :=
    List.length_pos_of_ne_nil (blockAlignedLightSegments_nonempty hk p hp)
  let last : Fin segments.length := ⟨segments.length - 1, by omega⟩
  let segment := blockAlignedLightSegmentAt hk p hp last
  have hr : 0 < segment.length :=
    blockAlignedLightSegment_length_pos hk p hp segment
  have hentry : deficitAt segment.deficitString (segment.length - 1) < k - 1 := by
    rw [deficitAt_eq_get segment.deficitString (segment.length - 1) (by
      simpa using (show segment.length - 1 < segment.length by omega))]
    exact (blockAlignedLightSegment_deficitString_legal hk p hp segment).entries_lt
      _ (List.get_mem _ _)
  have hvalue : deficitAt segment.deficitString (segment.length - 1) =
      blockAlignedLastDeficit hk p hp := by
    simpa [segments, last, segment] using lastLightSegment_lastDeficit hk p hp
  omega

private theorem blockAlignedFirstDeficit_le (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    blockAlignedFirstDeficit hk p hp ≤ k - 2 := by
  let segments := blockAlignedLightSegments hk p hp
  have hm : 0 < segments.length :=
    List.length_pos_of_ne_nil (blockAlignedLightSegments_nonempty hk p hp)
  let first : Fin segments.length := ⟨0, hm⟩
  let segment := blockAlignedLightSegmentAt hk p hp first
  have hr : 0 < segment.length :=
    blockAlignedLightSegment_length_pos hk p hp segment
  have hentry : deficitAt segment.deficitString 0 < k - 1 := by
    rw [deficitAt_eq_get segment.deficitString 0 (by simpa using hr)]
    exact (blockAlignedLightSegment_deficitString_legal hk p hp segment).entries_lt
      _ (List.get_mem _ _)
  have hvalue : deficitAt segment.deficitString 0 =
      blockAlignedFirstDeficit hk p hp := by
    simpa [segments, first, segment] using firstLightSegment_firstDeficit hk p hp
  omega

private theorem blockAlignedPhiAggregation (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    phiN (k - 1) (blockAlignedZ p hp) (by omega) (by
      rw [blockAlignedZ_eq_runCount_add_boundaryExcess hk p hp]
      have hq : 1 ≤ blockAlignedRunCount hk p hp := by
        unfold blockAlignedRunCount
        exact List.length_pos_of_ne_nil (blockAlignedRuns_nonempty hk p hp)
      omega) ≤
      (∑ i : Fin (blockAlignedLightSegments hk p hp).length,
        phiN (k - 1) (blockAlignedLightSegmentAt hk p hp i).length
          (by omega)
          (blockAlignedLightSegment_length_pos hk p hp
            (blockAlignedLightSegmentAt hk p hp i))) +
        (k - 1) * blockAlignedRunBoundaryExcess hk p hp := by
  let segments := blockAlignedLightSegments hk p hp
  have hm : 1 ≤ segments.length :=
    List.length_pos_of_ne_nil (blockAlignedLightSegments_nonempty hk p hp)
  have haggregate := phiN_aggregation
    (n := k - 1) (m := segments.length)
    (q := blockAlignedRunCount hk p hp)
    (A := blockAlignedRunBoundaryExcess hk p hp)
    (by omega) hm
    (fun i => (blockAlignedLightSegmentAt hk p hp i).length)
    (fun i => blockAlignedLightSegment_length_pos hk p hp
      (blockAlignedLightSegmentAt hk p hp i))
    (by simpa [segments] using blockAlignedLightSegmentLengths_fin_sum hk p hp)
    (by simpa [segments] using
      blockAlignedRunBoundaryExcess_ge_lightSegments_sub_one hk p hp)
  have hz := blockAlignedZ_eq_runCount_add_boundaryExcess hk p hp
  simpa only [hz] using haggregate

/-- Endpoint-charged capacity on an arbitrary actual block-aligned path.
This is the internal form used both by `lem:capacity` and by the literal
prepended path in `lem:cheapcapacity`. -/
private theorem blockAlignedCapacityWithEndpoints {a b : ℕ}
    (hk : 7 ≤ k) (p : OverlapPath k) (hp : IsBlockAligned p)
    (hq : 2 ≤ blockAlignedRunCount hk p hp)
    (ha : a ≤ k - 3) (hb : b ≤ k - 2)
    (hfirst : a ≤ blockAlignedFirstDeficit hk p hp)
    (hlast : b ≤ blockAlignedLastDeficit hk p hp) :
    pathBlockCount p + max 0 (a - 1) + endpointChargeB b ≤
      hN (k - 1) (blockAlignedZ p hp) (by omega) (by
        rw [blockAlignedZ_eq_runCount_add_boundaryExcess hk p hp]
        have _hqpos : 1 ≤ blockAlignedRunCount hk p hp := by
          unfold blockAlignedRunCount
          exact List.length_pos_of_ne_nil (blockAlignedRuns_nonempty hk p hp)
        omega) := by
  have haggregation := blockAlignedPhiAggregation hk p hp
  have hendpoints := blockAlignedSegmentEndpointSum hk p hp hq
    ha hb hfirst hlast
  have hdeficit : blockAlignedTotalDeficit hk p hp ≤
      (k - 1) * blockAlignedRunCount hk p hp :=
    blockAlignedTotalDeficit_le_capacity hk p hp
  have hblocks := pathBlockCount_eq_runCount_sub_totalDeficit hk p hp
  have hz := blockAlignedZ_eq_runCount_add_boundaryExcess hk p hp
  have hzMul : (k - 1) * blockAlignedZ p hp =
      (k - 1) * blockAlignedRunCount hk p hp +
        (k - 1) * blockAlignedRunBoundaryExcess hk p hp := by
    rw [hz, Nat.mul_add]
  unfold hN
  rw [hzMul]
  omega

/-- **Component capacity (Lemma `lem:capacity`), in its genuinely generic
form.**  The path need not be a forest component: only the accepted
block-aligned path data and its actual canonical runs/light segments enter. -/
theorem blockAlignedCapacity (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (hz : 2 ≤ blockAlignedZ p hp) :
    pathBlockCount p ≤
      hN (k - 1) (blockAlignedZ p hp) (by omega) (by omega) -
        endpointChargeB (blockAlignedLastDeficit hk p hp) := by
  have hq : 2 ≤ blockAlignedRunCount hk p hp := by
    have hqpos : 1 ≤ blockAlignedRunCount hk p hp := by
      unfold blockAlignedRunCount
      exact List.length_pos_of_ne_nil (blockAlignedRuns_nonempty hk p hp)
    by_contra hnot
    have hqone : blockAlignedRunCount hk p hp = 1 := by omega
    have hzOne := (blockAlignedZ_eq_one_iff_runCount_eq_one hk p hp).2 hqone
    omega
  have hbound := blockAlignedCapacityWithEndpoints
    (a := 0) (b := blockAlignedLastDeficit hk p hp)
    hk p hp hq (by omega) (blockAlignedLastDeficit_le hk p hp)
    (by simp) (by rfl)
  simp only [Nat.zero_sub, max_self, Nat.add_zero] at hbound
  omega

/-- The `z=1` clause of Lemma `lem:capacity`: there is exactly one run, its
first and last deficits coincide, and the block count is `n-d⁺`, with the
natural subtraction justified by the accepted total-deficit bound. -/
theorem blockAlignedCapacity_eq_of_z_one (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p)
    (hz : blockAlignedZ p hp = 1) :
    blockAlignedRunCount hk p hp = 1 ∧
      blockAlignedFirstDeficit hk p hp =
        blockAlignedLastDeficit hk p hp ∧
      pathBlockCount p = (k - 1) - blockAlignedLastDeficit hk p hp := by
  have hq := (blockAlignedZ_eq_one_iff_runCount_eq_one hk p hp).1 hz
  have hdLength : (blockAlignedDeficitString hk p hp).length = 1 := by
    simp [hq]
  have hfirstLast : blockAlignedFirstDeficit hk p hp =
      blockAlignedLastDeficit hk p hp := by
    rw [blockAlignedFirstDeficit_eq_deficitAt_zero hk p hp,
      blockAlignedLastDeficit_eq_deficitAt_last hk p hp, hq]
  have htotal : blockAlignedTotalDeficit hk p hp =
      blockAlignedLastDeficit hk p hp := by
    have hsingle := deficitSequenceTotal_eq_deficitAt_zero_of_length_one
      (d := blockAlignedDeficitString hk p hp) hdLength
    have hlastAt := blockAlignedLastDeficit_eq_deficitAt_last hk p hp
    change (blockAlignedDeficitString hk p hp).sum = _
    rw [show blockAlignedRunCount hk p hp - 1 = 0 by omega] at hlastAt
    exact hsingle.trans hlastAt.symm
  refine ⟨hq, hfirstLast, ?_⟩
  rw [pathBlockCount_eq_runCount_sub_totalDeficit hk p hp, hq,
    Nat.mul_one, htotal]

/-! ## Cheap entrances and the literal prepended path -/

private theorem cheapEntranceDoorClassOutside (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (hnonroot : C ≠ pathForestRootComponent (by omega) P)
    (hminto : pathForestMinto (by omega) P C
        (pathForestComponent_vertexSet_ne_univ_of_nonroot
          (by omega) P C hnonroot) = 2) :
    EntranceDoorClassOutside hk P C := by
  exact (pathForestComponent_minto_eq_two_iff hk P C
    (pathForestComponent_vertexSet_ne_univ_of_nonroot
      (by omega) P C hnonroot)).2.1 hminto

/-- **Cheap-entry deficit (Lemma `lem:cheapdeficit`).**  Its only component
hypotheses are literally `nonroot` and `minto = 2`; the conclusion exposes
both the outside-door fact and the exact deficit interval. -/
theorem pathForestComponentCheapDeficit (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (hnonroot : C ≠ pathForestRootComponent (by omega) P)
    (hminto : pathForestMinto (by omega) P C
        (pathForestComponent_vertexSet_ne_univ_of_nonroot
          (by omega) P C hnonroot) = 2) :
    EntranceDoorClassOutside hk P C ∧
      1 ≤ pathForestComponentFirstDeficit hk P C ∧
      pathForestComponentFirstDeficit hk P C ≤ k - 2 := by
  let r := pathForestComponentFirstRun hk P C
  let alpha := pathForestComponentEntranceDoor hk P C
  have houtside : EntranceDoorClassOutside hk P C :=
    cheapEntranceDoorClassOutside hk P C hnonroot hminto
  have hrPos : 1 ≤ r.length := pathForestRun_length_pos hk P r
  have hrLe : r.length ≤ k - 1 := pathForestRun_length_le hk P r
  have hrDoor : r.length ≤ k - 2 := by
    by_contra hnot
    have hrFull : r.length = k - 1 := by omega
    have hindex : k - 2 < r.length := by omega
    have hentry : r.entry = runMap (by omega) alpha := by
      simpa [r, alpha] using
        pathForestComponentFirstRun_entry_eq_runMap_entranceDoor hk P C
    have hpower : runMapPower (by omega) (k - 2) r.entry = alpha := by
      calc
        runMapPower (by omega) (k - 2) r.entry =
            runMapPower (by omega) (k - 2) (runMap (by omega) alpha) :=
          congrArg (runMapPower (by omega) (k - 2)) hentry
        _ = runMapPower (by omega) (k - 1) alpha := by
          change ((runMap (by omega))^[k - 2]) (runMap (by omega) alpha) =
            ((runMap (by omega))^[k - 1]) alpha
          simpa [show k - 2 + 1 = k - 1 by omega] using
            (Function.iterate_succ_apply (runMap (by omega)) (k - 2) alpha).symm
        _ = alpha := (runMap_order_exact (by omega) alpha).1
    have hoccupied : rotationClass alpha ∈ r.occupiedClasses := by
      rw [pathForestRun_occupiedClasses_eq_slots hk P r]
      refine Finset.mem_image.mpr ⟨k - 2, Finset.mem_range.mpr hindex, ?_⟩
      exact congrArg rotationClass hpower
    exact houtside
      (pathForestRun_occupiedClass_subset_component hk P r hoccupied)
  refine ⟨houtside, ?_⟩
  rw [pathForestComponentFirstDeficit_eq_firstRun_deficit hk P C]
  change 1 ≤ (k - 1) - r.length ∧ (k - 1) - r.length ≤ k - 2
  omega

/-- The literal block-entry list for `Q`: the entrance door `α_p`, followed
by the original component entries in their accepted canonical order. -/
noncomputable def cheapEntryPrependedBlockEntries (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    List (PermutationVertex k) :=
  pathForestComponentEntranceDoor hk P C ::
    pathForestComponentBlockEntries (by omega) P C

@[simp] theorem cheapEntryPrependedBlockEntries_length (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    (cheapEntryPrependedBlockEntries hk P C).length =
      (pathForestComponentBlockEntries (by omega) P C).length + 1 := by
  simp [cheapEntryPrependedBlockEntries]

set_option backward.isDefEq.respectTransparency false in
private theorem pathForestComponentBlockEntry_mem_component
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    {u : PermutationVertex k}
    (hu : u ∈ pathForestComponentBlockEntries (by omega) P C) :
    u ∈ weakComponentVertices C := by
  let p := pathForestComponentPath (by omega) P C
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hu
  have hi' : i.1 < pathBlockCount p := by
    simpa [p] using i.2
  have hentry :
      (pathForestComponentBlockEntries (by omega) P C).get i =
        p.vertex ⟨k * i.1, by
          rw [blockAligned_length_eq
            (pathForestComponentPath_blockAligned (by omega) P C)]
          exact Nat.mul_lt_mul_of_pos_left hi' (by omega)⟩ := by
    simp [pathForestComponentBlockEntries, p]
  have huPath : u ∈ p.vertices := by
    rw [← hi]
    rw [hentry]
    exact p.vertex_mem _
  rw [← pathForestComponentPath_vertexSet (by omega) P C]
  exact List.mem_toFinset.mpr huPath

/-- The prepended entrance-door class is new, and the entire literal entry
list therefore remains pairwise distinct in rotation class. -/
theorem cheapEntryPrependedBlockEntries_pairwiseDistinct
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (houtside : EntranceDoorClassOutside hk P C) :
    PairwiseDistinctRotationClasses
      (cheapEntryPrependedBlockEntries hk P C) := by
  classical
  rw [PairwiseDistinctRotationClasses]
  apply List.pairwise_cons.mpr
  refine ⟨?_, pathForestComponentBlockEntries_pairwiseDistinct
    (by omega) P C⟩
  intro u hu hclasses
  apply houtside
  have huComponent := pathForestComponentBlockEntry_mem_component hk P C hu
  have hsubset := pathForest_component_contains_rotationClass
    (by omega) P C (mem_weakComponentVertices.mp huComponent)
  rw [hclasses]
  exact hsubset

/-- The actual literal prepended overlap path `Q`.  The `blockSequencePath`
constructor expands exactly the entry list `α_p :: entries(p)`. -/
noncomputable def cheapEntryPrependedPath (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (houtside : EntranceDoorClassOutside hk P C) : OverlapPath k :=
  blockSequencePath (by omega)
    (cheapEntryPrependedBlockEntries hk P C)
    (by simp [cheapEntryPrependedBlockEntries])
    (cheapEntryPrependedBlockEntries_pairwiseDistinct hk P C houtside)

/-- `Q` satisfies the accepted strong locality condition. -/
theorem cheapEntryPrependedPath_stronglyExitless (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (houtside : EntranceDoorClassOutside hk P C) :
    IsStronglyExitless (cheapEntryPrependedPath hk P C houtside) := by
  unfold cheapEntryPrependedPath
  exact blockSequencePath_stronglyExitless (by omega) _ _ _

/-- In particular, the literal path `Q` is an actual block-aligned exitless
path, so the generic capacity theory applies to it. -/
theorem cheapEntryPrependedPath_blockAligned (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (houtside : EntranceDoorClassOutside hk P C) :
    IsBlockAligned (cheapEntryPrependedPath hk P C houtside) := by
  let Q := cheapEntryPrependedPath hk P C houtside
  have hstrong : IsStronglyExitless Q := by
    simpa [Q] using cheapEntryPrependedPath_stronglyExitless hk P C houtside
  refine ⟨hstrong.1, ?_⟩
  rw [show Q.length = k *
      (cheapEntryPrependedBlockEntries hk P C).length by
    exact blockSequencePath_length (by omega) _ _ _]
  exact dvd_mul_right k _

/-- Recovering block entries from `Q` returns the literal list used to build
it; in particular no abstract numerical surrogate has replaced the path. -/
theorem cheapEntryPrependedPath_blockEntries (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (houtside : EntranceDoorClassOutside hk P C) :
    blockAlignedBlockEntries hk (cheapEntryPrependedPath hk P C houtside)
        (cheapEntryPrependedPath_blockAligned hk P C houtside) =
      cheapEntryPrependedBlockEntries hk P C := by
  let entries := cheapEntryPrependedBlockEntries hk P C
  let Q := cheapEntryPrependedPath hk P C houtside
  have hcount : pathBlockCount Q = entries.length := by
    unfold pathBlockCount
    rw [show Q.length = k * entries.length by
      exact blockSequencePath_length (by omega) _ _ _]
    exact Nat.mul_div_cancel_left entries.length (by omega)
  apply List.ext_get
  · rw [blockAlignedBlockEntries_length]
    exact hcount
  · intro i hiLeft hiRight
    have hi : i < entries.length := by simpa [entries] using hiRight
    have hiQ : i < pathBlockCount Q := by omega
    rw [blockAlignedBlockEntry_eq_vertex hk Q
      (cheapEntryPrependedPath_blockAligned hk P C houtside) i hiQ]
    change Q.vertex ⟨k * i, _⟩ = entries.get ⟨i, hi⟩
    change (blockSequenceVertices (by omega) entries).get
      ⟨k * i, by simp; exact Nat.mul_lt_mul_of_pos_left hi (by omega)⟩ = _
    simp only [List.get_eq_getElem]
    rw [blockSequenceVertices_getElem (by omega) entries (k * i) (by
      exact Nat.mul_lt_mul_of_pos_left hi (by omega))]
    rw [Nat.mul_mod_right]
    simp only [rotationPower_zero]
    change entries.get _ = entries.get _
    apply congrArg entries.get
    apply Fin.ext
    exact Nat.mul_div_cancel_left i (by omega)

private theorem pathForestComponentBlockEntries_head_eq_tail
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    (pathForestComponentBlockEntries (by omega) P C).head
        (pathForestComponentBlockEntries_nonempty (by omega) P C) =
      pathForestComponentTail (by omega) P C := by
  let entries := pathForestComponentBlockEntries (by omega) P C
  have hentries : entries ≠ [] :=
    pathForestComponentBlockEntries_nonempty (by omega) P C
  rw [List.head_eq_getElem_zero hentries]
  simp [entries, pathForestComponentBlockEntries,
    pathForestComponentTail]

private theorem cheapEntryBoundary_weight_two (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    let oldEntries := pathForestComponentBlockEntries (by omega) P C
    overlapWeight
        (blockExit (pathForestComponentEntranceDoor hk P C))
        (oldEntries.head
          (pathForestComponentBlockEntries_nonempty (by omega) P C)) = 2 := by
  dsimp only
  let alpha := pathForestComponentEntranceDoor hk P C
  let tail := pathForestComponentTail (by omega) P C
  have hhead :
      (pathForestComponentBlockEntries (by omega) P C).head
          (pathForestComponentBlockEntries_nonempty (by omega) P C) = tail := by
    simpa [tail] using pathForestComponentBlockEntries_head_eq_tail hk P C
  have hdoor : door (blockExit alpha) = tail := by
    rw [door_blockExit (by omega)]
    dsimp [alpha, tail]
    rw [runMap_runMapInverse (by omega)]
  rw [hhead, ← hdoor]
  exact door_has_weight_two (k := k) _ (by omega)

private theorem cheapEntryPrependedPath_blockCount_aux (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (houtside : EntranceDoorClassOutside hk P C) :
    pathBlockCount (cheapEntryPrependedPath hk P C houtside) =
      pathForestComponentBlockCount (by omega) P C + 1 := by
  unfold pathBlockCount
  rw [show (cheapEntryPrependedPath hk P C houtside).length =
      k * (cheapEntryPrependedBlockEntries hk P C).length by
    unfold cheapEntryPrependedPath
    exact blockSequencePath_length (by omega) _ _ _]
  rw [Nat.mul_div_cancel_left _ (by omega)]
  simp [cheapEntryPrependedBlockEntries, pathForestComponentBlockCount]

/-- The new boundary in the literal path is genuinely the weight-two edge
from `ex(α_p)` to the old first entry. -/
theorem cheapEntryPrependedPath_newBoundaryWeight (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (houtside : EntranceDoorClassOutside hk P C) :
    (blockBoundaryWeights (cheapEntryPrependedPath hk P C houtside)
      (cheapEntryPrependedPath_blockAligned hk P C houtside)).head
        (by
          apply List.ne_nil_of_length_pos
          rw [blockBoundaryWeights_length]
          have hold := pathForestComponentBlockCount_pos (by omega) P C
          have hcount := cheapEntryPrependedPath_blockCount_aux
            hk P C houtside
          omega) = 2 := by
  let Q := cheapEntryPrependedPath hk P C houtside
  let hQ := cheapEntryPrependedPath_blockAligned hk P C houtside
  have hcount : 2 ≤ pathBlockCount Q := by
    have hold := pathForestComponentBlockCount_pos (by omega) P C
    change 2 ≤ pathBlockCount (cheapEntryPrependedPath hk P C houtside)
    rw [cheapEntryPrependedPath_blockCount_aux hk P C houtside]
    omega
  have hindexed := blockAlignedBoundaryWeight_eq hk Q hQ 0 (by omega)
  have hentriesEq : blockAlignedBlockEntries hk Q hQ =
      cheapEntryPrependedBlockEntries hk P C := by
    simpa [Q, hQ] using
      cheapEntryPrependedPath_blockEntries hk P C houtside
  rw [List.head_eq_getElem_zero] 
  change (blockBoundaryWeights Q hQ).get ⟨0, by
    rw [blockBoundaryWeights_length]
    omega⟩ = 2
  rw [hindexed]
  simp only [hentriesEq, cheapEntryPrependedBlockEntries, List.get_eq_getElem,
    List.getElem_cons_zero, List.getElem_cons_succ]
  simpa [List.head_eq_getElem_zero] using cheapEntryBoundary_weight_two hk P C

/-- Prepending one complete block changes the block count by exactly one. -/
theorem cheapEntryPrependedPath_blockCount (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (houtside : EntranceDoorClassOutside hk P C) :
    pathBlockCount (cheapEntryPrependedPath hk P C houtside) =
      pathForestComponentBlockCount (by omega) P C + 1 := by
  exact cheapEntryPrependedPath_blockCount_aux hk P C houtside

private def prependFirstGroup {alpha : Type*} (a : alpha) :
    List (List alpha) → List (List alpha)
  | [] => []
  | first :: rest => (a :: first) :: rest

private theorem splitBy_cons_eq_prependFirstGroup {alpha : Type*}
    (relation : alpha → alpha → Bool) (a : alpha)
    (xs : List alpha) (hxs : xs ≠ [])
    (hrel : relation a (xs.head hxs) = true) :
    (a :: xs).splitBy relation =
      prependFirstGroup a (xs.splitBy relation) := by
  let parts := xs.splitBy relation
  have hparts : parts ≠ [] := List.splitBy_ne_nil.mpr hxs
  cases hpartsEq : parts with
  | nil => exact (hparts hpartsEq).elim
  | cons first rest =>
      have hpartsEqSource : xs.splitBy relation = first :: rest := by
        simpa [parts] using hpartsEq
      have hfirstMem : first ∈ xs.splitBy relation := by
        rw [hpartsEqSource]
        simp
      have hfirstNe : first ≠ [] :=
        List.ne_nil_of_mem_splitBy hfirstMem
      have hflat : first ++ rest.flatten = xs := by
        have hsource := List.flatten_splitBy relation xs
        rw [hpartsEqSource] at hsource
        simpa using hsource
      have hfirstChain : first.IsChain (fun x y => relation x y) :=
        List.isChain_of_mem_splitBy hfirstMem
      have hhead : first.head hfirstNe = xs.head hxs := by
        have hsource := congrArg List.head? hflat
        simp only [List.head?_append] at hsource
        rw [List.head?_eq_some_head hfirstNe,
          List.head?_eq_some_head hxs] at hsource
        exact Option.some.inj (by simpa using hsource)
      have hsourceNoNil : [] ∉ first :: rest := by
        simpa [hpartsEqSource] using List.nil_notMem_splitBy relation xs
      have hsourceBoundary : (first :: rest).IsChain
          (fun left right => ∃ hleft hright,
            relation (left.getLast hleft) (right.head hright) = false) := by
        simpa [hpartsEqSource] using
          List.isChain_getLast_head_splitBy relation xs
      rw [show prependFirstGroup a (xs.splitBy relation) =
          (a :: first) :: rest by rw [hpartsEqSource]; rfl]
      rw [List.splitBy_eq_iff]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [← hflat]
      · intro hempty
        simp only [List.mem_cons] at hempty
        rcases hempty with hbad | hrest
        · contradiction
        · exact hsourceNoNil (List.mem_cons_of_mem first hrest)
      · intro group hgroup
        simp only [List.mem_cons] at hgroup
        rcases hgroup with rfl | hgroup
        · rw [List.isChain_cons]
          refine ⟨?_, hfirstChain⟩
          intro x hx
          have hxEq : first.head hfirstNe = x := by
            have hsome := hx
            rw [List.head?_eq_some_head hfirstNe] at hsome
            exact Option.some.inj hsome
          subst x
          simpa [hhead] using hrel
        · exact List.isChain_of_mem_splitBy (by
            rw [hpartsEqSource]
            exact List.mem_cons_of_mem first hgroup)
      · cases rest with
        | nil => simp
        | cons second tail =>
            rw [List.isChain_cons] at hsourceBoundary ⊢
            refine ⟨?_, hsourceBoundary.2⟩
            intro group hgroup
            obtain ⟨hleft, hright, hrelation⟩ :=
              hsourceBoundary.1 group hgroup
            refine ⟨by simp, hright, ?_⟩
            simpa [hfirstNe] using hrelation

/-- Canonical-run preservation for the literal `Q`: the new entry is joined
by the proved weight-two boundary to the old first run, and every remaining
run is literally unchanged. -/
theorem cheapEntryPrependedPath_runs (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (houtside : EntranceDoorClassOutside hk P C) :
    blockAlignedRuns hk (cheapEntryPrependedPath hk P C houtside)
        (cheapEntryPrependedPath_blockAligned hk P C houtside) =
      prependFirstGroup (pathForestComponentEntranceDoor hk P C)
        (pathForestComponentRuns hk P C) := by
  let Q := cheapEntryPrependedPath hk P C houtside
  let hQ := cheapEntryPrependedPath_blockAligned hk P C houtside
  let alpha := pathForestComponentEntranceDoor hk P C
  let oldEntries := pathForestComponentBlockEntries (by omega) P C
  have hentries : oldEntries ≠ [] := by
    simpa [oldEntries] using
      pathForestComponentBlockEntries_nonempty (by omega) P C
  have hrel : isWeightTwoBoundary alpha (oldEntries.head hentries) = true := by
    simp only [isWeightTwoBoundary, decide_eq_true_eq]
    simpa [alpha, oldEntries] using cheapEntryBoundary_weight_two hk P C
  have hsplit := splitBy_cons_eq_prependFirstGroup
    isWeightTwoBoundary alpha oldEntries hentries hrel
  unfold blockAlignedRuns weightTwoRuns
  rw [show blockAlignedBlockEntries hk Q hQ = alpha :: oldEntries by
    simpa [Q, hQ, alpha, oldEntries, cheapEntryPrependedBlockEntries] using
      cheapEntryPrependedPath_blockEntries hk P C houtside]
  simpa [pathForestComponentRuns, weightTwoRuns, Q, hQ, alpha, oldEntries]
    using hsplit

/-- The literal prepending operation preserves the number of canonical
runs. -/
theorem cheapEntryPrependedPath_runCount (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (houtside : EntranceDoorClassOutside hk P C) :
    blockAlignedRunCount hk (cheapEntryPrependedPath hk P C houtside)
        (cheapEntryPrependedPath_blockAligned hk P C houtside) =
      pathForestComponentRunCount hk P C := by
  rw [blockAlignedRunCount, cheapEntryPrependedPath_runs hk P C houtside]
  unfold pathForestComponentRunCount
  let runs := pathForestComponentRuns hk P C
  have hruns : runs ≠ [] := by
    simpa [runs] using pathForestComponentRuns_nonempty hk P C
  cases h : runs with
  | nil => exact (hruns h).elim
  | cons first rest =>
      rw [show pathForestComponentRuns hk P C = first :: rest by
        simpa [runs] using h]
      simp [prependFirstGroup]

private def replaceFirstGroupHead {alpha : Type*} (newHead : alpha) :
    List (List alpha) → List (List alpha)
  | [] => []
  | [] :: groups => [] :: groups
  | (_oldHead :: firstTail) :: groups =>
      (newHead :: firstTail) :: groups

/-- Canonical light-segment preservation: the first run is replaced by its
literal prepended version inside the first light segment, while every other
run and every other segment remains definitionally in place. -/
theorem cheapEntryPrependedPath_lightSegments (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (houtside : EntranceDoorClassOutside hk P C) :
    let oldRuns := pathForestComponentRuns hk P C
    let newFirst := pathForestComponentEntranceDoor hk P C ::
      oldRuns.head (pathForestComponentRuns_nonempty hk P C)
    blockAlignedLightSegments hk (cheapEntryPrependedPath hk P C houtside)
        (cheapEntryPrependedPath_blockAligned hk P C houtside) =
      replaceFirstGroupHead newFirst
        (blockAlignedLightSegments hk
          (pathForestComponentPath (by omega) P C)
          (pathForestComponentPath_blockAligned (by omega) P C)) := by
  dsimp only
  let Q := cheapEntryPrependedPath hk P C houtside
  let hQ := cheapEntryPrependedPath_blockAligned hk P C houtside
  let p := pathForestComponentPath (by omega) P C
  let hp := pathForestComponentPath_blockAligned (by omega) P C
  let oldRuns := pathForestComponentRuns hk P C
  have hruns : oldRuns ≠ [] := by
    simpa [oldRuns] using pathForestComponentRuns_nonempty hk P C
  let alpha := pathForestComponentEntranceDoor hk P C
  let oldFirst := oldRuns.head hruns
  let newFirst := alpha :: oldFirst
  have hQruns : blockAlignedRuns hk Q hQ =
      prependFirstGroup alpha oldRuns := by
    simpa [Q, hQ, alpha, oldRuns] using
      cheapEntryPrependedPath_runs hk P C houtside
  have hpruns : blockAlignedRuns hk p hp = oldRuns := by
    simpa [p, hp, oldRuns] using
      (pathForestComponentRuns_eq_blockAlignedRuns hk P C).symm
  unfold blockAlignedLightSegments
  rw [hQruns, hpruns]
  change (prependFirstGroup alpha oldRuns).splitBy isLightRunBoundary =
    replaceFirstGroupHead newFirst (oldRuns.splitBy isLightRunBoundary)
  cases hOld : oldRuns with
  | nil => exact (hruns hOld).elim
  | cons first rest =>
      have hfirstEq : oldFirst = first := by
        simp [oldFirst, hOld]
      have hnewEq : newFirst = alpha :: first := by
        simp [newFirst, hfirstEq]
      simp only [prependFirstGroup]
      rw [hnewEq]
      cases rest with
      | nil =>
          have hold : [first].splitBy isLightRunBoundary = [[first]] :=
            List.splitBy_of_isChain (by simp) (by simp)
          have hnew : [alpha :: first].splitBy isLightRunBoundary =
              [[alpha :: first]] :=
            List.splitBy_of_isChain (by simp) (by simp)
          rw [hold, hnew]
          rfl
      | cons second more =>
          have hfirstMem : first ∈ oldRuns := by rw [hOld]; simp
          have hsecondMem : second ∈ oldRuns := by rw [hOld]; simp
          have hfirstNe : first ≠ [] := by
            intro hnil
            apply (pathForestComponentRuns_spec hk P C).2.1
            rw [← hnil]
            simpa [oldRuns] using hfirstMem
          have hsecondNe : second ≠ [] := by
            intro hnil
            apply (pathForestComponentRuns_spec hk P C).2.1
            rw [← hnil]
            simpa [oldRuns] using hsecondMem
          have hrelEq :
              isLightRunBoundary (alpha :: first) second =
                isLightRunBoundary first second := by
            simp [hfirstNe, hsecondNe, List.getLast?_eq_some_getLast,
              List.head?_eq_some_head, isLightRunBoundary,
              IsLightRunBoundary, runBoundaryWeight]
          by_cases hrel : isLightRunBoundary first second = true
          · have hrelNew :
                isLightRunBoundary (alpha :: first) second = true := by
              rw [hrelEq, hrel]
            have hold := splitBy_cons_eq_prependFirstGroup
              isLightRunBoundary first (second :: more) (by simp) (by
                simpa using hrel)
            have hnew := splitBy_cons_eq_prependFirstGroup
              isLightRunBoundary (alpha :: first) (second :: more) (by simp)
                (by simpa using hrelNew)
            rw [hold, hnew]
            have htail : (second :: more).splitBy isLightRunBoundary ≠ [] :=
              List.splitBy_ne_nil.mpr (by simp)
            cases hparts : (second :: more).splitBy isLightRunBoundary with
            | nil => exact (htail hparts).elim
            | cons group groups =>
                simp [prependFirstGroup, replaceFirstGroupHead]
          · have hrelFalse :
                isLightRunBoundary first second = false := by
              exact Bool.eq_false_of_not_eq_true hrel
            have hrelNewFalse :
                isLightRunBoundary (alpha :: first) second = false := by
              rw [hrelEq, hrelFalse]
            have hold := List.splitBy_append_cons
              (r := isLightRunBoundary) (l := [first]) more (a := second)
              (by
                intro x hx
                simp at hx
                subst x
                exact hrelFalse)
            have hnew := List.splitBy_append_cons
              (r := isLightRunBoundary) (l := [alpha :: first]) more
              (a := second) (by
                intro x hx
                simp at hx
                subst x
                exact hrelNewFalse)
            have hsingle : [first].splitBy isLightRunBoundary = [[first]] :=
              List.splitBy_of_isChain (by simp) (by simp)
            have hsingleNew : [alpha :: first].splitBy
                isLightRunBoundary = [[alpha :: first]] :=
              List.splitBy_of_isChain (by simp) (by simp)
            have hold' : (first :: second :: more).splitBy
                isLightRunBoundary =
                [[first]] ++ (second :: more).splitBy
                  isLightRunBoundary := by
              rw [hsingle] at hold
              simpa using hold
            have hnew' : ((alpha :: first) :: second :: more).splitBy
                isLightRunBoundary =
                [[alpha :: first]] ++ (second :: more).splitBy
                  isLightRunBoundary := by
              rw [hsingleNew] at hnew
              simpa using hnew
            rw [hold', hnew']
            rfl

private theorem runBoundaryWeight_prepend_left
    (a : PermutationVertex k) {left right : List (PermutationVertex k)}
    (hleft : left ≠ []) :
    runBoundaryWeight (a :: left) right =
      runBoundaryWeight left right := by
  unfold runBoundaryWeight
  simp [hleft, List.getLast?_eq_some_getLast]

/-- The literal run-boundary excess `A_h` is preserved by `Q`; this follows
from the exact run list, since prepending changes no last entry of the first
run. -/
theorem cheapEntryPrependedPath_runBoundaryExcess (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (houtside : EntranceDoorClassOutside hk P C) :
    blockAlignedRunBoundaryExcess hk
        (cheapEntryPrependedPath hk P C houtside)
        (cheapEntryPrependedPath_blockAligned hk P C houtside) =
      blockAlignedRunBoundaryExcess hk
        (pathForestComponentPath (by omega) P C)
        (pathForestComponentPath_blockAligned (by omega) P C) := by
  let Q := cheapEntryPrependedPath hk P C houtside
  let hQ := cheapEntryPrependedPath_blockAligned hk P C houtside
  let p := pathForestComponentPath (by omega) P C
  let hp := pathForestComponentPath_blockAligned (by omega) P C
  let alpha := pathForestComponentEntranceDoor hk P C
  let oldRuns := pathForestComponentRuns hk P C
  have hruns : oldRuns ≠ [] := by
    simpa [oldRuns] using pathForestComponentRuns_nonempty hk P C
  have hQruns : blockAlignedRuns hk Q hQ =
      prependFirstGroup alpha oldRuns := by
    simpa [Q, hQ, alpha, oldRuns] using
      cheapEntryPrependedPath_runs hk P C houtside
  have hpruns : blockAlignedRuns hk p hp = oldRuns := by
    simpa [p, hp, oldRuns] using
      (pathForestComponentRuns_eq_blockAlignedRuns hk P C).symm
  unfold blockAlignedRunBoundaryExcess
  rw [hQruns, hpruns]
  cases hOld : oldRuns with
  | nil => exact (hruns hOld).elim
  | cons first rest =>
      have hfirstMem : first ∈ pathForestComponentRuns hk P C := by
        simp [oldRuns, hOld]
      have hfirstNe : first ≠ [] := by
        intro hnil
        apply (pathForestComponentRuns_spec hk P C).2.1
        rw [← hnil]
        exact hfirstMem
      cases rest with
      | nil => simp [prependFirstGroup, adjacentExcess]
      | cons second more =>
          simp only [prependFirstGroup, adjacentExcess]
          rw [runBoundaryWeight_prepend_left alpha hfirstNe]

/-- The ordinary path excess `ε` is unchanged by the new weight-two
boundary. -/
theorem cheapEntryPrependedPath_excess (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (houtside : EntranceDoorClassOutside hk P C) :
    pathExcess (cheapEntryPrependedPath hk P C houtside)
        (cheapEntryPrependedPath_blockAligned hk P C houtside) =
      pathExcess (pathForestComponentPath (by omega) P C)
        (pathForestComponentPath_blockAligned (by omega) P C) := by
  let Q := cheapEntryPrependedPath hk P C houtside
  let hQ := cheapEntryPrependedPath_blockAligned hk P C houtside
  let p := pathForestComponentPath (by omega) P C
  let hp := pathForestComponentPath_blockAligned (by omega) P C
  have hQdecomp :=
    blockAlignedExcess_eq_runCount_sub_one_add_boundaryExcess hk Q hQ
  have hpdecomp :=
    blockAlignedExcess_eq_runCount_sub_one_add_boundaryExcess hk p hp
  have hq : blockAlignedRunCount hk Q hQ =
      blockAlignedRunCount hk p hp := by
    calc
      blockAlignedRunCount hk Q hQ =
          pathForestComponentRunCount hk P C := by
        simpa [Q, hQ] using cheapEntryPrependedPath_runCount hk P C houtside
      _ = blockAlignedRunCount hk p hp :=
        pathForestComponentRunCount_eq_blockAlignedRunCount hk P C
  have hA : blockAlignedRunBoundaryExcess hk Q hQ =
      blockAlignedRunBoundaryExcess hk p hp := by
    simpa [Q, hQ, p, hp] using
      cheapEntryPrependedPath_runBoundaryExcess hk P C houtside
  change pathExcess Q hQ = pathExcess p hp
  calc
    pathExcess Q hQ =
        blockAlignedRunCount hk Q hQ - 1 +
          blockAlignedRunBoundaryExcess hk Q hQ := hQdecomp
    _ = blockAlignedRunCount hk p hp - 1 +
          blockAlignedRunBoundaryExcess hk p hp := by rw [hq, hA]
    _ = pathExcess p hp := hpdecomp.symm

/-- Consequently `z=ε+1` is literally unchanged. -/
theorem cheapEntryPrependedPath_z (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (houtside : EntranceDoorClassOutside hk P C) :
    blockAlignedZ (cheapEntryPrependedPath hk P C houtside)
        (cheapEntryPrependedPath_blockAligned hk P C houtside) =
      pathForestComponentZ (by omega) P C := by
  unfold blockAlignedZ pathForestComponentZ
  rw [cheapEntryPrependedPath_excess hk P C houtside]

private theorem pathForestComponentFirstDeficit_eq_deficitAt_zero
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    pathForestComponentFirstDeficit hk P C =
      deficitAt (pathForestComponentDeficitString hk P C) 0 := by
  let d := pathForestComponentDeficitString hk P C
  have hd : d ≠ [] := by
    simpa [d, pathForestComponentDeficitString] using
      pathForestComponentRuns_nonempty hk P C
  rw [deficitAt_eq_get d 0 (List.length_pos_of_ne_nil hd)]
  change d.head hd = d.get ⟨0, List.length_pos_of_ne_nil hd⟩
  exact List.head_eq_getElem_zero hd

private theorem pathForestComponentLastDeficit_eq_deficitAt_last
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    pathForestComponentLastDeficit hk P C =
      deficitAt (pathForestComponentDeficitString hk P C)
        (pathForestComponentRunCount hk P C - 1) := by
  let d := pathForestComponentDeficitString hk P C
  have hd : d ≠ [] := by
    simpa [d, pathForestComponentDeficitString] using
      pathForestComponentRuns_nonempty hk P C
  have hlength : d.length = pathForestComponentRunCount hk P C := by
    simp [d, pathForestComponentDeficitString,
      pathForestComponentRunCount]
  rw [show pathForestComponentRunCount hk P C - 1 = d.length - 1 by
    rw [hlength]]
  rw [deficitAt_eq_get d (d.length - 1) (by
    exact Nat.sub_lt (List.length_pos_of_ne_nil hd) (by omega))]
  change d.getLast hd = d.get
    ⟨d.length - 1, Nat.sub_lt (List.length_pos_of_ne_nil hd) (by omega)⟩
  exact List.getLast_eq_getElem hd

private theorem deficitAt_cons_succ (x : ℕ) (d : List ℕ) (i : ℕ) :
    deficitAt (x :: d) (i + 1) = deficitAt d i := by
  simp [deficitAt]

/-- The first deficit drops by one and the total deficit drops by one.
The positivity hypothesis is exactly what justifies both natural-number
subtractions. -/
theorem cheapEntryPrependedPath_deficitChanges (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (houtside : EntranceDoorClassOutside hk P C)
    (hfirstPositive : 1 ≤ pathForestComponentFirstDeficit hk P C) :
    blockAlignedFirstDeficit hk
        (cheapEntryPrependedPath hk P C houtside)
        (cheapEntryPrependedPath_blockAligned hk P C houtside) =
        pathForestComponentFirstDeficit hk P C - 1 ∧
      blockAlignedTotalDeficit hk
        (cheapEntryPrependedPath hk P C houtside)
        (cheapEntryPrependedPath_blockAligned hk P C houtside) =
        pathForestComponentTotalDeficit hk P C - 1 := by
  let Q := cheapEntryPrependedPath hk P C houtside
  let hQ := cheapEntryPrependedPath_blockAligned hk P C houtside
  let alpha := pathForestComponentEntranceDoor hk P C
  let oldRuns := pathForestComponentRuns hk P C
  have hruns : oldRuns ≠ [] := by
    simpa [oldRuns] using pathForestComponentRuns_nonempty hk P C
  have hQruns : blockAlignedRuns hk Q hQ =
      prependFirstGroup alpha oldRuns := by
    simpa [Q, hQ, alpha, oldRuns] using
      cheapEntryPrependedPath_runs hk P C houtside
  cases hOld : oldRuns with
  | nil => exact (hruns hOld).elim
  | cons first rest =>
      have hOldActual : pathForestComponentRuns hk P C = first :: rest := by
        simpa [oldRuns] using hOld
      let tailDeficits := rest.map (fun run => (k - 1) - run.length)
      have hQDeficits : blockAlignedDeficitString hk Q hQ =
          ((k - 1) - (first.length + 1)) :: tailDeficits := by
        unfold blockAlignedDeficitString
        rw [hQruns]
        simp [prependFirstGroup, hOld, tailDeficits]
      have hOldDeficits : pathForestComponentDeficitString hk P C =
          ((k - 1) - first.length) :: tailDeficits := by
        unfold pathForestComponentDeficitString
        rw [hOldActual]
        rfl
      have hfirstPositive' : 1 ≤ (k - 1) - first.length := by
        rw [pathForestComponentFirstDeficit_eq_deficitAt_zero hk P C,
          hOldDeficits] at hfirstPositive
        simpa [deficitAt] using hfirstPositive
      constructor
      · rw [blockAlignedFirstDeficit_eq_deficitAt_zero hk Q hQ,
          pathForestComponentFirstDeficit_eq_deficitAt_zero hk P C,
          hQDeficits, hOldDeficits]
        simp [deficitAt]
        omega
      · unfold blockAlignedTotalDeficit pathForestComponentTotalDeficit
        rw [hQDeficits, hOldDeficits]
        simp
        omega

/-- With at least two runs, the old last run is not the modified first run,
so the last deficit is literally preserved. -/
theorem cheapEntryPrependedPath_lastDeficit (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (houtside : EntranceDoorClassOutside hk P C)
    (hq : 2 ≤ pathForestComponentRunCount hk P C) :
    blockAlignedLastDeficit hk
        (cheapEntryPrependedPath hk P C houtside)
        (cheapEntryPrependedPath_blockAligned hk P C houtside) =
      pathForestComponentLastDeficit hk P C := by
  let Q := cheapEntryPrependedPath hk P C houtside
  let hQ := cheapEntryPrependedPath_blockAligned hk P C houtside
  let alpha := pathForestComponentEntranceDoor hk P C
  let oldRuns := pathForestComponentRuns hk P C
  have hruns : oldRuns ≠ [] := by
    simpa [oldRuns] using pathForestComponentRuns_nonempty hk P C
  have hQruns : blockAlignedRuns hk Q hQ =
      prependFirstGroup alpha oldRuns := by
    simpa [Q, hQ, alpha, oldRuns] using
      cheapEntryPrependedPath_runs hk P C houtside
  have hlength : 2 ≤ oldRuns.length := by
    simpa [oldRuns, pathForestComponentRunCount] using hq
  cases hOld : oldRuns with
  | nil => exact (hruns hOld).elim
  | cons first rest =>
      cases rest with
      | nil => simp [hOld] at hlength
      | cons second more =>
          have hOldActual : pathForestComponentRuns hk P C =
              first :: second :: more := by
            simpa [oldRuns] using hOld
          let tailDeficits := ((k - 1) - second.length) ::
            more.map (fun run => (k - 1) - run.length)
          have hQDeficits : blockAlignedDeficitString hk Q hQ =
              ((k - 1) - (first.length + 1)) :: tailDeficits := by
            unfold blockAlignedDeficitString
            rw [hQruns]
            simp [prependFirstGroup, hOld, tailDeficits]
          have hOldDeficits : pathForestComponentDeficitString hk P C =
              ((k - 1) - first.length) :: tailDeficits := by
            unfold pathForestComponentDeficitString
            rw [hOldActual]
            rfl
          rw [blockAlignedLastDeficit_eq_deficitAt_last hk Q hQ,
            pathForestComponentLastDeficit_eq_deficitAt_last hk P C]
          rw [cheapEntryPrependedPath_runCount hk P C houtside]
          rw [hQDeficits, hOldDeficits]
          have hindex : pathForestComponentRunCount hk P C - 1 =
              (pathForestComponentRunCount hk P C - 2) + 1 := by omega
          rw [hindex, deficitAt_cons_succ, deficitAt_cons_succ]

private theorem pathForestComponentLastDeficit_eq_blockAlignedLastDeficit
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    pathForestComponentLastDeficit hk P C =
      blockAlignedLastDeficit hk
        (pathForestComponentPath (by omega) P C)
        (pathForestComponentPath_blockAligned (by omega) P C) := by
  rw [pathForestComponentLastDeficit_eq_deficitAt_last hk P C,
    blockAlignedLastDeficit_eq_deficitAt_last hk
      (pathForestComponentPath (by omega) P C)
      (pathForestComponentPath_blockAligned (by omega) P C),
    pathForestComponentDeficitString_eq_blockAlignedDeficitString hk P C,
    pathForestComponentRunCount_eq_blockAlignedRunCount hk P C]

private theorem pathForestComponentFirstDeficit_eq_blockAlignedFirstDeficit
    (hk : 7 ≤ k) (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    pathForestComponentFirstDeficit hk P C =
      blockAlignedFirstDeficit hk
        (pathForestComponentPath (by omega) P C)
        (pathForestComponentPath_blockAligned (by omega) P C) := by
  rw [pathForestComponentFirstDeficit_eq_deficitAt_zero hk P C,
    blockAlignedFirstDeficit_eq_deficitAt_zero hk
      (pathForestComponentPath (by omega) P C)
      (pathForestComponentPath_blockAligned (by omega) P C),
    pathForestComponentDeficitString_eq_blockAlignedDeficitString hk P C]

/-- Forest-component specialization of the genuinely generic capacity
theorem. -/
theorem pathForestComponentCapacity (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (hz : 2 ≤ pathForestComponentZ (by omega) P C) :
    pathForestComponentBlockCount (by omega) P C ≤
      hN (k - 1) (pathForestComponentZ (by omega) P C)
          (by omega) (by omega) -
        endpointChargeB (pathForestComponentLastDeficit hk P C) := by
  let p := pathForestComponentPath (by omega) P C
  let hp := pathForestComponentPath_blockAligned (by omega) P C
  have hzGeneric : blockAlignedZ p hp =
      pathForestComponentZ (by omega) P C := rfl
  have hcapacity := blockAlignedCapacity hk p hp (by
    rw [hzGeneric]
    exact hz)
  have hlast := pathForestComponentLastDeficit_eq_blockAlignedLastDeficit
    hk P C
  simpa [p, hp, pathForestComponentBlockCount, hzGeneric, hlast] using
    hcapacity

/-- Exact equivalence used in Remark `rem:noqone`: for every actual
block-aligned path, `z≥2` exactly when there are at least two runs. -/
theorem blockAlignedZ_ge_two_iff_runCount_ge_two (hk : 7 ≤ k)
    (p : OverlapPath k) (hp : IsBlockAligned p) :
    2 ≤ blockAlignedZ p hp ↔
      2 ≤ blockAlignedRunCount hk p hp := by
  have hqPos : 1 ≤ blockAlignedRunCount hk p hp := by
    unfold blockAlignedRunCount
    exact List.length_pos_of_ne_nil (blockAlignedRuns_nonempty hk p hp)
  constructor
  · intro hz
    by_contra hnot
    have hqOne : blockAlignedRunCount hk p hp = 1 := by omega
    have hzOne := (blockAlignedZ_eq_one_iff_runCount_eq_one hk p hp).2 hqOne
    omega
  · intro hq
    rw [blockAlignedZ_eq_runCount_add_boundaryExcess hk p hp]
    omega

/-- **Cheap-entry capacity (Lemma `lem:cheapcapacity`).**  The proof applies
the endpoint-charged generic capacity theorem to the literal prepended path
`Q`, using its proved path/run/segment/deficit identities. -/
theorem pathForestComponentCheapCapacity (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (hnonroot : C ≠ pathForestRootComponent (by omega) P)
    (hminto : pathForestMinto (by omega) P C
        (pathForestComponent_vertexSet_ne_univ_of_nonroot
          (by omega) P C hnonroot) = 2)
    (hz : 2 ≤ pathForestComponentZ (by omega) P C) :
    pathForestComponentBlockCount (by omega) P C ≤
      hN (k - 1) (pathForestComponentZ (by omega) P C)
          (by omega) (by omega) - 1 -
        endpointChargeA (pathForestComponentFirstDeficit hk P C) -
        endpointChargeB (pathForestComponentLastDeficit hk P C) := by
  let dminus := pathForestComponentFirstDeficit hk P C
  let dplus := pathForestComponentLastDeficit hk P C
  have hcheap := pathForestComponentCheapDeficit hk P C hnonroot hminto
  have houtside : EntranceDoorClassOutside hk P C := hcheap.1
  let Q := cheapEntryPrependedPath hk P C houtside
  let hQ := cheapEntryPrependedPath_blockAligned hk P C houtside
  have hdminusPos : 1 ≤ dminus := by simpa [dminus] using hcheap.2.1
  have hdminusLe : dminus ≤ k - 2 := by simpa [dminus] using hcheap.2.2
  have hqComponent : 2 ≤ pathForestComponentRunCount hk P C := by
    let p := pathForestComponentPath (by omega) P C
    let hp := pathForestComponentPath_blockAligned (by omega) P C
    have hzGeneric : blockAlignedZ p hp =
        pathForestComponentZ (by omega) P C := rfl
    have hqGeneric :=
      (blockAlignedZ_ge_two_iff_runCount_ge_two hk p hp).1 (by
        rw [hzGeneric]
        exact hz)
    rw [pathForestComponentRunCount_eq_blockAlignedRunCount hk P C]
    simpa [p, hp] using hqGeneric
  have hqQ : 2 ≤ blockAlignedRunCount hk Q hQ := by
    rw [show blockAlignedRunCount hk Q hQ =
        pathForestComponentRunCount hk P C by
      simpa [Q, hQ] using cheapEntryPrependedPath_runCount hk P C houtside]
    exact hqComponent
  have hdeficits := cheapEntryPrependedPath_deficitChanges hk P C
    houtside hdminusPos
  have hfirstQ : dminus - 1 ≤ blockAlignedFirstDeficit hk Q hQ := by
    have := hdeficits.1
    simpa [Q, hQ, dminus] using this.symm.le
  have hlastQ : dplus ≤ blockAlignedLastDeficit hk Q hQ := by
    have hlast := cheapEntryPrependedPath_lastDeficit hk P C
      houtside hqComponent
    simpa [Q, hQ, dplus] using hlast.symm.le
  have hdplusLe : dplus ≤ k - 2 := by
    have hlastOld := pathForestComponentLastDeficit_eq_blockAlignedLastDeficit
      hk P C
    have hbound := blockAlignedLastDeficit_le hk
      (pathForestComponentPath (by omega) P C)
      (pathForestComponentPath_blockAligned (by omega) P C)
    simpa [dplus, hlastOld] using hbound
  have hcapacity := blockAlignedCapacityWithEndpoints
    (a := dminus - 1) (b := dplus) hk Q hQ hqQ
    (by omega) hdplusLe hfirstQ hlastQ
  have hblockCount : pathBlockCount Q =
      pathForestComponentBlockCount (by omega) P C + 1 := by
    simpa [Q] using cheapEntryPrependedPath_blockCount hk P C houtside
  have hzQ : blockAlignedZ Q hQ =
      pathForestComponentZ (by omega) P C := by
    simpa [Q, hQ] using cheapEntryPrependedPath_z hk P C houtside
  have hleftCharge : max 0 ((dminus - 1) - 1) =
      endpointChargeA dminus := by
    unfold endpointChargeA
    rw [Nat.sub_sub]
  rw [hleftCharge] at hcapacity
  change pathBlockCount Q + endpointChargeA dminus + endpointChargeB dplus ≤
    hN (k - 1) (blockAlignedZ Q hQ) (by omega) (by omega) at hcapacity
  rw [hblockCount] at hcapacity
  have hcapacity' :
      pathForestComponentBlockCount (by omega) P C + 1 +
          endpointChargeA dminus + endpointChargeB dplus ≤
        hN (k - 1) (pathForestComponentZ (by omega) P C)
          (by omega) (by omega) := by
    simpa only [hzQ] using hcapacity
  change pathForestComponentBlockCount (by omega) P C ≤ _
  change pathForestComponentBlockCount (by omega) P C ≤
    hN (k - 1) (pathForestComponentZ (by omega) P C)
        (by omega) (by omega) - 1 - endpointChargeA dminus -
          endpointChargeB dplus
  omega

/-- Component form of the exact `z≥2 ↔ q≥2` consequence in
Remark `rem:noqone`. -/
theorem pathForestComponentZ_ge_two_iff_runCount_ge_two (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P)) :
    2 ≤ pathForestComponentZ (by omega) P C ↔
      2 ≤ pathForestComponentRunCount hk P C := by
  let p := pathForestComponentPath (by omega) P C
  let hp := pathForestComponentPath_blockAligned (by omega) P C
  have hgeneric := blockAlignedZ_ge_two_iff_runCount_ge_two hk p hp
  have hz : blockAlignedZ p hp = pathForestComponentZ (by omega) P C := rfl
  have hq := pathForestComponentRunCount_eq_blockAlignedRunCount hk P C
  simpa [p, hp, hz, hq] using hgeneric

/-- The remaining cheap `z=1` alternative from Remark `rem:noqone`:
there is one run, its two endpoint deficits coincide and are positive, and
the exact block count is `n-d`. -/
theorem pathForestComponentCheapZOne (hk : 7 ≤ k)
    (P : HamiltonianPath k)
    (C : WeakComponent (pathForest (by omega) P))
    (hnonroot : C ≠ pathForestRootComponent (by omega) P)
    (hminto : pathForestMinto (by omega) P C
        (pathForestComponent_vertexSet_ne_univ_of_nonroot
          (by omega) P C hnonroot) = 2)
    (hz : pathForestComponentZ (by omega) P C = 1) :
    pathForestComponentRunCount hk P C = 1 ∧
      pathForestComponentFirstDeficit hk P C =
        pathForestComponentLastDeficit hk P C ∧
      1 ≤ pathForestComponentFirstDeficit hk P C ∧
      pathForestComponentBlockCount (by omega) P C =
        (k - 1) - pathForestComponentFirstDeficit hk P C := by
  let p := pathForestComponentPath (by omega) P C
  let hp := pathForestComponentPath_blockAligned (by omega) P C
  have hzGeneric : blockAlignedZ p hp = 1 := by
    change pathForestComponentZ (by omega) P C = 1
    exact hz
  have hone := blockAlignedCapacity_eq_of_z_one hk p hp hzGeneric
  have hq : pathForestComponentRunCount hk P C = 1 := by
    rw [pathForestComponentRunCount_eq_blockAlignedRunCount hk P C]
    simpa [p, hp] using hone.1
  have hfirstLast : pathForestComponentFirstDeficit hk P C =
      pathForestComponentLastDeficit hk P C := by
    rw [pathForestComponentFirstDeficit_eq_deficitAt_zero hk P C,
      pathForestComponentLastDeficit_eq_deficitAt_last hk P C, hq]
  have hpositive :=
    (pathForestComponentCheapDeficit hk P C hnonroot hminto).2.1
  have hlast := pathForestComponentLastDeficit_eq_blockAlignedLastDeficit
    hk P C
  have hblocks : pathForestComponentBlockCount (by omega) P C =
      (k - 1) - pathForestComponentFirstDeficit hk P C := by
    change pathBlockCount p = _
    rw [hfirstLast]
    simpa [p, hp, hlast] using hone.2.2
  exact ⟨hq, hfirstLast, hpositive, hblocks⟩

end SuperpermutationLowerBound
