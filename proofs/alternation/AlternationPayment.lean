module

public import SuperpermutationLowerBound.Refinement.ChainPackingUniversal

@[expose] public section

/-! The weighted reserve in Section 5 of the frozen manuscript.  The input
is a literal list of positive chain lengths satisfying `FourChainTrap`.
No assertion about superpermutation words is encoded as an axiom here. -/

namespace SuperpermutationLowerBound.Refinement.ChainReturns

open SuperpermutationLowerBound.Refinement

def lossMass (b : ℕ) (ls : List ℕ) : ℕ := (ls.map (fun x => b - x)).sum
def oneCount (ls : List ℕ) : ℕ := (ls.map singletonIndicator).sum
def ordinaryBadIndicator (b x : ℕ) : ℕ := if 2 ≤ b - x ∧ x ≠ 1 then 1 else 0
def ordinaryBadCount (b : ℕ) (ls : List ℕ) : ℕ :=
  (ls.map (ordinaryBadIndicator b)).sum
def markerCount (b : ℕ) (ls : List ℕ) : ℕ :=
  (ls.map (fun x => singletonIndicator x + nonmaxIndicator b x)).sum

def windowWitness (b : ℕ) (ls : List ℕ) (i : ℕ) : ℕ :=
  singletonIndicator (deficitAt ls i) +
  nonmaxIndicator b (deficitAt ls (i + 1)) +
  nonmaxIndicator b (deficitAt ls (i + 2)) +
  singletonIndicator (deficitAt ls (i + 3))

def excessWitness (b : ℕ) (ls : List ℕ) : ℕ :=
  ∑ i ∈ Finset.range (ls.length - 3), (windowWitness b ls i - 1)

theorem weighted_vertex_reserve {b x : ℕ} (hb : 5 ≤ b)
    (hx : 1 ≤ x) (hxb : x ≤ b) :
    ordinaryBadIndicator b x + (b - 3) * singletonIndicator x +
      (singletonIndicator x + nonmaxIndicator b x) ≤ b - x := by
  unfold ordinaryBadIndicator singletonIndicator nonmaxIndicator
  split_ifs <;> omega

theorem weighted_total_reserve {b : ℕ} (hb : 5 ≤ b) (ls : List ℕ)
    (hbound : ∀ x ∈ ls, 1 ≤ x ∧ x ≤ b) :
    ordinaryBadCount b ls + (b - 3) * oneCount ls + markerCount b ls ≤
      lossMass b ls := by
  induction ls with
  | nil => simp [ordinaryBadCount, oneCount, markerCount, lossMass]
  | cons x xs ih =>
      have hx := hbound x (by simp)
      have htail := ih (by intro y hy; exact hbound y (by simp [hy]))
      have hv := weighted_vertex_reserve hb hx.1 hx.2
      simp only [ordinaryBadCount, oneCount, markerCount, lossMass, List.map_cons,
        List.sum_cons, Nat.mul_add] at *
      omega

theorem windowWitness_pos {b : ℕ} (ls : List ℕ)
    (hbound : ∀ x ∈ ls, 1 ≤ x ∧ x ≤ b) (htrap : FourChainTrap b ls)
    (i : ℕ) (hi : i < ls.length - 3) : 1 ≤ windowWitness b ls i := by
  have hir : i + 3 < ls.length := by omega
  exact four_chain_indicator
    (hbound _ (deficitAt_mem ls i (by omega))).1
    (hbound _ (deficitAt_mem ls (i + 3) hir)).1 (htrap.at i hir)

theorem witness_mass_eq {b : ℕ} (ls : List ℕ)
    (hbound : ∀ x ∈ ls, 1 ≤ x ∧ x ≤ b) (htrap : FourChainTrap b ls) :
    (ls.length - 3) + excessWitness b ls =
      ∑ i ∈ Finset.range (ls.length - 3), windowWitness b ls i := by
  unfold excessWitness
  calc
    _ = (∑ _i ∈ Finset.range (ls.length - 3), 1) +
        ∑ i ∈ Finset.range (ls.length - 3), (windowWitness b ls i - 1) := by simp
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have h := windowWitness_pos ls hbound htrap i (Finset.mem_range.mp hi)
      omega

theorem witness_mass_le_markers {b : ℕ} (ls : List ℕ) :
    (∑ i ∈ Finset.range (ls.length - 3), windowWitness b ls i) ≤
      2 * markerCount b ls := by
  by_cases hlen : 3 ≤ ls.length
  swap
  · simp [show ls.length - 3 = 0 by omega]
  let q := ls.length - 3
  let one := fun i => singletonIndicator (deficitAt ls i)
  let nonmax := fun i => nonmaxIndicator b (deficitAt ls i)
  have h0 := nat_sum_range_shift_le one ls.length 0 q (by dsimp [q]; omega)
  have h1 := nat_sum_range_shift_le nonmax ls.length 1 q (by dsimp [q]; omega)
  have h2 := nat_sum_range_shift_le nonmax ls.length 2 q (by dsimp [q]; omega)
  have h3 := nat_sum_range_shift_le one ls.length 3 q (by dsimp [q]; omega)
  have hm := sum_range_deficitAt
    (fun x => singletonIndicator x + nonmaxIndicator b x) ls
  simp only [Finset.sum_add_distrib, Nat.zero_add, Nat.add_comm 1,
    Nat.add_comm 2, Nat.add_comm 3] at *
  change (∑ i ∈ Finset.range q, (one i + nonmax (i + 1) + nonmax (i + 2) +
    one (i + 3))) ≤ 2 * markerCount b ls
  simp only [Finset.sum_add_distrib]
  dsimp [one, nonmax] at *
  unfold markerCount
  omega

def doubleMaxIndicator (b x y : ℕ) : ℕ := if x = b ∧ y = b then 1 else 0
def doubleNearMaxIndicator (b x y : ℕ) : ℕ :=
  if x = b - 1 ∧ y = b - 1 then 1 else 0

/-- A binary `00` cut has a singleton witness at one of its two outer
positions.  No coverage or aggregate-capacity premise is used. -/
theorem doubleMax_paid_by_singletons {b x y z w : ℕ}
    (hx : 1 ≤ x) (hw : 1 ≤ w)
    (htrap : 2 ≤ x → 2 ≤ w → ¬ (y = b ∧ z = b)) :
    doubleMaxIndicator b y z ≤ singletonIndicator x + singletonIndicator w := by
  by_cases hx1 : x = 1
  · simp only [doubleMaxIndicator, singletonIndicator, hx1, ↓reduceIte]
    split_ifs <;> omega
  by_cases hw1 : w = 1
  · simp only [doubleMaxIndicator, singletonIndicator, hw1, ↓reduceIte]
    split_ifs <;> omega
  have hnot := htrap (by omega) (by omega)
  simp [doubleMaxIndicator, hnot]

/-- A binary `11` cut contributes an extra witness to its unique window. -/
theorem doubleNearMax_paid_by_excess {b x y z w : ℕ} (hb : 1 ≤ b) :
    doubleNearMaxIndicator b y z ≤
      singletonIndicator x + nonmaxIndicator b y + nonmaxIndicator b z +
        singletonIndicator w - 1 := by
  unfold doubleNearMaxIndicator nonmaxIndicator
  split_ifs <;> omega

def doubleMaxCount (b : ℕ) (ls : List ℕ) : ℕ :=
  ∑ i ∈ Finset.range (ls.length - 3),
    doubleMaxIndicator b (deficitAt ls (i + 1)) (deficitAt ls (i + 2))
def doubleNearMaxCount (b : ℕ) (ls : List ℕ) : ℕ :=
  ∑ i ∈ Finset.range (ls.length - 3),
    doubleNearMaxIndicator b (deficitAt ls (i + 1)) (deficitAt ls (i + 2))

theorem doubleNearMax_count_le_excess {b : ℕ} (hb : 1 ≤ b) (ls : List ℕ) :
    doubleNearMaxCount b ls ≤ excessWitness b ls := by
  apply Finset.sum_le_sum
  intro i _
  exact doubleNearMax_paid_by_excess hb

theorem doubleMax_count_le_twice_singletons {b : ℕ} (ls : List ℕ)
    (hbound : ∀ x ∈ ls, 1 ≤ x ∧ x ≤ b) (htrap : FourChainTrap b ls) :
    doubleMaxCount b ls ≤ 2 * oneCount ls := by
  by_cases hlen : 3 ≤ ls.length
  swap
  · simp [doubleMaxCount, show ls.length - 3 = 0 by omega]
  let one := fun i => singletonIndicator (deficitAt ls i)
  have hlocal : ∀ i ∈ Finset.range (ls.length - 3),
      doubleMaxIndicator b (deficitAt ls (i + 1)) (deficitAt ls (i + 2)) ≤
        one i + one (i + 3) := by
    intro i hi
    have hir : i + 3 < ls.length := by
      have := Finset.mem_range.mp hi
      omega
    exact doubleMax_paid_by_singletons
      (hbound _ (deficitAt_mem ls i (by omega))).1
      (hbound _ (deficitAt_mem ls (i + 3) hir)).1 (htrap.at i hir)
  have hs := Finset.sum_le_sum hlocal
  have h0 := nat_sum_range_shift_le one ls.length 0 (ls.length - 3) (by omega)
  have h3 := nat_sum_range_shift_le one ls.length 3 (ls.length - 3) (by omega)
  have ho := sum_range_deficitAt singletonIndicator ls
  simp only [Finset.sum_add_distrib, Nat.zero_add, Nat.add_comm 3] at *
  change doubleMaxCount b ls ≤ 2 * oneCount ls
  dsimp [one] at *
  unfold doubleMaxCount oneCount
  omega

/-- Both kinds of equal binary adjacency are now paid, with their actual
positions retained throughout the count. -/
theorem equal_cuts_paid {b : ℕ} (hb : 1 ≤ b) (ls : List ℕ)
    (hbound : ∀ x ∈ ls, 1 ≤ x ∧ x ≤ b) (htrap : FourChainTrap b ls) :
    doubleMaxCount b ls + doubleNearMaxCount b ls ≤
      2 * oneCount ls + excessWitness b ls := by
  have h0 := doubleMax_count_le_twice_singletons ls hbound htrap
  have h1 := doubleNearMax_count_le_excess hb ls
  omega

/-- The reserve inequality before subtracting the mandatory window witnesses.
It retains the exact extra-witness count rather than replacing it by zero. -/
theorem weighted_defect_payment {b : ℕ} (hb : 5 ≤ b) (ls : List ℕ)
    (hbound : ∀ x ∈ ls, 1 ≤ x ∧ x ≤ b) (htrap : FourChainTrap b ls) :
    2 * ordinaryBadCount b ls + 2 * (b - 3) * oneCount ls +
      excessWitness b ls + (ls.length - 3) ≤ 2 * lossMass b ls := by
  have hv := weighted_total_reserve hb ls hbound
  have hw := witness_mass_eq ls hbound htrap
  have hm := witness_mass_le_markers (b := b) ls
  nlinarith

/-- Algebraic final step of the alternation argument.  The cut count is an
explicit hypothesis; proving it from the bounded alternating factors is the
separate combinatorial decomposition theorem. -/
theorem alternation_allowance_of_cut_count {b R : ℕ} (hb : 5 ≤ b)
    (hR : 1 ≤ R) (ls : List ℕ) (hq : 3 ≤ ls.length)
    (hbound : ∀ x ∈ ls, 1 ≤ x ∧ x ≤ b) (htrap : FourChainTrap b ls)
    (hcuts : ls.length - 2 ≤ ordinaryBadCount b ls + oneCount ls +
      2 * R * (ordinaryBadCount b ls + 3 * oneCount ls + excessWitness b ls + 1)) :
    (ls.sum : ℚ) ≤ ((b : ℚ) + 3 / 2 + 1 / (4 * (R : ℚ))) +
      (((2 * (b : ℚ) - 1) - 1 / (2 * (R : ℚ))) / 2) *
        ((ls.length : ℚ) - 1) := by
  have hp := weighted_defect_payment hb ls hbound htrap
  have hmass := sum_add_chain_deficits b ls (by intro x hx; exact (hbound x hx).2)
  have hbR : (1 + 2 * R) * ordinaryBadCount b ls ≤
      4 * R * ordinaryBadCount b ls := by nlinarith
  have hwR : (1 + 6 * R) * oneCount ls ≤
      4 * R * (b - 3) * oneCount ls := by
    have hb3 : 2 ≤ b - 3 := by omega
    have hcoeff : 1 + 6 * R ≤ 4 * R * (b - 3) := by nlinarith
    exact Nat.mul_le_mul_right _ hcoeff
  have hpaid : ls.length - 2 ≤
      2 * R * (2 * lossMass b ls - (ls.length - 3) + 1) := by
    have hsub : 2 * ordinaryBadCount b ls + 2 * (b - 3) * oneCount ls +
        excessWitness b ls ≤ 2 * lossMass b ls - (ls.length - 3) := by omega
    have hweighted := Nat.mul_le_mul_left (2 * R) hsub
    nlinarith
  have hdef : ls.length - 3 ≤ 2 * lossMass b ls := by omega
  have hpoly : ls.length + 2 * R * ls.length ≤ 4 * R * lossMass b ls + 8 * R + 2 := by
    have hq2 : ls.length - 2 + 2 = ls.length := Nat.sub_add_cancel (by omega)
    have hq3 : ls.length - 3 + 3 = ls.length := Nat.sub_add_cancel hq
    have hd := Nat.sub_add_cancel hdef
    have hq3R := congrArg (fun v => 2 * R * v) hq3
    have hdR := congrArg (fun v => 2 * R * v) hd
    nlinarith
  have hpaidQ : (ls.length : ℚ) + 2 * (R : ℚ) * ls.length ≤
      4 * (R : ℚ) * lossMass b ls + 8 * (R : ℚ) + 2 := by
    exact_mod_cast hpoly
  have hmassQ : (ls.sum : ℚ) + (lossMass b ls : ℚ) = (b : ℚ) * ls.length := by
    exact_mod_cast hmass
  have hRQ : (0 : ℚ) < R := by exact_mod_cast (show 0 < R by omega)
  have hscaled : (1 / (4 * (R : ℚ))) * (ls.length : ℚ) + (ls.length : ℚ) / 2 ≤
      lossMass b ls + 2 + 2 * (1 / (4 * (R : ℚ))) := by
    calc
      _ = (1 / (4 * (R : ℚ))) *
          ((ls.length : ℚ) + 2 * (R : ℚ) * ls.length) := by
        field_simp [ne_of_gt hRQ]
        ring
      _ ≤ (1 / (4 * (R : ℚ))) *
          (4 * (R : ℚ) * lossMass b ls + 8 * (R : ℚ) + 2) := by
        exact mul_le_mul_of_nonneg_left hpaidQ (by positivity)
      _ = _ := by
        field_simp [ne_of_gt hRQ]
        ring
  have hhalf : 1 / (2 * (R : ℚ)) = 2 * (1 / (4 * (R : ℚ))) := by
    field_simp [ne_of_gt hRQ]
    ring
  rw [hhalf]
  nlinarith

end SuperpermutationLowerBound.Refinement.ChainReturns
