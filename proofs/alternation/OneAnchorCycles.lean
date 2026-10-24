module

public import ReturnOneAnchors
public import FrozenStatement

@[expose] public section

/-! Closing the five anchor walks gives the six symbolic return exponents.
The finite cases are only anchor labels and m modulo six. -/

namespace SuperpermutationLowerBound.Refinement.ChainReturns

open SuperpermutationBounds.ChainReturns

theorem iterate_chain_step {α : Type*} (f : α → α) {p q : ℕ} {a b c : α}
    (hp : (f^[p]) a = b) (hq : (f^[q]) b = c) : (f^[p+q]) a = c := by
  rw [Nat.add_comm p q, Function.iterate_add_apply, hp, hq]

theorem iterate_fixed_multiple {α : Type*} (f : α → α) {p R : ℕ} {a : α}
    (hp : (f^[p]) a = a) (hd : p ∣ R) : (f^[R]) a = a := by
  obtain ⟨d, rfl⟩ := hd
  rw [Function.iterate_mul]
  exact Function.iterate_fixed hp d

theorem anchor_cycle_r0_a1 (h : ℕ) (hm : 3 ≤ 6*h+0) :
    ((efficientOneValue (6*h+0))^[18*h+1]) 1 = 1 := by
  have hh := (iterate_chain_step (efficientOneValue (6*h+0)) (iterate_chain_step (efficientOneValue (6*h+0)) (iterate_chain_step (efficientOneValue (6*h+0)) (iterate_chain_step (efficientOneValue (6*h+0)) (anchor_r0_a1 h hm) (anchor_r0_a4 h hm)) (anchor_r0_a5 h hm)) (anchor_r0_a2 h hm)) (anchor_r0_a3 h hm))
  convert hh using 1 <;> congr 1 <;> omega

theorem anchor_cycle_r0_a2 (h : ℕ) (hm : 3 ≤ 6*h+0) :
    ((efficientOneValue (6*h+0))^[18*h+1]) 2 = 2 := by
  have hh := (iterate_chain_step (efficientOneValue (6*h+0)) (iterate_chain_step (efficientOneValue (6*h+0)) (iterate_chain_step (efficientOneValue (6*h+0)) (iterate_chain_step (efficientOneValue (6*h+0)) (anchor_r0_a2 h hm) (anchor_r0_a3 h hm)) (anchor_r0_a1 h hm)) (anchor_r0_a4 h hm)) (anchor_r0_a5 h hm))
  convert hh using 1 <;> congr 1 <;> omega

theorem anchor_cycle_r0_a3 (h : ℕ) (hm : 3 ≤ 6*h+0) :
    ((efficientOneValue (6*h+0))^[18*h+1]) 3 = 3 := by
  have hh := (iterate_chain_step (efficientOneValue (6*h+0)) (iterate_chain_step (efficientOneValue (6*h+0)) (iterate_chain_step (efficientOneValue (6*h+0)) (iterate_chain_step (efficientOneValue (6*h+0)) (anchor_r0_a3 h hm) (anchor_r0_a1 h hm)) (anchor_r0_a4 h hm)) (anchor_r0_a5 h hm)) (anchor_r0_a2 h hm))
  convert hh using 1 <;> congr 1 <;> omega

theorem anchor_cycle_r0_a4 (h : ℕ) (hm : 3 ≤ 6*h+0) :
    ((efficientOneValue (6*h+0))^[18*h+1]) 4 = 4 := by
  have hh := (iterate_chain_step (efficientOneValue (6*h+0)) (iterate_chain_step (efficientOneValue (6*h+0)) (iterate_chain_step (efficientOneValue (6*h+0)) (iterate_chain_step (efficientOneValue (6*h+0)) (anchor_r0_a4 h hm) (anchor_r0_a5 h hm)) (anchor_r0_a2 h hm)) (anchor_r0_a3 h hm)) (anchor_r0_a1 h hm))
  convert hh using 1 <;> congr 1 <;> omega

theorem anchor_cycle_r0_a5 (h : ℕ) (hm : 3 ≤ 6*h+0) :
    ((efficientOneValue (6*h+0))^[18*h+1]) 5 = 5 := by
  have hh := (iterate_chain_step (efficientOneValue (6*h+0)) (iterate_chain_step (efficientOneValue (6*h+0)) (iterate_chain_step (efficientOneValue (6*h+0)) (iterate_chain_step (efficientOneValue (6*h+0)) (anchor_r0_a5 h hm) (anchor_r0_a2 h hm)) (anchor_r0_a3 h hm)) (anchor_r0_a1 h hm)) (anchor_r0_a4 h hm))
  convert hh using 1 <;> congr 1 <;> omega

theorem returnOne_residue_0 (h : ℕ) : returnOne (6*h+0) = 18*h+1 := by
  simp only [returnOne, show (6*h+0) % 6 = 0 by omega]
  change 3 * (6*h+0) + 1 = 18*h+1
  omega

theorem anchors_return_r0 (h : ℕ) (hm : 3 ≤ 6*h+0) (a : ℕ)
    (ha : 1 ≤ a) (ha5 : a ≤ 5) :
    ((efficientOneValue (6*h+0))^[returnOne (6*h+0)]) a = a := by
  interval_cases a
  · apply iterate_fixed_multiple (efficientOneValue (6*h+0)) (anchor_cycle_r0_a1 h hm)
    rw [returnOne_residue_0]
  · apply iterate_fixed_multiple (efficientOneValue (6*h+0)) (anchor_cycle_r0_a2 h hm)
    rw [returnOne_residue_0]
  · apply iterate_fixed_multiple (efficientOneValue (6*h+0)) (anchor_cycle_r0_a3 h hm)
    rw [returnOne_residue_0]
  · apply iterate_fixed_multiple (efficientOneValue (6*h+0)) (anchor_cycle_r0_a4 h hm)
    rw [returnOne_residue_0]
  · apply iterate_fixed_multiple (efficientOneValue (6*h+0)) (anchor_cycle_r0_a5 h hm)
    rw [returnOne_residue_0]

theorem anchor_cycle_r1_a1 (h : ℕ) (hm : 3 ≤ 6*h+1) :
    ((efficientOneValue (6*h+1))^[14*h+3]) 1 = 1 := by
  have hh := (iterate_chain_step (efficientOneValue (6*h+1)) (iterate_chain_step (efficientOneValue (6*h+1)) (iterate_chain_step (efficientOneValue (6*h+1)) (anchor_r1_a1 h hm) (anchor_r1_a3 h hm)) (anchor_r1_a2 h hm)) (anchor_r1_a5 h hm))
  convert hh using 1 <;> congr 1 <;> omega

theorem anchor_cycle_r1_a2 (h : ℕ) (hm : 3 ≤ 6*h+1) :
    ((efficientOneValue (6*h+1))^[14*h+3]) 2 = 2 := by
  have hh := (iterate_chain_step (efficientOneValue (6*h+1)) (iterate_chain_step (efficientOneValue (6*h+1)) (iterate_chain_step (efficientOneValue (6*h+1)) (anchor_r1_a2 h hm) (anchor_r1_a5 h hm)) (anchor_r1_a1 h hm)) (anchor_r1_a3 h hm))
  convert hh using 1 <;> congr 1 <;> omega

theorem anchor_cycle_r1_a3 (h : ℕ) (hm : 3 ≤ 6*h+1) :
    ((efficientOneValue (6*h+1))^[14*h+3]) 3 = 3 := by
  have hh := (iterate_chain_step (efficientOneValue (6*h+1)) (iterate_chain_step (efficientOneValue (6*h+1)) (iterate_chain_step (efficientOneValue (6*h+1)) (anchor_r1_a3 h hm) (anchor_r1_a2 h hm)) (anchor_r1_a5 h hm)) (anchor_r1_a1 h hm))
  convert hh using 1 <;> congr 1 <;> omega

theorem anchor_cycle_r1_a4 (h : ℕ) (hm : 3 ≤ 6*h+1) :
    ((efficientOneValue (6*h+1))^[4*h+1]) 4 = 4 := by
  exact anchor_r1_a4 h hm

theorem anchor_cycle_r1_a5 (h : ℕ) (hm : 3 ≤ 6*h+1) :
    ((efficientOneValue (6*h+1))^[14*h+3]) 5 = 5 := by
  have hh := (iterate_chain_step (efficientOneValue (6*h+1)) (iterate_chain_step (efficientOneValue (6*h+1)) (iterate_chain_step (efficientOneValue (6*h+1)) (anchor_r1_a5 h hm) (anchor_r1_a1 h hm)) (anchor_r1_a3 h hm)) (anchor_r1_a2 h hm))
  convert hh using 1 <;> congr 1 <;> omega

theorem returnOne_residue_1 (h : ℕ) : returnOne (6*h+1) = Nat.lcm (4*h+1) (14*h+3) := by
  simp only [returnOne, show (6*h+1) % 6 = 1 by omega]
  change Nat.lcm ((2 * (6*h+1) + 1) / 3) ((7 * (6*h+1) + 2) / 3) = Nat.lcm (4*h+1) (14*h+3)
  congr 1 <;> omega

theorem anchors_return_r1 (h : ℕ) (hm : 3 ≤ 6*h+1) (a : ℕ)
    (ha : 1 ≤ a) (ha5 : a ≤ 5) :
    ((efficientOneValue (6*h+1))^[returnOne (6*h+1)]) a = a := by
  interval_cases a
  · apply iterate_fixed_multiple (efficientOneValue (6*h+1)) (anchor_cycle_r1_a1 h hm)
    rw [returnOne_residue_1]
    exact Nat.dvd_lcm_right _ _
  · apply iterate_fixed_multiple (efficientOneValue (6*h+1)) (anchor_cycle_r1_a2 h hm)
    rw [returnOne_residue_1]
    exact Nat.dvd_lcm_right _ _
  · apply iterate_fixed_multiple (efficientOneValue (6*h+1)) (anchor_cycle_r1_a3 h hm)
    rw [returnOne_residue_1]
    exact Nat.dvd_lcm_right _ _
  · apply iterate_fixed_multiple (efficientOneValue (6*h+1)) (anchor_cycle_r1_a4 h hm)
    rw [returnOne_residue_1]
    exact Nat.dvd_lcm_left _ _
  · apply iterate_fixed_multiple (efficientOneValue (6*h+1)) (anchor_cycle_r1_a5 h hm)
    rw [returnOne_residue_1]
    exact Nat.dvd_lcm_right _ _

theorem anchor_cycle_r2_a1 (h : ℕ) (hm : 3 ≤ 6*h+2) :
    ((efficientOneValue (6*h+2))^[18*h+7]) 1 = 1 := by
  have hh := (iterate_chain_step (efficientOneValue (6*h+2)) (iterate_chain_step (efficientOneValue (6*h+2)) (iterate_chain_step (efficientOneValue (6*h+2)) (iterate_chain_step (efficientOneValue (6*h+2)) (anchor_r2_a1 h hm) (anchor_r2_a5 h hm)) (anchor_r2_a2 h hm)) (anchor_r2_a4 h hm)) (anchor_r2_a3 h hm))
  convert hh using 1 <;> congr 1 <;> omega

theorem anchor_cycle_r2_a2 (h : ℕ) (hm : 3 ≤ 6*h+2) :
    ((efficientOneValue (6*h+2))^[18*h+7]) 2 = 2 := by
  have hh := (iterate_chain_step (efficientOneValue (6*h+2)) (iterate_chain_step (efficientOneValue (6*h+2)) (iterate_chain_step (efficientOneValue (6*h+2)) (iterate_chain_step (efficientOneValue (6*h+2)) (anchor_r2_a2 h hm) (anchor_r2_a4 h hm)) (anchor_r2_a3 h hm)) (anchor_r2_a1 h hm)) (anchor_r2_a5 h hm))
  convert hh using 1 <;> congr 1 <;> omega

theorem anchor_cycle_r2_a3 (h : ℕ) (hm : 3 ≤ 6*h+2) :
    ((efficientOneValue (6*h+2))^[18*h+7]) 3 = 3 := by
  have hh := (iterate_chain_step (efficientOneValue (6*h+2)) (iterate_chain_step (efficientOneValue (6*h+2)) (iterate_chain_step (efficientOneValue (6*h+2)) (iterate_chain_step (efficientOneValue (6*h+2)) (anchor_r2_a3 h hm) (anchor_r2_a1 h hm)) (anchor_r2_a5 h hm)) (anchor_r2_a2 h hm)) (anchor_r2_a4 h hm))
  convert hh using 1 <;> congr 1 <;> omega

theorem anchor_cycle_r2_a4 (h : ℕ) (hm : 3 ≤ 6*h+2) :
    ((efficientOneValue (6*h+2))^[18*h+7]) 4 = 4 := by
  have hh := (iterate_chain_step (efficientOneValue (6*h+2)) (iterate_chain_step (efficientOneValue (6*h+2)) (iterate_chain_step (efficientOneValue (6*h+2)) (iterate_chain_step (efficientOneValue (6*h+2)) (anchor_r2_a4 h hm) (anchor_r2_a3 h hm)) (anchor_r2_a1 h hm)) (anchor_r2_a5 h hm)) (anchor_r2_a2 h hm))
  convert hh using 1 <;> congr 1 <;> omega

theorem anchor_cycle_r2_a5 (h : ℕ) (hm : 3 ≤ 6*h+2) :
    ((efficientOneValue (6*h+2))^[18*h+7]) 5 = 5 := by
  have hh := (iterate_chain_step (efficientOneValue (6*h+2)) (iterate_chain_step (efficientOneValue (6*h+2)) (iterate_chain_step (efficientOneValue (6*h+2)) (iterate_chain_step (efficientOneValue (6*h+2)) (anchor_r2_a5 h hm) (anchor_r2_a2 h hm)) (anchor_r2_a4 h hm)) (anchor_r2_a3 h hm)) (anchor_r2_a1 h hm))
  convert hh using 1 <;> congr 1 <;> omega

theorem returnOne_residue_2 (h : ℕ) : returnOne (6*h+2) = 18*h+7 := by
  simp only [returnOne, show (6*h+2) % 6 = 2 by omega]
  change 3 * (6*h+2) + 1 = 18*h+7
  omega

theorem anchors_return_r2 (h : ℕ) (hm : 3 ≤ 6*h+2) (a : ℕ)
    (ha : 1 ≤ a) (ha5 : a ≤ 5) :
    ((efficientOneValue (6*h+2))^[returnOne (6*h+2)]) a = a := by
  interval_cases a
  · apply iterate_fixed_multiple (efficientOneValue (6*h+2)) (anchor_cycle_r2_a1 h hm)
    rw [returnOne_residue_2]
  · apply iterate_fixed_multiple (efficientOneValue (6*h+2)) (anchor_cycle_r2_a2 h hm)
    rw [returnOne_residue_2]
  · apply iterate_fixed_multiple (efficientOneValue (6*h+2)) (anchor_cycle_r2_a3 h hm)
    rw [returnOne_residue_2]
  · apply iterate_fixed_multiple (efficientOneValue (6*h+2)) (anchor_cycle_r2_a4 h hm)
    rw [returnOne_residue_2]
  · apply iterate_fixed_multiple (efficientOneValue (6*h+2)) (anchor_cycle_r2_a5 h hm)
    rw [returnOne_residue_2]

theorem anchor_cycle_r3_a1 (h : ℕ) (hm : 3 ≤ 6*h+3) :
    ((efficientOneValue (6*h+3))^[11*h+6]) 1 = 1 := by
  have hh := (iterate_chain_step (efficientOneValue (6*h+3)) (iterate_chain_step (efficientOneValue (6*h+3)) (anchor_r3_a1 h hm) (anchor_r3_a4 h hm)) (anchor_r3_a5 h hm))
  convert hh using 1 <;> congr 1 <;> omega

theorem anchor_cycle_r3_a2 (h : ℕ) (hm : 3 ≤ 6*h+3) :
    ((efficientOneValue (6*h+3))^[7*h+4]) 2 = 2 := by
  have hh := (iterate_chain_step (efficientOneValue (6*h+3)) (anchor_r3_a2 h hm) (anchor_r3_a3 h hm))
  convert hh using 1 <;> congr 1 <;> omega

theorem anchor_cycle_r3_a3 (h : ℕ) (hm : 3 ≤ 6*h+3) :
    ((efficientOneValue (6*h+3))^[7*h+4]) 3 = 3 := by
  have hh := (iterate_chain_step (efficientOneValue (6*h+3)) (anchor_r3_a3 h hm) (anchor_r3_a2 h hm))
  convert hh using 1 <;> congr 1 <;> omega

theorem anchor_cycle_r3_a4 (h : ℕ) (hm : 3 ≤ 6*h+3) :
    ((efficientOneValue (6*h+3))^[11*h+6]) 4 = 4 := by
  have hh := (iterate_chain_step (efficientOneValue (6*h+3)) (iterate_chain_step (efficientOneValue (6*h+3)) (anchor_r3_a4 h hm) (anchor_r3_a5 h hm)) (anchor_r3_a1 h hm))
  convert hh using 1 <;> congr 1 <;> omega

theorem anchor_cycle_r3_a5 (h : ℕ) (hm : 3 ≤ 6*h+3) :
    ((efficientOneValue (6*h+3))^[11*h+6]) 5 = 5 := by
  have hh := (iterate_chain_step (efficientOneValue (6*h+3)) (iterate_chain_step (efficientOneValue (6*h+3)) (anchor_r3_a5 h hm) (anchor_r3_a1 h hm)) (anchor_r3_a4 h hm))
  convert hh using 1 <;> congr 1 <;> omega

theorem returnOne_residue_3 (h : ℕ) : returnOne (6*h+3) = Nat.lcm (7*h+4) (11*h+6) := by
  simp only [returnOne, show (6*h+3) % 6 = 3 by omega]
  change Nat.lcm ((7 * (6*h+3) + 3) / 6) ((11 * (6*h+3) + 3) / 6) = Nat.lcm (7*h+4) (11*h+6)
  congr 1 <;> omega

theorem anchors_return_r3 (h : ℕ) (hm : 3 ≤ 6*h+3) (a : ℕ)
    (ha : 1 ≤ a) (ha5 : a ≤ 5) :
    ((efficientOneValue (6*h+3))^[returnOne (6*h+3)]) a = a := by
  interval_cases a
  · apply iterate_fixed_multiple (efficientOneValue (6*h+3)) (anchor_cycle_r3_a1 h hm)
    rw [returnOne_residue_3]
    exact Nat.dvd_lcm_right _ _
  · apply iterate_fixed_multiple (efficientOneValue (6*h+3)) (anchor_cycle_r3_a2 h hm)
    rw [returnOne_residue_3]
    exact Nat.dvd_lcm_left _ _
  · apply iterate_fixed_multiple (efficientOneValue (6*h+3)) (anchor_cycle_r3_a3 h hm)
    rw [returnOne_residue_3]
    exact Nat.dvd_lcm_left _ _
  · apply iterate_fixed_multiple (efficientOneValue (6*h+3)) (anchor_cycle_r3_a4 h hm)
    rw [returnOne_residue_3]
    exact Nat.dvd_lcm_right _ _
  · apply iterate_fixed_multiple (efficientOneValue (6*h+3)) (anchor_cycle_r3_a5 h hm)
    rw [returnOne_residue_3]
    exact Nat.dvd_lcm_right _ _

theorem anchor_cycle_r4_a1 (h : ℕ) (hm : 3 ≤ 6*h+4) :
    ((efficientOneValue (6*h+4))^[7*h+5]) 1 = 1 := by
  have hh := (iterate_chain_step (efficientOneValue (6*h+4)) (anchor_r4_a1 h hm) (anchor_r4_a3 h hm))
  convert hh using 1 <;> congr 1 <;> omega

theorem anchor_cycle_r4_a2 (h : ℕ) (hm : 3 ≤ 6*h+4) :
    ((efficientOneValue (6*h+4))^[7*h+5]) 2 = 2 := by
  have hh := (iterate_chain_step (efficientOneValue (6*h+4)) (anchor_r4_a2 h hm) (anchor_r4_a5 h hm))
  convert hh using 1 <;> congr 1 <;> omega

theorem anchor_cycle_r4_a3 (h : ℕ) (hm : 3 ≤ 6*h+4) :
    ((efficientOneValue (6*h+4))^[7*h+5]) 3 = 3 := by
  have hh := (iterate_chain_step (efficientOneValue (6*h+4)) (anchor_r4_a3 h hm) (anchor_r4_a1 h hm))
  convert hh using 1 <;> congr 1 <;> omega

theorem anchor_cycle_r4_a4 (h : ℕ) (hm : 3 ≤ 6*h+4) :
    ((efficientOneValue (6*h+4))^[4*h+3]) 4 = 4 := by
  exact anchor_r4_a4 h hm

theorem anchor_cycle_r4_a5 (h : ℕ) (hm : 3 ≤ 6*h+4) :
    ((efficientOneValue (6*h+4))^[7*h+5]) 5 = 5 := by
  have hh := (iterate_chain_step (efficientOneValue (6*h+4)) (anchor_r4_a5 h hm) (anchor_r4_a2 h hm))
  convert hh using 1 <;> congr 1 <;> omega

theorem returnOne_residue_4 (h : ℕ) : returnOne (6*h+4) = Nat.lcm (4*h+3) (7*h+5) := by
  simp only [returnOne, show (6*h+4) % 6 = 4 by omega]
  change Nat.lcm ((2 * (6*h+4) + 1) / 3) ((7 * (6*h+4) + 2) / 6) = Nat.lcm (4*h+3) (7*h+5)
  congr 1 <;> omega

theorem anchors_return_r4 (h : ℕ) (hm : 3 ≤ 6*h+4) (a : ℕ)
    (ha : 1 ≤ a) (ha5 : a ≤ 5) :
    ((efficientOneValue (6*h+4))^[returnOne (6*h+4)]) a = a := by
  interval_cases a
  · apply iterate_fixed_multiple (efficientOneValue (6*h+4)) (anchor_cycle_r4_a1 h hm)
    rw [returnOne_residue_4]
    exact Nat.dvd_lcm_right _ _
  · apply iterate_fixed_multiple (efficientOneValue (6*h+4)) (anchor_cycle_r4_a2 h hm)
    rw [returnOne_residue_4]
    exact Nat.dvd_lcm_right _ _
  · apply iterate_fixed_multiple (efficientOneValue (6*h+4)) (anchor_cycle_r4_a3 h hm)
    rw [returnOne_residue_4]
    exact Nat.dvd_lcm_right _ _
  · apply iterate_fixed_multiple (efficientOneValue (6*h+4)) (anchor_cycle_r4_a4 h hm)
    rw [returnOne_residue_4]
    exact Nat.dvd_lcm_left _ _
  · apply iterate_fixed_multiple (efficientOneValue (6*h+4)) (anchor_cycle_r4_a5 h hm)
    rw [returnOne_residue_4]
    exact Nat.dvd_lcm_right _ _

theorem anchor_cycle_r5_a1 (h : ℕ) (hm : 3 ≤ 6*h+5) :
    ((efficientOneValue (6*h+5))^[7*h+6]) 1 = 1 := by
  have hh := (iterate_chain_step (efficientOneValue (6*h+5)) (anchor_r5_a1 h hm) (anchor_r5_a5 h hm))
  convert hh using 1 <;> congr 1 <;> omega

theorem anchor_cycle_r5_a2 (h : ℕ) (hm : 3 ≤ 6*h+5) :
    ((efficientOneValue (6*h+5))^[11*h+10]) 2 = 2 := by
  have hh := (iterate_chain_step (efficientOneValue (6*h+5)) (iterate_chain_step (efficientOneValue (6*h+5)) (anchor_r5_a2 h hm) (anchor_r5_a4 h hm)) (anchor_r5_a3 h hm))
  convert hh using 1 <;> congr 1 <;> omega

theorem anchor_cycle_r5_a3 (h : ℕ) (hm : 3 ≤ 6*h+5) :
    ((efficientOneValue (6*h+5))^[11*h+10]) 3 = 3 := by
  have hh := (iterate_chain_step (efficientOneValue (6*h+5)) (iterate_chain_step (efficientOneValue (6*h+5)) (anchor_r5_a3 h hm) (anchor_r5_a2 h hm)) (anchor_r5_a4 h hm))
  convert hh using 1 <;> congr 1 <;> omega

theorem anchor_cycle_r5_a4 (h : ℕ) (hm : 3 ≤ 6*h+5) :
    ((efficientOneValue (6*h+5))^[11*h+10]) 4 = 4 := by
  have hh := (iterate_chain_step (efficientOneValue (6*h+5)) (iterate_chain_step (efficientOneValue (6*h+5)) (anchor_r5_a4 h hm) (anchor_r5_a3 h hm)) (anchor_r5_a2 h hm))
  convert hh using 1 <;> congr 1 <;> omega

theorem anchor_cycle_r5_a5 (h : ℕ) (hm : 3 ≤ 6*h+5) :
    ((efficientOneValue (6*h+5))^[7*h+6]) 5 = 5 := by
  have hh := (iterate_chain_step (efficientOneValue (6*h+5)) (anchor_r5_a5 h hm) (anchor_r5_a1 h hm))
  convert hh using 1 <;> congr 1 <;> omega

theorem returnOne_residue_5 (h : ℕ) : returnOne (6*h+5) = Nat.lcm (7*h+6) (11*h+10) := by
  simp only [returnOne, show (6*h+5) % 6 = 5 by omega]
  change Nat.lcm ((7 * (6*h+5) + 1) / 6) ((11 * (6*h+5) + 5) / 6) = Nat.lcm (7*h+6) (11*h+10)
  congr 1 <;> omega

theorem anchors_return_r5 (h : ℕ) (hm : 3 ≤ 6*h+5) (a : ℕ)
    (ha : 1 ≤ a) (ha5 : a ≤ 5) :
    ((efficientOneValue (6*h+5))^[returnOne (6*h+5)]) a = a := by
  interval_cases a
  · apply iterate_fixed_multiple (efficientOneValue (6*h+5)) (anchor_cycle_r5_a1 h hm)
    rw [returnOne_residue_5]
    exact Nat.dvd_lcm_left _ _
  · apply iterate_fixed_multiple (efficientOneValue (6*h+5)) (anchor_cycle_r5_a2 h hm)
    rw [returnOne_residue_5]
    exact Nat.dvd_lcm_right _ _
  · apply iterate_fixed_multiple (efficientOneValue (6*h+5)) (anchor_cycle_r5_a3 h hm)
    rw [returnOne_residue_5]
    exact Nat.dvd_lcm_right _ _
  · apply iterate_fixed_multiple (efficientOneValue (6*h+5)) (anchor_cycle_r5_a4 h hm)
    rw [returnOne_residue_5]
    exact Nat.dvd_lcm_right _ _
  · apply iterate_fixed_multiple (efficientOneValue (6*h+5)) (anchor_cycle_r5_a5 h hm)
    rw [returnOne_residue_5]
    exact Nat.dvd_lcm_left _ _

theorem efficientOne_anchors_return (m : ℕ) (hm : 3 ≤ m) (a : ℕ)
    (ha : 1 ≤ a) (ha5 : a ≤ 5) : ((efficientOneValue m)^[returnOne m]) a = a := by
  have hres : m % 6 < 6 := Nat.mod_lt _ (by omega)
  interval_cases hr : m % 6
  · have he : m = 6*(m/6)+0 := by omega
    rw [he]
    exact anchors_return_r0 (m/6) (by omega) a ha ha5
  · have he : m = 6*(m/6)+1 := by omega
    rw [he]
    exact anchors_return_r1 (m/6) (by omega) a ha ha5
  · have he : m = 6*(m/6)+2 := by omega
    rw [he]
    exact anchors_return_r2 (m/6) (by omega) a ha ha5
  · have he : m = 6*(m/6)+3 := by omega
    rw [he]
    exact anchors_return_r3 (m/6) (by omega) a ha ha5
  · have he : m = 6*(m/6)+4 := by omega
    rw [he]
    exact anchors_return_r4 (m/6) (by omega) a ha ha5
  · have he : m = 6*(m/6)+5 := by omega
    rw [he]
    exact anchors_return_r5 (m/6) (by omega) a ha ha5

end SuperpermutationLowerBound.Refinement.ChainReturns
