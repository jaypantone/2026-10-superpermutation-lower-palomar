module

public import ReturnOneDescent

@[expose] public section

/-! The five first-return arcs, in each residue class of m modulo six.
Only the return identities are needed; minimality of these times is not asserted. -/
namespace SuperpermutationLowerBound.Refinement.ChainReturns

theorem anchor_r0_a1 (h : ℕ) (hm : 3 ≤ 6*h+0) :
    ((efficientOneValue (6*h+0))^[4*h]) 1 = 4 := by
  have hs : efficientOneValue (6*h+0) 1 = 9*(2*h-1)+8 := by
    norm_num [efficientOneValue]
    omega
  have ht : 4*h = (2*(2*h-1)+1) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_eight_descent (6*h+0) (2*h-1)

theorem anchor_r0_a2 (h : ℕ) (hm : 3 ≤ 6*h+0) :
    ((efficientOneValue (6*h+0))^[4*h]) 2 = 3 := by
  have hs : efficientOneValue (6*h+0) 2 = 9*(2*h-1)+7 := by
    norm_num [efficientOneValue]
    omega
  have ht : 4*h = (2*(2*h-1)+1) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_seven_descent (6*h+0) (2*h-1)

theorem anchor_r0_a3 (h : ℕ) (hm : 3 ≤ 6*h+0) :
    ((efficientOneValue (6*h+0))^[3*h]) 3 = 1 := by
  have hs : efficientOneValue (6*h+0) 3 = 6*(3*h-2)+9 := by
    norm_num [efficientOneValue]
    omega
  have ht : 3*h = ((3*h-2)+1) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_nine_descent (6*h+0) (3*h-2)

theorem anchor_r0_a4 (h : ℕ) (hm : 3 ≤ 6*h+0) :
    ((efficientOneValue (6*h+0))^[4*h]) 4 = 5 := by
  have hs : efficientOneValue (6*h+0) 4 = 9*(2*h-1)+10 := by
    norm_num [efficientOneValue]
    omega
  have ht : 4*h = (2*(2*h-1)+1) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_ten_descent (6*h+0) (2*h-1)

theorem anchor_r0_a5 (h : ℕ) (hm : 3 ≤ 6*h+0) :
    ((efficientOneValue (6*h+0))^[3*h+1]) 5 = 2 := by
  have hs : efficientOneValue (6*h+0) 5 = 6*(3*h-1)+6 := by
    norm_num [efficientOneValue]
    omega
  have ht : 3*h+1 = ((3*h-1)+1) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_six_descent (6*h+0) (3*h-1)

theorem anchor_r1_a1 (h : ℕ) (hm : 3 ≤ 6*h+1) :
    ((efficientOneValue (6*h+1))^[4*h+1]) 1 = 3 := by
  have hs : efficientOneValue (6*h+1) 1 = 9*(2*h-1)+11 := by
    norm_num [efficientOneValue]
    omega
  have ht : 4*h+1 = (2*(2*h-1)+2) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_eleven_descent (6*h+1) (2*h-1)

theorem anchor_r1_a2 (h : ℕ) (hm : 3 ≤ 6*h+1) :
    ((efficientOneValue (6*h+1))^[4*h]) 2 = 5 := by
  have hs : efficientOneValue (6*h+1) 2 = 9*(2*h-1)+10 := by
    norm_num [efficientOneValue]
    omega
  have ht : 4*h = (2*(2*h-1)+1) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_ten_descent (6*h+1) (2*h-1)

theorem anchor_r1_a3 (h : ℕ) (hm : 3 ≤ 6*h+1) :
    ((efficientOneValue (6*h+1))^[3*h+1]) 3 = 2 := by
  have hs : efficientOneValue (6*h+1) 3 = 6*(3*h-1)+6 := by
    norm_num [efficientOneValue]
    omega
  have ht : 3*h+1 = ((3*h-1)+1) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_six_descent (6*h+1) (3*h-1)

theorem anchor_r1_a4 (h : ℕ) (hm : 3 ≤ 6*h+1) :
    ((efficientOneValue (6*h+1))^[4*h+1]) 4 = 4 := by
  have hs : efficientOneValue (6*h+1) 4 = 9*(2*h)+4 := by
    norm_num [efficientOneValue]
    omega
  have ht : 4*h+1 = (2*(2*h)) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_four_descent (6*h+1) (2*h)

theorem anchor_r1_a5 (h : ℕ) (hm : 3 ≤ 6*h+1) :
    ((efficientOneValue (6*h+1))^[3*h+1]) 5 = 1 := by
  have hs : efficientOneValue (6*h+1) 5 = 6*(3*h-1)+9 := by
    norm_num [efficientOneValue]
    omega
  have ht : 3*h+1 = ((3*h-1)+1) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_nine_descent (6*h+1) (3*h-1)

theorem anchor_r2_a1 (h : ℕ) (hm : 3 ≤ 6*h+2) :
    ((efficientOneValue (6*h+2))^[4*h+1]) 1 = 5 := by
  have hs : efficientOneValue (6*h+2) 1 = 9*(2*h)+5 := by
    norm_num [efficientOneValue]
    omega
  have ht : 4*h+1 = (2*(2*h)) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_five_descent (6*h+2) (2*h)

theorem anchor_r2_a2 (h : ℕ) (hm : 3 ≤ 6*h+2) :
    ((efficientOneValue (6*h+2))^[4*h+1]) 2 = 4 := by
  have hs : efficientOneValue (6*h+2) 2 = 9*(2*h)+4 := by
    norm_num [efficientOneValue]
    omega
  have ht : 4*h+1 = (2*(2*h)) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_four_descent (6*h+2) (2*h)

theorem anchor_r2_a3 (h : ℕ) (hm : 3 ≤ 6*h+2) :
    ((efficientOneValue (6*h+2))^[3*h+1]) 3 = 1 := by
  have hs : efficientOneValue (6*h+2) 3 = 6*(3*h-1)+9 := by
    norm_num [efficientOneValue]
    omega
  have ht : 3*h+1 = ((3*h-1)+1) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_nine_descent (6*h+2) (3*h-1)

theorem anchor_r2_a4 (h : ℕ) (hm : 3 ≤ 6*h+2) :
    ((efficientOneValue (6*h+2))^[4*h+2]) 4 = 3 := by
  have hs : efficientOneValue (6*h+2) 4 = 9*(2*h)+7 := by
    norm_num [efficientOneValue]
    omega
  have ht : 4*h+2 = (2*(2*h)+1) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_seven_descent (6*h+2) (2*h)

theorem anchor_r2_a5 (h : ℕ) (hm : 3 ≤ 6*h+2) :
    ((efficientOneValue (6*h+2))^[3*h+2]) 5 = 2 := by
  have hs : efficientOneValue (6*h+2) 5 = 6*(3*h)+6 := by
    norm_num [efficientOneValue]
    omega
  have ht : 3*h+2 = ((3*h)+1) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_six_descent (6*h+2) (3*h)

theorem anchor_r3_a1 (h : ℕ) (hm : 3 ≤ 6*h+3) :
    ((efficientOneValue (6*h+3))^[4*h+2]) 1 = 4 := by
  have hs : efficientOneValue (6*h+3) 1 = 9*(2*h)+8 := by
    norm_num [efficientOneValue]
    omega
  have ht : 4*h+2 = (2*(2*h)+1) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_eight_descent (6*h+3) (2*h)

theorem anchor_r3_a2 (h : ℕ) (hm : 3 ≤ 6*h+3) :
    ((efficientOneValue (6*h+3))^[4*h+2]) 2 = 3 := by
  have hs : efficientOneValue (6*h+3) 2 = 9*(2*h)+7 := by
    norm_num [efficientOneValue]
    omega
  have ht : 4*h+2 = (2*(2*h)+1) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_seven_descent (6*h+3) (2*h)

theorem anchor_r3_a3 (h : ℕ) (hm : 3 ≤ 6*h+3) :
    ((efficientOneValue (6*h+3))^[3*h+2]) 3 = 2 := by
  have hs : efficientOneValue (6*h+3) 3 = 6*(3*h)+6 := by
    norm_num [efficientOneValue]
    omega
  have ht : 3*h+2 = ((3*h)+1) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_six_descent (6*h+3) (3*h)

theorem anchor_r3_a4 (h : ℕ) (hm : 3 ≤ 6*h+3) :
    ((efficientOneValue (6*h+3))^[4*h+2]) 4 = 5 := by
  have hs : efficientOneValue (6*h+3) 4 = 9*(2*h)+10 := by
    norm_num [efficientOneValue]
    omega
  have ht : 4*h+2 = (2*(2*h)+1) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_ten_descent (6*h+3) (2*h)

theorem anchor_r3_a5 (h : ℕ) (hm : 3 ≤ 6*h+3) :
    ((efficientOneValue (6*h+3))^[3*h+2]) 5 = 1 := by
  have hs : efficientOneValue (6*h+3) 5 = 6*(3*h)+9 := by
    norm_num [efficientOneValue]
    omega
  have ht : 3*h+2 = ((3*h)+1) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_nine_descent (6*h+3) (3*h)

theorem anchor_r4_a1 (h : ℕ) (hm : 3 ≤ 6*h+4) :
    ((efficientOneValue (6*h+4))^[4*h+3]) 1 = 3 := by
  have hs : efficientOneValue (6*h+4) 1 = 9*(2*h)+11 := by
    norm_num [efficientOneValue]
    omega
  have ht : 4*h+3 = (2*(2*h)+2) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_eleven_descent (6*h+4) (2*h)

theorem anchor_r4_a2 (h : ℕ) (hm : 3 ≤ 6*h+4) :
    ((efficientOneValue (6*h+4))^[4*h+2]) 2 = 5 := by
  have hs : efficientOneValue (6*h+4) 2 = 9*(2*h)+10 := by
    norm_num [efficientOneValue]
    omega
  have ht : 4*h+2 = (2*(2*h)+1) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_ten_descent (6*h+4) (2*h)

theorem anchor_r4_a3 (h : ℕ) (hm : 3 ≤ 6*h+4) :
    ((efficientOneValue (6*h+4))^[3*h+2]) 3 = 1 := by
  have hs : efficientOneValue (6*h+4) 3 = 6*(3*h)+9 := by
    norm_num [efficientOneValue]
    omega
  have ht : 3*h+2 = ((3*h)+1) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_nine_descent (6*h+4) (3*h)

theorem anchor_r4_a4 (h : ℕ) (hm : 3 ≤ 6*h+4) :
    ((efficientOneValue (6*h+4))^[4*h+3]) 4 = 4 := by
  have hs : efficientOneValue (6*h+4) 4 = 9*(2*h+1)+4 := by
    norm_num [efficientOneValue]
    omega
  have ht : 4*h+3 = (2*(2*h+1)) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_four_descent (6*h+4) (2*h+1)

theorem anchor_r4_a5 (h : ℕ) (hm : 3 ≤ 6*h+4) :
    ((efficientOneValue (6*h+4))^[3*h+3]) 5 = 2 := by
  have hs : efficientOneValue (6*h+4) 5 = 6*(3*h+1)+6 := by
    norm_num [efficientOneValue]
    omega
  have ht : 3*h+3 = ((3*h+1)+1) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_six_descent (6*h+4) (3*h+1)

theorem anchor_r5_a1 (h : ℕ) (hm : 3 ≤ 6*h+5) :
    ((efficientOneValue (6*h+5))^[4*h+3]) 1 = 5 := by
  have hs : efficientOneValue (6*h+5) 1 = 9*(2*h+1)+5 := by
    norm_num [efficientOneValue]
    omega
  have ht : 4*h+3 = (2*(2*h+1)) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_five_descent (6*h+5) (2*h+1)

theorem anchor_r5_a2 (h : ℕ) (hm : 3 ≤ 6*h+5) :
    ((efficientOneValue (6*h+5))^[4*h+3]) 2 = 4 := by
  have hs : efficientOneValue (6*h+5) 2 = 9*(2*h+1)+4 := by
    norm_num [efficientOneValue]
    omega
  have ht : 4*h+3 = (2*(2*h+1)) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_four_descent (6*h+5) (2*h+1)

theorem anchor_r5_a3 (h : ℕ) (hm : 3 ≤ 6*h+5) :
    ((efficientOneValue (6*h+5))^[3*h+3]) 3 = 2 := by
  have hs : efficientOneValue (6*h+5) 3 = 6*(3*h+1)+6 := by
    norm_num [efficientOneValue]
    omega
  have ht : 3*h+3 = ((3*h+1)+1) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_six_descent (6*h+5) (3*h+1)

theorem anchor_r5_a4 (h : ℕ) (hm : 3 ≤ 6*h+5) :
    ((efficientOneValue (6*h+5))^[4*h+4]) 4 = 3 := by
  have hs : efficientOneValue (6*h+5) 4 = 9*(2*h+1)+7 := by
    norm_num [efficientOneValue]
    omega
  have ht : 4*h+4 = (2*(2*h+1)+1) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_seven_descent (6*h+5) (2*h+1)

theorem anchor_r5_a5 (h : ℕ) (hm : 3 ≤ 6*h+5) :
    ((efficientOneValue (6*h+5))^[3*h+3]) 5 = 1 := by
  have hs : efficientOneValue (6*h+5) 5 = 6*(3*h+1)+9 := by
    norm_num [efficientOneValue]
    omega
  have ht : 3*h+3 = ((3*h+1)+1) + 1 := by omega
  rw [ht, Function.iterate_succ_apply, hs]
  exact efficientOne_nine_descent (6*h+5) (3*h+1)

end SuperpermutationLowerBound.Refinement.ChainReturns
