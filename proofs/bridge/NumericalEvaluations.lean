module

public import bridge.ParameterGates

@[expose] public section

/-! Exact evaluations of the frozen formula. These are arithmetic identities,
not independent word bounds; use `word_bound_of_actualPacking` and discharge
its actual-segment geometric premise to obtain the latter. -/
namespace SuperpermutationLowerBound.ChainReturns

theorem bound_8 : bound 8 10 (46 / 3) = 46130 := by
  have hceil : ⌈((94024 : ℚ) / 123)⌉₊ = 765 := by
    apply (Nat.ceil_eq_iff (by norm_num)).2
    norm_num
  norm_num [bound, lam, intercept, Nat.factorial, hceil]

theorem bound_9 : bound 9 15 (287 / 12) = 408469 := by
  have hceil : ⌈((34229311 : ℚ) / 6505)⌉₊ = 5263 := by
    apply (Nat.ceil_eq_iff (by norm_num)).2
    norm_num
  norm_num [bound, lam, intercept, Nat.factorial, hceil]

theorem bound_10 : bound 10 (521 / 80) (359 / 40) = 4033374 := by
  have hceil : ⌈((882880254 : ℚ) / 21179)⌉₊ = 41687 := by
    apply (Nat.ceil_eq_iff (by norm_num)).2
    norm_num
  norm_num [bound, lam, intercept, Nat.factorial, hceil]

theorem bound_11 : bound 11 21 (263 / 12) = 43917903 := by
  have hceil : ⌈((1257983043 : ℚ) / 3379)⌉₊ = 372295 := by
    apply (Nat.ceil_eq_iff (by norm_num)).2
    norm_num
  norm_num [bound, lam, intercept, Nat.factorial, hceil]

theorem bound_12 : bound 12 28 (195 / 4) = 522622380 := by
  have hceil : ⌈((69734645252 : ℚ) / 18827)⌉₊ = 3703971 := by
    apply (Nat.ceil_eq_iff (by norm_num)).2
    norm_num
  norm_num [bound, lam, intercept, Nat.factorial, hceil]

theorem bound_13 : bound 13 (1191 / 140) (909 / 70) = 6746626531 := by
  have hceil : ⌈((714510716270 : ℚ) / 17597)⌉₊ = 40604121 := by
    apply (Nat.ceil_eq_iff (by norm_num)).2
    norm_num
  norm_num [bound, lam, intercept, Nat.factorial, hceil]

theorem bound_14 : bound 14 36 (569 / 15) = 93891141149 := by
  have hceil : ⌈((12929370849128 : ℚ) / 26613)⌉₊ = 485829138 := by
    apply (Nat.ceil_eq_iff (by norm_num)).2
    norm_num
  norm_num [bound, lam, intercept, Nat.factorial, hceil]

end SuperpermutationLowerBound.ChainReturns
