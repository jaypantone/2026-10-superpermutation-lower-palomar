module

public import Mathlib.Tactic

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

/-- A large chain and its successor cost at most `t`; only a pair at the
right endpoint may cost one additional unit. Quantification uses literal
factors so every suffix inherits the condition. -/
def TerminalPairBound (r : ℕ) (t : ℚ) (ls : List ℕ) : Prop :=
  ∀ before after : List ℕ, ∀ x y : ℕ,
    ls = before ++ x :: y :: after → r < x →
      (x : ℚ) + y ≤ t + if after = [] then 1 else 0

theorem TerminalPairBound.suffix {r : ℕ} {t : ℚ} {ls before suffix : List ℕ}
    (h : TerminalPairBound r t ls) (heq : ls = before ++ suffix) :
    TerminalPairBound r t suffix := by
  intro pre after x y hs hx
  apply h (before ++ pre) after x y
  · simp [heq, hs, List.append_assoc]
  · exact hx

/-- Greedy pairing with the terminal exception retained. Entries need only
be nonnegative; positivity is supplied by the chain interpretation. -/
theorem chainLengths_pairing {r : ℕ} {p t : ℚ}
    (hsmall : 2 * (r : ℚ) ≤ t) (hend : t + 2 ≤ 2 * p)
    (ls : List ℕ) (hne : ls ≠ [])
    (hbound : ∀ x ∈ ls, (x : ℚ) ≤ p)
    (hpair : TerminalPairBound r t ls) :
    2 * (ls.sum : ℚ) ≤ 2 * p + t * ((ls.length : ℚ) - 1) := by
  induction ls using List.twoStepInduction with
  | nil => contradiction
  | singleton x =>
      have hx := hbound x (by simp)
      simp only [List.sum_singleton, List.length_singleton, Nat.cast_one, sub_self,
        mul_zero, add_zero]
      linarith
  | cons_cons x y after ihAfter ihCons =>
      by_cases hx : x ≤ r
      · have hxs : ∀ z ∈ y :: after, (z : ℚ) ≤ p := by
          intro z hz; exact hbound z (List.mem_cons_of_mem x hz)
        have hps := hpair.suffix (before := [x]) (suffix := y :: after) (by simp)
        have hi := ihCons y (by simp) hxs hps
        have hxQ : (x : ℚ) ≤ r := by exact_mod_cast hx
        simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one] at *
        nlinarith
      · have hx' : r < x := by omega
        have hpay := hpair [] after x y (by simp) hx'
        by_cases hafter : after = []
        · subst after
          simp at hpay
          simp only [List.sum_cons, List.sum_nil, Nat.add_zero, List.length_cons,
            List.length_nil, Nat.cast_add, Nat.cast_one, Nat.cast_zero]
          nlinarith
        · have hxs : ∀ z ∈ after, (z : ℚ) ≤ p := by
            intro z hz; exact hbound z (by simp [hz])
          have hps := hpair.suffix (before := [x, y]) (suffix := after) (by simp)
          have hi := ihAfter hafter hxs hps
          simp [hafter] at hpay
          simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one] at *
          nlinarith

end SuperpermutationLowerBound.Refinement
