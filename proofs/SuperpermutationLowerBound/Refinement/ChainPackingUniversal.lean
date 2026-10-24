module

public import SuperpermutationLowerBound.Refinement.ChainPacking

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

set_option linter.unusedSimpArgs false

/-- The forbidden four-chain pattern, on literal contiguous factors. -/
def FourChainTrap (b : ℕ) (ls : List ℕ) : Prop :=
  ∀ before after : List ℕ, ∀ x y z w : ℕ,
    ls = before ++ x :: y :: z :: w :: after →
      2 ≤ x → 2 ≤ w → ¬ (y = b ∧ z = b)

def singletonIndicator (x : ℕ) : ℕ := if x = 1 then 1 else 0
def nonmaxIndicator (b x : ℕ) : ℕ := if x = b then 0 else 1

theorem indicator_le_deficit {b x : ℕ} (hb : 3 ≤ b) (hx : 1 ≤ x) (hxb : x ≤ b) :
    singletonIndicator x + nonmaxIndicator b x ≤ b - x := by
  unfold singletonIndicator nonmaxIndicator
  split_ifs <;> omega

theorem four_chain_indicator {b x y z w : ℕ} (hx : 1 ≤ x) (hw : 1 ≤ w)
    (htrap : 2 ≤ x → 2 ≤ w → ¬ (y = b ∧ z = b)) :
    1 ≤ singletonIndicator x + nonmaxIndicator b y + nonmaxIndicator b z + singletonIndicator w := by
  by_cases hx1 : x = 1
  · simp [singletonIndicator, hx1]
    omega
  by_cases hw1 : w = 1
  · simp [singletonIndicator, hw1]
  have hnot := htrap (by omega) (by omega)
  unfold singletonIndicator nonmaxIndicator
  split_ifs <;> (first | contradiction | omega)

theorem nat_sum_range_shift_le (f : ℕ → ℕ) (L off q : ℕ) (hbound : off + q ≤ L) :
    (∑ i ∈ Finset.range q, f (off + i)) ≤ ∑ i ∈ Finset.range L, f i := by
  have hfirst := Finset.sum_range_add f off q
  have hlast := Finset.sum_range_add f (off + q) (L - (off + q))
  rw [Nat.add_sub_of_le hbound] at hlast
  omega

theorem sum_range_deficitAt (f : ℕ → ℕ) (ls : List ℕ) :
    (∑ i ∈ Finset.range ls.length, f (deficitAt ls i)) = (ls.map f).sum := by
  induction ls with
  | nil => simp
  | cons x xs ih =>
      simp only [List.length_cons, Finset.sum_range_succ', deficitAt,
        List.getElem?_cons_zero, Option.getD_some, List.getElem?_cons_succ,
        List.map_cons, List.sum_cons] at *
      omega

theorem deficitAt_mem (ls : List ℕ) (i : ℕ) (hi : i < ls.length) : deficitAt ls i ∈ ls := by
  rw [deficitAt_eq_get ls i hi]
  exact List.get_mem _ _

theorem FourChainTrap.at {b : ℕ} {ls : List ℕ} (h : FourChainTrap b ls)
    (i : ℕ) (hi : i + 3 < ls.length) :
    2 ≤ deficitAt ls i → 2 ≤ deficitAt ls (i + 3) →
      ¬ (deficitAt ls (i + 1) = b ∧ deficitAt ls (i + 2) = b) := by
  have hdrop : ls.drop i = ls[i]'(by omega) :: ls[i + 1]'(by omega) ::
      ls[i + 2]'(by omega) :: ls[i + 3]'hi :: ls.drop (i + 4) := by
    rw [List.drop_eq_getElem_cons (by omega : i < ls.length),
      List.drop_eq_getElem_cons (by omega : i + 1 < ls.length),
      List.drop_eq_getElem_cons (by omega : i + 2 < ls.length),
      List.drop_eq_getElem_cons hi]
  have hfactor : ls = ls.take i ++ deficitAt ls i :: deficitAt ls (i + 1) ::
      deficitAt ls (i + 2) :: deficitAt ls (i + 3) :: ls.drop (i + 4) := by
    conv_lhs => rw [← List.take_append_drop i ls]
    rw [hdrop]
    simp only [deficitAt, List.getElem?_eq_getElem (show i < ls.length by omega),
      List.getElem?_eq_getElem (show i + 1 < ls.length by omega),
      List.getElem?_eq_getElem (show i + 2 < ls.length by omega),
      List.getElem?_eq_getElem hi, Option.getD_some]
  exact h (ls.take i) (ls.drop (i + 4)) _ _ _ _ hfactor

/-- Summing the four-window obstruction counts each of its four indicator
types at most once per offset. Thus each vertex deficit is charged at most twice. -/
theorem fourChainTrap_deficit_count {b : ℕ} (hb : 3 ≤ b) (ls : List ℕ)
    (hbound : ∀ x ∈ ls, 1 ≤ x ∧ x ≤ b) (htrap : FourChainTrap b ls) :
    ls.length - 3 ≤ 2 * (ls.map (fun x => b - x)).sum := by
  by_cases hlen : 3 ≤ ls.length
  swap
  · rw [show ls.length - 3 = 0 by omega]
    exact Nat.zero_le _
  let q := ls.length - 3
  let one := fun i => singletonIndicator (deficitAt ls i)
  let nonmax := fun i => nonmaxIndicator b (deficitAt ls i)
  have hlocal : ∀ i ∈ Finset.range q,
      1 ≤ one i + nonmax (i + 1) + nonmax (i + 2) + one (i + 3) := by
    intro i hi
    have hir : i + 3 < ls.length := by simp only [Finset.mem_range] at hi; dsimp [q] at hi; omega
    exact four_chain_indicator
      (hbound _ (deficitAt_mem ls i (by omega))).1
      (hbound _ (deficitAt_mem ls (i + 3) hir)).1 (htrap.at i hir)
  have hsum := Finset.sum_le_sum hlocal
  have h0 := nat_sum_range_shift_le one ls.length 0 q (by dsimp [q]; omega)
  have h1 := nat_sum_range_shift_le nonmax ls.length 1 q (by
    dsimp [q]
    by_cases h : 3 ≤ ls.length <;> omega)
  have h2 := nat_sum_range_shift_le nonmax ls.length 2 q (by
    dsimp [q]
    by_cases h : 3 ≤ ls.length <;> omega)
  have h3 := nat_sum_range_shift_le one ls.length 3 q (by
    dsimp [q]
    by_cases h : 3 ≤ ls.length <;> omega)
  have hind : ∀ i ∈ Finset.range ls.length,
      one i + nonmax i ≤ b - deficitAt ls i := by
    intro i hi
    have hbnd := hbound _ (deficitAt_mem ls i (Finset.mem_range.mp hi))
    exact indicator_le_deficit hb hbnd.1 hbnd.2
  have htotal := Finset.sum_le_sum hind
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
    mul_one, Nat.zero_add, Nat.add_comm 1, Nat.add_comm 2, Nat.add_comm 3] at *
  have hz := sum_range_deficitAt (fun x => b - x) ls
  omega

theorem sum_add_chain_deficits (b : ℕ) (ls : List ℕ)
    (hbound : ∀ x ∈ ls, x ≤ b) :
    ls.sum + (ls.map (fun x => b - x)).sum = b * ls.length := by
  induction ls with
  | nil => simp
  | cons x xs ih =>
      have hx := hbound x (by simp)
      have htail := ih (by intro y hy; exact hbound y (by simp [hy]))
      simp only [List.sum_cons, List.map_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

/-- The universal `2p-3` chain allowance, including the precise three-unit
boundary allowance. The geometric nontrivial paths have `b=p-1`. -/
theorem chainLengths_universal {b : ℕ} (hb : 3 ≤ b) (ls : List ℕ)
    (hq : 2 ≤ ls.length) (hbound : ∀ x ∈ ls, 1 ≤ x ∧ x ≤ b)
    (htrap : FourChainTrap b ls) :
    2 * (ls.sum : ℚ) ≤ 2 * ((b : ℚ) + 1) +
      (2 * ((b : ℚ) + 1) - 3) * ((ls.length : ℚ) - 1) := by
  have hdef := fourChainTrap_deficit_count hb ls hbound htrap
  have hmass := sum_add_chain_deficits b ls (by intro x hx; exact (hbound x hx).2)
  have hnat : ls.length ≤ 2 * (ls.map (fun x => b - x)).sum + 3 := by omega
  have hdefQ : (ls.length : ℚ) ≤ 2 * ((ls.map (fun x => b - x)).sum : ℚ) + 3 := by
    exact_mod_cast hnat
  have hmassQ : (ls.sum : ℚ) + (ls.map (fun x => b - x)).sum = (b : ℚ) * ls.length := by
    exact_mod_cast hmass
  nlinarith

end SuperpermutationLowerBound.Refinement
