module

public import SuperpermutationLowerBound.Refinement.ChainTrapEncoding
public import SuperpermutationLowerBound.Refinement.Parameters

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

/-- The complete finite list of symbolic geometric exclusions. Each premise
concerns actual zero-bounded factors, and the residue-specific premises apply
only in their declared residue. -/
structure ReturnAvoidance (n : ℕ) (d : List ℕ) : Prop where
  basic : BasicCellAvoidance (n-2) (period n) d
  residueZero : n % 3 = 0 → UniversalAvoidance (n-2) (period n) d
  residueOne : n % 3 = 1 → ResidueOneAvoidance (n-2) (n/3) d
  residueTwo : n % 3 = 2 → ResidueTwoAvoidance (n-2) (2*(n/3)*(n/3+1)) d

theorem chain_sum_of_returnAvoidance {n : ℕ} (hn : 7 ≤ n) {ls d : List ℕ}
    (H : ReturnAvoidance n d) (hr : RealizesChains (n-2) ls d)
    (hne : ls ≠ []) (hpos : ∀ x ∈ ls, 1 ≤ x) :
    2 * (ls.sum : ℚ) ≤ 2 * (period n : ℚ) +
      chainAllowance n * ((ls.length : ℚ) - 1) := by
  have hp := period_ge_two hn
  have hbound := chain_bound_of_pure hr H.basic.pure
  by_cases hlen : 2 ≤ ls.length
  · have hb := chain_bound_of_basic (by omega : 1 ≤ period n) hr hpos H.basic hlen
    have hpcast : ((period n-1 : ℕ) : ℚ) = (period n : ℚ)-1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ period n), Nat.cast_one]
    have hm : 2 ≤ n/3 := by omega
    have hmq : (2 : ℚ) ≤ (n/3 : ℕ) := by exact_mod_cast hm
    have hmod := Nat.mod_lt n (by omega : 0 < 3)
    have hboundQ : ∀ x ∈ ls, (x : ℚ) ≤ period n := by
      intro x hx
      exact_mod_cast hbound x hx
    by_cases h0 : n%3 = 0
    · have hm3 : 3 ≤ n/3 := by omega
      have hp0 : period n = 2*(n/3) := by simp [period, h0]
      have hb3 : 3 ≤ period n-1 := by omega
      have hsum := chainLengths_universal hb3 ls hlen
        (fun x hx => ⟨hpos x hx, hb x hx⟩)
        (fourChainTrap_of_universal hr (H.residueZero h0))
      simpa [hpcast, chainAllowance, h0] using hsum
    · by_cases h1 : n%3 = 1
      · have hp1 : period n = (n/3)*(2*(n/3)+1) := by simp [period, h0, h1]
        have ht : ((period n-1 : ℕ) : ℚ) + (n/3 : ℕ) - 1 = chainAllowance n := by
          simp only [hpcast, chainAllowance, if_neg h0, if_pos h1]
          ring
        have hpair := residueOne_terminal_pair hr hpos hb (H.residueOne h1)
        rw [ht] at hpair
        apply chainLengths_pairing (r := n/3) _ _ ls hne hboundQ hpair
        · simp only [chainAllowance, if_neg h0, if_pos h1, hp1]
          push_cast
          nlinarith
        · simp only [chainAllowance, if_neg h0, if_pos h1, hp1]
          push_cast
          nlinarith
      · have h2 : n%3 = 2 := by omega
        let v := 2*(n/3)*(n/3+1)
        have hp2 : period n = (n/3+1)*(2*(n/3)+1) := by simp [period, h0, h1]
        have hpv : period n = v + n/3 + 1 := by rw [hp2]; dsimp [v]; ring
        have hv : 1 ≤ v := by dsimp [v]; nlinarith
        have hbv : v+2 ≤ period n-1 := by omega
        have hpvq : (period n : ℚ) = (v : ℚ) + (n/3 : ℕ) + 1 := by exact_mod_cast hpv
        have ht : ((period n-1 : ℕ) : ℚ) + (v : ℚ) - 2 = chainAllowance n := by
          simp only [hpcast, chainAllowance, if_neg h0, if_neg h1]
          linarith
        have hpair := residueTwo_terminal_pair hv hbv hr hpos hb (H.residueTwo h2)
        rw [ht] at hpair
        apply chainLengths_pairing (r := v) _ _ ls hne hboundQ hpair
        · simp only [chainAllowance, if_neg h0, if_neg h1]
          linarith
        · simp only [chainAllowance, if_neg h0, if_neg h1]
          linarith
  · have hl : ls.length = 1 := by
      have hposlen := List.length_pos_iff.mpr hne
      omega
    obtain ⟨x, he⟩ := List.length_eq_one_iff.mp hl
    have hx : (x : ℚ) ≤ period n := by exact_mod_cast hbound x (by simp [he])
    simp only [he, List.sum_singleton, List.length_singleton, Nat.cast_one,
      sub_self, mul_zero, add_zero]
    linarith

/-- Geometry enters the scalar argument only through this hereditary packing
statement; the exact number of shortened links is retained. -/
theorem chainPacking_of_returnAvoidance {n : ℕ} (hn : 7 ≤ n) {d : List ℕ}
    (H : ReturnAvoidance n d) :
    ChainPacking (n-2) (period n) (chainAllowance n) d := by
  intro gaps hg before after hd
  have hreal := realizes_chainLengths (by omega : 3 ≤ n-2) hg hd
  have hsum := chain_sum_of_returnAvoidance hn H hreal
    (chainLengthsFrom_nonempty (n-2) 1 gaps) (chainLengths_positive (n-2) gaps)
  rw [chainLengths_sum, chainLengths_length] at hsum
  push_cast at hsum
  linarith

end SuperpermutationLowerBound.Refinement
