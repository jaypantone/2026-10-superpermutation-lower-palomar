module

public import FrozenStatement
public import Mathlib.Tactic

@[expose] public section

/-! Positivity of the literal return-order definitions. No geometric return
assertion is needed or claimed in this arithmetic module. -/
namespace SuperpermutationBounds.ChainReturns

private theorem find_some_of_exists (p : ℕ → Bool) (xs : List ℕ)
    (h : ∃ x ∈ xs, p x = true) :
    ∃ x, xs.find? p = some x ∧ x ∈ xs ∧ p x = true := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      by_cases hx : p x = true
      · exact ⟨x, by simp [List.find?, hx], by simp, hx⟩
      · obtain ⟨y, hy, hpy⟩ := h
        have hyxs : y ∈ xs := by
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact False.elim (hx hpy)
          · exact hy
        obtain ⟨z, hz, hzm, hzp⟩ := ih ⟨y, hyxs, hpy⟩
        exact ⟨z, by simpa [List.find?, hx] using hz, by simp [hzm], hzp⟩

/-- An inverse exists, with its standard representative, whenever n>1 and
seven does not divide n. The six choices only witness existence; the frozen
return order continues to use the literal finite search. -/
theorem exists_inverse_seven {n : ℕ} (hn : 2 ≤ n) (hmod : n % 7 ≠ 0) :
    ∃ u : ℕ, u < n ∧ (7 * u) % n = 1 := by
  have hres : n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨
      n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by omega
  rcases hres with hr | hr | hr | hr | hr | hr
  · refine ⟨(6 * n + 1) / 7, by omega, ?_⟩
    have he : 7 * ((6 * n + 1) / 7) = 6 * n + 1 := by omega
    rw [he]
    simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < n)]
  · refine ⟨(3 * n + 1) / 7, by omega, ?_⟩
    have he : 7 * ((3 * n + 1) / 7) = 3 * n + 1 := by omega
    rw [he]
    simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < n)]
  · refine ⟨(2 * n + 1) / 7, by omega, ?_⟩
    have he : 7 * ((2 * n + 1) / 7) = 2 * n + 1 := by omega
    rw [he]
    simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < n)]
  · refine ⟨(5 * n + 1) / 7, by omega, ?_⟩
    have he : 7 * ((5 * n + 1) / 7) = 5 * n + 1 := by omega
    rw [he]
    simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < n)]
  · refine ⟨(4 * n + 1) / 7, by omega, ?_⟩
    have he : 7 * ((4 * n + 1) / 7) = 4 * n + 1 := by omega
    rw [he]
    simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < n)]
  · refine ⟨(n + 1) / 7, by omega, ?_⟩
    have he : 7 * ((n + 1) / 7) = n + 1 := by omega
    rw [he]
    simp [Nat.mod_eq_of_lt (by omega : 1 < n)]

theorem inverseSeven_spec {n : ℕ} (hn : 2 ≤ n) (hmod : n % 7 ≠ 0) :
    0 < inverseSeven n ∧ inverseSeven n < n ∧ (7 * inverseSeven n) % n = 1 := by
  obtain ⟨u, hun, hu⟩ := exists_inverse_seven hn hmod
  have hex : ∃ x ∈ List.range n, ((7 * x) % n == 1) = true := by
    exact ⟨u, List.mem_range.mpr hun, by simp [hu]⟩
  obtain ⟨v, hv, hvm, hvp⟩ := find_some_of_exists
    (fun x => (7 * x) % n == 1) (List.range n) hex
  have hveq : (7 * v) % n = 1 := by simpa using hvp
  have hvpos : 0 < v := by
    by_contra hz
    have hvzero : v = 0 := by omega
    simp [hvzero] at hveq
  have hvn : v < n := List.mem_range.mp hvm
  simpa [inverseSeven, hv] using And.intro hvpos (And.intro hvn hveq)

theorem returnZero_pos {n : ℕ} (hn : 2 ≤ n) : 0 < returnZero n := by
  unfold returnZero
  split_ifs with hmod
  · have hn7 : 7 ≤ n := by omega
    omega
  · obtain ⟨hu, hun, _⟩ := inverseSeven_spec hn hmod
    exact Nat.mul_pos hu (Nat.sub_pos_of_lt hun)

theorem returnOne_pos {m : ℕ} (hm : 3 ≤ m) : 0 < returnOne m := by
  unfold returnOne
  split <;> try omega
  all_goals exact Nat.lcm_pos (by omega) (by omega)

/-- The representative found by the finite search is the unique inverse in
`0,...,n-1`; this connects explicit arithmetic orbit lengths to the definition. -/
theorem inverseSeven_eq_of_spec {n u : ℕ} (hn : 2 ≤ n) (hmod : n % 7 ≠ 0)
    (hun : u < n) (hu : (7 * u) % n = 1) : inverseSeven n = u := by
  obtain ⟨_, hvn, hv⟩ := inverseSeven_spec hn hmod
  have h1 : ((7 * inverseSeven n) * u) % n = u % n := by
    simp [Nat.mul_mod, hv]
  have h2 : ((7 * u) * inverseSeven n) % n = inverseSeven n % n := by
    simp [Nat.mul_mod, hu]
  calc
    inverseSeven n = inverseSeven n % n := (Nat.mod_eq_of_lt hvn).symm
    _ = ((7 * u) * inverseSeven n) % n := h2.symm
    _ = ((7 * inverseSeven n) * u) % n := by congr 1; ring
    _ = u % n := h1
    _ = u := Nat.mod_eq_of_lt hun

/-- The quadratic bound used by the alternative frozen parameter table. -/
theorem returnZero_quadratic {n : ℕ} (hn : 2 ≤ n) :
    4 * returnZero n ≤ n^2 := by
  unfold returnZero
  split_ifs with hmod
  · have hn7 : 7 ≤ n := by omega
    have he : 7 * (2 * n / 7) = 2 * n := by omega
    nlinarith
  · obtain ⟨_, hun, _⟩ := inverseSeven_spec hn hmod
    have hsum : inverseSeven n + (n - inverseSeven n) = n := by omega
    have hsumQ : (inverseSeven n : ℚ) + (n - inverseSeven n : ℕ) = n := by
      exact_mod_cast hsum
    have hs := sq_nonneg ((inverseSeven n : ℚ) - (n - inverseSeven n : ℕ))
    have hq : 4 * (inverseSeven n : ℚ) * (n - inverseSeven n : ℕ) ≤ (n : ℚ)^2 := by
      nlinarith
    have hnat : 4 * inverseSeven n * (n - inverseSeven n) ≤ n^2 := by
      exact_mod_cast hq
    simpa [Nat.mul_assoc] using hnat

private theorem lcm_quadratic_of_sum {a b N : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hsum : a+b ≤ N) : 4 * Nat.lcm a b ≤ N^2 := by
  have hl : (Nat.lcm a b : ℚ) ≤ (a : ℚ)*b := by
    exact_mod_cast Nat.lcm_le_mul ha hb
  have hsumQ : (a : ℚ) + b ≤ N := by exact_mod_cast hsum
  have hs := sq_nonneg ((a : ℚ) - b)
  have hp := mul_nonneg (sub_nonneg.mpr hsumQ)
    (show (0 : ℚ) ≤ (N : ℚ) + a + b by positivity)
  have hq : 4 * (Nat.lcm a b : ℚ) ≤ (N : ℚ)^2 := by nlinarith
  exact_mod_cast hq

/-- The efficient-pair return exponent satisfies the advertised quadratic
upper bound in every residue class modulo six. -/
theorem returnOne_quadratic {m : ℕ} (hm : 3 ≤ m) :
    4 * returnOne m ≤ (3*m+1)^2 := by
  unfold returnOne
  split <;> try nlinarith
  all_goals exact lcm_quadratic_of_sum (by omega) (by omega) (by omega)

end SuperpermutationBounds.ChainReturns
