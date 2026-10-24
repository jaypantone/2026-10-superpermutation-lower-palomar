module

public import SuperpermutationLowerBound.Refinement.ChainPatterns
public import SuperpermutationLowerBound.Refinement.ChainPackingPairing
public import SuperpermutationLowerBound.Refinement.ChainPackingUniversal

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

/-- The geometric return traps used at every residue. Bounding zeros are
retained, so no continuation is asserted at a nonexistent endpoint. -/
structure BasicCellAvoidance (a p : ℕ) (d : List ℕ) : Prop where
  pure : ¬CellFactor a (List.replicate p false) d
  right : ¬CellFactor a (chainWindow 0 (p-1) []) d
  left : ¬CellFactor a (chainWindow (p-1) 0 []) d

structure ResidueOneAvoidance (a m : ℕ) (d : List ℕ) : Prop where
  pair : ¬CellFactor a (chainWindow m m []) d
  triple : ¬CellFactor a (chainWindow m 0 [m]) d

structure ResidueTwoAvoidance (a v : ℕ) (d : List ℕ) : Prop where
  pair : ¬CellFactor a (chainWindow v (v-1) []) d
  triple : ¬CellFactor a (chainWindow (v+1) 0 [v-1]) d

def UniversalAvoidance (a p : ℕ) (d : List ℕ) : Prop :=
  ¬CellFactor a (chainWindow 1 1 [p-1,p-1]) d

def RealizesChains (a : ℕ) (ls d : List ℕ) : Prop :=
  ∀ pattern, MarkFactor pattern (chainCells ls) → CellFactor a pattern d

theorem realizes_chainLengths {a : ℕ} (ha : 3 ≤ a)
    {gaps before after d : List ℕ}
    (hg : ∀ g ∈ gaps, g = a-1 ∨ g = a-2)
    (hd : d = before ++ (0 :: (regularPath gaps ++ [0])) ++ after) :
    RealizesChains a (chainLengths a gaps) d := by
  intro pattern hp
  exact chain_factor_realization ha hg hd hp

theorem chain_bound_of_pure {a p : ℕ} {ls d : List ℕ}
    (H : RealizesChains a ls d) (hpure : ¬CellFactor a (List.replicate p false) d) :
    ∀ x ∈ ls, x ≤ p := by
  intro x hx
  by_contra hb
  obtain ⟨pre, post, he⟩ := List.mem_iff_append.mp hx
  apply hpure
  exact H _ (full_mark_factor_of_list he (by omega))

theorem chain_pair_bounds {a p : ℕ} (hp : 1 ≤ p) {ls d : List ℕ}
    (H : RealizesChains a ls d) (hpos : ∀ x ∈ ls, 1 ≤ x)
    (hbasic : BasicCellAvoidance a p d)
    {pre post : List ℕ} {x y : ℕ} (he : ls = pre ++ x :: y :: post) :
    x ≤ p-1 ∧ y ≤ p-1 := by
  have hx : 1 ≤ x := hpos x (by simp [he])
  have hy : 1 ≤ y := hpos y (by simp [he])
  have he' : ls = pre ++ (x :: ([] ++ [y])) ++ post := by simpa using he
  constructor
  · by_contra hb
    exact hbasic.left (H _ (chainWindow_factor_of_list he' (by omega) hy))
  · by_contra hb
    exact hbasic.right (H _ (chainWindow_factor_of_list he' hx (by omega)))

theorem all_bounds_from_pairs (b : ℕ) (ls : List ℕ) (hlen : 2 ≤ ls.length)
    (H : ∀ pre post x y, ls = pre ++ x :: y :: post → x ≤ b ∧ y ≤ b) :
    ∀ x ∈ ls, x ≤ b := by
  induction ls with
  | nil => simp at hlen
  | cons x xs ih =>
    cases xs with
    | nil => simp at hlen
    | cons y ys =>
      have hxy := H [] ys x y (by simp)
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hxy.1
      · by_cases hy : ys = []
        · have hzy : z = y := by simpa [hy] using hz
          simpa [hzy] using hxy.2
        · apply ih (by simp; exact List.length_pos_iff.mpr hy) _ z hz
          intro pre post u v he
          apply H (x :: pre) post u v
          simp [he]

theorem chain_bound_of_basic {a p : ℕ} (hp : 1 ≤ p) {ls d : List ℕ}
    (H : RealizesChains a ls d) (hpos : ∀ x ∈ ls, 1 ≤ x)
    (hbasic : BasicCellAvoidance a p d) (hlen : 2 ≤ ls.length) :
    ∀ x ∈ ls, x ≤ p-1 := by
  apply all_bounds_from_pairs (p-1) ls hlen
  intro pre post x y he
  exact chain_pair_bounds hp H hpos hbasic he

theorem residueOne_terminal_pair {a b m : ℕ} {ls d : List ℕ}
    (H : RealizesChains a ls d) (hpos : ∀ x ∈ ls, 1 ≤ x)
    (hbound : ∀ x ∈ ls, x ≤ b) (havoid : ResidueOneAvoidance a m d) :
    TerminalPairBound m ((b : ℚ) + m - 1) ls := by
  intro pre after x y he hx
  have hxb : (x : ℚ) ≤ b := by exact_mod_cast hbound x (by simp [he])
  have hym : y ≤ m := by
    by_contra hbad
    have he' : ls = pre ++ (x :: ([] ++ [y])) ++ after := by simpa using he
    exact havoid.pair (H _ (chainWindow_factor_of_list he' (by omega) (by omega)))
  by_cases hafter : after = []
  · have hyq : (y : ℚ) ≤ m := by exact_mod_cast hym
    simp only [if_pos hafter]
    linarith
  · have hylt : y < m := by
      by_contra hbad
      have hy : y = m := by omega
      cases after with
      | nil => contradiction
      | cons z zs =>
        have hz := hpos z (by simp [he])
        have he' : ls = pre ++ (x :: ([m] ++ [z])) ++ zs := by simpa [hy] using he
        exact havoid.triple (H _ (chainWindow_factor_of_list he' (by omega) hz))
    have hyq : (y : ℚ) + 1 ≤ m := by exact_mod_cast hylt
    simp only [if_neg hafter]
    linarith

theorem residueTwo_terminal_pair {a b v : ℕ} (hv : 1 ≤ v) (hbv : v+2 ≤ b)
    {ls d : List ℕ} (H : RealizesChains a ls d) (hpos : ∀ x ∈ ls, 1 ≤ x)
    (hbound : ∀ x ∈ ls, x ≤ b) (havoid : ResidueTwoAvoidance a v d) :
    TerminalPairBound v ((b : ℚ) + v - 2) ls := by
  intro pre after x y he hx
  have hxb : (x : ℚ) ≤ b := by exact_mod_cast hbound x (by simp [he])
  have hyv : y < v := by
    by_contra hbad
    have he' : ls = pre ++ (x :: ([] ++ [y])) ++ after := by simpa using he
    exact havoid.pair (H _ (chainWindow_factor_of_list he' (by omega) (by omega)))
  have hyq : (y : ℚ) + 1 ≤ v := by exact_mod_cast hyv
  by_cases hafter : after = []
  · simp only [if_pos hafter]
    linarith
  · simp only [if_neg hafter]
    by_cases hxsmall : x ≤ v+1
    · have hxq : (x : ℚ) ≤ v+1 := by exact_mod_cast hxsmall
      have hbq : (v : ℚ)+2 ≤ b := by exact_mod_cast hbv
      linarith
    · have hystrict : y+2 ≤ v := by
        by_contra hbad
        have hy : y = v-1 := by omega
        cases after with
        | nil => contradiction
        | cons z zs =>
          have hz := hpos z (by simp [he])
          have he' : ls = pre ++ (x :: ([v-1] ++ [z])) ++ zs := by simpa [hy] using he
          exact havoid.triple (H _ (chainWindow_factor_of_list he' (by omega) hz))
      have hyq' : (y : ℚ)+2 ≤ v := by exact_mod_cast hystrict
      linarith

theorem fourChainTrap_of_universal {a p : ℕ} {ls d : List ℕ}
    (H : RealizesChains a ls d) (havoid : UniversalAvoidance a p d) :
    FourChainTrap (p-1) ls := by
  intro pre after x y z w he hx hw hmiddle
  obtain ⟨rfl, rfl⟩ := hmiddle
  have he' : ls = pre ++ (x :: ([p-1,p-1] ++ [w])) ++ after := by simpa using he
  exact havoid (H _ (chainWindow_factor_of_list he' hx hw))

end SuperpermutationLowerBound.Refinement
