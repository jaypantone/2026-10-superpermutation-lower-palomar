module

public import pairs.TwoClassification
public import pairs.PaidOne

@[expose] public section

namespace ChainReturns

def TwoSuccessors (m : ℕ) (xs : List ℕ) : Prop :=
  ∀ before after : List ℕ, ∀ x y : ℕ,
    xs = before ++ x :: y :: after → twoThreshold m < x →
      y ≤ twoThreshold m - 1 ∧
        (after ≠ [] → twoThreshold m + 2 ≤ x → y ≤ twoThreshold m - 2)

theorem TwoSuccessors.suffix {m : ℕ} {xs before tail : List ℕ}
    (h : TwoSuccessors m xs) (he : xs = before ++ tail) : TwoSuccessors m tail := by
  intro pre post x y htail hx
  apply h (before ++ pre) post x y _ hx
  simp [he, htail, List.append_assoc]

theorem greedy_two_valid (m : ℕ) (xs : List ℕ)
    (hbound : ∀ x ∈ xs, x ≤ twoMax m) (hsucc : TwoSuccessors m xs) :
    ValidChunks (TwoInterior m) (TwoFinal m) (greedyChunks (twoThreshold m) xs) := by
  induction xs using List.twoStepInduction with
  | nil => trivial
  | singleton x => exact hbound x (by simp)
  | cons_cons x y xs ihAfter ihCons =>
      by_cases hx : x ≤ twoThreshold m
      · simp only [greedyChunks, if_pos hx]
        apply ValidChunks.cons (greedyChunks_ne_nil _ (by simp)) hx
        apply ihCons y
        · intro z hz
          exact hbound z (by simp [hz])
        · exact hsucc.suffix (before := [x]) (by simp)
      · have hx' : twoThreshold m < x := by omega
        have hs := hsucc [] xs x y (by simp) hx'
        simp only [greedyChunks, if_neg hx]
        by_cases hxs : xs = []
        · subst xs
          exact ⟨hbound x (by simp), hs.1⟩
        · apply ValidChunks.cons (greedyChunks_ne_nil _ hxs)
          · exact ⟨hbound x (by simp), hx', hs.1, hs.2 hxs⟩
          · apply ihAfter
            · intro z hz
              exact hbound z (by simp [hz])
            · exact hsucc.suffix (before := [x, y]) (by simp)

end ChainReturns

namespace SuperpermutationLowerBound.Refinement

open ChainReturns

theorem twoSuccessors_of_avoidance {a m : ℕ} (hm : 2 ≤ m) {ls d : List ℕ}
    (H : RealizesChains a ls d) (hpos : ∀ x ∈ ls, 1 ≤ x)
    (havoid : ResidueTwoAvoidance a (twoThreshold m) d) : TwoSuccessors m ls := by
  intro pre after x y he hx
  have hv : 2 ≤ twoThreshold m := by dsimp [twoThreshold]; nlinarith
  have hy : y < twoThreshold m := by
    by_contra hbad
    have he' : ls = pre ++ (x :: ([] ++ [y])) ++ after := by simpa using he
    exact havoid.pair (H _ (chainWindow_factor_of_list he' (by omega) (by omega)))
  refine ⟨by omega, ?_⟩
  intro hafter hxstrong
  by_contra hbad
  have hy' : y = twoThreshold m - 1 := by omega
  cases after with
  | nil => contradiction
  | cons z zs =>
      have hz := hpos z (by simp [he])
      have he' : ls = pre ++ (x :: ([twoThreshold m - 1] ++ [z])) ++ zs := by
        simpa [hy'] using he
      exact havoid.triple (H _ (chainWindow_factor_of_list he' (by omega) hz))

end SuperpermutationLowerBound.Refinement
