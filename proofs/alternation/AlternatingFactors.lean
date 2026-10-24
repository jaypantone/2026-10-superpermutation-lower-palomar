module

public import alternation.InteriorLosses
public import pairs.PeriodicReturns
public import SuperpermutationLowerBound.Refinement.ChainTrapEncoding

@[expose] public section

namespace SuperpermutationLowerBound.Refinement.ChainReturns

open SuperpermutationLowerBound.Refinement

def alternatingLengths (x y : ℕ) : ℕ → List ℕ
  | 0 => [x]
  | r + 1 => x :: y :: alternatingLengths x y r

@[simp] theorem alternatingLengths_nonempty (x y r : ℕ) :
    alternatingLengths x y r ≠ [] := by cases r <;> simp [alternatingLengths]

@[simp] theorem alternatingLengths_length (x y r : ℕ) :
    (alternatingLengths x y r).length = 2 * r + 1 := by
  induction r with
  | zero => simp [alternatingLengths]
  | succ r ih => simp [alternatingLengths, ih]; omega

theorem binaryPrefixLength_head_le_one {x : ℕ} {xs : List ℕ}
    (h : 1 ≤ binaryPrefixLength (x :: xs)) : x ≤ 1 := by
  by_contra hx
  simp [binaryPrefixLength, hx] at h

theorem binaryPrefixLength_two_step {x y : ℕ} {xs : List ℕ}
    (h : 2 ≤ binaryPrefixLength (x :: y :: xs)) :
    x ≤ 1 ∧ y ≤ 1 ∧ x ≠ y ∧
      binaryPrefixLength (x :: y :: xs) = 1 + binaryPrefixLength (y :: xs) := by
  have hx := binaryPrefixLength_head_le_one (by omega : 1 ≤ binaryPrefixLength (x :: y :: xs))
  have hy : y ≤ 1 ∧ x ≠ y := by
    by_contra hy
    simp [binaryPrefixLength, hx, hy] at h
  exact ⟨hx, hy.1, hy.2, by simp [binaryPrefixLength, hx, hy.1, hy.2]⟩

theorem binaryPrefixLength_long_factor (r : ℕ) (xs : List ℕ)
    (h : 2 * r + 1 ≤ binaryPrefixLength xs) :
    ∃ x post, x ≤ 1 ∧ xs = alternatingLengths x (1 - x) r ++ post := by
  induction r generalizing xs with
  | zero =>
      cases xs with
      | nil => simp [binaryPrefixLength] at h
      | cons x xs =>
          exact ⟨x, xs, binaryPrefixLength_head_le_one (by simpa using h), by simp [alternatingLengths]⟩
  | succ r ih =>
      cases xs with
      | nil => simp [binaryPrefixLength] at h
      | cons x xs =>
          cases xs with
          | nil => simp [binaryPrefixLength] at h; split_ifs at h <;> omega
          | cons y ys =>
              have ht := binaryPrefixLength_two_step (by omega : 2 ≤ binaryPrefixLength (x :: y :: ys))
              have hrest : 2 ≤ binaryPrefixLength (y :: ys) := by omega
              cases ys with
              | nil => simp [binaryPrefixLength] at hrest; split_ifs at hrest <;> omega
              | cons z zs =>
                  have hu := binaryPrefixLength_two_step hrest
                  have hxz : z = x := by omega
                  have hxy : y = 1 - x := by omega
                  have hrank : 2 * r + 1 ≤ binaryPrefixLength (z :: zs) := by omega
                  obtain ⟨v, post, hv, he⟩ := ih (z :: zs) hrank
                  have hzv : z = v := by
                    cases r <;> simp [alternatingLengths] at he <;> exact he.1
                  refine ⟨x, post, ht.1, ?_⟩
                  rw [show v = x by omega] at he
                  simp only [alternatingLengths, List.cons_append]
                  rw [hxy, he]

theorem binaryPrefixLength_append_ge (xs ys : List ℕ) :
    binaryPrefixLength xs ≤ binaryPrefixLength (xs ++ ys) := by
  induction xs with
  | nil => simp [binaryPrefixLength]
  | cons x xs ih =>
      cases xs with
      | nil =>
          cases ys with
          | nil => simp
          | cons y ys => simp only [binaryPrefixLength, List.singleton_append]; split_ifs <;> omega
      | cons y xs =>
          simp only [List.cons_append, binaryPrefixLength]
          simp only [List.cons_append, binaryPrefixLength] at ih
          split_ifs at * <;> omega

theorem BoundedAlternation.take {L : ℕ} {xs : List ℕ}
    (h : BoundedAlternation L xs) (k : ℕ) : BoundedAlternation L (xs.take k) := by
  induction k generalizing xs with
  | zero => simp [BoundedAlternation]
  | succ k ih =>
      cases xs with
      | nil => simp [BoundedAlternation]
      | cons x xs =>
          constructor
          · have he := binaryPrefixLength_append_ge ((x :: xs).take (k + 1)) ((x :: xs).drop (k + 1))
            rw [List.take_append_drop] at he
            exact he.trans h.1
          · exact ih h.2

theorem BoundedAlternation.drop {L : ℕ} {xs : List ℕ}
    (h : BoundedAlternation L xs) (k : ℕ) : BoundedAlternation L (xs.drop k) := by
  induction k generalizing xs with
  | zero => exact h
  | succ k ih =>
      cases xs with
      | nil => simp [BoundedAlternation]
      | cons x xs => exact ih h.2

theorem BoundedAlternation.interior {b L : ℕ} {ls : List ℕ}
    (h : BoundedAlternation L (ls.map (fun x => b - x))) :
    BoundedAlternation L (interiorLosses b ls) := by
  simpa only [interiorLosses, List.map_take, List.map_drop] using
    (h.drop 1).take (ls.length - 2)

theorem alternatingLengths_map (f : ℕ → ℕ) (x y r : ℕ) :
    (alternatingLengths x y r).map f = alternatingLengths (f x) (f y) r := by
  induction r with
  | zero => simp [alternatingLengths]
  | succ r ih => simp [alternatingLengths, ih]

theorem loss_map_involution (b : ℕ) (ls : List ℕ)
    (hbound : ∀ x ∈ ls, x ≤ b) :
    (ls.map (fun x => b - x)).map (fun x => b - x) = ls := by
  induction ls with
  | nil => rfl
  | cons x xs ih =>
      have hx := hbound x (by simp)
      have ht := ih (by intro y hy; exact hbound y (by simp [hy]))
      simp only [List.map_cons, ht]
      congr 1
      omega

theorem binaryPrefixLength_chain_factor (b r : ℕ) (ls : List ℕ)
    (hbound : ∀ x ∈ ls, x ≤ b)
    (h : 2 * r + 1 ≤ binaryPrefixLength (ls.map (fun x => b - x))) :
    ∃ post, ls = alternatingLengths b (b - 1) r ++ post ∨
      ls = alternatingLengths (b - 1) b r ++ post := by
  obtain ⟨x, post, hx, he⟩ := binaryPrefixLength_long_factor r _ h
  have he' := congrArg (List.map (fun x => b - x)) he
  rw [loss_map_involution b ls hbound, List.map_append, alternatingLengths_map] at he'
  refine ⟨post.map (fun x => b - x), ?_⟩
  have hx01 : x = 0 ∨ x = 1 := by omega
  rcases hx01 with rfl | rfl
  · exact Or.inl (by simpa using he')
  · exact Or.inr (by simpa using he')

def NoAlternatingFactor (b R : ℕ) (ls : List ℕ) : Prop :=
  ∀ pre post, ls ≠ pre ++ alternatingLengths b (b - 1) R ++ post ∧
    ls ≠ pre ++ alternatingLengths (b - 1) b R ++ post

theorem boundedAlternation_of_no_factor (b R : ℕ) (ls : List ℕ)
    (hbound : ∀ x ∈ ls, x ≤ b) (havoid : NoAlternatingFactor b R ls) :
    BoundedAlternation (2 * R) (ls.map (fun x => b - x)) := by
  induction ls with
  | nil => trivial
  | cons x xs ih =>
      constructor
      · by_contra hbad
        obtain ⟨post, hp | hp⟩ := binaryPrefixLength_chain_factor b R (x :: xs)
          hbound (by simpa only [List.map_cons] using Nat.succ_le_of_lt (Nat.lt_of_not_ge hbad))
        · exact (havoid [] post).1 (by simpa using hp)
        · exact (havoid [] post).2 (by simpa using hp)
      · apply ih (by intro y hy; exact hbound y (by simp [hy]))
        intro pre post
        constructor
        · intro he
          exact (havoid (x :: pre) post).1 (by simp [he, List.append_assoc])
        · intro he
          exact (havoid (x :: pre) post).2 (by simp [he, List.append_assoc])

theorem chainCells_alternating (x y r : ℕ) :
    chainCells (alternatingLengths x y r) =
      repeatedCells (completedPair x y) r ++ List.replicate (x - 1) false := by
  induction r with
  | zero => simp [alternatingLengths, repeatedCells, chainCells]
  | succ r ih =>
      simp [alternatingLengths, chainCells, alternatingLengths_nonempty, ih,
        repeatedCells, completedPair, completedChain, List.append_assoc]

theorem repeatedPair_factor_of_alternating {ls pre post : List ℕ} {x y R : ℕ}
    (he : ls = pre ++ alternatingLengths x y R ++ post) :
    MarkFactor (repeatedCells (completedPair x y) R) (chainCells ls) := by
  have hin : MarkFactor (repeatedCells (completedPair x y) R)
      (chainCells (alternatingLengths x y R)) :=
    ⟨[], List.replicate (x - 1) false, by simp [chainCells_alternating]⟩
  rw [he]
  exact hin.trans (chainCells_factor pre _ post (alternatingLengths_nonempty _ _ _))

theorem no_alternatingFactor_of_periodic_avoidance {a b R : ℕ} {ls d : List ℕ}
    (hreal : RealizesChains a ls d)
    (hfirst : ¬CellFactor a (repeatedCells (completedPair b (b - 1)) R) d)
    (hsecond : ¬CellFactor a (repeatedCells (completedPair (b - 1) b) R) d) :
    NoAlternatingFactor b R ls := by
  intro pre post
  constructor
  · intro he
    exact hfirst (hreal _ (repeatedPair_factor_of_alternating he))
  · intro he
    exact hsecond (hreal _ (repeatedPair_factor_of_alternating he))

end SuperpermutationLowerBound.Refinement.ChainReturns
