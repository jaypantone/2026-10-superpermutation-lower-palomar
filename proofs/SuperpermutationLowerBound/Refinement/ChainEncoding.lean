module

public import SuperpermutationLowerBound.Refinement.ChainPacking

@[expose] public section

/-! Exact list encodings connecting the geometric C/B words to the lengths
of maximal chains. All decompositions preserve literal contiguous factors. -/
namespace SuperpermutationLowerBound.Refinement

def cellDigits (a : ℕ) (shortened : Bool) : List ℕ :=
  2 :: List.replicate (if shortened then a-2 else a-1) 0

def cellWord (a : ℕ) (cells : List Bool) : List ℕ := cells.flatMap (cellDigits a)

def gapWord (gaps : List ℕ) : List ℕ :=
  gaps.flatMap (fun g => 2 :: List.replicate g 0)

@[simp] theorem cellWord_nil (a : ℕ) : cellWord a [] = [] := rfl

@[simp] theorem cellWord_append (a : ℕ) (xs ys : List Bool) :
    cellWord a (xs ++ ys) = cellWord a xs ++ cellWord a ys := by
  simp [cellWord]

@[simp] theorem gapWord_append (xs ys : List ℕ) :
    gapWord (xs ++ ys) = gapWord xs ++ gapWord ys := by simp [gapWord]

theorem regularPath_eq_gapWord (gaps : List ℕ) : regularPath gaps = gapWord gaps ++ [2] := by
  induction gaps with
  | nil => rfl
  | cons g gs ih => simp [regularPath, gapWord, ih, List.append_assoc]

theorem gapWord_eq_cellWord {a : ℕ} {gaps : List ℕ}
    (h : ∀ g ∈ gaps, g = a-1 ∨ g = a-2) :
    gapWord gaps = cellWord a (gaps.map (fun g => decide (g = a-2))) := by
  induction gaps with
  | nil => rfl
  | cons g gs ih =>
    have hg := h g (by simp)
    have hgs : ∀ x ∈ gs, x = a-1 ∨ x = a-2 := fun x hx => h x (by simp [hx])
    have ht := ih hgs
    change (2 :: List.replicate g 0) ++ gapWord gs =
      cellDigits a (decide (g = a-2)) ++ cellWord a (gs.map (fun g => decide (g = a-2)))
    rw [ht]
    have hc : cellDigits a (decide (g = a-2)) = 2 :: List.replicate g 0 := by
      by_cases he : g = a-2
      · simp [cellDigits, he]
      · have hf : g = a-1 := hg.resolve_right he
        have hne : a-1 ≠ a-2 := by omega
        simp [cellDigits, hf, hne]
    rw [hc]

/-- Accumulate a chain until a shortened gap ends it. -/
def chainLengthsFrom (a r : ℕ) : List ℕ → List ℕ
  | [] => [r]
  | g :: gs => if g = a-2 then r :: chainLengthsFrom a 1 gs
      else chainLengthsFrom a (r+1) gs

def chainLengths (a : ℕ) (gaps : List ℕ) : List ℕ := chainLengthsFrom a 1 gaps

theorem chainLengthsFrom_nonempty (a r : ℕ) (gaps : List ℕ) :
    chainLengthsFrom a r gaps ≠ [] := by
  induction gaps generalizing r with
  | nil => simp [chainLengthsFrom]
  | cons g gs ih => simp only [chainLengthsFrom]; split <;> simp_all

theorem chainLengthsFrom_positive {a r : ℕ} (hr : 1 ≤ r) (gaps : List ℕ) :
    ∀ x ∈ chainLengthsFrom a r gaps, 1 ≤ x := by
  induction gaps generalizing r with
  | nil => simpa [chainLengthsFrom] using hr
  | cons g gs ih =>
    simp only [chainLengthsFrom]
    split
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hr
      · exact ih (by omega) x hx
    · exact ih (by omega)

theorem chainLengthsFrom_sum (a r : ℕ) (gaps : List ℕ) :
    (chainLengthsFrom a r gaps).sum = r + gaps.length := by
  induction gaps generalizing r with
  | nil => simp [chainLengthsFrom]
  | cons g gs ih =>
    simp only [chainLengthsFrom]
    split <;> simp [List.sum_cons, ih] <;> omega

theorem chainLengthsFrom_length (a r : ℕ) (gaps : List ℕ) :
    (chainLengthsFrom a r gaps).length = gaps.count (a-2) + 1 := by
  induction gaps generalizing r with
  | nil => simp [chainLengthsFrom]
  | cons g gs ih =>
    simp only [chainLengthsFrom]
    split_ifs with h
    · simp [ih, h]
    · simp [ih, h]

def chainGaps (a : ℕ) : List ℕ → List ℕ
  | [] => []
  | r :: rs => List.replicate (r-1) (a-1) ++
      if rs = [] then [] else (a-2) :: chainGaps a rs

theorem chainGaps_from {a r : ℕ} (hr : 1 ≤ r) {gaps : List ℕ}
    (h : ∀ g ∈ gaps, g = a-1 ∨ g = a-2) :
    chainGaps a (chainLengthsFrom a r gaps) = List.replicate (r-1) (a-1) ++ gaps := by
  induction gaps generalizing r with
  | nil => simp [chainLengthsFrom, chainGaps]
  | cons g gs ih =>
    have hg := h g (by simp)
    have hgs : ∀ x ∈ gs, x = a-1 ∨ x = a-2 := fun x hx => h x (by simp [hx])
    by_cases he : g = a-2
    · have hr1 := ih (r := 1) (by omega) hgs
      simp only [Nat.sub_self, List.replicate_zero, List.nil_append] at hr1
      rw [chainLengthsFrom, if_pos he, chainGaps,
        if_neg (chainLengthsFrom_nonempty a 1 gs), hr1, he]
    · have hf : g = a-1 := hg.resolve_right he
      rw [chainLengthsFrom, if_neg he, ih (by omega) hgs]
      rw [show r+1-1 = (r-1)+1 by omega, List.replicate_add]
      simp [hf, List.append_assoc]

theorem chainLengths_sum (a : ℕ) (gaps : List ℕ) :
    (chainLengths a gaps).sum = gaps.length + 1 := by
  simpa [chainLengths, Nat.add_comm] using chainLengthsFrom_sum a 1 gaps

theorem chainLengths_length (a : ℕ) (gaps : List ℕ) :
    (chainLengths a gaps).length = gaps.count (a-2) + 1 :=
  chainLengthsFrom_length a 1 gaps

theorem chainLengths_positive (a : ℕ) (gaps : List ℕ) :
    ∀ x ∈ chainLengths a gaps, 1 ≤ x := chainLengthsFrom_positive (by omega) gaps

theorem chainGaps_chainLengths {a : ℕ} {gaps : List ℕ}
    (h : ∀ g ∈ gaps, g = a-1 ∨ g = a-2) : chainGaps a (chainLengths a gaps) = gaps := by
  simpa [chainLengths] using chainGaps_from (r := 1) (by omega) h

theorem chainGaps_append (a : ℕ) {xs ys : List ℕ} (hx : xs ≠ []) (hy : ys ≠ []) :
    chainGaps a (xs ++ ys) = chainGaps a xs ++ (a-2) :: chainGaps a ys := by
  induction xs with
  | nil => contradiction
  | cons r rs ih =>
    by_cases hr : rs = []
    · simp [chainGaps, hr, hy]
    · simp [chainGaps, hr, hy, ih hr, List.append_assoc]

theorem chainGaps_factor (a : ℕ) (before middle after : List ℕ) (hm : middle ≠ []) :
    ∃ pre post, chainGaps a (before ++ middle ++ after) =
      pre ++ chainGaps a middle ++ post := by
  by_cases hb : before = []
  · subst before
    by_cases ha : after = []
    · subst after
      exact ⟨[], [], by simp⟩
    · exact ⟨[], (a-2) :: chainGaps a after, by simp [chainGaps_append a hm ha]⟩
  · by_cases ha : after = []
    · subst after
      exact ⟨chainGaps a before ++ [a-2], [], by
        simp [chainGaps_append a hb hm, List.append_assoc]⟩
    · refine ⟨chainGaps a before ++ [a-2], (a-2) :: chainGaps a after, ?_⟩
      rw [chainGaps_append a (by simp [hb] : before ++ middle ≠ []) ha,
        chainGaps_append a hb hm]
      simp [List.append_assoc]

theorem gapWord_factor {gaps before middle after : List ℕ}
    (h : gaps = before ++ middle ++ after) :
    gapWord gaps = gapWord before ++ gapWord middle ++ gapWord after := by
  simp [h]

theorem cellWord_factor {a : ℕ} {cells before middle after : List Bool}
    (h : cells = before ++ middle ++ after) :
    cellWord a cells = cellWord a before ++ cellWord a middle ++ cellWord a after := by
  simp [h]

/-- A contiguous sublist of gaps retains its closing singleton two. -/
theorem regularPath_factor {gaps before middle after : List ℕ}
    (h : gaps = before ++ middle ++ after) :
    ∃ pre post, regularPath gaps = pre ++ regularPath middle ++ post := by
  cases after with
  | nil => exact ⟨gapWord before, [], by simp [h, regularPath_eq_gapWord, List.append_assoc]⟩
  | cons g gs =>
    refine ⟨gapWord before, List.replicate g 0 ++ regularPath gs, ?_⟩
    simp [h, regularPath_eq_gapWord, gapWord, List.append_assoc]

/-- A selected run of at least `r` full cells contains the exact `C^r 2`
factor, regardless of preceding or following cells. -/
theorem regularPath_full_factor (a r l : ℕ) (hr : r ≤ l) (before after : List ℕ) :
    ∃ pre post, regularPath (before ++ List.replicate l (a-1) ++ after) =
      pre ++ (cellWord a (List.replicate r false) ++ [2]) ++ post := by
  have hrebuild : before ++ List.replicate l (a-1) ++ after =
      before ++ List.replicate r (a-1) ++ (List.replicate (l-r) (a-1) ++ after) := by
    have hrepl : List.replicate l (a-1) =
        List.replicate r (a-1) ++ List.replicate (l-r) (a-1) := by
      rw [← List.replicate_add, Nat.add_sub_of_le hr]
    simpa only [List.append_assoc] using
      congrArg (fun xs => before ++ xs ++ after) hrepl
  have he : regularPath (List.replicate r (a-1)) =
      cellWord a (List.replicate r false) ++ [2] := by
    rw [regularPath_eq_gapWord]
    simp [gapWord, cellWord, List.flatMap_replicate, cellDigits]
  obtain ⟨pre, post, hf⟩ := regularPath_factor hrebuild
  exact ⟨pre, post, by simpa only [he] using hf⟩

end SuperpermutationLowerBound.Refinement
