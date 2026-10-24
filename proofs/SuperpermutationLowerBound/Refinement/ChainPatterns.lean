module

public import SuperpermutationLowerBound.Refinement.ChainFactors

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

def MarkFactor (pattern cells : List Bool) : Prop :=
  ∃ before after, cells = before ++ pattern ++ after

theorem MarkFactor.trans {pattern middle cells : List Bool}
    (h : MarkFactor pattern middle) (h' : MarkFactor middle cells) : MarkFactor pattern cells := by
  obtain ⟨pre, post, hp⟩ := h
  obtain ⟨pre', post', hp'⟩ := h'
  exact ⟨pre' ++ pre, post ++ post', by simp [hp', hp, List.append_assoc]⟩

theorem MarkFactor.to_cellFactor {a : ℕ} (ha : 3 ≤ a) {pattern cells : List Bool}
    (h : MarkFactor pattern cells) : CellFactor a pattern (zeroCell a cells) := by
  obtain ⟨pre, post, hp⟩ := h
  exact cellFactor_of_mark_factor ha hp

theorem chainCells_factor (before middle after : List ℕ) (hm : middle ≠ []) :
    MarkFactor (chainCells middle) (chainCells (before ++ middle ++ after)) := by
  by_cases hb : before = []
  · subst before
    by_cases ha : after = []
    · subst after
      exact ⟨[], [], by simp⟩
    · exact ⟨[], true :: chainCells after, by simp [chainCells_append hm ha]⟩
  · by_cases ha : after = []
    · subst after
      exact ⟨chainCells before ++ [true], [], by
        simp [chainCells_append hb hm, List.append_assoc]⟩
    · refine ⟨chainCells before ++ [true], true :: chainCells after, ?_⟩
      rw [chainCells_append (by simp [hb] : before ++ middle ≠ []) ha,
        chainCells_append hb hm]
      simp [List.append_assoc]

theorem full_mark_factor (r l : ℕ) (hr : r ≤ l) :
    MarkFactor (List.replicate r false) (List.replicate l false) := by
  refine ⟨[], List.replicate (l-r) false, ?_⟩
  simp only [List.nil_append, ← List.replicate_add, Nat.add_sub_of_le hr]

def chainWindow (r s : ℕ) (middle : List ℕ) : List Bool :=
  List.replicate r false ++
    (if middle = [] then [true] else true :: (chainCells middle ++ [true])) ++
    List.replicate s false

theorem chainWindow_factor {x y r s : ℕ} (hr : r+1 ≤ x) (hs : s+1 ≤ y)
    (middle : List ℕ) :
    MarkFactor (chainWindow r s middle) (chainCells (x :: (middle ++ [y]))) := by
  have hx : List.replicate (x-1) false =
      List.replicate (x-1-r) false ++ List.replicate r false := by
    rw [← List.replicate_add, Nat.sub_add_cancel (by omega : r ≤ x-1)]
  have hy : List.replicate (y-1) false =
      List.replicate s false ++ List.replicate (y-1-s) false := by
    rw [← List.replicate_add, Nat.add_sub_of_le (by omega : s ≤ y-1)]
  refine ⟨List.replicate (x-1-r) false, List.replicate (y-1-s) false, ?_⟩
  by_cases hm : middle = []
  · subst middle
    simp only [chainCells, List.nil_append, List.cons_ne_self, List.cons_ne_nil,
      ↓reduceIte, List.append_nil, hx, hy, chainWindow, List.append_assoc]
    simp only [List.cons_append, List.nil_append, List.append_assoc]
  · rw [chainCells, if_neg (by simp : middle ++ [y] ≠ []),
      chainCells_append hm (by simp), chainCells]
    simp only [↓reduceIte, List.append_nil, hx, hy, chainWindow, if_neg hm,
      List.append_assoc]
    simp only [List.cons_append, List.nil_append, List.append_assoc]

theorem chainWindow_factor_of_list {ls before after middle : List ℕ} {x y r s : ℕ}
    (he : ls = before ++ (x :: (middle ++ [y])) ++ after)
    (hr : r+1 ≤ x) (hs : s+1 ≤ y) :
    MarkFactor (chainWindow r s middle) (chainCells ls) := by
  rw [he]
  exact (chainWindow_factor hr hs middle).trans
    (chainCells_factor before _ after (by simp))

theorem full_mark_factor_of_list {ls before after : List ℕ} {x r : ℕ}
    (he : ls = before ++ x :: after) (hr : r+1 ≤ x) :
    MarkFactor (List.replicate r false) (chainCells ls) := by
  have hc := chainCells_factor before [x] after (by simp)
  have hfull := full_mark_factor r (x-1) (by omega)
  have hc' : MarkFactor (List.replicate (x-1) false) (chainCells ls) := by
    simpa [chainCells, he] using hc
  exact hfull.trans hc'

/-- Every chain-factor witness becomes a literal, zero-bounded deficit factor. -/
theorem chain_factor_realization {a : ℕ} (ha : 3 ≤ a)
    {gaps before after d : List ℕ}
    (hg : ∀ g ∈ gaps, g = a-1 ∨ g = a-2)
    (hd : d = before ++ (0 :: (regularPath gaps ++ [0])) ++ after)
    {pattern : List Bool} (h : MarkFactor pattern (chainCells (chainLengths a gaps))) :
    CellFactor a pattern d := by
  have he : zeroCell a (chainCells (chainLengths a gaps)) = zeroRegular gaps := by
    rw [← zeroRegular_chainGaps, chainGaps_chainLengths hg]
  have hf := h.to_cellFactor ha
  rw [he] at hf
  exact hf.trans hd

end SuperpermutationLowerBound.Refinement
