module

public import SuperpermutationLowerBound.Refinement.GeometryPatternCells
public import SuperpermutationLowerBound.Refinement.ReturnNormalization

@[expose] public section

namespace SuperpermutationLowerBound.Refinement

@[simp] theorem cellWord_cons (a : ℕ) (b : Bool) (bs : List Bool) :
    cellWord a (b :: bs) = cellDigits a b ++ cellWord a bs := rfl

theorem cellWord_following_digit (a : ℕ) (cells : List Bool) {d : ℕ}
    (hd : d ≤ 2) (tail : List ℕ) :
    ∃ next rest, cellWord a cells ++ d :: tail = next :: rest ∧ next ≤ 2 := by
  cases cells with
  | nil => exact ⟨d, tail, by simp, hd⟩
  | cons b bs =>
    refine ⟨2, List.replicate (if b then a-2 else a-1) 0 ++
      (cellWord a bs ++ d :: tail), ?_, by omega⟩
    simp [cellWord_cons, cellDigits, List.append_assoc]

namespace PatternAt

variable {n : ℕ} (hn : 7 ≤ n) {hk : 7 ≤ n+1}
  {p : OverlapPath (n+1)} {hp : IsBlockAligned p}
  {segment : BlockAlignedLightSegment hk p hp} {start : ℕ}

/-- Iterate the forced C/B transitions on an actual contiguous segment.
The final digit may be full or short, retaining both terminal trap cases. -/
theorem cellWord_entry {cells : List Bool} {d : ℕ} {tail : List ℕ}
    (h : PatternAt segment start (cellWord (n-2) cells ++ d :: tail)) (hd : d ≤ 2)
    (e : Fin (n+1) ≃ Alphabet (n+1))
    (he : (segment.actualRun ⟨start, by
      have := h.1
      simp only [List.length_append, List.length_cons] at this
      omega⟩).entry = shortEntry n hn e) :
    (segment.actualRun ⟨start + (cellWord (n-2) cells).length, by
      have := h.1
      simp only [List.length_append, List.length_cons] at this
      omega⟩).entry = shortEntry n hn ((cellNormalization n hn cells).symm.trans e) := by
  induction cells generalizing start e with
  | nil =>
    have hone : ((1 : Equiv.Perm (Fin (n+1))).symm.trans e) = e := by ext i; rfl
    simpa only [cellWord_nil, List.length_nil, Nat.add_zero, cellNormalization_nil, hone] using he
  | cons b bs ih =>
    have h' : PatternAt segment start
        (cellDigits (n-2) b ++ (cellWord (n-2) bs ++ d :: tail)) := by
      simpa only [cellWord_cons, List.append_assoc] using h
    obtain ⟨next, rest, hrest, hnext⟩ := cellWord_following_digit (n-2) bs hd tail
    have hstep : PatternAt segment start (cellDigits (n-2) b ++ next :: rest) := by
      rw [← hrest]
      exact h'
    let move := if b then cellRho n hn * cellG n hn else cellG n hn
    have hentry := hstep.cell_step_entry hn hnext e he
    have htail := h'.append_right
    have hfinal := ih htail (move.symm.trans e) hentry
    have hcoords : (cellNormalization n hn bs).symm.trans (move.symm.trans e) =
        (cellNormalization n hn (b::bs)).symm.trans e := by
      apply Equiv.ext
      intro i
      rfl
    simpa only [cellWord_cons, List.length_append, Nat.add_assoc, hcoords] using hfinal

/-- The same actual entry formula at every cell boundary, not just the end. -/
theorem cellWord_prefix_entry {before after : List Bool} {d : ℕ} {tail : List ℕ}
    (h : PatternAt segment start (cellWord (n-2) (before ++ after) ++ d :: tail))
    (hd : d ≤ 2) (e : Fin (n+1) ≃ Alphabet (n+1))
    (he : (segment.actualRun ⟨start, by
      have := h.1
      simp only [List.length_append, List.length_cons] at this
      omega⟩).entry = shortEntry n hn e) :
    (segment.actualRun ⟨start + (cellWord (n-2) before).length, by
      have := h.1
      simp only [cellWord_append, List.length_append, List.length_cons] at this
      omega⟩).entry = shortEntry n hn ((cellNormalization n hn before).symm.trans e) := by
  obtain ⟨next, rest, hrest, hnext⟩ := cellWord_following_digit (n-2) after hd tail
  have h' : PatternAt segment start (cellWord (n-2) before ++ next :: rest) := by
    rw [← hrest]
    simpa only [cellWord_append, List.append_assoc] using h
  exact h'.cellWord_entry hn hnext e he

theorem cellWord_initial_coordinates {cells : List Bool} {d : ℕ} {tail : List ℕ}
    (h : PatternAt segment start (cellWord (n-2) cells ++ d :: tail)) :
    ∃ e : Fin (n+1) ≃ Alphabet (n+1),
      (segment.actualRun ⟨start, by
        have := h.1
        simp only [List.length_append, List.length_cons] at this
        omega⟩).entry = shortEntry n hn e := by
  let u := (segment.actualRun ⟨start, by
    have := h.1
    simp only [List.length_append, List.length_cons] at this
    omega⟩).entry
  exact ⟨(cellY n hn).symm.trans (vertexCoordinates u), (shortEntry_normalize n hn u).symm⟩

end PatternAt

theorem CellFactor.exists_patternAt {n : ℕ} {hk : 7 ≤ n+1}
    {p : OverlapPath (n+1)} {hp : IsBlockAligned p}
    {segment : BlockAlignedLightSegment hk p hp} {cells : List Bool}
    (h : CellFactor (n-2) cells segment.deficitString) :
    ∃ start, PatternAt segment start (cellWord (n-2) cells ++ [2,0]) := by
  obtain ⟨pre, post, he⟩ := h
  have hpattern := PatternAt.of_factor he
  exact ⟨pre.length+1, hpattern.cons_tail⟩

end SuperpermutationLowerBound.Refinement
