module

public import SuperpermutationLowerBound.Refinement.GeometryPatternCells

@[expose] public section

namespace SuperpermutationLowerBound.Refinement
open PermutationVertex
namespace PatternAt
variable {n : ℕ} (hn : 7 ≤ n) {hk : 7 ≤ n + 1}
  {p : OverlapPath (n + 1)} {hp : IsBlockAligned p}
  {segment : BlockAlignedLightSegment hk p hp} {start : ℕ}

theorem cell_step_incoming {b : Bool} {d : ℕ} {tail : List ℕ}
    (h : PatternAt segment start (cellDigits (n - 2) b ++ d :: tail)) (hd : d ≤ 2) :
    let next := start + (cellDigits (n - 2) b).length
    let before := segment.actualRun ⟨next - 1, by
      have := h.1
      simp only [List.length_append, List.length_cons] at this
      omega⟩
    let after := segment.actualRun ⟨next, by
      have := h.1
      simp only [List.length_append, List.length_cons] at this
      omega⟩
    before.length = n ∧ fullRunMap (by omega) before.entry = after.entry := by
  dsimp only
  let g := if b then (n - 2) - 2 else (n - 2) - 1
  have hg : 0 < g := by dsimp [g]; split_ifs <;> omega
  have hstart : start < segment.length := by
    have := h.1
    simp only [cellDigits, List.length_append, List.length_cons, List.length_replicate] at this
    omega
  let u := (segment.actualRun ⟨start, hstart⟩).entry
  let e := (cellY n hn).symm.trans (vertexCoordinates u)
  have he : u = shortEntry n hn e := (shortEntry_normalize n hn u).symm
  have hstep := h.cell_step_entry hn hd e he
  have hfull := h.cell_full_entry hn e he (g - 1) (by dsimp [g]; split_ifs <;> omega)
  have hidx : start + (cellDigits (n - 2) b).length - 1 = start + 1 + (g - 1) := by
    simp only [cellDigits, List.length_cons, List.length_replicate]
    dsimp [g]
    omega
  have h' : PatternAt segment start (2 :: List.replicate g 0 ++ d :: tail) := h
  have hzeros := h'.cons_tail.append_left (xs := List.replicate g 0)
  have hlen := hzeros.actual_length (g - 1) (by simpa using Nat.sub_lt hg (by decide : 0 < 1))
  constructor
  · simp only [List.getElem_replicate, Nat.add_sub_cancel, Nat.sub_zero] at hlen
    simpa only [hidx] using hlen
  · have hnextFormula : (segment.actualRun
        ⟨start + (cellDigits (n - 2) b).length, by
          have := h.1
          simp only [List.length_append, List.length_cons] at this
          omega⟩).entry = fullRunMapPower (by omega) g (fullEntry n hn e) := by
      rw [hstep]
      cases b with
      | false => simpa only [Bool.false_eq_true, ↓reduceIte, g,
          show n - 2 - 1 = n - 3 by omega] using (regularCell_entry_transfer n hn e).symm
      | true => simpa only [↓reduceIte, g,
          show n - 2 - 2 = n - 4 by omega] using (shortenedCell_entry_transfer n hn e).symm
    simp only [hidx]
    rw [hfull, hnextFormula]
    conv_rhs => rw [show g = (g - 1) + 1 by omega]
    simp only [fullRunMapPower, Function.iterate_succ_apply']

end PatternAt

end SuperpermutationLowerBound.Refinement
