module

public import H20.WindowScalar
public import SuperpermutationLowerBound.Refinement.WordBound

@[expose] public section

/-!
Conditional final numerical corollaries. These are not unconditional until
the corresponding window certificate is checked. No CP hypothesis is used.
-/
namespace H20
open SuperpermutationLowerBound
open SuperpermutationLowerBound.Refinement
open SuperpermLowerBounds

theorem k10_shortest_of_window (HW : S.WStatement 10 31 508 127) :
    4033379 ≤ shortestSuperpermutationLength 10 := by
  have H := hereditary_of_wstatement (k := 10) (cn := 31) (bn := 508) (q := 127)
    (by norm_num) (by norm_num) (by norm_num) HW
  have H' : HereditarySegmentBound (by norm_num : 7 ≤ 10) (127 / 429) (1270 / 429) := by
    norm_num at H ⊢
    exact H
  obtain ⟨P, hP⟩ := exists_reducedMinimumPath (by norm_num : 3 ≤ 10)
  have hf := pathForest_affine_assembly (by norm_num : 7 ≤ 10) H'
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) P hP
  norm_num at hf
  have hstrict : (41691 : ℚ) <
      (pathForestTotalBudget (by norm_num) P : ℚ) + (pathForestV (by norm_num) P : ℚ) := by
    linarith
  have hbudget : 41692 ≤ pathForestTotalBudget (by norm_num) P + pathForestV (by norm_num) P := by
    have hh : 41691 < pathForestTotalBudget (by norm_num) P + pathForestV (by norm_num) P := by
      exact_mod_cast hstrict
    omega
  have hr := pathForest_residual_RV (by norm_num : 7 ≤ 10) P hP
  norm_num at hr
  rw [shortestSuperpermutationLength_eq_add_minimumHamiltonianPathWeight 10 (by norm_num)]
  have hw := hP.1
  omega

theorem k13_shortest_of_window (HW : S.WStatement 13 86 2100 525) :
    6746627228 ≤ shortestSuperpermutationLength 13 := by
  have H := hereditary_of_wstatement (k := 13) (cn := 86) (bn := 2100) (q := 525)
    (by norm_num) (by norm_num) (by norm_num) HW
  have H' : HereditarySegmentBound (by norm_num : 7 ≤ 13) (525 / 2582) (6825 / 2582) := by
    norm_num at H ⊢
    exact H
  obtain ⟨P, hP⟩ := exists_reducedMinimumPath (by norm_num : 3 ≤ 13)
  have hf := pathForest_affine_assembly (by norm_num : 7 ≤ 13) H'
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) P hP
  norm_num at hf
  have hstrict : (40604817 : ℚ) <
      (pathForestTotalBudget (by norm_num) P : ℚ) + (pathForestV (by norm_num) P : ℚ) := by
    linarith
  have hbudget : 40604818 ≤ pathForestTotalBudget (by norm_num) P + pathForestV (by norm_num) P := by
    have hh : 40604817 < pathForestTotalBudget (by norm_num) P + pathForestV (by norm_num) P := by
      exact_mod_cast hstrict
    omega
  have hr := pathForest_residual_RV (by norm_num : 7 ≤ 13) P hP
  norm_num at hr
  rw [shortestSuperpermutationLength_eq_add_minimumHamiltonianPathWeight 13 (by norm_num)]
  have hw := hP.1
  omega

/-- Reuse the established one-based/Fin-alphabet transport. -/
theorem covers_length_ge_shortest {K : ℕ} (w : List (Fin K))
    (hw : SuperpermutationBounds.Covers w) : shortestSuperpermutationLength K ≤ w.length := by
  classical
  let e : Alphabet K ≃ Fin K := Fintype.equivFinOfCardEq (by simp [Alphabet])
  let W : Word K := w.map e.symm
  have hW : IsSuperpermutation W := by
    intro p
    have hlength : (p.1.map e).length = K := by simpa only [List.length_map] using p.length
    have hnodup : (p.1.map e).Nodup := p.nodup.map e.injective
    obtain ⟨u, v, heq⟩ := hw (p.1.map e) hlength hnodup
    refine ⟨u.map e.symm, v.map e.symm, ?_⟩
    have hmapped := congrArg (List.map e.symm) heq
    simpa [W, List.map_append, List.map_map, Function.comp_def] using hmapped.symm
  simpa only [W, List.length_map] using shortestSuperpermutationLength_le W hW

theorem k10_word_of_window (HW : S.WStatement 10 31 508 127)
    (w : List (Fin 10)) (hw : SuperpermutationBounds.Covers w) : 4033379 ≤ w.length :=
  (k10_shortest_of_window HW).trans (covers_length_ge_shortest w hw)

theorem k13_word_of_window (HW : S.WStatement 13 86 2100 525)
    (w : List (Fin 13)) (hw : SuperpermutationBounds.Covers w) : 6746627228 ≤ w.length :=
  (k13_shortest_of_window HW).trans (covers_length_ge_shortest w hw)
end H20
