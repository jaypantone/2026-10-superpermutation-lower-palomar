module

public import LowerBounds.SGen.C10_31_508_127
public import LowerBounds.SSound
public import H20.FiniteWords

@[expose] public section

/-!
The ten-letter finite improvement. The only hypothesis on the final word
is the original covering predicate. The full finite exclusion is assembled
from kernel-checked literals, frontier covers and subtree checks; the
all-length completeness theorem then supplies the window statement.

Attribution: the search/completeness and list-capacity framework are
Halfar's pinned source. This development supplies the stronger parameter certificate
and the direct bridge to our existing actual-segment/forest development.
-/
namespace H20.K10
open SuperpermLowerBounds

set_option maxRecDepth 100000

/-- One block cannot be followed by eight full pieces. -/
theorem run_checked : S.runSearch 10 = false := by
  decide +kernel

/-- All model windows, of arbitrary finite length, satisfy these parameters. -/
theorem window_checked : S.WStatement 10 31 508 127 :=
  S.wstatement_of_search (A := 858) (q2 := 254) (C1 := 1524) (C2 := 1778) (fuel := 614)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) run_checked SGen.search_C10_31_508_127

/-- The minimum length on ten symbols is at least4,033,379. -/
theorem shortest_lower_bound :
    4033379 ≤ SuperpermutationLowerBound.shortestSuperpermutationLength 10 :=
  H20.k10_shortest_of_window window_checked

/-- Every ten-symbol covering word has at least4,033,379 letters. -/
theorem word_lower_bound (w : List (Fin 10))
    (hw : SuperpermutationBounds.Covers w) : 4033379 ≤ w.length :=
  H20.k10_word_of_window window_checked w hw

end H20.K10

#print axioms H20.K10.run_checked
#print axioms H20.K10.window_checked
#print axioms H20.K10.shortest_lower_bound
#print axioms H20.K10.word_lower_bound
