# What changed for Palomar

The mathematical results come from the frozen October 2026 development at
`c9ccb6a0d9ddd1007fdce6efab50807ec47464b9`. This repository retains the exact
270-module dependency closure of the general bounds, asymptotics, and finite
results at ten and fourteen symbols. Each of the four submissions now has an
independent Challenge containing its full definitions and theorem statements.

The port uses Lean 4.35's module system, public imports, and exposed public
declarations. Fourteen inherited modules use Lean's
`backward.privateInPublic` compatibility setting: their public definitions
refer to existing private helper declarations, which must also be exported.
This preserves their names, definitions, and proofs and adds no axiom. The
affected modules are listed in [port-compatibility.json](../port-compatibility.json).
One explicit `Mathlib.Data.List.Nodup` import was added to
`proofs/LowerBounds/SWord.lean`, where an earlier transitive import had supplied
three list lemmas. No inherited mathematical statement or proof body was changed.

The asymptotic interface uses a fresh namespace, `SuperpermutationPalomar`.
Its Challenge and Solution contain identical, fully specified definitions;
the Solution proves each of the thirteen statements by applying the original
theorem, with Lean checking definitional equality. This avoids a difference
in the names of auxiliary pattern matchers generated when definitions are
inlined in one environment and imported in the other. The first Comparator
attempt detected that difference. The repair changes neither the formulas
nor the claims and introduces no definition hole or additional assumption.

[source-provenance.json](../source-provenance.json) records the original source
identities and retained modules. Independent reverse comparison recovered all
270 original sources after removing the documented visibility directives and
their explanatory comments and added blank lines, and that explicit Mathlib
import. That comparison concerns the original port snapshot. Eleven
module comments were subsequently edited to remove obsolete archive references
and clarify descriptions. The [comment-edit record](../verification/comment-edits.json)
preserves the before/after hashes and verifies that every noncomment byte is
unchanged. Build and replay evidence retains the checked snapshot in
[verification.json](../verification.json); no new run is claimed for these
comment edits.

The papers' repository references were updated. The native-qualified
thirteen-symbol certificate remains in the original repository, outside this
submission's source closure. Its discussion in the finite-bound paper is
explicitly marked as context. No search was repeated and no new bound is
claimed by this port.
