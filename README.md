# Lower bounds for superpermutations

The research presented here, the Lean formalization, and this document were
generated entirely by AI systems under Jay Pantone's direction. The inherited
mathematical work and software retain their original credits. Independent AI
review is not human peer review.

This is a separate Palomar submission candidate for Jay Pantone's general lower
bounds, their asymptotics, and the finite improvements at ten and fourteen
symbols. It is derived from the frozen results repository at commit
`c9ccb6a0d9ddd1007fdce6efab50807ec47464b9`. The mathematical statements are unchanged.

Let S(n) be the shortest length of a word containing every permutation of n
symbols as a contiguous factor, and set F3(n) = n! + (n-1)! + (n-2)!.
The general theorem gives two explicit lower bounds for every n >= 8. Their
leading correction to F3(n) is (2 + o(1))(n-4)!. The asymptotic results also
compare them with the preceding general formula and with the Fritsch-Halfar
all-size formula; they do not compare with separately searched finite bounds.

More precisely, let B(n) be the exact-order formula here and H(n) the
Fritsch-Halfar general formula defined in the asymptotic Challenge. The proved
limits give:

| Residue of n modulo 3 | Asymptotic gain B(n) − H(n) |
| ---: | --- |
| 1 | (3 + o(1))(n−6)! |
| 2 | (18 + o(1))(n−7)! |
| 0 | (9 + o(1))(n−7)! |

Thus B(n) exceeds H(n) for all sufficiently large n. The quadratic-order
formula has the same three asymptotic gains. Halfar's separately computed
finite bounds are discussed in the papers.

The [informal statement](docs/INFORMAL_STATEMENT.md) explains the argument and
gives the complete formulas. The [related-work note](docs/RELATED_WORK.md)
distinguishes the general comparison from the finite bounds announced in
October 2026. The companion [upper-bound repository](https://github.com/jaypantone/2026-10-superpermutation-upper-palomar)
contains the construction results.

## The statements to inspect

Each submission has a self-contained `Challenge.lean` importing only Mathlib.
It contains the complete definitions and target theorem statements, with
`by sorry` placeholders. Its corresponding `Solution.lean` provides proofs under the same names,
without importing that challenge. Comparator
checks the two separate environments.

The asymptotic submission uses the namespace `SuperpermutationPalomar` for its
independently repeated definitions. Its solution repeats exactly the same
definitions and applies the original theorems by definitional equality. This
keeps Lean’s local generation of pattern matchers identical in the two
environments; it introduces no assumption or definition hole.

| Submission | Claims | Independent statement | Proof environment |
| --- | ---: | --- | --- |
| General | 2 | [Challenge](Submissions/General/Challenge.lean) | [Solution](Submissions/General/Solution.lean) |
| Asymptotics | 13 | [Challenge](Submissions/Asymptotics/Challenge.lean) | [Solution](Submissions/Asymptotics/Solution.lean) |
| Ten | 1 | [Challenge](Submissions/Ten/Challenge.lean) | [Solution](Submissions/Ten/Solution.lean) |
| Fourteen | 1 | [Challenge](Submissions/Fourteen/Challenge.lean) | [Solution](Submissions/Fourteen/Solution.lean) |

The finite claims are S(10) >= 4,033,379 and S(14) >= 93,891,141,150.
There is no path, search, or normalization hypothesis on the words in these
statements. The general theorem and its asymptotics likewise concern arbitrary
covering words.

## Scope and provenance

The supporting library is the exact recursive local import closure of these
four result families, with 270 inherited modules. [source-provenance.json](source-provenance.json)
records the original source hashes and import graph. The [porting note](docs/PORTING.md) records the visibility and import
changes, together with the subsequent edits to module comments. The original
source hashes and the checked source snapshot are preserved.
No inherited theorem statement or proof body has changed. Fourteen modules
use Lean's official private-declaration export compatibility option; the
[compatibility record](port-compatibility.json) identifies each use. This changes
visibility and adds no axiom. The original sources remain in the frozen repository.

The stronger thirteen-symbol finite result from the frozen repository is
**not submitted here**. Its proof uses native-computation assumptions. No part
of its `H20Native` proof or certificate family is in this repository's proof
closure. The general theorem still applies at thirteen symbols, as it does at
every n >= 8, with its own standard-axiom bound.

All 279 modules in this migrated proof compile with the pinned Lean 4.35.0.
The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`
for all seventeen selected declarations. A Palomar submission candidate is
not a Palomar registration; the additional verification checks are recorded below.

## Checking this version

The project pins Lean 4.35.0 and a fixed Mathlib revision. The
[build guide](docs/BUILD.md) describes the Lake build, shared storage, and resource limits. The [verification record](verification.json) records completed checks;
compilation alone does not establish Comparator agreement or independent kernel
replay.

The local macOS diagnostics give the following results. These runs use the
explicitly unsandboxed diagnostic mode and are not the protected Palomar workflow.

| Submission | Statement and axiom comparison | Fresh Lean replay | NanoDa replay |
| --- | --- | --- | --- |
| General | Passed | Passed | Passed |
| Asymptotics | Passed | Passed | Passed |
| Ten | Passed | Passed | Passed |
| Fourteen | Passed | Passed | Passed |

Ten's fresh Lean and NanoDa replays completed in a later run with an explicit
longer deadline. The complete protected Linux Palomar workflow remains unrun
for all four configurations. Since those checks, eleven module comments have been edited; all
proof code remains unchanged. The [comment-edit record](verification/comment-edits.json)
binds those edits to the checked sources.

The four entries are selected by [the general configuration](comparator.json),
[the asymptotic configuration](comparator-asymptotics.json),
[the ten-symbol configuration](comparator-ten.json), and
[the fourteen-symbol configuration](comparator-fourteen.json). All permit only
Lean's three standard axioms and enable NanoDa. The
[Palomar guide](docs/PALOMAR.md) distinguishes local diagnostics from the full
protected verification workflow and explains the remaining publication steps.

To rebuild the two papers with an installed TeX engine, run
`python3 -B tools/build_papers.py lower finite`. Intermediate files are temporary.

## Mathematical accounts

[The general lower-bound paper](papers/lower/lower-bounds.pdf) develops the
chain-return arguments and the comparisons. Its [TeX source](papers/lower/lower-bounds.tex)
is included.

[The finite-bound paper](papers/finite/finite-lower-bounds.pdf) explains the
finite certificates and the fourteen-symbol compatibility argument. Its
[TeX source](papers/finite/finite-lower-bounds.tex) is included. That paper also
discusses the native-qualified thirteen-symbol result as context; that result
is outside all four submission configurations in this repository.

The ten-symbol proof uses Jakub Halfar's window-search framework and kernel
certificate method. The provenance and upstream notices are retained in
[NOTICE](NOTICE) and [licenses/Halfar-NOTICE](licenses/Halfar-NOTICE).
The repository is distributed under [Apache License 2.0](LICENSE).
