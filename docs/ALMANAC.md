# Superpermutation Almanac submission: lower

This branch is one standalone submission for the lower repository. Submit the
companion repository separately. The source snapshot follows the live
[Lean directions](https://web-production-daed9.up.railway.app/lean) and
[agent directions](https://web-production-daed9.up.railway.app/lean.txt)
read on October 28, 2026. It replaces the old single-`almanac_claim` interface.
The original Palomar metadata, independent Challenges and historical receipts
remain available for their original purpose; they do not configure this batch.

## Selected results

Write F₃(n) = n! + (n−1)! + (n−2)!.

| Entry theorem | Kind | Statement |
|---|---|---|
| `general_lower` | Custom: `AlmanacAdapter.ExactWordBound` | The exact-order general lower formula, for every n ≥ 8 and every covering word. |
| `lower10` | `Almanac.LowerBoundAt 10 4033379` | S(10) ≥ 4,033,379. |
| `lower12` | `Almanac.LowerBoundAt 12 522622380` | S(12) ≥ 522,622,380. |
| `lower14` | `Almanac.LowerBoundAt 14 93891141150` | S(14) ≥ 93,891,141,150. |
| `asymptotic_lower_four` | `Almanac.AsymptoticLowerAt 4 2` | Eventually, S(n) ≥ F₃(n) + (2−ε)(n−4)! for every positive rational ε. |

The three finite consequences improving the public records read on October 28,
2026 are n=10 (+1), n=12 (+2), and n=14 (+142). The general theorem supplies
n=12; the separate Lean lemma `AlmanacAdapter.lower12` proves that consequence
in the site's vocabulary, and the `lower12` batch entry exposes it for automatic
recognition and inclusion in the preview's points estimate. The general theorem
also gives 93,891,141,149 at n=14; the separate refinement is one stronger.
The hosted preview and custom review must recheck eligibility at submission time.

## The custom statement and its review

`general_lower` has no construction, path, or search premise. It quantifies
over all `Almanac.Word n` satisfying the site's `IsSuperpermutation` predicate.
`AlmanacAdapter.covers_iff` proves the connection to the proof library's
predicate; the wrapper adds no hypothesis. Its bound is exactly
`SuperpermutationPalomar.GeneralLower.paperBound n (exactParameters n).1
(exactParameters n).2`, whose definitions are in
`Submissions/Asymptotics/Solution.lean`. The mathematical account is
`paper/lower/lower-bounds.pdf` and `docs/INFORMAL_STATEMENT.md`.

Ceilings alone do not obstruct a formula template: for an integer length,
comparison with a ceiling can be written as comparison with its rational
argument (with the appropriate casts and base term). Here the exact-order
parameters also use residue cases, a modular inverse and LCMs. Those are
outside `Almanac.Expr`, so the complete general statement is custom. Custom
statements may use these definitions; the template's formula restrictions
do not apply to them.

Suggested review interpretation: for every n ≥ 8, the shortest
superpermutation length is at least the exact-order formula in the paper,
with no hypothesis on the word other than coverage. At n=12 it yields
522,622,380. Its proof is checked by the site's kernels; its mathematical
interpretation still requires the site's custom-review process. The preview
cannot automatically include consequences of the custom statement in the points
estimate; the separate `lower12` template entry makes that consequence explicit.

The coefficient-2 entry is an epsilon lower bound, not an assertion that the
optimal coefficient is exactly 2. No novelty claim is made here for that
coefficient. The site supports this fourth-factorial template with no points
prize; it will reject a tie if an equally strong kernel-checked bound is
already listed. Keep its interpretation separate from the general theorem's
finer improvements. Custom review currently records finite consequences and
the third-factorial coefficient; the fourth-factorial consequence therefore
has its own template entry.

The quadratic-order alternative, two formula limits, six reference comparisons,
and four gains over the preceding formula remain supporting results in the
proof library and paper. They are not separate headline entries. The
native-qualified thirteen-symbol result is not part of this proof package.

## Files and papers

`AlmanacSolution.lean` contains only imports, the `AlmanacSubmission` namespace,
and one theorem per result proved by a named imported theorem. Linking proofs
are in `AlmanacAdapter.lean`; `AlmanacAxioms.lean` reports every entry's axioms.
The four reserved libraries are declared at the root in `lakefile.toml`.

Lean is pinned to `leanprover/lean4:v4.35.0`, with Mathlib at
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The three judge-owned files are exact
copies of the site's batch scaffold, version 2. Neither placeholder is imported
by the proof. The judge replaces them with its own files.

The site archives `paper/`, not `papers/`. `paper/` contains byte-identical
copies of the existing papers and their sources. After editing/rebuilding
`papers/`, refresh these copies before submitting. The preflight verifies that
they agree and that the site selects every file. The copies do not alter the
mathematical content or extend the submitted theorem scope.

## Reproduce the preparation checks

On this Mac, use the existing shared compiler and expanded Mathlib cache,
with outputs outside Dropbox:

```sh
python3 -B tools/check.py AlmanacAxioms --receipt almanac-batch-20261028.json
```

In an external checkout with the pinned toolchain and dependencies, the site's
build command is `lake build AlmanacSolution`; `lake build AlmanacAxioms`
additionally prints the assumptions. Ordinary Lake does not inherit this
repository's local compiler/memory/disk guard; see [BUILD.md](BUILD.md).

Download and unpack the current
[judge source](https://web-production-daed9.up.railway.app/lean/judge-source.tar.gz)
outside Dropbox. From that directory:

```sh
python3 -B -m lean.batch.validate /absolute/path/to/this/repository
```

Then run this repository's fuller static preflight:

```sh
python3 -B scripts/check-almanac.py \
  --judge-source /absolute/path/to/unpacked-judge \
  --mathlib-manifest /absolute/path/to/pinned/mathlib/lake-manifest.json \
  --receipt verification/almanac/preflight.json
```

It checks the official batch grammar, root layout, exact judge files, pinned
manifest, repository/source restrictions, and paper selection. The source scan
can report `sorry` in the retained independent Palomar Challenges and custom
macros in supporting proofs. Those are not proof axioms: the solution does not
import a Challenge, and this batch uses only standard-axiom proofs, not
`native_decide`. The axiom audit must report only `propext`, `Classical.choice`,
and `Quot.sound` for each submitted theorem.

`verification/almanac/` records download hashes, static checks, the local build
and axiom output. A local build and these source checks are not a fresh Lean
export replay, NanoDa replay, hosted preview, acceptance, or publication. The
site performs its own build, comparison, axiom checks and both kernel replays.

## Submit this repository

1. Push branch `almanac/batch-2026-10-28` to
   `https://github.com/jaypantone/2026-10-superpermutation-lower-palomar`.
2. Sign in at the [Lean submission form](https://web-production-daed9.up.railway.app/lean/submit).
   Select that repository and the branch, or paste the full commit hash.
3. Read the generated preview, including each statement, current eligibility,
   authors and paper files. Credit Jay Pantone (`jaypantone`); inherited work's
   attribution is retained in the repository notices.
4. Give the source-hosting permission in the form and submit. The judge uses
   the previewed immutable commit even if the branch later moves.
5. Keep the branch until My submissions says Archived. Submit the companion
   repository as a separate batch; an account may have only one batch being
   checked at a time.

This preparation makes no submission and does not push the branch. Both
repositories' `main` references remain unchanged.
