# Palomar submission

This repository contains the statements, proofs, metadata, and pinned build
inputs for a single submission. It has not yet been registered with
Palomar. The [official submission guide](https://palomar-registry.org/how-to-submit)
describes the current process; its requirements were reviewed on 24 October
2026.

## The entry

Submit this repository once, selecting `comparator.json`. It includes all
seventeen claims: the two general lower bounds, thirteen asymptotic statements
and comparisons, and the finite refinements S(10) >= 4,033,379 and
S(14) >= 93,891,141,150.

Use the full 40-character commit SHA. The project directory is the repository
root, and the metadata file is `formalization.yaml`.

The [informal statement](INFORMAL_STATEMENT.md) explains the results, gives
the full formulas, and maps them to the selected Lean declarations.
The independent [Challenge](../Submissions/Challenge.lean) defines coverage
and the bound formulas using only Mathlib imports. Its deliberate proof holes
specify the statements. The [Solution](../Submissions/Solution.lean) is
compiled separately and does not import the Challenge. The configuration
permits only `propext`, `Classical.choice`, and `Quot.sound`, enables NanoDa,
and provides no replaceable definition bodies.

## Static checks

Run the source-size and module-header scan with Python 3:

```sh
python3 scripts/check-lean-sources.py
```

For the metadata and configuration checks, use an external checkout of
[PalomarSubmission at the recorded revision](https://github.com/PalomarRegistry/PalomarSubmission/tree/ad5db9e7ff8b17523d73aeb244aaeabcde810c64):

```sh
python3 scripts/validate-submission.py --palomar-source /path/to/PalomarSubmission
```

The second command requires PyYAML. It uses the pinned official validator and
also enforces the source-type vocabulary in the current submission standard.
These are static checks; they do not run Lean or the independent kernels.
The source scanner is retained from
[the official starter](https://github.com/PalomarRegistry/PalomarTemplate/tree/2891de4c48955af824969a263d31b25e7a9a1406),
under Apache-2.0. Metadata uses schema v0.4.

The repository pins Lean 4.35.0, which meets the current minimum release
requirement. All retained Lean sources use modules and satisfy the source
length limits. The Challenge also satisfies its stricter size and import
limits. The root licence was classified as Apache-2.0; the
[classification record](../verification/licensee.json) preserves the original
check and identifies the unchanged licence and current metadata declaration.

## Verification and registration

The [build guide](BUILD.md) and [verification record](../verification.json)
describe the completed local checks. Local verification is distinct from
Palomar's protected Linux verification and editorial review.

Submit the public repository and chosen commit at
[Palomar's submission page](https://submit.palomar-registry.org/), selecting
`comparator.json`. Palomar verifies the submitted
snapshot on its own public GitHub Actions infrastructure. Human form
intake starts that verification after authentication; it does not require
a separate Actions run in this repository. The agent API route additionally
requires a passing complete hosted preflight at the exact submitted commit.
An agent must not use the human authentication flow to bypass that
requirement. The included preflight workflow has not been run.

After verification, Palomar presents an automated review. Registration is a
subsequent choice made after reading that review. The metadata records the
mathematical sources and states that the research, formalization, and
documents were generated entirely by AI under Jay Pantone's direction.
Inherited contributions retain their credits; agent review is not human
peer review.
