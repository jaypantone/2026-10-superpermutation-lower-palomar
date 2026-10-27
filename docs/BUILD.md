# Building and checking the proofs

The project pins Lean 4.35.0 and Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`. All project proof sources are
included; the earlier results repository is a source citation, not a build
dependency.

## Lake build

With Elan installed, run these commands from a checkout:

```sh
lake exe cache get
lake build
```

Lake downloads the pinned dependencies and creates build outputs in `.lake`.
Use a checkout outside cloud-synchronized storage, and reuse matching expanded
dependencies where possible. The supplied local tools instead use `~/.elan`
and `~/Library/Caches/LeanShared`, with separate project build directories.

On this Almanac branch the default Lake targets are `AlmanacSolution` and
`AlmanacAxioms`. The site's public rules allow only `-Doption=value` in Lake's
extra compiler arguments, so the former `-j1`/`-M4096` package arguments have
been removed. The local `tools/check.py` runner still passes both limits to
Lean directly, enforces the project lock, and keeps all outputs outside Dropbox.
A plain Lake invocation does not inherit those local resource controls.


## Almanac interface

`AlmanacSolution.lean` provides the theorem `almanac_claim`.
`AlmanacAdapter.lean` connects the proof library's word predicate to
`Almanac.IsSuperpermutation`. The public judge supplies `AlmanacDefs.lean`,
`AlmanacStatement.lean`, and `AlmanacChallenge.lean`; the local copies allow
the interface to be built and checked before submission.

The default Lake targets build the solution and its axiom report. With the
existing shared Lean setup, the equivalent local source checks are:

```sh
python3 -B tools/check.py AlmanacAxioms --receipt almanac-preparation.json
python3 -B tools/check.py AlmanacChallenge --receipt almanac-challenge.json
```

The technical receipts under `verification/almanac/` record source hashes,
repository-rule checks, statement comparison, and the axiom audit. They do
not replace the site's kernel replays. The older Palomar verification is
recorded separately below.

## Verification

The single `comparator.json` selects all seventeen submitted claims. The
Challenge and Solution declare the same names in separate environments; do
not import both into one module. `AxiomCheck.lean` reports the assumptions of the
selected theorems.

Before consolidation, all four result families passed local statement and
axiom comparison, fresh Lean export replay, and NanoDa replay in separate
configurations. Subsequent edits to eleven module comments leave all proof
code unchanged; their before/after hashes are recorded separately. The
verification record identifies the checks performed after combining the
claims into one Challenge and Solution. All seventeen selected declarations
use only the three standard axioms.

A successful Lake build checks the Lean proofs. Comparator additionally
compares the independent statements and checks their axioms; NanoDa provides
an independent kernel replay. The [verification record](../verification.json)
identifies the source snapshots, checks performed, and limitations.
Palomar's own verification and review are separate; see
[the submission guide](PALOMAR.md).

## Local checking tools

`tools/check.py` and `tools/local_compare.py` implement the recorded macOS
checking procedure using shared storage. Their guard permits one compiler per
project, samples aggregate process-group memory against an 8 GiB threshold,
and requires 15 GiB free disk. The default deadline is 300 seconds; the replay
tool accepts an explicit kernel deadline of at most 10,800 seconds. These
tools do not monitor host memory pressure, and their sampled watchdog is not
an operating-system memory cap. A timeout or resource stop is an incomplete
check.

The recorded lower-bound checks used these local tools, with an extended
kernel deadline for the ten-symbol certificate. The verification record
retains the actual limits and outcomes of those historical checks.
