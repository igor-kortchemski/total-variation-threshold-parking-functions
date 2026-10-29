# Total variation threshold for parking functions

[![Build and audit](https://github.com/igor-kortchemski/total-variation-threshold-parking-functions/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/igor-kortchemski/total-variation-threshold-parking-functions/actions/workflows/build.yml)
[![Private proof verification](https://github.com/igor-kortchemski/total-variation-threshold-parking-functions/actions/workflows/private-comparator.yml/badge.svg?branch=main)](https://github.com/igor-kortchemski/total-variation-threshold-parking-functions/actions/workflows/private-comparator.yml)

A Lean formalization of Igor Kortchemski's **A total variation threshold for the first coordinates of uniform parking functions via Lorentzian polynomials**.

How many initial coordinates of a uniform parking function can be approximated by independent uniform variables? The threshold is at scale $n/\log n$. This library proves quantitative total variation bounds, the limiting profile at the threshold, and an entropy comparison with independent marginals.

**[Read the statements](docs/RESULTS.md) · [Explore the proofs](docs/PROOF-GUIDE.md) · [Reproduce the verification](docs/GETTING-STARTED.md)**

The repository is currently private. The article's arXiv link will be added when its identifier is available. Build CI runs on pushes and pull requests; the second badge tracks a separate, manually triggered proof verification. Each badge describes a workflow run: consult its checked commit and [verification scope](docs/VERIFICATION.md).

## Paper and formalization

| Paper | Result | Lean statement | Proof entry point |
| --- | --- | --- | --- |
| Theorem 1.1 | Uniform finite-size total variation bounds | [Main bounds](Parking/Frozen/MainBounds.lean#L38) | [Main bounds proof](Parking/Provider/MainBounds.lean#L38) |
| Theorem 1.2 | Limiting profile, including zero and infinite parameters | [Profile](Parking/Frozen/Profile.lean#L42) | [Profile proof](Parking/Provider/Profile.lean#L46) |
| Proposition 1.3 | KL divergence and total variation bounds against independent marginals | [Decoupling](Parking/Frozen/Decoupling.lean#L41) | [Decoupling proof](Parking/Provider/Decoupling.lean#L46) |

The **[complete correspondence](docs/RESULTS.md)** also covers the intermediate lemmas, introductory consequences, and the separate Pitman–Stanley volume-polynomial remark. The **[notation guide](docs/NOTATION.md)** explains how the paper's objects appear in Lean.

The implementation has complete proofs. [Challenge.lean](Challenge.lean) is a small statement interface with exactly **three deliberate proof placeholders**; [Solution.lean](Solution.lean) imports the complete proofs of those same statements. These placeholders are excluded from the implementation audit. See [how the two files are checked](docs/VERIFICATION.md#challenge-and-solution).

## Quick start

Install Git and [Lean through elan](https://lean-lang.org/install/), then run:

```sh
git clone https://github.com/igor-kortchemski/total-variation-threshold-parking-functions.git
cd total-variation-threshold-parking-functions
scripts/compile-lock.sh lake exe cache get
scripts/compile-lock.sh lake build
```

Cloning requires access while the repository is private. The project selects **Lean 4.35.0** and pins Mathlib to **`56a005855ea17e0b0958f73ec801ae140b0a1679`**. Open the cloned folder in VS Code with the Lean 4 extension to inspect statements and follow definitions.

For prerequisites, audit commands, resource measurements, and troubleshooting, see **[Getting started](docs/GETTING-STARTED.md)**.

## Verification

The automatic [build workflow](.github/workflows/build.yml) builds all 79 implementation modules plus Challenge and Solution, checks source and metadata constraints, and audits all implementation declarations in Lean's kernel. It also checks the allowed axiom dependencies and rejects a deliberately corrupted proof.

The separate [proof verification workflow](.github/workflows/private-comparator.yml) compares the three recorded statements and their concrete definitions with the supplied proofs, then checks the exports with Lean and NanoDa, with con-ron as an additional advisory checker. The other results in the library are covered by the implementation build and kernel audit, not additional Comparator targets.

See **[verification results and exact checked commits](docs/VERIFICATION.md)**. Official Palomar full preflight and registration are separate later steps.

## Errata and deviations

The [source comparison](docs/ERRATA-AND-DEVIATIONS.md) records **0 identified mathematical errata and 6 encoding or elaboration entries** for the supplied manuscript. These include zero-based indexing, extended-real parameters, and explicit versions of estimates. The [proof guide](docs/PROOF-GUIDE.md) describes the project's arguments and its use of Mathlib.

## Citation

Use **[CITATION.cff](CITATION.cff)** for the software citation and record the commit used (`git rev-parse HEAD`). The accompanying paper is:

> Igor Kortchemski. *A total variation threshold for the first coordinates of uniform parking functions via Lorentzian polynomials*.

The arXiv identifier will be added to the citation and project metadata when available. No identifier has been assigned in these files.

## License and provenance

The formalization is licensed under **[Apache-2.0](LICENSE)**; retained contributions are credited in [NOTICE](NOTICE) and [Provenance](docs/PROVENANCE.md). Manuscript source and PDF are not included, and the code license does not license the article. Proof development and source review used AI assistance under the author's direction; independent human peer review is not claimed.
