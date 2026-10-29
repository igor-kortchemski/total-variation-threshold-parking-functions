# Parking functions: total variation threshold

[![Private Comparator verification](https://github.com/igor-kortchemski/total-variation-threshold-parking-functions/actions/workflows/private-comparator.yml/badge.svg)](https://github.com/igor-kortchemski/total-variation-threshold-parking-functions/actions/workflows/private-comparator.yml)

This Lean library reconstructs the supplied parking-function manuscript. The active export uses Lean **4.35.0** and Mathlib **`56a005855ea17e0b0958f73ec801ae140b0a1679`**. All 79 implementation modules and both interface modules build; the implementation has complete proofs and only the three standard logical axioms.

The repository is reserved for **private GitHub verification**. The badge and [Actions runs](https://github.com/igor-kortchemski/total-variation-threshold-parking-functions/actions/workflows/private-comparator.yml) require repository access. Hosted Comparator evidence is recorded per run; a completed run verifies only its recorded commit and checks. No public release, Palomar intake, registration or successful full preflight is claimed.

## Mathematical results

Write $P_{n,k}$ for the first $k$ coordinates of a uniform parking function, $Q_{n,k}$ for independent uniform coordinates, and $\mu_n$ for one coordinate's marginal law.

- **Theorem 1.1:** one universal constant $C\ge1$ gives, for every $n\ge2$ and $1\le k\le n$,

$$
\sqrt{\frac{k\log(k+1)}{Cn+k\log(k+1)}}\le d_{\mathrm{TV}}(P_{n,k},Q_{n,k})\le\min\left(1,C\sqrt{\frac{k\log(k+1)}n}\right).
$$

- **Theorem 1.2:** if $k_n\log n/n\to\lambda\in[0,\infty]$, total variation tends to $2\Phi(\sqrt{\lambda/\pi})-1$ for finite $\lambda$, and to one for $\lambda=\infty$.
- **Proposition 1.3:** KL divergence from $P_{n,k}$ to $\mu_n^{\otimes k}$ is at most $k(k-1)\log n/[n(n-1)]$, with the corresponding Pinsker TV bound.

[Challenge.lean](Challenge.lean) gives the actual laws, 19 supporting declarations and these three signatures, with exactly three approved theorem placeholders. [Solution.lean](Solution.lean) imports their complete [Frozen proofs](docs/FROZEN.md). The implementation also proves the introductory corollaries and the separate Pitman–Stanley volume-polynomial remark. [Metadata](formalization.yaml), [Comparator configuration](comparator.json), and [errata and encoding notes](docs/ERRATA-AND-DEVIATIONS.md) describe the scope.

## Completed local verification

| Check | Current Lean 4.35 result |
| --- | --- |
| Build | All 81 sources; 3,444 Lake jobs. [Coverage](evidence/build-coverage.json), [final-source build](evidence/build-final-source.log). |
| Source fidelity | Exactly six proof-only edits in four implementation files; all statement and concrete-law source unchanged. [Review](evidence/active-source-review.md). |
| Implementation kernel replay | 1,570 constants: 1,477 theorems and 93 definitions. The 62,604 reachable constants use only `propext`, `Classical.choice`, `Quot.sound`; a corrupted proof was rejected. [Log](evidence/audit/kernel-replay.log). |
| Statement ABI | Both Challenge and Solution match all three originally approved ABI hashes. [Details](docs/CHALLENGE-FIDELITY.md). |
| Local raw closure diagnostic | Three target `ConstantVal` records and 34,347 supporting constants match, including 24,773 supporting theorem bodies and 4,036 private names. [Log](evidence/closure-comparison.log). This is not the official Comparator. |

[Preparation](docs/PREPARATION.md) distinguishes these checks from hosted Comparator/NanoDa verification and the official full preflight. Earlier Lean 4.34 results are retained only in [historical evidence](evidence/history-4.34/).

## Build and check

From a fresh checkout with the pinned toolchain installed, run these commands sequentially:

```sh
scripts/compile-lock.sh lake exe cache get
scripts/compile-lock.sh lake build
python3 scripts/check-package.py
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb formalization.yaml
scripts/audit-project.sh
```

The build includes `Parking`, `Challenge` and `Solution`. The audit excludes Challenge's deliberate placeholders and replays every implementation declaration in Lean's kernel. The Ruby check validates starter metadata fields; it is not the complete schema or Palomar policy validator. The [private workflow](.github/workflows/private-comparator.yml) provides the supported Linux verification environment; [the full preflight workflow](.github/workflows/palomar-preflight.yml) is a separate, unrun process requiring a later-authorized public snapshot.

## License and provenance

The export is licensed under [Apache-2.0](LICENSE), with retained attribution in [NOTICE](NOTICE) and [Provenance](docs/PROVENANCE.md). The manuscript source, bibliography and PDF are excluded. [Approval](docs/APPROVAL.md) records the export changes and subsequent authorization for a private repository, push and manual verification. The original reference projects and verified development library remain unchanged. AI source review is recorded; independent human peer review is not claimed.
