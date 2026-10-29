# Export verification status

The active export uses Lean `v4.35.0` and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. The author approved its migration, licensing and Challenge/Solution interface, then requested private GitHub Comparator verification. The repository must remain private. This preparation has not entered Palomar intake or registration.

## Completed local checks

| Check | Result and evidence |
| --- | --- |
| Build | PASS: all 79 implementation modules plus Challenge and Solution, 3,444 Lake jobs. [Coverage](../evidence/build-coverage.json), [build](../evidence/build-4.35.log), [final-source build](../evidence/build-final-source.log). The project build began empty in an isolated export; completed builds reused only its own valid artifacts and matching dependency caches. |
| Source fidelity | PASS: all 79 development source hashes checked. After comments, 75 files are identical; six proof edits in four files preserve every theorem statement and concrete definition. [Independent adaptation review](../evidence/active-source-review.md), [hash evidence](../evidence/active-source-review.json). |
| Implementation axiom closure | PASS: 1,570 project constants, with 62,604 reachable constants; only `propext`, `Classical.choice` and `Quot.sound`. [Audit log](../evidence/audit/kernel-replay.log). |
| Lean kernel replay | PASS: all 1,477 project theorems and 93 definitions rechecked; types and values retained exactly. A deliberately corrupted proof was rejected. [Audit log](../evidence/audit/kernel-replay.log). |
| Challenge/Solution ABI | PASS: all three type/definition-closure SHA-256 values equal the original approved hashes in both environments. [Challenge output](../evidence/challenge-abi-raw.txt), [Solution output](../evidence/solution-abi-raw.txt), [anchors](../frozen-anchors.json). |
| Local structural diagnostic | PASS: three target `ConstantVal` records and 34,347 supporting `ConstantInfo` records match exactly, including 24,773 supporting theorem bodies and 4,036 private names. [Log](../evidence/closure-comparison.log). No private-helper exclusion or proof-irrelevance shortcut is used. This is not the official Comparator. |

The current [source manifest](../evidence/source-manifest.json) identifies the 81 source files. [Environment evidence](../evidence/environment.json), [proof spelling adaptations](../evidence/structural-proof-adaptations.json), [compatibility repairs](../evidence/toolchain-proof-repairs.json), and [Frozen successor records](../evidence/frozen-successors.json) identify the approved changes. Failed intermediate builds are not evidence of a pass.

## Reproduce local checks

Use a clean checkout, obtain the pinned Mathlib cache, and serialize all Lean commands:

```sh
scripts/compile-lock.sh lake exe cache get
scripts/compile-lock.sh lake build
python3 scripts/check-package.py
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb formalization.yaml
scripts/audit-project.sh
```

`check-package.py` checks the current source manifest, three authorized Challenge holes, copied source blocks, sealed successor hashes, licensing, dependency pins and import quarantine. `check-lean-sources.py` checks the starter's source requirements. The Ruby validator checks starter metadata fields, not the complete schema or binding policy. `audit-project.sh` regenerates the implementation inventory and runs its retained probe under the compile lock; Challenge is excluded from that kernel replay.

The retained [ABI probe](../scripts/frozen_abi.lean.in) and [raw closure probe](../scripts/compare-closures.lean.in) are templates, not production `.lean` files. Temporary probe files must be removed before source scanning. ABI hashes are computed from the exact delimited output blocks, excluding delimiters and the terminal newline. Structural diagnostic success does not replace the export-format comparison or independent kernels.

## Private hosted verification

The authorized [private workflow](../.github/workflows/private-comparator.yml) runs manually in [GitHub Actions](https://github.com/igor-kortchemski/total-variation-threshold-parking-functions/actions/workflows/private-comparator.yml). Read each run's exact source commit and retained report for its actual result before attributing a result to a checkout. Repository access is required to view the run and artifacts.

The [standalone verifier](../scripts/verify-comparator.sh) requires supported Linux and Bubblewrap, authenticated checker inputs and a separate output directory. It records Comparator/Lean/NanoDa outcomes and the separately pinned advisory checker. Its report explicitly distinguishes private standalone verification from the official full Palomar preflight. No hosted pass is inferred from local source, ABI or raw closure checks.

The [official full preflight workflow](../.github/workflows/palomar-preflight.yml) remains unrun. Its public immutable GitHub snapshot and truthful authorization input require a separate authorized publication step; the private-repository request does not authorize changing visibility or submitting to Palomar.

## Historical evidence and pins

All earlier Lean 4.34 records are under [evidence/history-4.34](../evidence/history-4.34/). They document the verified development snapshot and initial export, not current toolchain checks. The original development replay involved 1,574 project declarations; the active 4.35 replay involves 1,570 because generated declarations differ. Source fidelity and the current replay are checked independently.

The retained official references are [policy](https://github.com/PalomarRegistry/PalomarPolicy/tree/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60), [pipeline](https://github.com/PalomarRegistry/PalomarSubmission/tree/14aa8d6b3c2f14a8540605e37144560b9a00e7e7), [template](https://github.com/PalomarRegistry/PalomarTemplate/tree/2891de4c48955af824969a263d31b25e7a9a1406), and [metadata schema](https://github.com/mathlib-initiative/formalization.yaml/tree/99c678e569c7c4c0772db297c5ddd5e4c9b6322e). [Pin evidence](../evidence/policy-pins.json) records the inspected revisions. Source, documentation, scripts and curated evidence are included; dependency caches, build products, temporary probes, drafts and manuscript files are excluded.
