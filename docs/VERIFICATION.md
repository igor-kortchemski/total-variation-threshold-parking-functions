# Verification

[Overview](../README.md) · [Results](RESULTS.md) · [Getting started](GETTING-STARTED.md)

## What each check establishes

| Check | Scope | Where to inspect it |
| --- | --- | --- |
| Automatic build and audit | All 79 implementation modules plus Challenge and Solution build. Source and metadata constraints pass. All implementation declarations undergo an axiom-dependency audit and Lean-kernel replay, with an invalid-proof negative control. | [Build workflow](../.github/workflows/build.yml), [runs](https://github.com/igor-kortchemski/total-variation-threshold-parking-functions/actions/workflows/build.yml) |
| Manual proof verification | The three declarations in `comparator.json`, including their concrete statement definitions, are compared between Challenge and Solution. The exported proofs are checked by Lean and NanoDa; con-ron is an additional advisory check. | [Comparator configuration](../comparator.json), [workflow](../.github/workflows/private-comparator.yml), [runs](https://github.com/igor-kortchemski/total-variation-threshold-parking-functions/actions/workflows/private-comparator.yml) |
| Source correspondence review | Definitions, assumptions, endpoint cases, and the paper's proof routes are compared with the formalization. This is an AI-assisted source review, distinct from kernel checking. | [Results](RESULTS.md), [errata and deviations](ERRATA-AND-DEVIATIONS.md), [source review](../evidence/active-source-review.md) |
| Official Palomar full preflight | The official pipeline checks its exact submitted repository snapshot and configuration. | [Workflow](../.github/workflows/palomar-preflight.yml), [runs](https://github.com/igor-kortchemski/total-variation-threshold-parking-functions/actions/workflows/palomar-preflight.yml); inspect the exact commit and completed report |

The additional lemmas, introductory consequences, and geometric remark are included in the implementation build and kernel audit. They are not separately selected targets of the three-result Comparator configuration. No independent human peer review is claimed.

## Registered snapshot

**[PALOMAR-2026-10-30-000007, version 1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-30-000007&version=1)** was registered on 30 October 2026. It records [v1.0.1](https://github.com/igor-kortchemski/total-variation-threshold-parking-functions/releases/tag/v1.0.1), commit [`f5daa3e5871a3d9e9c853334ca5b2e528f2309aa`](https://github.com/igor-kortchemski/total-variation-threshold-parking-functions/tree/f5daa3e5871a3d9e9c853334ca5b2e528f2309aa), with the three targets in `comparator.json`.

The [official submission verification](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/41020160464) passed with no errors or warnings: Comparator confirmed the statements, Lean and NanoDa accepted the proofs, and con-ron accepted all 60,681 exported declarations. The official automated editorial review identified no blocking problems, nonblocking warnings, comments or requested changes. The public Palomar record includes that review and the source-preservation record.

The same commit passed the [implementation build and audit](https://github.com/igor-kortchemski/total-variation-threshold-parking-functions/actions/runs/41017773613) and [official full preflight](https://github.com/igor-kortchemski/total-variation-threshold-parking-functions/actions/runs/41017884101); their reports are retained as v1.0.1 release assets. The registered tag remains fixed. Later documentation or citation commits on `main` do not change the source snapshot recorded by Palomar.

## Read the commit, not just the badge

The build badge follows the `main` branch's build workflow. Pull-request runs check GitHub's proposed merge commit. The full-preflight badge follows the latest manual run on `main`; it may describe an earlier commit than the current branch head. Open the run and inspect its SHA and report before attributing a result to a checkout.

The [v1.0.0 release](https://github.com/igor-kortchemski/total-variation-threshold-parking-functions/releases/tag/v1.0.0) retains successful [build/audit](https://github.com/igor-kortchemski/total-variation-threshold-parking-functions/actions/runs/40884107088) and [private proof-verification](https://github.com/igor-kortchemski/total-variation-threshold-parking-functions/actions/runs/40884237199) reports at commit `e154f9e40cc35bb795d3e007b13186bd028f62e0`. Comparator, Lean, NanoDa, con-ron, all six controls and source-integrity checks passed there; both report archives are attached to that release. An earlier retained [private run](https://github.com/igor-kortchemski/total-variation-threshold-parking-functions/actions/runs/40841476149) passed at `fee7091b77e32a82b771207093f084de0d3bb67a`. These are historical results for their recorded commits. Later builds and official full preflights carry their own exact source commit and report.

Build reports include the checked commit, step outcomes, timings, resource measurements, and logs. Comparator reports additionally identify the configuration, target declarations, tool pins, kernel outcomes, and source hashes. Download artifacts while available if you need a durable local record; the workflows specify their retention periods.

## Challenge and Solution

[Challenge.lean](../Challenge.lean) is the small statement interface intended for inspection. It defines the actual objects used in the results and contains exactly three authorized `by sorry` proof bodies:

- `Parking.tvDist_firstCoordsLaw_bounds`;
- `Parking.tendsto_tvDist_firstCoordsLaw`;
- `Parking.klDiv_tvDist_firstCoordsLaw_le`.

[Solution.lean](../Solution.lean) imports the complete proofs of the same declarations from the three [Frozen modules](FROZEN.md). “Frozen” means that the statement and its defining context are preserved while the proof is assembled through the corresponding provider. The implementation does not import Challenge. Comparator checks that Solution proves the declarations stated by Challenge, with the permitted axioms.

The implementation's allowed axioms are **`propext`, `Classical.choice`, and `Quot.sound`**. Its audit excludes Challenge's deliberate placeholders; it permits no implementation proof hole, custom axiom, or trusted-computation shortcut. [Challenge fidelity](CHALLENGE-FIDELITY.md) documents the statement and definition comparisons.

## Retained Lean 4.35 evidence

The existing [implementation audit](../evidence/audit/kernel-replay.log) covers **1,570 declarations: 1,477 theorems and 93 definitions**, with **62,604 reachable constants**. It reports only the three allowed axioms and rejects a corrupted proof. The [source manifest](../evidence/source-manifest.json) identifies the checked Lean sources. Future runs determine their own counts from their checked source.

The [full preparation record](PREPARATION.md) contains the build, source fidelity, frozen-interface hashes, and diagnostic evidence. Earlier Lean 4.34 results are retained under [historical evidence](../evidence/history-4.34/) and are not current toolchain verification. The local raw-closure diagnostic is distinct from the hosted Comparator check.

## Reproduce and interpret the results

Follow [Getting started](GETTING-STARTED.md) for the fresh-checkout build and full implementation audit. The [manual workflow](../.github/workflows/private-comparator.yml) supplies the Linux sandbox and authenticated toolchain inputs required for the standalone proof check. Its private-repository guard remains in force. For the now-public repository, use the [official full preflight](../.github/workflows/palomar-preflight.yml); earlier private results remain available in the v1.0.0 release assets.

An incomplete, cancelled, or failed run does not establish a pass. A resource or bootstrap failure needs diagnosis before it can say anything about the proofs. The independent con-ron checker is advisory under the pinned policy; its reported acceptance or decline is separate from the mandatory Lean and NanoDa outcomes.

The README, citation file and mathematical-source metadata identify [arXiv:2610.40082v1](https://arxiv.org/abs/2610.40082v1). The [source comparison](../evidence/arxiv-v1-correspondence.json) preserves the historical manuscript hashes and checks its mathematical statements and proofs. The official Palomar full preflight must pass on the final public commit before intake. Neither a private check nor a full preflight constitutes registry submission or registration.
